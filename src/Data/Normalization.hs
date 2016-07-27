{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GADTs #-}

{- |

Normalization toolkit. At the most basic level, normalization is assigning
keys to values to minimize data redundancy. Say you have a tree of values:

@
banana
├── apple
│   ├── cherry
│   │   └── tomato
│   ├── lemon
│   ├── peach
│   │   ├── tomato
│   │   ├── peach
│   │   └── apple
│   ├── lemon
│   └── tomato
└── lemon
@

Note that there are duplicate objects. Now, it poses some problems:

  * if you want to update an object, you have to update all its instantiations;
  * if there are expensive operations on the objects, you have to perform
    them for each instantiation separately or maintain a HashMap (and thus
    perform a lot of 'hash' and '==' operations to identify objects).

To avoid these issues, we'd rather store the objects in a vector and store
their indices in the tree instead:

@
0        1       2        3        4       5
banana | apple | cherry | tomato | lemon | peach
@

@
0
├── 1
│   ├── 2
│   │   └── 3
│   ├── 4
│   ├── 5
│   │   ├── 3
│   │   ├── 5
│   │   └── 1
│   ├── 4
│   └── 3
└── 4
@

Although it solves the aforementioned problems, the naive implementation
creates new ones:

  * we need to pass the vector manually to fetch the values;
  * if there are multiple vectors it is easy to make a mistake and perform
    a lookup in the wrong one, creating hard-to-detect bugs that manifest
    themselves as out-of-bounds errors (if you're lucky).

Using some type-level machinery, this normalization toolkit suffers from
none of the above problems. Enjoy your normalized data!

-}

module Data.Normalization
  (
  -- * Core definitions
    type (~~>)
  , Key
  , Scope(..)
  , withScope
  , hoistScope
  , UnsafeScope(..)
  , fromUnsafeScope
  , toUnsafeScope
  , normalize
  , denormalize
  , fetch
  -- * Relations
  , VectorOf
  , mkVectorOf
  , fetchFrom
  -- * Re-exports
  , Proxy(..)
  , Reifies(..)
  , reify
  ) where

import Control.Monad.State.Strict as State
import Control.Monad.ST as ST
import Data.Hashable
import Data.Traversable
import Data.Proxy
import Data.List as List
import Data.Reflection
import Data.Vector as Vector
import Data.Vector.Mutable as MVector
import Data.Vector.Binary ()
import Data.Map.Lazy as Map
import Control.Lens (itraverse_)
import GHC.Generics (Generic)
import Data.Binary as Bin
import Data.Coerce
import Data.Function
import Unsafe.Coerce
import Test.QuickCheck

{- |

In a context where @i '~~>' a@ is satisfied, the 'fetch' function can be used
to retrieve an 'a' by its @'Key' i@. You can think of the @i@ type variable as
the table name, and @'Key' i@ points to an object in the table @i@. It makes
sure that:

* all lookups happen in the correct tables;
* the tables are passed automatically.

-}
class Reifies i (Vector a) => (~~>) i a | i -> a

instance Reifies i (Vector a) => (~~>) i a

{- |

An integer key parametrized by its scope. The constructor is not exported
intentionally: to construct a key you have to perform normalization. This gives
us some desirable properties:

* all keys point to existing objects;
* all keys point to distinct objects.

-}
newtype Key i = Key Int
  deriving (Eq, Ord, Show, Hashable)

-- | A scope consists of a container with keys and a vector of objects
-- referenced by those keys.
data Scope f a where
  Scope :: (i ~~> a) => f (Key i) -> Scope f a

-- | The existential deconstructor.
withScope
  :: (forall (i :: k) . (i ~~> a) => f (Key i) -> r)
  -> Scope f a
  -> r
withScope cont (Scope fk) = cont fk
{-# INLINE withScope #-}

infix 8 `withScope`

-- | Map a natural transformation over a scope.
hoistScope
  :: (forall (i :: k) . f (Key i) -> g (Key i))
  -> Scope f a
  -> Scope g a
hoistScope nt (Scope fk) = Scope (nt fk)
{-# INLINE hoistScope #-}

instance (Traversable f, Ord a, Arbitrary (f a)) => Arbitrary (Scope f a) where
  arbitrary = normalize <$> arbitrary
  shrink = List.map normalize . shrink . denormalize

instance Functor f => Functor (Scope f) where
  fmap f = fromUnsafeScope . fmap f . toUnsafeScope

instance Functor f => Foldable (Scope f) where
  foldMap f = foldMap f . toUnsafeScope

instance Functor f => Traversable (Scope f) where
  traverse f = fmap fromUnsafeScope . traverse f . toUnsafeScope

instance (Eq (UnsafeScope f a), Functor f) => Eq (Scope f a) where
  (==) = (==) `on` toUnsafeScope

instance (Ord (UnsafeScope f a), Functor f) => Ord (Scope f a) where
  compare = compare `on` toUnsafeScope

instance (Show (UnsafeScope f a), Functor f) => Show (Scope f a) where
  showsPrec n = showsPrec n . toUnsafeScope

instance (Binary (UnsafeScope f a), Functor f) => Binary (Scope f a) where
  get = fromUnsafeScope <$> Bin.get
  put = Bin.put . toUnsafeScope

-- | An unsafe version of 'Scope'. Useful for intermediate manipulations.
data UnsafeScope f a = UnsafeScope (Vector a) (f Int)
  deriving (Generic, Functor, Foldable, Traversable)

deriving instance (Eq a, Eq (f Int)) => Eq (UnsafeScope f a)

deriving instance (Ord a, Ord (f Int)) => Ord (UnsafeScope f a)

deriving instance (Show a, Show (f Int)) => Show (UnsafeScope f a)

instance (Binary a, Binary (f Int)) => Binary (UnsafeScope f a)

-- | Hail parametricity for the safety guarantees it grants us.
-- 'fmap coerce = unsafeCoerce' for any law-abiding 'Functor'.
fmapCoerce :: (Functor f, Coercible a b) => f a -> f b
fmapCoerce = unsafeCoerce

-- | Convert an unsafely constructed scope to a scope. It is the caller's
-- responsibility to verify that the unsafely constructed scope is well-formed.
-- That is, there should be no out-of-scope references. There can be runtime
-- failures otherwise. Avoid using this function if you don't know what you're
-- doing. O(1).
fromUnsafeScope :: forall f a . Functor f => UnsafeScope f a -> Scope f a
fromUnsafeScope (UnsafeScope vec fa) = reify vec (Scope . mkF)
  where
    mkF :: (i ~~> a) => Proxy i -> f (Key i)
    mkF _ = fmapCoerce fa

-- | Discard the safety guarantees and convert a scope to an unsafe scope.
-- This is, in fact, a safe function. O(1).
toUnsafeScope :: forall f a . Functor f => Scope f a -> UnsafeScope f a
toUnsafeScope (Scope fk) = UnsafeScope (vecOf fk) (fmapCoerce fk)
  where
    vecOf :: forall i . (i ~~> a) => f (Key i) -> Vector a
    vecOf _ = reflect (Proxy :: Proxy i)

-- | Normalize values in a container. E.g if you have a list of objects
-- @[obj0, obj1, obj2, obj1]@, after normalization you will have a list of
-- indices @[0, 1, 2, 1]@ and a vector @[obj0, obj1, obj2]@. Left-biased.
normalize :: (Traversable f, Ord a) => f a -> Scope f a
normalize fa = fromUnsafeScope (UnsafeScope vec f')
  where
    -- Replace all values with their indices and collect the actual values
    -- in a Map from values to indices, then invert this Map to get a
    -- Vector of values.
    (f', unsafeInvertMap -> vec) = (`runState` Map.empty) $ do
      for fa $ \a -> do
        acc <- State.get
        let
          n           = Map.size acc
          (mk', acc') = Map.insertLookupWithKey (\_ _ k -> k) a n acc
        case mk' of
          Just k  -> return k
          Nothing -> n <$ State.put acc'

-- | Precondition (unchecked): the 'Int' values in the 'Map' should be
-- continuous and start from 0.
unsafeInvertMap :: Ord a => Map a Int -> Vector a
unsafeInvertMap m = runST $ do
  vec <- MVector.unsafeNew (Map.size m)
  itraverse_ (\a i -> MVector.unsafeWrite vec i a) m
  Vector.unsafeFreeze vec

-- | Inverse of 'normalize'. The objects remain shared in memory.
denormalize :: Traversable f => Scope f a -> f a
denormalize = withScope (fmap fetch)

-- | Fetch a normalized value. O(1).
fetch :: (i ~~> a) => Key i -> a
fetch k@(Key i) = Vector.unsafeIndex (reflect k) i
{-# INLINE fetch #-}

-- | A vector of values derived from normalized values.
-- Parametrized by its scope.
newtype VectorOf i a = VectorOf (Vector a)
  deriving (Functor, Foldable, Traversable)

-- | Fetch from a derived vector. O(1).
fetchFrom :: VectorOf i a -> Key i -> a
fetchFrom (VectorOf vec) (Key i) = Vector.unsafeIndex vec i
{-# INLINE fetchFrom #-}

-- | Derive a vector using a function.
mkVectorOf :: forall i a b . (i ~~> a) => (a -> b) -> VectorOf i b
mkVectorOf f = VectorOf (Vector.map f vec)
  where
    vec = reflect (Proxy :: Proxy i)
