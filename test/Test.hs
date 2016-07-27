{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Data.Normalization

import Test.Tasty
import Test.Tasty.QuickCheck

main :: IO ()
main = defaultMain suite

suite :: TestTree
suite = testGroup "Normalization" [test1, test2]

test1 :: TestTree
test1 = testProperty "denormalize ∘ normalize = id" $
  \(a :: [Int]) -> (denormalize . normalize) a == a

test2 :: TestTree
test2 = testProperty "denormalize² ∘ normalize² = id" $
  \(a :: [Int]) -> (denormalize . denormalize . normalize . normalize) a == a
