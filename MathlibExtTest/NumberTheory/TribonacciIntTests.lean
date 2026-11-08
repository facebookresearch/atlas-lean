/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.TribonacciInt

@[expose] public section

open MetaMathlibExt

example : tribonacciInt 3 = 2 := by rfl

example : tribonacciInt (-4) = 0 := by rfl

example (n : ℤ) :
    tribonacciInt (n + 3) = tribonacciInt (n + 2) + tribonacciInt (n + 1) + tribonacciInt n :=
  tribonacciInt_add_three n

example (n : ℕ) : tribonacciInt (n : ℤ) = (tribonacci (n + 1) : ℤ) :=
  tribonacciInt_nat_eq n
