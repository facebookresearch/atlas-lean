/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SuperFibocatalan

/-! # Boundary and sign checks for the Fibonacci product identity -/

open MathlibExt.NumberTheory.SuperFibocatalanWanted

example : (Nat.fib 0 : ℤ) * Nat.fib 2 - (Nat.fib 2 : ℤ) * Nat.fib 0 = 0 :=
  fib_mul_sub_mul 0

example : (Nat.fib 6 : ℤ) * Nat.fib 5 - (Nat.fib 8 : ℤ) * Nat.fib 3 = -2 :=
  fib_mul_sub_mul 3

example : (Nat.fib 8 : ℤ) * Nat.fib 6 - (Nat.fib 10 : ℤ) * Nat.fib 4 = 3 :=
  fib_mul_sub_mul 4
