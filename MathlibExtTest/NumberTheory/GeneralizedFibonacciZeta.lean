/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralizedFibonacciZeta
import Mathlib.Data.Int.Fib.Basic

open MetaMathlibExt

/-- At order two the initial window consists only of zero, so integer Fibonacci is a witness. -/
private theorem fib_is_order_two : IsLGeneralizedFibonacci 2 Int.fib := by
  refine ⟨fun n hlo hhi => ?_, Int.fib_one, fun n _ => ?_⟩
  · have : n = 0 := by omega
    simp [this]
  · have h := Int.fib_add_two (n - 2)
    simp [Finset.sum_range_succ]
    convert h using 1 <;> ring_nf

-- A nonreal exponent with real part strictly between zero and one.
example :
    Summable (fun j : ℕ => ‖(Int.fib ((j : ℤ) + 1) : ℂ) ^ (-((2 : ℂ)⁻¹ + Complex.I))‖) := by
  apply lGeneralizedFibonacciZeta_summable 2 (by decide) Int.fib fib_is_order_two
  norm_num
