/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralizedFibonacciZeta
import Mathlib.Data.Int.Fib.Basic
import Mathlib.NumberTheory.Real.GoldenRatio

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

-- Even order: for the Fibonacci recurrence with the golden ratio and `k = 1`, the possible poles
-- `-2 + πi(2n + 1) / log φ` sit at odd multiples of `πi / log φ`.
example (n : ℤ) :
    -(2 : ℂ) + Complex.I * Real.pi * (2 * n + 1) / Complex.log Real.goldenRatio ∈
      lGeneralizedFibonacciZetaPoleSet 2 Real.goldenRatio := by
  have h := lGeneralizedFibonacciZeta_corollaryPole_mem 2 le_rfl Real.goldenRatio
    Real.one_lt_goldenRatio (by simp [Finset.sum_range_succ, Real.goldenRatio_sq, add_comm]) 1
    (by norm_num) n
  convert h using 1
  simp [lGeneralizedFibonacciZetaCorollaryPole]

-- Odd order: at `ℓ = 3` with `k = 4` (so `q = 2`), the possible poles `-6 + 2πin / log α` sit
-- at even multiples of `πi / log α`, for the dominant root `α` of `X³ - X² - X - 1`.
example (α : ℝ) (hα : 1 < α) (hroot : α ^ 3 = 1 + α + α ^ 2) (n : ℤ) :
    -(6 : ℂ) + Complex.I * (2 * n * Real.pi) / Complex.log α ∈
      lGeneralizedFibonacciZetaPoleSet 3 α := by
  have h := lGeneralizedFibonacciZeta_corollaryPole_mem 3 (by norm_num) α hα
    (by simp [Finset.sum_range_succ, hroot]) 4 (by norm_num) n
  convert h using 1
  simp [lGeneralizedFibonacciZetaCorollaryPole, show ¬ Even 3 by decide]
