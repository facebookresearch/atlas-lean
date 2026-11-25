/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.Recurrences.TribonacciSumOfProducts
import MathlibExt.NumberTheory.TribonacciInt

/-! # Endpoint tests for the Tribonacci product sum -/

namespace MathlibExtTest.TribonacciSumOfProducts

open MathlibExt.NumberTheory.Recurrences.TribonacciTetranacciSumsOfSquaresWanted MetaMathlibExt

example (T : ℤ → ℤ) (hT : ∀ m : ℤ, T (m + 3) = T (m + 2) + T (m + 1) + T m) :
    4 * (∑ k ∈ Finset.Icc (1 : ℕ) 0, T k * T ((k : ℤ) - 2)) = 0 := by
  rw [four_mul_sum_tribonacci_mul_sub_two T hT]
  simp

-- The shift gives T(-1) = 2 and T(1) = -1, so the first product is negative.
example : 4 * (∑ k ∈ Finset.Icc (1 : ℕ) 1,
    tribonacciInt (-4 + k) * tribonacciInt (-4 + ((k : ℤ) - 2))) = -8 := by
  rw [four_mul_sum_tribonacci_mul_sub_two (fun m => tribonacciInt (-4 + m))
    (fun m => by simpa only [← add_assoc] using tribonacciInt_add_three (-4 + m))]
  decide

end MathlibExtTest.TribonacciSumOfProducts
