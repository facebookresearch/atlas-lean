/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalksSelfConvolution
import Mathlib.Tactic.NormNum

/-! # Tests for higher-order Fibonacci self-convolution -/

namespace MathlibExtTest.NumberTheory.Recurrences.HigherFibonacciWalksSelfConvolution

open MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalksWanted

-- At the first admissible index for order two the shifted index is zero, so both weighted
-- sums and both first moments are empty.
example (F : ℤ → ℚ) (hF : IsStandardHigherFib 2 F) :
    (∑ i ∈ Finset.range 3, F (i : ℤ) * F (2 - (i : ℤ))) = 1 := by
  simpa [weightedHigherFibSum, weightedHigherFibMomentSum] using
    (higherFib_selfConvolution_eq_weighted_sums 2 (by decide) F hF 2 (by decide)).2

-- At order one the shift vanishes and the moment sums are nonempty at n = 3.
example : (∑ _i ∈ Finset.range 4, (1 : ℚ) * 1) = 4 := by
  have hF : IsStandardHigherFib 1 (fun _ => 1) := by
    simp [IsStandardHigherFib, IsHigherFibRecurrence]
  convert (higherFib_selfConvolution_eq_weighted_sums 1 le_rfl (fun _ => 1) hF 3
    (by decide)).2 using 1
  decide +kernel

-- The ordinary Fibonacci sequence gives a nonzero shift and nonempty weighted sums at n = 5.
example : (∑ i ∈ Finset.range 6, fibQ (i : ℤ) * fibQ (5 - (i : ℤ))) = 10 ∧
      higherFibWalk fibQ 2 3 = 10 := by
  have hF : IsStandardHigherFib 2 fibQ := by
    refine ⟨?_, ?_, by decide⟩
    · intro n
      have h := Int.fib_add_two (n - 2)
      rw [show n - 2 + 2 = n by omega, show n - 2 + 1 = n - 1 by omega] at h
      simp only [Finset.sum_range_succ, Finset.sum_range_zero,
        zero_add, Nat.cast_zero, Nat.cast_one, sub_zero, fibQ]
      rw [← Int.cast_add, show n - 1 - 1 = n - 2 by omega]
      exact_mod_cast h.trans (add_comm _ _)
    · intro i hi
      have : i = 0 := by omega
      subst i
      decide
  obtain ⟨hshift, hweighted⟩ :=
    higherFib_selfConvolution_eq_weighted_sums 2 (by decide) fibQ hF 5 (by decide)
  have hconv : (∑ i ∈ Finset.range 6, fibQ (i : ℤ) * fibQ (5 - (i : ℤ))) = 10 := by
    convert hweighted using 1
    decide +kernel
  exact ⟨hconv, hshift.symm.trans hconv⟩

end MathlibExtTest.NumberTheory.Recurrences.HigherFibonacciWalksSelfConvolution
