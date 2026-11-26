/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SquaresTriangularRepresentationsSumOfSquaresRepCountIntegerRoot

/-!
# Tests for integer zeros of the sums-of-squares counting polynomial
-/

namespace MathlibExtTest.NumberTheory.SquaresTriangularRepresentationsSumOfSquaresRepCountIntegerRoot

open MetaMathlibExt

-- The counting polynomial for `n = 1` vanishes at `0` and takes value `2` at `1`.
example : ∃ P : Polynomial ℤ, P.eval 0 = 0 ∧ P.eval 1 = 2 := by
  obtain ⟨P, hP, -⟩ := sumOfSquaresRepCount_integer_root 1
  refine ⟨P, ?_, ?_⟩
  · have h0 := hP 0
    have hr0 : sumOfSquaresRepCount 0 1 = 0 := by
      simp only [sumOfSquaresRepCount, zpow_zero, Units.val_one, PowerSeries.coeff_one]
      decide
    simp only [hr0, mul_zero] at h0
    exact h0
  · have h1 := hP 1
    rw [sumOfSquaresRepCount_one, coeff_squareThetaSeries_small.2.1] at h1
    simpa using h1

-- Every nonzero integer zero of `r_·(1)` divides a fixed integer.
example : ∃ c : ℤ, ∀ k : ℤ, k ≠ 0 → sumOfSquaresRepCount k 1 = 0 → k ∣ c := by
  obtain ⟨P, -, hP⟩ := sumOfSquaresRepCount_integer_root 1
  exact ⟨P.coeff 1, fun k hk h0 => (hP k hk h0).1⟩

end MathlibExtTest.NumberTheory.SquaresTriangularRepresentationsSumOfSquaresRepCountIntegerRoot
