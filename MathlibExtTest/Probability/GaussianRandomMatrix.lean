/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.GaussianRandomMatrix

/-!
# Tests for the largest singular value of a Gaussian matrix

We specialize the tail estimate to a single entry and check the empty-column event.
-/

open MeasureTheory ProbabilityTheory Matrix
open MathlibExt.Probability.GaussianRandomMatrixWanted

namespace MathlibExtTest.Probability.GaussianRandomMatrix

/-- For a single entry, `δ = 1` sets the absolute-value threshold to three. -/
example :
    (Measure.pi fun _ : Fin 1 × Fin 1 => gaussianReal 0 1).real
      {x | 3 ≤ |x (0, 0)|} ≤ Real.exp (-(1 : ℝ) / 2) := by
  have h := measureReal_sigmaMax_ge_le 1 1 (δ := 1) (hδ := zero_le_one)
  simp only [Nat.cast_one, Real.sqrt_one, one_mul, one_pow, neg_one_mul] at h
  refine (measureReal_mono ?_).trans h
  intro x hx
  have hxx : (3 : ℝ) ^ 2 ≤ x (0, 0) ^ 2 := by
    simpa [sq_abs] using (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 3) (abs_nonneg _)).mpr hx
  refine ⟨fun _ => 1, ?_, ?_⟩
  · intro he
    have := congrFun he (0 : Fin 1)
    norm_num at this
  · simpa [Fin.sum_univ_one, Matrix.mulVec, dotProduct,
      show (1 + 1 + 1 : ℝ) = 3 by norm_num] using hxx

/-- With zero columns, the amplification event has probability zero. -/
example (n : ℕ) (t : ℝ) :
    (Measure.pi fun _ : Fin n × Fin 0 => gaussianReal 0 1).real
      {x | ∃ u : Fin 0 → ℝ, u ≠ 0 ∧ t ^ 2 * ∑ j, u j ^ 2 ≤
        ∑ i, (Matrix.of (fun i j => x (i, j)) *ᵥ u) i ^ 2} = 0 := by
  simp

end MathlibExtTest.Probability.GaussianRandomMatrix
