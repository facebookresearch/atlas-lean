/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.CovarianceBanding

@[expose] public section

open Matrix Finset
open scoped Matrix.Norms.L2Operator

open MathlibExt.Probability.Statistics.CovarianceBanding

namespace MathlibExtTest.Probability.Statistics.CovarianceBanding

/-- Banding at width `0` keeps exactly the diagonal. -/
example (M : Matrix (Fin 3) (Fin 3) ℝ) : band 0 M 0 1 = 0 ∧ band 0 M 2 2 = M 2 2 := by
  simp [band_apply]

/-- Banding at width `1` keeps the first off-diagonals and drops the corner entry. -/
example (M : Matrix (Fin 3) (Fin 3) ℝ) : band 1 M 0 1 = M 0 1 ∧ band 1 M 0 2 = 0 := by
  simp [band_apply]

/-- The class `U(ε₀, α, C)` is not empty: it contains the identity matrix. -/
theorem one_mem_bandableClass (α : ℝ) {C : ℝ} (hC : 0 ≤ C) :
    (1 : Matrix (Fin 3) (Fin 3) ℝ) ∈ bandableClass 1 α C := by
  refine ⟨Matrix.transpose_one, fun x => by simp, fun k hk j => ?_⟩
  have h0 : ∑ i ∈ univ.filter (fun i : Fin 3 => k < ((i : ℤ) - j).natAbs),
      |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| = 0 := by
    refine sum_eq_zero fun i hi => ?_
    simp only [mem_filter, mem_univ, true_and] at hi
    have hij : i ≠ j := by
      rintro rfl
      simp at hi
    simp [Matrix.one_apply_ne hij]
  rw [h0]
  positivity

/-- The uniform bias bound (A6) applied to the identity matrix with `k = 2`. -/
example : ‖band 2 (1 : Matrix (Fin 3) (Fin 3) ℝ) - 1‖ ≤ 1 * (2 : ℝ) ^ (-(1 : ℝ)) :=
  norm_band_sub_le_of_mem_bandableClass zero_le_one (one_mem_bandableClass 1 zero_le_one)
    (by norm_num)

/-- The variance bound: a `4 × 4` matrix with entries in `[-1, 1]`, banded at width `1`, has
operator norm at most `3`. -/
example (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : ∀ i j, |A i j| ≤ 1) : ‖band 1 A‖ ≤ 3 := by
  have := norm_band_le 1 zero_le_one hA
  norm_num at this
  exact this

end MathlibExtTest.Probability.Statistics.CovarianceBanding
