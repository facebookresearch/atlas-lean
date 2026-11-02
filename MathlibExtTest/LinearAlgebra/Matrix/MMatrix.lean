/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.Matrix.MMatrix

/-! Tests for Hurwitz matrices and nonsingular M-matrices: positive scalar matrices are
nonsingular M-matrices (non-vacuity witness), their inverses are nonnegative, a matrix with a
positive off-diagonal entry is not a Z-matrix, and the Collatz–Wielandt bound for a
permutation matrix. -/

open Matrix

namespace MathlibExtTest.LinearAlgebra.Matrix.MMatrix

/-- The complexification of the real scalar matrix `c • 1` is the complex scalar `c`. -/
theorem map_smul_one (c : ℝ) :
    (c • (1 : Matrix (Fin 2) (Fin 2) ℝ)).map (algebraMap ℝ ℂ) =
      algebraMap ℂ (Matrix (Fin 2) (Fin 2) ℂ) (c : ℂ) := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.algebraMap_matrix_apply, h]

/-- The spectrum of the real scalar matrix `c • 1` is `{c}`. -/
theorem spectrum_smul_one (c : ℝ) :
    spectrum ℂ ((c • (1 : Matrix (Fin 2) (Fin 2) ℝ)).map (algebraMap ℝ ℂ)) = {(c : ℂ)} := by
  rw [map_smul_one, spectrum.scalar_eq]

/-- A negative scalar matrix is Hurwitz. -/
theorem isHurwitz_smul_one {c : ℝ} (hc : c < 0) :
    (c • (1 : Matrix (Fin 2) (Fin 2) ℝ)).IsHurwitz := by
  intro μ hμ
  rw [spectrum_smul_one, Set.mem_singleton_iff] at hμ
  simpa [hμ] using hc

/-- **Non-vacuity witness.** For `c > 0`, `c • 1` is a nonsingular M-matrix. -/
theorem isNonsingularMMatrix_smul_one {c : ℝ} (hc : 0 < c) :
    (c • (1 : Matrix (Fin 2) (Fin 2) ℝ)).IsNonsingularMMatrix := by
  refine ⟨fun i j hij => by simp [hij], ?_⟩
  rw [← neg_smul]
  exact isHurwitz_smul_one (by linarith)

/-- Its inverse is entrywise nonnegative, and it is invertible. -/
example : IsUnit ((2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    ∀ i j, 0 ≤ ((2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))⁻¹ i j :=
  ⟨(isNonsingularMMatrix_smul_one two_pos).isUnit,
    (isNonsingularMMatrix_smul_one two_pos).inv_nonneg⟩

/-- A matrix with a positive off-diagonal entry is not a Z-matrix. -/
example : ¬ (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).IsZMatrix := by
  intro h
  have := h 0 1 (by decide)
  norm_num at this

/-- `0` has spectral radius `0 < 1`, so `(1 - 0)⁻¹ = 1` is nonnegative. -/
example (i j : Fin 2) : 0 ≤ (1 - (0 : Matrix (Fin 2) (Fin 2) ℝ))⁻¹ i j := by
  refine inv_one_sub_nonneg (K := 0) (fun _ _ => le_rfl) ?_ i j
  rw [Matrix.map_zero _ (map_zero _), spectralRadius, quasispectrum_eq_spectrum_union_zero,
    spectrum.zero_eq]
  simp

/-- **Collatz–Wielandt.** The swap matrix fixes `(1, 1)`, so its spectral radius is `≥ 1`. -/
example : ENNReal.ofReal 1 ≤
    spectralRadius ℂ ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ).map (algebraMap ℝ ℂ)) := by
  refine le_spectralRadius_of_smul_le_mulVec (z := fun _ => 1) ?_ (fun _ => zero_le_one) ?_
    zero_le_one ?_
  · intro i j; fin_cases i <;> fin_cases j <;> simp
  · intro h; simpa using congr_fun h 0
  · intro i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

end MathlibExtTest.LinearAlgebra.Matrix.MMatrix
