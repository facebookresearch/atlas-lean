/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.LinearAlgebra.Matrix.GeneralizedHouseholder

open Matrix Polynomial WithLp

section UnitVector

variable {n : Type*} [Fintype n] [DecidableEq n] (v : n → ℝ) (hv : v ⬝ᵥ v = 1) (β : ℝ)

include hv

-- For a unit vector the statements take the form of the source.
example : (1 - β • vecMulVec v v) *ᵥ v = (1 - β) • v := by
  simpa [hv] using one_sub_smul_vecMulVec_mulVec_self β v

example : (1 - β • vecMulVec v v).det = 1 - β := by
  simpa [hv] using det_one_sub_smul_vecMulVec β v

example (hn : 1 < Fintype.card n) : spectrum ℝ (1 - β • vecMulVec v v) = {1, 1 - β} := by
  simpa [hv] using spectrum_one_sub_smul_vecMulVec hn β v

example (x : n → ℝ) :
    ‖toLp 2 ((1 - β • vecMulVec v v) *ᵥ x)‖ ^ 2 =
      ‖toLp 2 x‖ ^ 2 - β * (2 - β) * (v ⬝ᵥ x) ^ 2 := by
  simpa [hv] using norm_toLp_one_sub_smul_vecMulVec_mulVec_sq β v x

open scoped Matrix.Norms.L2Operator in
example : ‖(1 - β • vecMulVec v v : Matrix n n ℝ)‖ ≤ 1 ↔ β ∈ Set.Icc 0 2 := by
  simpa [hv] using l2_opNorm_one_sub_smul_vecMulVec_le_one_iff β v

-- With `β = 2`, the reflection sends `v` to `-v`.
example : toEuclideanLin (1 - (2 : ℝ) • vecMulVec v v) (toLp 2 v) = -toLp 2 v := by
  rw [toEuclideanLin_one_sub_smul_vecMulVec_eq_reflection (by rw [hv, mul_one])]
  exact Submodule.reflection_orthogonalComplement_singleton_eq_neg _

-- With `β = 1`, the projection sends `v` to `0`.
example : toEuclideanLin (1 - (1 : ℝ) • vecMulVec v v) (toLp 2 v) = 0 := by
  rw [toEuclideanLin_one_sub_smul_vecMulVec_eq_starProjection (by rw [hv, mul_one])]
  exact Submodule.starProjection_orthogonalComplement_singleton_eq_zero _

end UnitVector

-- The zero vector gives the identity, whose spectrum is `{1}`.
example {n : Type*} [Fintype n] [DecidableEq n] (hn : 1 < Fintype.card n) (β : ℝ) :
    spectrum ℝ (1 - β • vecMulVec (0 : n → ℝ) 0 : Matrix n n ℝ) = {1} := by
  simpa using spectrum_one_sub_smul_vecMulVec hn β (0 : n → ℝ)

-- With `β = 0` the matrix is the identity: determinant `1` and spectrum `{1}`.
example {n : Type*} [Fintype n] [DecidableEq n] (v : n → ℝ) :
    (1 - (0 : ℝ) • vecMulVec v v).det = 1 := by
  rw [det_one_sub_smul_vecMulVec, zero_mul, sub_zero]

example {n : Type*} [Fintype n] [DecidableEq n] (hn : 1 < Fintype.card n) (v : n → ℝ) :
    spectrum ℝ (1 - (0 : ℝ) • vecMulVec v v) = {1} := by
  simpa using spectrum_one_sub_smul_vecMulVec hn 0 v

-- A reflection in the plane: `I - 2 e₀ e₀ᵀ = diag(-1, 1)`, with spectrum `{1, -1}`.
example : (1 - (2 : ℝ) • vecMulVec ![1, 0] ![1, 0] : Matrix (Fin 2) (Fin 2) ℝ) =
    !![-1, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [vecMulVec_apply]

example : spectrum ℝ (1 - (2 : ℝ) • vecMulVec ![1, 0] ![1, 0] : Matrix (Fin 2) (Fin 2) ℝ) =
    {1, -1} := by
  rw [spectrum_one_sub_smul_vecMulVec (by simp)]
  norm_num [dotProduct, Fin.sum_univ_two]

-- With one index the spectrum is the single point `{1 - β vᵀ v}`: for `v = (1)` and `β = 1`
-- the matrix is zero, and `1` is not in its spectrum. So `spectrum_one_sub_smul_vecMulVec`
-- needs two indices.
example : (1 : ℝ) ∉ spectrum ℝ (1 - (1 : ℝ) • vecMulVec ![1] ![1] : Matrix (Fin 1) (Fin 1) ℝ) := by
  rw [mem_spectrum_iff_isRoot_charpoly, charpoly_one_sub_smul_vecMulVec]
  norm_num [dotProduct]

-- The determinant needs no lower bound on the dimension: with one index, `v = (1)` and `β = 1`,
-- the matrix is the zero `1 × 1` matrix and `det H = 1 - β vᵀ v = 0`.
example : (1 - (1 : ℝ) • vecMulVec ![1] ![1] : Matrix (Fin 1) (Fin 1) ℝ).det = 0 := by
  rw [det_fin_one]
  norm_num [vecMulVec_apply]

example : (1 - (1 : ℝ) • vecMulVec ![1] ![1] : Matrix (Fin 1) (Fin 1) ℝ).det = 0 := by
  rw [det_one_sub_smul_vecMulVec]
  norm_num [dotProduct]

-- An independent check of the determinant and the characteristic polynomial for
-- `v = (1, 1, 1)` and `β = 1`, where `vᵀ v = 3`.
example : (1 - (1 : ℝ) • vecMulVec ![1, 1, 1] ![1, 1, 1] : Matrix (Fin 3) (Fin 3) ℝ).det = -2 := by
  rw [det_fin_three]
  norm_num [vecMulVec_apply, one_apply]

example : (1 - (1 : ℝ) • vecMulVec ![1, 1, 1] ![1, 1, 1] : Matrix (Fin 3) (Fin 3) ℝ).det =
    1 - 1 * 3 := by
  rw [det_one_sub_smul_vecMulVec]
  norm_num [dotProduct, Fin.sum_univ_three]

example : (1 - (1 : ℝ) • vecMulVec ![1, 1, 1] ![1, 1, 1] : Matrix (Fin 3) (Fin 3) ℝ).charpoly =
    (X - 1) ^ 2 * (X - C (-2)) := by
  rw [charpoly_one_sub_smul_vecMulVec]
  norm_num [dotProduct, Fin.sum_univ_three]

-- `β = 3` and a unit vector: the operator norm exceeds `1`.
open scoped Matrix.Norms.L2Operator in
example : ¬ ‖(1 - (3 : ℝ) • vecMulVec ![1, 0] ![1, 0] : Matrix (Fin 2) (Fin 2) ℝ)‖ ≤ 1 := by
  rw [l2_opNorm_one_sub_smul_vecMulVec_le_one_iff]
  norm_num [dotProduct, Fin.sum_univ_two]

#print axioms Matrix.one_sub_smul_vecMulVec_mulVec_self
#print axioms Matrix.one_sub_smul_vecMulVec_mulVec_of_dotProduct_eq_zero
#print axioms Matrix.det_one_sub_smul_vecMulVec
#print axioms Matrix.charpoly_one_sub_smul_vecMulVec
#print axioms Matrix.spectrum_one_sub_smul_vecMulVec
#print axioms Matrix.eigenspace_toEuclideanLin_one_sub_smul_vecMulVec_one
#print axioms Matrix.eigenspace_toEuclideanLin_one_sub_smul_vecMulVec_one_sub
#print axioms Matrix.norm_toLp_one_sub_smul_vecMulVec_mulVec_sq
#print axioms Matrix.l2_opNorm_one_sub_smul_vecMulVec_le_one_iff
#print axioms Matrix.toEuclideanLin_one_sub_smul_vecMulVec_eq_starProjection
#print axioms Matrix.toEuclideanLin_one_sub_smul_vecMulVec_eq_reflection
