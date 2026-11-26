/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import MathlibExt.LinearAlgebra.Matrix.PlanarRotation

open Matrix MetaMathlibExt.Matrix Real

-- The entries, read by row and column.
example (θ : ℝ) :
    planarRotation θ 0 0 = cos θ ∧ planarRotation θ 0 1 = -sin θ ∧
      planarRotation θ 1 0 = sin θ ∧ planarRotation θ 1 1 = cos θ := by
  simp [planarRotation]

-- The rotation through `0` is the identity, and the one through `π / 2` is a quarter turn.
example : planarRotation 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [planarRotation]

example : planarRotation (π / 2) = !![0, -1; 1, 0] := by
  simp [planarRotation]

-- Composition adds the angles.
example (a b : ℝ) : planarRotation a * planarRotation b = planarRotation (a + b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planarRotation, Matrix.mul_apply, Fin.sum_univ_two, cos_add, sin_add] <;> ring

-- The transpose is the rotation through `-θ`, and it inverts the rotation.
example (θ : ℝ) : (planarRotation θ)ᵀ = planarRotation (-θ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [planarRotation]

example (θ : ℝ) : (planarRotation θ)ᵀ * planarRotation θ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planarRotation, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [sin_sq_add_cos_sq θ]

-- The determinant is `1`, so the rotation lies in the special orthogonal group.
example (θ : ℝ) : (planarRotation θ).det = 1 := by
  simp [planarRotation, Matrix.det_fin_two_of, ← sq, cos_sq_add_sin_sq]

example (θ : ℝ) : planarRotation θ ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
  simp [planarRotation, cos_sq_add_sin_sq]

-- Mathlib's `rotation` by `Circle.exp θ`, the point `exp (θ * I)` of the unit circle, has this
-- matrix in the basis `1, I` of `ℂ` over `ℝ`.
example (θ : ℝ) :
    LinearMap.toMatrix Complex.basisOneI Complex.basisOneI (rotation (Circle.exp θ)).toLinearEquiv =
      planarRotation θ := by
  rw [toMatrix_rotation]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planarRotation, Circle.coe_exp, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im]

open scoped InnerProductSpace

-- The public inverse and Euclidean norm statements apply at arbitrary real angles.
example (θ : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    (planarRotation θ)ᵀ = (planarRotation θ)⁻¹ ∧ ‖(planarRotation θ).toEuclideanLin x‖ = ‖x‖ := by
  obtain ⟨_, htranspose, hinverse, _, _, hnorm, _, _, _⟩ := planarRotation_identities 0 0 θ
  exact ⟨htranspose.trans hinverse, hnorm x⟩

-- The relative product at these angles is a negative quarter turn, not a positive one.
example : ((planarRotation (π / 2))ᵀ * planarRotation 0) 0 1 = 1 := by
  obtain ⟨_, _, _, _, _, _, hrelative, _, _⟩ := planarRotation_identities (π / 2) 0 0
  rw [hrelative]
  simp [planarRotation]

-- A positive quarter turn acts on 2 + 3i by multiplication by i, giving −3 + 2i.
example : Complex.orthonormalBasisOneI.repr.symm
    ((planarRotation (π / 2)).toEuclideanLin (WithLp.toLp 2 ![2, 3])) = ⟨-3, 2⟩ := by
  obtain ⟨_, _, _, _, _, _, _, haction, _⟩ := planarRotation_identities 0 0 (π / 2)
  rw [haction, Complex.exp_ofReal_mul_I, Complex.orthonormalBasisOneI_repr_symm_apply]
  apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im]

-- Conjugation makes the imaginary-coordinate contribution positive: 1 * 3 + 2 * 4 = 11.
example : ⟪(WithLp.toLp 2 ![1, 2] : EuclideanSpace ℝ (Fin 2)), WithLp.toLp 2 ![3, 4]⟫_ℝ = 11 := by
  obtain ⟨_, _, _, _, _, _, _, _, hinner⟩ := planarRotation_identities 0 0 0
  rw [hinner]
  norm_num [Complex.orthonormalBasisOneI_repr_symm_apply, Complex.mul_re, Complex.mul_im]
