/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Real planar rotation matrices

This file defines the rotation matrix through a real angle `θ`, the real `2 × 2` matrix
`!![cos θ, -sin θ; sin θ, cos θ]`.

Mathlib's `rotation` is a rotation of `ℂ` given by a point of the unit circle, as a linear
isometric equivalence; by `toMatrix_rotation`, its matrix in the basis `1, I` is given by
`Matrix.planeConformalMatrix`, which lands in `GL (Fin 2) ℝ`. Neither is a function of the angle
with values in real matrices.

## Main definitions

- `MetaMathlibExt.Matrix.planarRotation`: the rotation matrix through the angle `θ`.

## References

- J. Su, Y. Lu, S. Pan, A. Murtadha, B. Wen and Y. Liu, *RoFormer: Enhanced Transformer with
  Rotary Position Embedding*, arXiv:2104.09864 (v5), Section 3.2.1, equation (13).
-/

namespace MetaMathlibExt.Matrix

/-- **Real planar rotation matrix.** For $\theta \in \mathbb{R}$, the rotation matrix through the
angle $\theta$ is the real $2 \times 2$ matrix
$R(\theta) = \begin{pmatrix} \cos\theta & -\sin\theta \\ \sin\theta & \cos\theta \end{pmatrix}$.

Source: J. Su, Y. Lu, S. Pan, A. Murtadha, B. Wen and Y. Liu, *RoFormer: Enhanced Transformer
with Rotary Position Embedding*, arXiv:2104.09864 (v5), Section 3.2.1, equation (13) (the
rotation matrix through the angle $m\theta$). -/
@[expose] public noncomputable def planarRotation (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

open _root_.Matrix
open scoped ComplexConjugate InnerProductSpace

private theorem planarRotation_mul (a b : ℝ) :
    planarRotation a * planarRotation b = planarRotation (a + b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planarRotation, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add, Real.sin_add] <;> ring

private theorem planarRotation_transpose (θ : ℝ) :
    (planarRotation θ)ᵀ = planarRotation (-θ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [planarRotation]

private theorem planarRotation_toComplex (θ : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    Complex.orthonormalBasisOneI.repr.symm ((planarRotation θ).toEuclideanLin x) =
      Complex.exp ((θ : ℂ) * Complex.I) * Complex.orthonormalBasisOneI.repr.symm x := by
  rw [Complex.exp_ofReal_mul_I]
  apply Complex.ext <;>
    simp [Matrix.toLpLin_apply, dotProduct, Fin.sum_univ_two, planarRotation,
      Complex.mul_re, Complex.mul_im] <;> ring

/-- **Identities of planar rotation matrices.** Composition adds angles. Transposition negates
the angle and gives the inverse, so the matrix is orthogonal. The determinant is `1` and
the action on `EuclideanSpace ℝ (Fin 2)` preserves the Euclidean norm. The relative product
`R(a)ᵀ * R(b)` is `R(b - a)`.

The inverse coordinate map `Complex.orthonormalBasisOneI.repr.symm` sends `(x₀, x₁)` to
`x₀ + x₁ * I`. In these coordinates the rotation acts by multiplication by `exp (θ * I)`
and the real Euclidean inner product is the real part of `z * conj w`.

Source: Su et al., *RoFormer: Enhanced Transformer with Rotary Position Embedding*,
arXiv:2104.09864 (v5), Section 3.2.1, equations (12)–(13), for the real and complex forms
with angle `mθ`. The matrix identities are derived from these forms. -/
public theorem planarRotation_identities (a b θ : ℝ) :
    planarRotation a * planarRotation b = planarRotation (a + b) ∧
    (planarRotation θ)ᵀ = planarRotation (-θ) ∧
    planarRotation (-θ) = (planarRotation θ)⁻¹ ∧
    (planarRotation θ)ᵀ * planarRotation θ = 1 ∧
    (planarRotation θ).det = 1 ∧
    (∀ x : EuclideanSpace ℝ (Fin 2), ‖(planarRotation θ).toEuclideanLin x‖ = ‖x‖) ∧
    (planarRotation a)ᵀ * planarRotation b = planarRotation (b - a) ∧
    (∀ x : EuclideanSpace ℝ (Fin 2),
      Complex.orthonormalBasisOneI.repr.symm ((planarRotation θ).toEuclideanLin x) =
        Complex.exp ((θ : ℂ) * Complex.I) * Complex.orthonormalBasisOneI.repr.symm x) ∧
    ∀ x y : EuclideanSpace ℝ (Fin 2),
      ⟪x, y⟫_ℝ = (Complex.orthonormalBasisOneI.repr.symm x *
        conj (Complex.orthonormalBasisOneI.repr.symm y)).re := by
  have hleft : planarRotation (-θ) * planarRotation θ = 1 := by
    rw [planarRotation_mul, neg_add_cancel]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [planarRotation]
  refine ⟨planarRotation_mul a b, planarRotation_transpose θ, (Matrix.inv_eq_left_inv hleft).symm,
    ?_, ?_, ?_, ?_, planarRotation_toComplex θ, ?_⟩
  · rw [planarRotation_transpose, hleft]
  · simp [planarRotation, Matrix.det_fin_two_of, ← sq, Real.cos_sq_add_sin_sq]
  · intro x
    calc
      ‖(planarRotation θ).toEuclideanLin x‖ =
          ‖Complex.orthonormalBasisOneI.repr.symm ((planarRotation θ).toEuclideanLin x)‖ :=
        (Complex.orthonormalBasisOneI.repr.symm.norm_map _).symm
      _ = ‖x‖ := by
        rw [planarRotation_toComplex, Complex.norm_mul, Complex.norm_exp_ofReal_mul_I,
          one_mul, LinearIsometryEquiv.norm_map]
  · rw [planarRotation_transpose, planarRotation_mul, neg_add_eq_sub]
  · intro x y
    exact (real_inner_comm y x).trans
      (inner_map_complex Complex.orthonormalBasisOneI.repr.symm y x)

end MetaMathlibExt.Matrix
