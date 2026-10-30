/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.CStarAlgebra.Spectrum

@[expose] public section

open scoped ComplexOrder InnerProductSpace

/-!
# The Cayley transform of a bounded self-adjoint operator

For a self-adjoint operator `A` on a complex Hilbert space, the Cayley
transform is the unitary operator `U = (A - i) / (A + i)`, i.e.
`U = (A - i • 1) * (A + i • 1)⁻¹`, where the inverse is the ring inverse
(which agrees with the operator inverse here since `A + i • 1` is a unit).
It is the operator analogue of the Möbius map `λ ↦ (λ - i) / (λ + i)`
sending the real line to the unit circle, and it is the standard bridge
between self-adjoint and unitary operators.

This is a companion to the self-adjoint spectral theory in the book
*Introduction to Functional Analysis* (v1); the Cayley transform itself is not
one of the book's numbered targets, and it does not appear in Mathlib.

## Main declarations

* `ContinuousLinearMap.cayleyTransform`: the Cayley transform of an operator.
* `ContinuousLinearMap.mem_unitary_cayleyTransform`: the Cayley transform of
  a self-adjoint operator is unitary.
* `ContinuousLinearMap.eq_cayleyTransform_inv`: the inverse formula
  `A = i • (1 + U) * (1 - U)⁻¹`.
* `ContinuousLinearMap.spectrum_cayleyTransform`: the spectrum of `U` is the
  image of the spectrum of `A` under `λ ↦ (λ - i) / (λ + i)`.
* `ContinuousLinearMap.hasEigenvalue_cayleyTransform_iff`: the eigenvalue
  correspondence between `U` and `A`.
-/

namespace MathlibExt.Analysis.InnerProductSpace.CayleyTransform

namespace ContinuousLinearMap

section Basic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (A : H →L[ℂ] H)

/-- A nonzero scalar operator is a unit. -/
theorem isUnit_smul_one (z : ℂ) (hz : z ≠ 0) : IsUnit (z • (1 : H →L[ℂ] H)) := by
  exact ⟨⟨z • (1 : H →L[ℂ] H), z⁻¹ • (1 : H →L[ℂ] H),
    by rw [smul_mul_smul, mul_one, mul_inv_cancel₀ hz, one_smul],
    by rw [smul_mul_smul, mul_one, inv_mul_cancel₀ hz, one_smul]⟩, rfl⟩

/-- The ring inverse of a scalar operator is the scalar operator of the
inverse scalar. -/
theorem ringInverse_smul_one (z : ℂ) :
    Ring.inverse (z • (1 : H →L[ℂ] H)) = z⁻¹ • (1 : H →L[ℂ] H) := by
  by_cases hz : z = 0
  · simp [hz]
  · have hunit : IsUnit (z • (1 : H →L[ℂ] H)) := isUnit_smul_one _ hz
    rw [← hunit.unit_spec, Ring.inverse_unit]
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hunit.unit_spec, smul_mul_smul, mul_one, mul_inv_cancel₀ hz, one_smul]

/-- The Cayley transform of an operator `A`: `(A - i) * (A + i)⁻¹`. The
factor `A + i • 1` is a unit when `A` is self-adjoint on a complete Hilbert space (see
`isUnit_add_I_smul_one_of_isSelfAdjoint` below), in which case the ring
inverse here is the genuine operator inverse. -/
noncomputable def cayleyTransform : H →L[ℂ] H :=
  (A - Complex.I • (1 : H →L[ℂ] H)) * Ring.inverse (A + Complex.I • (1 : H →L[ℂ] H))

/-- The two factors of the Cayley transform commute. -/
theorem commute_sub_I_add_I :
    (A - Complex.I • (1 : H →L[ℂ] H)) * (A + Complex.I • (1 : H →L[ℂ] H))
      = (A + Complex.I • (1 : H →L[ℂ] H)) * (A - Complex.I • (1 : H →L[ℂ] H)) := by
  have hcomm : (Complex.I • (1 : H →L[ℂ] H)) * A = A * (Complex.I • (1 : H →L[ℂ] H)) := by
    rw [smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
  have e1 : (A - Complex.I • (1 : H →L[ℂ] H)) * (A + Complex.I • (1 : H →L[ℂ] H))
      = A * A - (Complex.I • (1 : H →L[ℂ] H)) * (Complex.I • (1 : H →L[ℂ] H)) := by
    rw [sub_mul, mul_add, mul_add, hcomm]
    noncomm_ring
  have e2 : (A + Complex.I • (1 : H →L[ℂ] H)) * (A - Complex.I • (1 : H →L[ℂ] H))
      = A * A - (Complex.I • (1 : H →L[ℂ] H)) * (Complex.I • (1 : H →L[ℂ] H)) := by
    rw [add_mul, mul_sub, mul_sub, ← hcomm]
    noncomm_ring
  rw [e1, e2]

end Basic

section SelfAdjoint

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (A : H →L[ℂ] H)

/-- For a self-adjoint operator, `A - w • 1` is a unit whenever `w` has
nonzero imaginary part. The proof is the norm estimate
`‖(A - w • 1) x‖ ≥ |w.im| * ‖x‖`, read off from the imaginary part of
`⟪(A - w • 1) x, x⟫`. -/
theorem isUnit_sub_smul_one_of_isSelfAdjoint_of_im_ne_zero (hA : IsSelfAdjoint A)
    {w : ℂ} (hw : w.im ≠ 0) : IsUnit (A - w • (1 : H →L[ℂ] H)) := by
  apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map _ (c := ⟨|w.im|, abs_nonneg _⟩)
    (by exact_mod_cast abs_pos.mpr hw)
  intro x
  have hinner : ⟪(A - w • (1 : H →L[ℂ] H)) x, x⟫_ℂ
      = ⟪A x, x⟫_ℂ - (starRingEnd ℂ) w * ⟪x, x⟫_ℂ := by
    have h1 : (A - w • (1 : H →L[ℂ] H)) x = A x - w • x := by simp
    rw [h1, inner_sub_left, inner_smul_left, sub_eq_add_neg]
  have him : (⟪(A - w • (1 : H →L[ℂ] H)) x, x⟫_ℂ).im = w.im * ‖x‖ ^ 2 := by
    rw [hinner]
    have hAIm : (⟪A x, x⟫_ℂ).im = 0 := hA.isSymmetric.im_inner_apply_self x
    simp [Complex.sub_im, Complex.mul_im, hAIm, Complex.conj_re, Complex.conj_im,
      ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im]
  have hle := Complex.abs_im_le_norm (⟪(A - w • (1 : H →L[ℂ] H)) x, x⟫_ℂ)
  rw [him, abs_mul, abs_of_nonneg (sq_nonneg ‖x‖), mul_comm (|w.im| : ℝ) (‖x‖ ^ 2)] at hle
  show ‖x‖ ^ 2 * |w.im| ≤ ‖⟪(A - w • (1 : H →L[ℂ] H)) x, x⟫_ℂ‖
  exact hle

/-- For a self-adjoint operator, `A + i • 1` is a unit. -/
theorem isUnit_add_I_smul_one_of_isSelfAdjoint (hA : IsSelfAdjoint A) :
    IsUnit (A + Complex.I • (1 : H →L[ℂ] H)) := by
  have h := isUnit_sub_smul_one_of_isSelfAdjoint_of_im_ne_zero A hA
    (w := -Complex.I) (by simp)
  rwa [neg_smul, sub_neg_eq_add] at h

/-- For a self-adjoint operator, `A - i • 1` is a unit. -/
theorem isUnit_sub_I_smul_one_of_isSelfAdjoint (hA : IsSelfAdjoint A) :
    IsUnit (A - Complex.I • (1 : H →L[ℂ] H)) :=
  isUnit_sub_smul_one_of_isSelfAdjoint_of_im_ne_zero A hA (w := Complex.I) (by simp)

/-- The inverse of `A + i • 1` is a unit for self-adjoint `A`. -/
theorem isUnit_ringInverse_add_I_of_isSelfAdjoint (hA : IsSelfAdjoint A) :
    IsUnit (Ring.inverse (A + Complex.I • (1 : H →L[ℂ] H))) := by
  have hAdd := isUnit_add_I_smul_one_of_isSelfAdjoint A hA
  rw [← hAdd.unit_spec, Ring.inverse_unit]
  exact Units.isUnit _

/-- The adjoint of the Cayley transform. -/
theorem star_cayleyTransform (hA : IsSelfAdjoint A) :
    star (cayleyTransform A)
      = Ring.inverse (A - Complex.I • (1 : H →L[ℂ] H))
          * (A + Complex.I • (1 : H →L[ℂ] H)) := by
  calc star (cayleyTransform A)
      = star (Ring.inverse (A + Complex.I • (1 : H →L[ℂ] H)))
          * star (A - Complex.I • (1 : H →L[ℂ] H)) := by
        rw [cayleyTransform, star_mul]
    _ = Ring.inverse (star (A + Complex.I • (1 : H →L[ℂ] H)))
          * star (A - Complex.I • (1 : H →L[ℂ] H)) := by
        rw [Ring.inverse_star]
    _ = Ring.inverse (A - Complex.I • (1 : H →L[ℂ] H))
          * (A + Complex.I • (1 : H →L[ℂ] H)) := by
        rw [show star (A + Complex.I • (1 : H →L[ℂ] H))
            = A - Complex.I • (1 : H →L[ℂ] H) from by
          simp [star_add, hA.star_eq, Complex.conj_I, sub_eq_add_neg],
          show star (A - Complex.I • (1 : H →L[ℂ] H))
            = A + Complex.I • (1 : H →L[ℂ] H) from by
          simp [star_sub, hA.star_eq, Complex.conj_I, sub_neg_eq_add]]

/-- The Cayley transform of a self-adjoint operator satisfies `U† * U = 1`. -/
theorem star_mul_self_cayleyTransform (hA : IsSelfAdjoint A) :
    star (cayleyTransform A) * cayleyTransform A = 1 := by
  have hAdd := isUnit_add_I_smul_one_of_isSelfAdjoint A hA
  have hSub := isUnit_sub_I_smul_one_of_isSelfAdjoint A hA
  calc star (cayleyTransform A) * cayleyTransform A
      = Ring.inverse (A - Complex.I • (1 : H →L[ℂ] H))
          * ((A + Complex.I • (1 : H →L[ℂ] H)) * (A - Complex.I • (1 : H →L[ℂ] H)))
          * Ring.inverse (A + Complex.I • (1 : H →L[ℂ] H)) := by
        rw [star_cayleyTransform A hA, cayleyTransform]
        simp only [mul_assoc]
    _ = Ring.inverse (A - Complex.I • (1 : H →L[ℂ] H))
          * ((A - Complex.I • (1 : H →L[ℂ] H)) * (A + Complex.I • (1 : H →L[ℂ] H)))
          * Ring.inverse (A + Complex.I • (1 : H →L[ℂ] H)) := by
        rw [commute_sub_I_add_I]
    _ = (Ring.inverse (A - Complex.I • (1 : H →L[ℂ] H))
          * (A - Complex.I • (1 : H →L[ℂ] H)))
          * ((A + Complex.I • (1 : H →L[ℂ] H))
          * Ring.inverse (A + Complex.I • (1 : H →L[ℂ] H))) := by
        simp only [mul_assoc]
    _ = 1 := by
        rw [Ring.inverse_mul_cancel _ hSub, Ring.mul_inverse_cancel _ hAdd, mul_one]

/-- The Cayley transform of a self-adjoint operator satisfies `U * U† = 1`. -/
theorem mul_star_self_cayleyTransform (hA : IsSelfAdjoint A) :
    cayleyTransform A * star (cayleyTransform A) = 1 := by
  have hAdd := isUnit_add_I_smul_one_of_isSelfAdjoint A hA
  have hSub := isUnit_sub_I_smul_one_of_isSelfAdjoint A hA
  have hinv_comm : Ring.inverse (A + Complex.I • (1 : H →L[ℂ] H))
        * Ring.inverse (A - Complex.I • (1 : H →L[ℂ] H))
      = Ring.inverse (A - Complex.I • (1 : H →L[ℂ] H))
        * Ring.inverse (A + Complex.I • (1 : H →L[ℂ] H)) := by
    rw [← Ring.inverse_mul (Or.inl hSub), ← Ring.inverse_mul (Or.inl hAdd),
      commute_sub_I_add_I]
  calc cayleyTransform A * star (cayleyTransform A)
      = (A - Complex.I • (1 : H →L[ℂ] H))
          * ((Ring.inverse (A + Complex.I • (1 : H →L[ℂ] H))
            * Ring.inverse (A - Complex.I • (1 : H →L[ℂ] H)))
            * (A + Complex.I • (1 : H →L[ℂ] H))) := by
        rw [star_cayleyTransform A hA, cayleyTransform]
        simp only [mul_assoc]
    _ = (A - Complex.I • (1 : H →L[ℂ] H))
          * ((Ring.inverse (A - Complex.I • (1 : H →L[ℂ] H))
            * Ring.inverse (A + Complex.I • (1 : H →L[ℂ] H)))
            * (A + Complex.I • (1 : H →L[ℂ] H))) := by
        rw [hinv_comm]
    _ = ((A - Complex.I • (1 : H →L[ℂ] H))
          * Ring.inverse (A - Complex.I • (1 : H →L[ℂ] H)))
          * (Ring.inverse (A + Complex.I • (1 : H →L[ℂ] H))
          * (A + Complex.I • (1 : H →L[ℂ] H))) := by
        simp only [mul_assoc]
    _ = 1 := by
        rw [Ring.mul_inverse_cancel _ hSub, Ring.inverse_mul_cancel _ hAdd, mul_one]

/-- The Cayley transform of a self-adjoint operator is a unit. -/
theorem isUnit_cayleyTransform (hA : IsSelfAdjoint A) : IsUnit (cayleyTransform A) := by
  show IsUnit ((A - Complex.I • (1 : H →L[ℂ] H))
    * Ring.inverse (A + Complex.I • (1 : H →L[ℂ] H)))
  exact IsUnit.mul (isUnit_sub_I_smul_one_of_isSelfAdjoint A hA)
    (isUnit_ringInverse_add_I_of_isSelfAdjoint A hA)

/-- The Cayley transform of a self-adjoint operator is unitary. -/
theorem mem_unitary_cayleyTransform (hA : IsSelfAdjoint A) :
    cayleyTransform A ∈ unitary (H →L[ℂ] H) :=
  (IsUnit.mem_unitary_iff_star_mul_self (isUnit_cayleyTransform A hA)).mpr
    (star_mul_self_cayleyTransform A hA)

/-- The Cayley transform of a self-adjoint operator is an isometry. -/
theorem norm_cayleyTransform_apply (hA : IsSelfAdjoint A) (x : H) :
    ‖cayleyTransform A x‖ = ‖x‖ :=
  ContinuousLinearMap.norm_map_of_mem_unitary (mem_unitary_cayleyTransform A hA) x

/-- On a nontrivial space, the Cayley transform has operator norm `1`. -/
theorem norm_cayleyTransform (hA : IsSelfAdjoint A) [Nontrivial H] :
    ‖cayleyTransform A‖ = 1 := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
      rw [norm_cayleyTransform_apply A hA x, one_mul])
  · obtain ⟨x, hx⟩ : ∃ x : H, ‖x‖ = 1 := by
      obtain ⟨x, hx0⟩ := exists_ne (0 : H)
      exact ⟨‖x‖⁻¹ • x, by
        rw [norm_smul, norm_inv, Real.norm_of_nonneg (norm_nonneg x),
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx0)]⟩
    calc 1 = ‖cayleyTransform A x‖ := by rw [norm_cayleyTransform_apply A hA x, hx]
      _ ≤ ‖cayleyTransform A‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖cayleyTransform A‖ := by rw [hx, mul_one]

/-- `1 + U` is `2 • A` times the inverse of `A + i • 1`. -/
theorem one_add_cayleyTransform (hA : IsSelfAdjoint A) :
    1 + cayleyTransform A
      = (2 : ℂ) • A * Ring.inverse (A + Complex.I • (1 : H →L[ℂ] H)) := by
  have hAdd := isUnit_add_I_smul_one_of_isSelfAdjoint A hA
  have h1 : (1 : H →L[ℂ] H)
      = (A + Complex.I • (1 : H →L[ℂ] H)) * Ring.inverse (A + Complex.I • (1 : H →L[ℂ] H)) :=
    (Ring.mul_inverse_cancel _ hAdd).symm
  calc 1 + cayleyTransform A
      = ((A + Complex.I • (1 : H →L[ℂ] H)) + (A - Complex.I • (1 : H →L[ℂ] H)))
          * Ring.inverse (A + Complex.I • (1 : H →L[ℂ] H)) := by
        conv_lhs => rw [h1, cayleyTransform]
        rw [← add_mul]
    _ = (2 : ℂ) • A * Ring.inverse (A + Complex.I • (1 : H →L[ℂ] H)) := by
        congr 1
        module

/-- `1 - U` is `2 • (i • 1)` times the inverse of `A + i • 1`. -/
theorem one_sub_cayleyTransform (hA : IsSelfAdjoint A) :
    1 - cayleyTransform A
      = (2 : ℂ) • (Complex.I • (1 : H →L[ℂ] H))
          * Ring.inverse (A + Complex.I • (1 : H →L[ℂ] H)) := by
  have hAdd := isUnit_add_I_smul_one_of_isSelfAdjoint A hA
  have h1 : (1 : H →L[ℂ] H)
      = (A + Complex.I • (1 : H →L[ℂ] H)) * Ring.inverse (A + Complex.I • (1 : H →L[ℂ] H)) :=
    (Ring.mul_inverse_cancel _ hAdd).symm
  calc 1 - cayleyTransform A
      = ((A + Complex.I • (1 : H →L[ℂ] H)) - (A - Complex.I • (1 : H →L[ℂ] H)))
          * Ring.inverse (A + Complex.I • (1 : H →L[ℂ] H)) := by
        conv_lhs => rw [h1, cayleyTransform]
        rw [← sub_mul]
    _ = (2 : ℂ) • (Complex.I • (1 : H →L[ℂ] H))
          * Ring.inverse (A + Complex.I • (1 : H →L[ℂ] H)) := by
        congr 1
        module

/-- `1 - U` is a unit for the Cayley transform of a self-adjoint operator:
`1` is never in the spectrum of `U`. -/
theorem isUnit_one_sub_cayleyTransform (hA : IsSelfAdjoint A) :
    IsUnit (1 - cayleyTransform A) := by
  rw [one_sub_cayleyTransform A hA]
  apply IsUnit.mul _ (isUnit_ringInverse_add_I_of_isSelfAdjoint A hA)
  have hne : (2 : ℂ) * Complex.I ≠ 0 := by norm_num [Complex.ext_iff]
  have h2 : (2 : ℂ) • (Complex.I • (1 : H →L[ℂ] H))
      = (2 * Complex.I) • (1 : H →L[ℂ] H) := by rw [smul_smul]
  rw [h2]
  exact ⟨⟨(2 * Complex.I) • (1 : H →L[ℂ] H), (2 * Complex.I)⁻¹ • (1 : H →L[ℂ] H),
    by rw [smul_mul_smul, mul_one, mul_inv_cancel₀ hne, one_smul],
    by rw [smul_mul_smul, mul_one, inv_mul_cancel₀ hne, one_smul]⟩, rfl⟩

/-- The inverse Cayley formula: `A = i • (1 + U) * (1 - U)⁻¹`. -/
theorem eq_cayleyTransform_inv (hA : IsSelfAdjoint A) :
    A = Complex.I • (1 + cayleyTransform A) * Ring.inverse (1 - cayleyTransform A) := by
  have hIsUnitSub := isUnit_one_sub_cayleyTransform A hA
  have key : A * (1 - cayleyTransform A) = Complex.I • (1 + cayleyTransform A) := by
    rw [one_sub_cayleyTransform A hA, one_add_cayleyTransform A hA]
    have e1 : A * ((2 : ℂ) • (Complex.I • (1 : H →L[ℂ] H)))
        = Complex.I • ((2 : ℂ) • A) := by
      calc A * ((2 : ℂ) • (Complex.I • (1 : H →L[ℂ] H)))
          = A * (((2 : ℂ) * Complex.I) • (1 : H →L[ℂ] H)) := by rw [← smul_smul]
        _ = ((2 : ℂ) * Complex.I) • (A * (1 : H →L[ℂ] H)) := by rw [mul_smul_comm]
        _ = ((2 : ℂ) * Complex.I) • A := by rw [mul_one]
        _ = Complex.I • ((2 : ℂ) • A) := by rw [smul_smul, mul_comm Complex.I (2 : ℂ)]
    calc A * (((2 : ℂ) • (Complex.I • (1 : H →L[ℂ] H)))
            * Ring.inverse (A + Complex.I • (1 : H →L[ℂ] H)))
        = (A * ((2 : ℂ) • (Complex.I • (1 : H →L[ℂ] H))))
            * Ring.inverse (A + Complex.I • (1 : H →L[ℂ] H)) := by rw [← mul_assoc]
      _ = (Complex.I • ((2 : ℂ) • A))
            * Ring.inverse (A + Complex.I • (1 : H →L[ℂ] H)) := by rw [e1]
      _ = Complex.I • (((2 : ℂ) • A)
            * Ring.inverse (A + Complex.I • (1 : H →L[ℂ] H))) := by rw [smul_mul_assoc]
  calc A = A * ((1 - cayleyTransform A) * Ring.inverse (1 - cayleyTransform A)) := by
        rw [Ring.mul_inverse_cancel _ hIsUnitSub, mul_one]
    _ = (A * (1 - cayleyTransform A)) * Ring.inverse (1 - cayleyTransform A) := by
        rw [mul_assoc]
    _ = Complex.I • (1 + cayleyTransform A) * Ring.inverse (1 - cayleyTransform A) := by
        rw [key]

/-- The resolvent-type factorization behind the spectral mapping: for
`μ ≠ 1` and `λ = i * (1 + μ) / (1 - μ)`,
`μ • 1 - U = ((μ - 1) • (A - λ • 1)) * (A + i • 1)⁻¹`. -/
theorem algebraMap_sub_cayleyTransform (hA : IsSelfAdjoint A) {μ : ℂ} (hμ : μ ≠ 1) :
    algebraMap ℂ (H →L[ℂ] H) μ - cayleyTransform A
      = ((μ - 1) • (A - (Complex.I * (1 + μ) / (1 - μ)) • (1 : H →L[ℂ] H)))
          * Ring.inverse (A + Complex.I • (1 : H →L[ℂ] H)) := by
  have hAdd := isUnit_add_I_smul_one_of_isSelfAdjoint A hA
  have h1m : (1 : ℂ) - μ ≠ 0 := sub_ne_zero.mpr (Ne.symm hμ)
  have hscalar : (μ - 1) * (Complex.I * (1 + μ) / (1 - μ)) = -(Complex.I * (μ + 1)) := by
    field_simp
    ring
  have hclm : μ • (A + Complex.I • (1 : H →L[ℂ] H)) - (A - Complex.I • (1 : H →L[ℂ] H))
      = (μ - 1) • (A - (Complex.I * (1 + μ) / (1 - μ)) • (1 : H →L[ℂ] H)) := by
    have e : (μ - 1) • ((Complex.I * (1 + μ) / (1 - μ)) • (1 : H →L[ℂ] H))
        = -(Complex.I * (μ + 1)) • (1 : H →L[ℂ] H) := by
      rw [smul_smul, hscalar]
    have e2 : μ • (Complex.I • (1 : H →L[ℂ] H)) + Complex.I • (1 : H →L[ℂ] H)
        = (Complex.I * (μ + 1)) • (1 : H →L[ℂ] H) := by
      calc μ • (Complex.I • (1 : H →L[ℂ] H)) + Complex.I • (1 : H →L[ℂ] H)
          = (μ + 1) • (Complex.I • (1 : H →L[ℂ] H)) := by module
        _ = ((μ + 1) * Complex.I) • (1 : H →L[ℂ] H) := by rw [smul_smul]
        _ = (Complex.I * (μ + 1)) • (1 : H →L[ℂ] H) := by rw [mul_comm]
    calc μ • (A + Complex.I • (1 : H →L[ℂ] H)) - (A - Complex.I • (1 : H →L[ℂ] H))
        = (μ - 1) • A + (μ • (Complex.I • (1 : H →L[ℂ] H)) + Complex.I • (1 : H →L[ℂ] H)) := by
          module
      _ = (μ - 1) • A + (Complex.I * (μ + 1)) • (1 : H →L[ℂ] H) := by rw [e2]
      _ = (μ - 1) • (A - (Complex.I * (1 + μ) / (1 - μ)) • (1 : H →L[ℂ] H)) := by
          rw [smul_sub, e, neg_smul, sub_neg_eq_add]
  have step1 : μ • (1 : H →L[ℂ] H)
      = (μ • (A + Complex.I • (1 : H →L[ℂ] H)))
          * Ring.inverse (A + Complex.I • (1 : H →L[ℂ] H)) := by
    rw [smul_mul_assoc, Ring.mul_inverse_cancel _ hAdd]
  calc algebraMap ℂ (H →L[ℂ] H) μ - cayleyTransform A
      = (μ • (A + Complex.I • (1 : H →L[ℂ] H))) * Ring.inverse (A + Complex.I • (1 : H →L[ℂ] H))
          - (A - Complex.I • (1 : H →L[ℂ] H)) * Ring.inverse (A + Complex.I • (1 : H →L[ℂ] H)) := by
        rw [Algebra.algebraMap_eq_smul_one, step1, cayleyTransform]
    _ = (μ • (A + Complex.I • (1 : H →L[ℂ] H)) - (A - Complex.I • (1 : H →L[ℂ] H)))
          * Ring.inverse (A + Complex.I • (1 : H →L[ℂ] H)) := by
        conv_rhs => rw [sub_mul]
    _ = ((μ - 1) • (A - (Complex.I * (1 + μ) / (1 - μ)) • (1 : H →L[ℂ] H)))
          * Ring.inverse (A + Complex.I • (1 : H →L[ℂ] H)) := by rw [hclm]

/-- `1` is never in the spectrum of the Cayley transform. -/
theorem one_notMem_spectrum_cayleyTransform (hA : IsSelfAdjoint A) :
    (1 : ℂ) ∉ spectrum ℂ (cayleyTransform A) := by
  rw [spectrum.mem_iff, map_one]
  exact fun h => h (isUnit_one_sub_cayleyTransform A hA)

/-- The image direction of the spectral mapping: if `w` is in the spectrum
of `A`, then `(w - i) / (w + i)` is in the spectrum of `U`. -/
theorem mem_spectrum_cayleyTransform_of_mem_spectrum (hA : IsSelfAdjoint A)
    {w : ℂ} (hw : w ∈ spectrum ℂ A) :
    (w - Complex.I) / (w + Complex.I) ∈ spectrum ℂ (cayleyTransform A) := by
  have hwI : w + Complex.I ≠ 0 := by
    intro h
    have hw' : w = -Complex.I := by linear_combination h
    rw [spectrum.mem_iff] at hw
    apply hw
    rw [hw']
    have hEq : algebraMap ℂ (H →L[ℂ] H) (-Complex.I) - A
        = -(A + Complex.I • (1 : H →L[ℂ] H)) := by
      rw [map_neg, Algebra.algebraMap_eq_smul_one]
      module
    rw [hEq]
    exact (isUnit_add_I_smul_one_of_isSelfAdjoint A hA).neg
  set μ := (w - Complex.I) / (w + Complex.I) with hμdef
  have hμ1 : μ ≠ 1 := by
    intro h
    rw [hμdef, div_eq_one_iff_eq hwI] at h
    have hI : Complex.I = 0 := by linear_combination -h / 2
    exact Complex.I_ne_zero hI
  have h1m : (1 : ℂ) - μ ≠ 0 := sub_ne_zero.mpr (Ne.symm hμ1)
  have hwval : w = Complex.I * (1 + μ) / (1 - μ) := by
    rw [hμdef, div_eq_iff hwI] at *
    -- goal: w = i * (1 + (w - i)/(w + i)) / (1 - (w - i)/(w + i))
    rw [eq_div_iff h1m]
    field_simp
    ring
  rw [spectrum.mem_iff] at hw ⊢
  intro hunitU
  apply hw
  have hfact := algebraMap_sub_cayleyTransform A hA hμ1
  rw [hfact] at hunitU
  have hunitS : IsUnit ((μ - 1) • (A - (Complex.I * (1 + μ) / (1 - μ)) • (1 : H →L[ℂ] H))) := by
    have hInv : IsUnit (Ring.inverse (A + Complex.I • (1 : H →L[ℂ] H))) :=
      isUnit_ringInverse_add_I_of_isSelfAdjoint A hA
    have h := IsUnit.mul hunitU (show IsUnit (Ring.inverse
      (Ring.inverse (A + Complex.I • (1 : H →L[ℂ] H)))) from by
      rw [← hInv.unit_spec, Ring.inverse_unit]; exact Units.isUnit _)
    rwa [mul_assoc, Ring.mul_inverse_cancel _ hInv, mul_one] at h
  rw [← hwval] at hunitS
  have hunitA : IsUnit (A - w • (1 : H →L[ℂ] H)) := by
    have hsmul : (μ - 1) • (A - w • (1 : H →L[ℂ] H))
        = ((μ - 1) • (1 : H →L[ℂ] H)) * (A - w • (1 : H →L[ℂ] H)) := by
      rw [Algebra.smul_def, Algebra.algebraMap_eq_smul_one]
    rw [hsmul] at hunitS
    have h := IsUnit.mul (show IsUnit (Ring.inverse ((μ - 1) • (1 : H →L[ℂ] H))) from by
      rw [← (isUnit_smul_one _ (sub_ne_zero.mpr hμ1)).unit_spec, Ring.inverse_unit]
      exact Units.isUnit _) hunitS
    rwa [← mul_assoc, Ring.inverse_mul_cancel _ (isUnit_smul_one _ (sub_ne_zero.mpr hμ1)),
      one_mul] at h
  rw [Algebra.algebraMap_eq_smul_one, ← neg_sub]
  exact hunitA.neg

/-- The preimage direction of the spectral mapping: every point of the
spectrum of `U` is `(w - i) / (w + i)` for some `w` in the spectrum of `A`. -/
theorem exists_mem_spectrum_of_mem_spectrum_cayleyTransform (hA : IsSelfAdjoint A)
    {μ : ℂ} (hμ : μ ∈ spectrum ℂ (cayleyTransform A)) :
    ∃ w ∈ spectrum ℂ A, (w - Complex.I) / (w + Complex.I) = μ := by
  have hμ1 : μ ≠ 1 := fun h => one_notMem_spectrum_cayleyTransform A hA (h ▸ hμ)
  have h1m : (1 : ℂ) - μ ≠ 0 := sub_ne_zero.mpr (Ne.symm hμ1)
  set w := Complex.I * (1 + μ) / (1 - μ) with hwdef
  have hwI : w + Complex.I ≠ 0 := by
    have hval : w + Complex.I = 2 * Complex.I / (1 - μ) := by
      rw [hwdef]
      field_simp
      ring
    rw [hval]
    exact div_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) h1m
  have hμeq : μ = (w - Complex.I) / (w + Complex.I) := by
    rw [hwdef]
    field_simp
    ring
  have hwmem : w ∈ spectrum ℂ A := by
    rw [spectrum.mem_iff] at hμ ⊢
    intro hunitA
    apply hμ
    have hfact := algebraMap_sub_cayleyTransform A hA hμ1
    have hneg : A - (Complex.I * (1 + μ) / (1 - μ)) • (1 : H →L[ℂ] H)
        = -(algebraMap ℂ (H →L[ℂ] H) w - A) := by
      rw [← hwdef, Algebra.algebraMap_eq_smul_one, neg_sub]
    rw [hfact, hneg]
    have hunit1 : IsUnit ((μ - 1) • (algebraMap ℂ (H →L[ℂ] H) w - A)) := by
      rw [Algebra.smul_def]
      have hscalar : IsUnit (algebraMap ℂ (H →L[ℂ] H) (μ - 1)) := by
        rw [Algebra.algebraMap_eq_smul_one]
        exact isUnit_smul_one _ (sub_ne_zero.mpr hμ1)
      exact IsUnit.mul hscalar hunitA
    have hunit2 : IsUnit (((μ - 1) • (-(algebraMap ℂ (H →L[ℂ] H) w - A)))
        * Ring.inverse (A + Complex.I • (1 : H →L[ℂ] H))) := by
      apply IsUnit.mul _ (isUnit_ringInverse_add_I_of_isSelfAdjoint A hA)
      rw [smul_neg]
      exact hunit1.neg
    exact hunit2
  exact ⟨w, hwmem, hμeq.symm⟩

/-- The spectrum of the Cayley transform is the image of the spectrum of `A`
under the Möbius map `λ ↦ (λ - i) / (λ + i)`. -/
theorem spectrum_cayleyTransform (hA : IsSelfAdjoint A) :
    spectrum ℂ (cayleyTransform A)
      = (fun w => (w - Complex.I) / (w + Complex.I)) '' spectrum ℂ A := by
  ext μ
  constructor
  · intro hμ
    exact exists_mem_spectrum_of_mem_spectrum_cayleyTransform A hA hμ
  · rintro ⟨w, hw, rfl⟩
    exact mem_spectrum_cayleyTransform_of_mem_spectrum A hA hw

/-- Points of the spectrum of the Cayley transform lie on the unit circle. -/
theorem norm_eq_one_of_mem_spectrum_cayleyTransform (hA : IsSelfAdjoint A)
    {μ : ℂ} (hμ : μ ∈ spectrum ℂ (cayleyTransform A)) : ‖μ‖ = 1 := by
  exact spectrum.norm_eq_one_of_unitary (mem_unitary_cayleyTransform A hA) hμ

/-- The eigenvalue correspondence: for `μ ≠ 1`, `μ` is an eigenvalue of the
Cayley transform `U` iff `i * (1 + μ) / (1 - μ)` is an eigenvalue of `A`. -/
theorem hasEigenvalue_cayleyTransform_iff (hA : IsSelfAdjoint A) {μ : ℂ} (hμ : μ ≠ 1) :
    Module.End.HasEigenvalue ((cayleyTransform A : H →L[ℂ] H) : Module.End ℂ H) μ ↔
      Module.End.HasEigenvalue ((A : H →L[ℂ] H) : Module.End ℂ H)
        (Complex.I * (1 + μ) / (1 - μ)) := by
  have hAdd := isUnit_add_I_smul_one_of_isSelfAdjoint A hA
  have h1m : (1 : ℂ) - μ ≠ 0 := sub_ne_zero.mpr (Ne.symm hμ)
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h.exists_hasEigenvector
    have hUx : cayleyTransform A x = μ • x := by
      have hmem := Module.End.mem_eigenspace_iff.mp hx.1
      simpa using hmem
    set y := Ring.inverse (A + Complex.I • (1 : H →L[ℂ] H)) x with hy
    have hxy : (A + Complex.I • (1 : H →L[ℂ] H)) y = x := by
      rw [hy, ← mul_apply_eq_comp, Ring.mul_inverse_cancel _ hAdd, one_apply_eq_self]
    have hy0 : y ≠ 0 := by
      intro hy0
      apply hx.2
      rw [← hxy, hy0, map_zero]
    have h1 : (A - Complex.I • (1 : H →L[ℂ] H)) y = μ • ((A + Complex.I • (1 : H →L[ℂ] H)) y) := by
      rw [hxy]
      have hUx' := hUx
      rw [cayleyTransform, mul_apply_eq_comp, ← hy] at hUx'
      exact hUx'
    have hsub : A y - μ • (A y) = Complex.I • y + μ • (Complex.I • y) := by
      have h1' : A y - Complex.I • y = μ • (A y) + μ • (Complex.I • y) := by
        rw [sub_apply, smul_apply,
          one_apply_eq_self, add_apply,
          smul_apply, one_apply_eq_self, smul_add] at h1
        exact h1
      calc A y - μ • (A y)
          = (A y - Complex.I • y) + (Complex.I • y - μ • (A y)) := by module
        _ = (μ • (A y) + μ • (Complex.I • y)) + (Complex.I • y - μ • (A y)) := by rw [h1']
        _ = Complex.I • y + μ • (Complex.I • y) := by module
    have h2 : (1 - μ) • (A y) = ((1 + μ) * Complex.I) • y := by
      calc (1 - μ) • (A y) = A y - μ • (A y) := by rw [sub_smul, one_smul]
        _ = Complex.I • y + μ • (Complex.I • y) := hsub
        _ = ((1 + μ) * Complex.I) • y := by rw [← smul_smul]; module
    have hAyeq : A y = (Complex.I * (1 + μ) / (1 - μ)) • y := by
      calc A y = (1 - μ)⁻¹ • ((1 - μ) • (A y)) := by rw [inv_smul_smul₀ h1m]
        _ = (1 - μ)⁻¹ • (((1 + μ) * Complex.I) • y) := by rw [h2]
        _ = (((1 - μ)⁻¹ * ((1 + μ) * Complex.I)) • y) := by rw [smul_smul]
        _ = (Complex.I * (1 + μ) / (1 - μ)) • y := by
            congr 1
            rw [div_eq_mul_inv, mul_comm ((1 - μ)⁻¹ : ℂ) ((1 + μ) * Complex.I),
              mul_comm (1 + μ) Complex.I]
    refine Module.End.hasEigenvalue_of_hasEigenvector ⟨?_, hy0⟩
    rw [Module.End.mem_eigenspace_iff]
    exact hAyeq
  · intro h
    obtain ⟨y, hy⟩ := h.exists_hasEigenvector
    have hAy : A y = (Complex.I * (1 + μ) / (1 - μ)) • y := by
      have hmem := Module.End.mem_eigenspace_iff.mp hy.1
      simpa using hmem
    set x := (A + Complex.I • (1 : H →L[ℂ] H)) y with hx
    have hx0 : x ≠ 0 := by
      intro hx0
      have hy' : y = Ring.inverse (A + Complex.I • (1 : H →L[ℂ] H))
          ((A + Complex.I • (1 : H →L[ℂ] H)) y) := by
        rw [← mul_apply_eq_comp, Ring.inverse_mul_cancel _ hAdd, one_apply_eq_self]
      have h1 : Ring.inverse (A + Complex.I • (1 : H →L[ℂ] H)) x = y := by
        rw [hx, ← hy']
      have hy0 : y = 0 := by rw [← h1, hx0, map_zero]
      exact hy.2 hy0
    have hsc : (Complex.I * (1 + μ) / (1 - μ)) - Complex.I
        = μ * (Complex.I * (1 + μ) / (1 - μ) + Complex.I) := by
      field_simp
      ring
    have hUx : cayleyTransform A x = μ • x := by
      have hx1 : cayleyTransform A x
          = (A - Complex.I • (1 : H →L[ℂ] H)) y := by
        rw [cayleyTransform, mul_apply_eq_comp, hx]
        congr 1
        rw [← mul_apply_eq_comp, Ring.inverse_mul_cancel _ hAdd, one_apply_eq_self]
      rw [hx1]
      have e1 : (A - Complex.I • (1 : H →L[ℂ] H)) y
          = (Complex.I * (1 + μ) / (1 - μ) - Complex.I) • y := by
        rw [sub_apply, smul_apply,
          one_apply_eq_self, hAy, ← sub_smul]
      have e2 : μ • x = (μ * (Complex.I * (1 + μ) / (1 - μ) + Complex.I)) • y := by
        rw [hx, add_apply, smul_apply,
          one_apply_eq_self, hAy, ← add_smul, smul_smul]
      rw [e1, e2, hsc]
    refine Module.End.hasEigenvalue_of_hasEigenvector ⟨?_, hx0⟩
    rw [Module.End.mem_eigenspace_iff]
    exact hUx

end SelfAdjoint

end ContinuousLinearMap

end MathlibExt.Analysis.InnerProductSpace.CayleyTransform
