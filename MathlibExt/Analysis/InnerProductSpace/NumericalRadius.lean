/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Complex.Module

/-!
# The numerical radius of a bounded operator

For a bounded operator `T` on a complex Hilbert space, the numerical radius is

  `w(T) = sup { ‖⟪T x, x⟫‖ : ‖x‖ = 1 }`,

the supremum of the moduli in the numerical range. It need not be attained.
The existing `numericalRange` API in
`MathlibExt/Analysis/InnerProductSpace/ToeplitzHausdorff.lean` uses the same
quadratic form on unit vectors. The main results here are the
standard two-sided estimate, valid for complex Hilbert spaces only:

* `w(T) ≤ ‖T‖`, by Cauchy–Schwarz;
* `‖T‖ ≤ 2 * w(T)`, via the Cartesian decomposition `T = A + i * B` into
  the self-adjoint parts `A = (T + T*) / 2` and `B = (T - T*) / (2 * i)`,
  whose quadratic forms are the real and imaginary parts of `⟪T x, x⟫`
  (up to the sign coming from Mathlib's convention that the inner product
  is conjugate-linear in its first argument), combined with the fact that
  a self-adjoint operator has norm equal to the supremum of its Rayleigh
  quotient.

Consequences included: the radius of a self-adjoint operator equals its
operator norm, and the radius is invariant under taking adjoints. The bound
`‖T‖ ≤ 2 * w(T)` is false over the reals (a quarter-turn rotation of `ℝ²`
has numerical radius `0` and norm `1`), so everything is stated over `ℂ`.

This is a companion to the self-adjoint / spectral material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`
(May 2021). It is a newly proved supporting result outside the 72 v1 targets.
The radius is linked to the existing numerical range; the Cartesian parts
are coerced aliases of Mathlib's `realPart` and `imaginaryPart`.
The two-sided estimate uses Mathlib's adjoint and Rayleigh-quotient APIs.

## Main declarations

* `numericalRadius` : the numerical radius `w(T)`.
* `cartesianRealPart` / `cartesianImagPart` : the Cartesian (self-adjoint)
  parts of `T`, as compatible aliases of Mathlib's self-adjoint subtype values.
* `numericalRadius_le_norm` : `w(T) ≤ ‖T‖`.
* `norm_le_two_mul_numericalRadius` : `‖T‖ ≤ 2 * w(T)`.
* `numericalRadius_eq_norm_of_isSelfAdjoint` : `w(T) = ‖T‖` for `T`
  self-adjoint.
* `numericalRadius_adjoint` : `w(T*) = w(T)`.
-/

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.NumericalRadius

open scoped _root_.InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The numerical radius of a bounded operator on a complex Hilbert space:
the supremum of `‖⟪T x, x⟫‖` over unit vectors `x`. -/
noncomputable def numericalRadius (T : H →L[ℂ] H) : ℝ :=
  ⨆ x : { x : H // ‖x‖ = 1 }, ‖⟪T (x : H), (x : H)⟫_ℂ‖

/-- The operator-valued alias of Mathlib's `realPart T`: `(T + T*) / 2`. -/
noncomputable def cartesianRealPart (T : H →L[ℂ] H) : H →L[ℂ] H :=
  ↑(realPart T)

/-- The operator-valued alias of Mathlib's `imaginaryPart T`: `(T - T*) / (2 * i)`. -/
noncomputable def cartesianImagPart (T : H →L[ℂ] H) : H →L[ℂ] H :=
  ↑(imaginaryPart T)

omit [CompleteSpace H] in
/-- The family defining the numerical radius is bounded above by `‖T‖`. -/
theorem bddAbove_numericalRadius (T : H →L[ℂ] H) :
    BddAbove (Set.range fun x : { x : H // ‖x‖ = 1 } => ‖⟪T (x : H), (x : H)⟫_ℂ‖) := by
  refine ⟨‖T‖, ?_⟩
  rintro r ⟨x, rfl⟩
  calc ‖⟪T (x : H), (x : H)⟫_ℂ‖ ≤ ‖T (x : H)‖ * ‖(x : H)‖ := norm_inner_le_norm _ _
    _ = ‖T (x : H)‖ := by rw [x.property, mul_one]
    _ ≤ ‖T‖ * ‖(x : H)‖ := T.le_opNorm _
    _ = ‖T‖ := by rw [x.property, mul_one]

omit [CompleteSpace H] in
/-- The numerical radius is nonnegative. -/
theorem numericalRadius_nonneg (T : H →L[ℂ] H) : 0 ≤ numericalRadius T := by
  show 0 ≤ ⨆ x : { x : H // ‖x‖ = 1 }, ‖⟪T (x : H), (x : H)⟫_ℂ‖
  exact Real.iSup_nonneg fun _ => norm_nonneg _

omit [CompleteSpace H] in
/-- The numerical radius dominates the quadratic form at any unit vector. -/
theorem le_numericalRadius {T : H →L[ℂ] H} {x : H} (hx : ‖x‖ = 1) :
    ‖⟪T x, x⟫_ℂ‖ ≤ numericalRadius T := by
  show ‖⟪T x, x⟫_ℂ‖
    ≤ ⨆ y : { y : H // ‖y‖ = 1 }, ‖⟪T (y : H), (y : H)⟫_ℂ‖
  exact le_ciSup (bddAbove_numericalRadius T) ⟨x, hx⟩

omit [CompleteSpace H] in
/-- A uniform bound on the quadratic form over unit vectors bounds the
numerical radius. -/
theorem numericalRadius_le {T : H →L[ℂ] H} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x : H, ‖x‖ = 1 → ‖⟪T x, x⟫_ℂ‖ ≤ c) : numericalRadius T ≤ c := by
  show (⨆ y : { y : H // ‖y‖ = 1 }, ‖⟪T (y : H), (y : H)⟫_ℂ‖) ≤ c
  exact Real.iSup_le (fun ⟨x, hx⟩ => h x hx) hc

omit [CompleteSpace H] in
/-- The numerical radius is at most the operator norm (Cauchy–Schwarz). -/
theorem numericalRadius_le_norm (T : H →L[ℂ] H) : numericalRadius T ≤ ‖T‖ := by
  refine numericalRadius_le (norm_nonneg T) fun x hx => ?_
  calc ‖⟪T x, x⟫_ℂ‖ ≤ ‖T x‖ * ‖x‖ := norm_inner_le_norm _ _
    _ = ‖T x‖ := by rw [hx, mul_one]
    _ ≤ ‖T‖ * ‖x‖ := T.le_opNorm _
    _ = ‖T‖ := by rw [hx, mul_one]

omit [CompleteSpace H] in
/-- The quadratic form scales quadratically: evaluating at `‖x‖⁻¹ • x`
divides it by `‖x‖²`. -/
theorem quadForm_scale (T : H →L[ℂ] H) {x : H} :
    ⟪T ((RCLike.ofReal (‖x‖⁻¹) : ℂ) • x), ((RCLike.ofReal (‖x‖⁻¹) : ℂ) • x)⟫_ℂ
      = (RCLike.ofReal ((‖x‖ ^ 2)⁻¹) : ℂ) * ⟪T x, x⟫_ℂ := by
  rw [map_smul, inner_smul_left, inner_smul_right, RCLike.conj_ofReal,
    ← mul_assoc, ← RCLike.ofReal_mul]
  congr 1
  rw [← inv_pow, pow_two]

omit [CompleteSpace H] in
/-- The unit vector obtained by normalizing `x`. -/
theorem norm_normalize {x : H} (hx : x ≠ 0) :
    ‖((RCLike.ofReal (‖x‖⁻¹) : ℂ) • x)‖ = 1 := by
  rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

omit [CompleteSpace H] in
/-- The real part of the quadratic form, divided by `‖x‖²`, is at most the
numerical radius. -/
theorem abs_re_quadForm_div_le_numericalRadius (T : H →L[ℂ] H) (x : H) :
    |RCLike.re ⟪T x, x⟫_ℂ| / ‖x‖ ^ 2 ≤ numericalRadius T := by
  by_cases hx : x = 0
  · subst hx
    simp [numericalRadius_nonneg]
  · have h2 : (0 : ℝ) < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx) 2
    calc |RCLike.re ⟪T x, x⟫_ℂ| / ‖x‖ ^ 2
        = |RCLike.re ⟪T ((RCLike.ofReal (‖x‖⁻¹) : ℂ) • x),
            ((RCLike.ofReal (‖x‖⁻¹) : ℂ) • x)⟫_ℂ| := by
          rw [quadForm_scale T, RCLike.re_ofReal_mul, abs_mul,
            abs_of_pos (inv_pos.mpr h2), div_eq_mul_inv, mul_comm]
      _ ≤ ‖⟪T ((RCLike.ofReal (‖x‖⁻¹) : ℂ) • x),
            ((RCLike.ofReal (‖x‖⁻¹) : ℂ) • x)⟫_ℂ‖ :=
          RCLike.abs_re_le_norm _
      _ ≤ numericalRadius T := le_numericalRadius (norm_normalize hx)

omit [CompleteSpace H] in
/-- The imaginary part of the quadratic form, divided by `‖x‖²`, is at most
the numerical radius. -/
theorem abs_im_quadForm_div_le_numericalRadius (T : H →L[ℂ] H) (x : H) :
    |RCLike.im ⟪T x, x⟫_ℂ| / ‖x‖ ^ 2 ≤ numericalRadius T := by
  by_cases hx : x = 0
  · subst hx
    simp [numericalRadius_nonneg]
  · have h2 : (0 : ℝ) < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx) 2
    calc |RCLike.im ⟪T x, x⟫_ℂ| / ‖x‖ ^ 2
        = |RCLike.im ⟪T ((RCLike.ofReal (‖x‖⁻¹) : ℂ) • x),
            ((RCLike.ofReal (‖x‖⁻¹) : ℂ) • x)⟫_ℂ| := by
          rw [quadForm_scale T, RCLike.im_ofReal_mul, abs_mul,
            abs_of_pos (inv_pos.mpr h2), div_eq_mul_inv, mul_comm]
      _ ≤ ‖⟪T ((RCLike.ofReal (‖x‖⁻¹) : ℂ) • x),
            ((RCLike.ofReal (‖x‖⁻¹) : ℂ) • x)⟫_ℂ‖ :=
          RCLike.abs_im_le_norm _
      _ ≤ numericalRadius T := le_numericalRadius (norm_normalize hx)

omit [CompleteSpace H] in
/-- The absolute Rayleigh quotient at any vector is at most the numerical
radius. -/
theorem abs_rayleighQuotient_le_numericalRadius (T : H →L[ℂ] H) (x : H) :
    |T.rayleighQuotient x| ≤ numericalRadius T := by
  rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
    abs_div, abs_of_nonneg (sq_nonneg (‖x‖))]
  exact abs_re_quadForm_div_le_numericalRadius T x

/-- Conjugation of the scalar `1 / 2`. -/
theorem starRingEnd_half : starRingEnd ℂ (1 / 2 : ℂ) = 1 / 2 := by
  rw [map_div₀, map_one, map_ofNat]

/-- Conjugation of the scalar `-i / 2` is `i / 2`. -/
theorem starRingEnd_neg_I_div_two :
    starRingEnd ℂ (-(Complex.I / 2) : ℂ) = Complex.I / 2 := by
  rw [show (Complex.I : ℂ) = RCLike.I from rfl, map_neg, map_div₀, RCLike.conj_I,
    map_ofNat]
  ring

/-- The real Cartesian part is symmetric. -/
theorem isSymmetric_cartesianRealPart (T : H →L[ℂ] H) :
    LinearMap.IsSymmetric (cartesianRealPart T : H →ₗ[ℂ] H) := by
  exact (show IsSelfAdjoint (cartesianRealPart T) from (realPart T).property).isSymmetric

/-- The imaginary Cartesian part is symmetric. -/
theorem isSymmetric_cartesianImagPart (T : H →L[ℂ] H) :
    LinearMap.IsSymmetric (cartesianImagPart T : H →ₗ[ℂ] H) := by
  exact (show IsSelfAdjoint (cartesianImagPart T) from (imaginaryPart T).property).isSymmetric

/-- The quadratic form of the real Cartesian part is the real part of the
quadratic form. -/
theorem quadForm_cartesianRealPart (T : H →L[ℂ] H) (x : H) :
    ⟪cartesianRealPart T x, x⟫_ℂ = (RCLike.ofReal (RCLike.re ⟪T x, x⟫_ℂ) : ℂ) := by
  simp only [cartesianRealPart]
  rw [realPart_apply_coe, ← Complex.coe_smul, ContinuousLinearMap.star_eq_adjoint]
  have hhalf : (((2 : ℝ)⁻¹ : ℝ) : ℂ) = (1 / 2 : ℂ) := by norm_num
  rw [hhalf]
  simp only [smul_apply, add_apply, inner_smul_left, inner_add_left,
    ContinuousLinearMap.adjoint_inner_left]
  rw [show ⟪x, T x⟫_ℂ = starRingEnd ℂ ⟪T x, x⟫_ℂ from (inner_conj_symm x (T x)).symm,
    starRingEnd_half, RCLike.add_conj, ← mul_assoc]
  norm_num

/-- The quadratic form of the imaginary Cartesian part is the negative
imaginary part of the quadratic form. The sign is the shadow of Mathlib's
convention that the inner product is conjugate-linear in its first
argument: for the Cartesian decomposition `T = A + i * B`, one has
`⟪T x, x⟫ = ⟪A x, x⟫ - i * ⟪B x, x⟫`, so `⟪B x, x⟫ = -Im ⟪T x, x⟫`. -/
theorem quadForm_cartesianImagPart (T : H →L[ℂ] H) (x : H) :
    ⟪cartesianImagPart T x, x⟫_ℂ = (RCLike.ofReal (-(RCLike.im ⟪T x, x⟫_ℂ)) : ℂ) := by
  simp only [cartesianImagPart]
  rw [imaginaryPart_apply_coe, ← Complex.coe_smul,
    ContinuousLinearMap.star_eq_adjoint, smul_smul]
  have hhalf : (((2 : ℝ)⁻¹ : ℝ) : ℂ) = (1 / 2 : ℂ) := by norm_num
  rw [hhalf]
  have hcoeff : -(Complex.I) * (1 / 2 : ℂ) = -(Complex.I / 2) := by ring
  rw [hcoeff]
  simp only [smul_apply, sub_apply, inner_smul_left, inner_sub_left,
    ContinuousLinearMap.adjoint_inner_left]
  rw [show ⟪x, T x⟫_ℂ = starRingEnd ℂ ⟪T x, x⟫_ℂ from (inner_conj_symm x (T x)).symm,
    starRingEnd_neg_I_div_two, RCLike.sub_conj,
    show (Complex.I : ℂ) = RCLike.I from rfl]
  calc (RCLike.I / 2 : ℂ) * (2 * (RCLike.ofReal (RCLike.im ⟪T x, x⟫_ℂ) : ℂ) * RCLike.I)
      = (RCLike.ofReal (RCLike.im ⟪T x, x⟫_ℂ) : ℂ) * (RCLike.I * RCLike.I) := by ring
    _ = (RCLike.ofReal (-(RCLike.im ⟪T x, x⟫_ℂ)) : ℂ) := by
        rw [RCLike.I_mul_I_of_nonzero (by
          rw [show (RCLike.I : ℂ) = Complex.I from rfl]; exact Complex.I_ne_zero),
          RCLike.ofReal_neg]
        ring

/-- The Cartesian decomposition `T = A + i * B`. -/
theorem cartesian_decomposition (T : H →L[ℂ] H) :
    T = cartesianRealPart T + Complex.I • cartesianImagPart T := by
  exact (realPart_add_I_smul_imaginaryPart T).symm

/-- The norm of the real Cartesian part is at most the numerical radius. -/
theorem norm_cartesianRealPart_le_numericalRadius (T : H →L[ℂ] H) :
    ‖cartesianRealPart T‖ ≤ numericalRadius T := by
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient (cartesianRealPart T)
    (realPart T).property.isSymmetric]
  refine Real.iSup_le ?_ (numericalRadius_nonneg T)
  intro x
  rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
    quadForm_cartesianRealPart, RCLike.ofReal_re, abs_div,
    abs_of_nonneg (sq_nonneg (‖x‖))]
  exact abs_re_quadForm_div_le_numericalRadius T x

/-- The norm of the imaginary Cartesian part is at most the numerical radius. -/
theorem norm_cartesianImagPart_le_numericalRadius (T : H →L[ℂ] H) :
    ‖cartesianImagPart T‖ ≤ numericalRadius T := by
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient (cartesianImagPart T)
    (imaginaryPart T).property.isSymmetric]
  refine Real.iSup_le ?_ (numericalRadius_nonneg T)
  intro x
  rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
    quadForm_cartesianImagPart]
  have h : RCLike.re ((RCLike.ofReal (-(RCLike.im ⟪T x, x⟫_ℂ)) : ℂ))
      = -RCLike.im ⟪T x, x⟫_ℂ :=
    RCLike.ofReal_re _
  rw [h, abs_div, abs_neg, abs_of_nonneg (sq_nonneg (‖x‖))]
  exact abs_im_quadForm_div_le_numericalRadius T x

/-- The operator norm is at most twice the numerical radius. -/
theorem norm_le_two_mul_numericalRadius (T : H →L[ℂ] H) :
    ‖T‖ ≤ 2 * numericalRadius T := by
  conv_lhs => rw [cartesian_decomposition T]
  calc ‖cartesianRealPart T + Complex.I • cartesianImagPart T‖
      ≤ ‖cartesianRealPart T‖ + ‖Complex.I • cartesianImagPart T‖ := norm_add_le _ _
    _ = ‖cartesianRealPart T‖ + ‖cartesianImagPart T‖ := by
        rw [norm_smul, Complex.norm_I, one_mul]
    _ ≤ numericalRadius T + numericalRadius T :=
        add_le_add (norm_cartesianRealPart_le_numericalRadius T)
          (norm_cartesianImagPart_le_numericalRadius T)
    _ = 2 * numericalRadius T := by ring

/-- For a self-adjoint operator, the numerical radius equals the operator
norm. -/
theorem numericalRadius_eq_norm_of_isSelfAdjoint {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) :
    numericalRadius T = ‖T‖ := by
  apply le_antisymm (numericalRadius_le_norm T)
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient T hT.isSymmetric]
  exact Real.iSup_le (fun x => abs_rayleighQuotient_le_numericalRadius T x)
    (numericalRadius_nonneg T)

/-- The norm of the quadratic form is unchanged by taking the adjoint,
since `⟪T* x, x⟫` is the conjugate of `⟪T x, x⟫`. -/
theorem norm_quadForm_adjoint (T : H →L[ℂ] H) (x : H) :
    ‖⟪ContinuousLinearMap.adjoint T x, x⟫_ℂ‖ = ‖⟪T x, x⟫_ℂ‖ := by
  rw [ContinuousLinearMap.adjoint_inner_left,
    show ⟪x, T x⟫_ℂ = starRingEnd ℂ ⟪T x, x⟫_ℂ from (inner_conj_symm x (T x)).symm,
    starRingEnd_apply, norm_star]

/-- The numerical radius is invariant under taking adjoints. -/
theorem numericalRadius_adjoint (T : H →L[ℂ] H) :
    numericalRadius (ContinuousLinearMap.adjoint T) = numericalRadius T := by
  apply le_antisymm
  · refine numericalRadius_le (numericalRadius_nonneg T) fun x hx => ?_
    rw [norm_quadForm_adjoint]
    exact le_numericalRadius hx
  · refine numericalRadius_le (numericalRadius_nonneg _) fun x hx => ?_
    rw [← norm_quadForm_adjoint]
    exact le_numericalRadius (T := ContinuousLinearMap.adjoint T) hx

end MathlibExt.Analysis.InnerProductSpace.NumericalRadius
