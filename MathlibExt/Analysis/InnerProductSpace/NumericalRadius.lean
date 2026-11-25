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

/-- **Numerical radius.** The numerical radius of a bounded linear operator $T$ on a complex
Hilbert space $H$ is the real number
$w(T) = \sup \{ |\langle T x, x \rangle| : x \in H,\ \|x\| = 1 \}$, the supremum of the moduli of
the values $\langle T x, x \rangle$ over the unit vectors of $H$ (taken to be $0$ when $H = 0$). -/
noncomputable def numericalRadius (T : H →L[ℂ] H) : ℝ :=
  ⨆ x : { x : H // ‖x‖ = 1 }, ‖⟪T (x : H), (x : H)⟫_ℂ‖

/-- **Real Cartesian part of an operator.** For a bounded linear operator $T$ on a complex Hilbert
space with adjoint $T^*$, the real Cartesian part of $T$ is the bounded linear operator
$(T + T^*)/2$. -/
noncomputable def cartesianRealPart (T : H →L[ℂ] H) : H →L[ℂ] H :=
  ↑(realPart T)

/-- **Imaginary Cartesian part of an operator.** For a bounded linear operator $T$ on a complex
Hilbert space with adjoint $T^*$, the imaginary Cartesian part of $T$ is the bounded linear
operator $(T - T^*)/(2i)$. -/
noncomputable def cartesianImagPart (T : H →L[ℂ] H) : H →L[ℂ] H :=
  ↑(imaginaryPart T)

omit [CompleteSpace H] in
/-- **The numerical-radius family is bounded above.** Let $T$ be a bounded linear operator on a
complex inner product space $H$. The set $\{|\langle Tx, x\rangle| : x \in H,\ \|x\| = 1\}$ is
bounded above.

The proof shows that $\|T\|$ is an upper bound, by the Cauchy–Schwarz inequality. -/
theorem bddAbove_numericalRadius (T : H →L[ℂ] H) :
    BddAbove (Set.range fun x : { x : H // ‖x‖ = 1 } => ‖⟪T (x : H), (x : H)⟫_ℂ‖) := by
  refine ⟨‖T‖, ?_⟩
  rintro r ⟨x, rfl⟩
  calc ‖⟪T (x : H), (x : H)⟫_ℂ‖ ≤ ‖T (x : H)‖ * ‖(x : H)‖ := norm_inner_le_norm _ _
    _ = ‖T (x : H)‖ := by rw [x.property, mul_one]
    _ ≤ ‖T‖ * ‖(x : H)‖ := T.le_opNorm _
    _ = ‖T‖ := by rw [x.property, mul_one]

omit [CompleteSpace H] in
/-- **Nonnegativity of the numerical radius.** For every bounded operator $T$ on a complex inner
product space, the numerical radius $w(T)$ of $T$ satisfies $w(T) \ge 0$. -/
theorem numericalRadius_nonneg (T : H →L[ℂ] H) : 0 ≤ numericalRadius T := by
  show 0 ≤ ⨆ x : { x : H // ‖x‖ = 1 }, ‖⟪T (x : H), (x : H)⟫_ℂ‖
  exact Real.iSup_nonneg fun _ => norm_nonneg _

omit [CompleteSpace H] in
/-- **The numerical radius bounds the quadratic form on unit vectors.** Let $T$ be a bounded
linear operator on a complex inner product space $H$, with numerical radius $w(T)$. For every
$x \in H$ with $\|x\| = 1$, $|\langle Tx, x\rangle| \le w(T)$. -/
theorem le_numericalRadius {T : H →L[ℂ] H} {x : H} (hx : ‖x‖ = 1) :
    ‖⟪T x, x⟫_ℂ‖ ≤ numericalRadius T := by
  show ‖⟪T x, x⟫_ℂ‖
    ≤ ⨆ y : { y : H // ‖y‖ = 1 }, ‖⟪T (y : H), (y : H)⟫_ℂ‖
  exact le_ciSup (bddAbove_numericalRadius T) ⟨x, hx⟩

omit [CompleteSpace H] in
/-- **Bounding the numerical radius from above.** Let $T$ be a bounded operator on a complex
inner product space $H$ and let $c \ge 0$ be a real number. If $|\langle T x, x\rangle| \le c$
for every unit vector $x \in H$, then the numerical radius of $T$ satisfies $w(T) \le c$.

The hypothesis $c \ge 0$ matters only when $H = 0$: there are no unit vectors, and $w(T) = 0$. -/
theorem numericalRadius_le {T : H →L[ℂ] H} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x : H, ‖x‖ = 1 → ‖⟪T x, x⟫_ℂ‖ ≤ c) : numericalRadius T ≤ c := by
  show (⨆ y : { y : H // ‖y‖ = 1 }, ‖⟪T (y : H), (y : H)⟫_ℂ‖) ≤ c
  exact Real.iSup_le (fun ⟨x, hx⟩ => h x hx) hc

omit [CompleteSpace H] in
/-- **Numerical radius at most the operator norm.** For every bounded operator $T$ on a complex
inner product space, the numerical radius $w(T)$ is at most the operator norm: $w(T) \le \|T\|$.

The proof is the Cauchy–Schwarz inequality. -/
theorem numericalRadius_le_norm (T : H →L[ℂ] H) : numericalRadius T ≤ ‖T‖ := by
  refine numericalRadius_le (norm_nonneg T) fun x hx => ?_
  calc ‖⟪T x, x⟫_ℂ‖ ≤ ‖T x‖ * ‖x‖ := norm_inner_le_norm _ _
    _ = ‖T x‖ := by rw [hx, mul_one]
    _ ≤ ‖T‖ * ‖x‖ := T.le_opNorm _
    _ = ‖T‖ := by rw [hx, mul_one]

omit [CompleteSpace H] in
/-- **Quadratic form at the normalized vector.** Let $T$ be a bounded operator on a complex inner
product space $H$. For every $x \in H$,
$\langle T(\|x\|^{-1} x), \|x\|^{-1} x \rangle = \|x\|^{-2} \langle T x, x \rangle$,
where $0^{-1}$ is read as $0$, so that for $x = 0$ both sides vanish. -/
theorem quadForm_scale (T : H →L[ℂ] H) {x : H} :
    ⟪T ((RCLike.ofReal (‖x‖⁻¹) : ℂ) • x), ((RCLike.ofReal (‖x‖⁻¹) : ℂ) • x)⟫_ℂ
      = (RCLike.ofReal ((‖x‖ ^ 2)⁻¹) : ℂ) * ⟪T x, x⟫_ℂ := by
  rw [map_smul, inner_smul_left, inner_smul_right, RCLike.conj_ofReal,
    ← mul_assoc, ← RCLike.ofReal_mul]
  congr 1
  rw [← inv_pow, pow_two]

omit [CompleteSpace H] in
/-- **Normalizing a nonzero vector gives a unit vector.** Let $x$ be a nonzero vector in a
complex inner product space. Then the vector $\|x\|^{-1} x$ has norm $1$. -/
theorem norm_normalize {x : H} (hx : x ≠ 0) :
    ‖((RCLike.ofReal (‖x‖⁻¹) : ℂ) • x)‖ = 1 := by
  rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

omit [CompleteSpace H] in
/-- **Numerical radius bounds the normalized real part of the quadratic form.** Let $T$ be a
bounded linear operator on a complex inner product space $H$, with numerical radius $w(T)$. For
every $x \in H$, $|\operatorname{Re} \langle Tx, x\rangle| / \|x\|^2 \le w(T)$, where division by
zero is taken to be $0$, so the case $x = 0$ is trivial. -/
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
/-- **Numerical radius bounds the normalized imaginary part of the quadratic form.** Let $T$ be
a bounded linear operator on a complex inner product space $H$, with numerical radius $w(T)$. For
every $x \in H$, $|\operatorname{Im} \langle Tx, x\rangle| / \|x\|^2 \le w(T)$, where division by
zero is taken to be $0$, so the case $x = 0$ is trivial. -/
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
/-- **Numerical radius bounds the Rayleigh quotient.** Let $T$ be a bounded linear operator on a
complex inner product space $H$, with numerical radius $w(T)$. For every $x \in H$, the Rayleigh
quotient $R_T(x) = \operatorname{Re} \langle Tx, x\rangle / \|x\|^2$, taken to be $0$ at $x = 0$,
satisfies $|R_T(x)| \le w(T)$. -/
theorem abs_rayleighQuotient_le_numericalRadius (T : H →L[ℂ] H) (x : H) :
    |T.rayleighQuotient x| ≤ numericalRadius T := by
  rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
    abs_div, abs_of_nonneg (sq_nonneg (‖x‖))]
  exact abs_re_quadForm_div_le_numericalRadius T x

/-- **Complex conjugate of one half.** The complex conjugate of $1/2 \in \mathbb{C}$ is $1/2$, that
is, $\overline{1/2} = 1/2$. -/
theorem starRingEnd_half : starRingEnd ℂ (1 / 2 : ℂ) = 1 / 2 := by
  rw [map_div₀, map_one, map_ofNat]

/-- **Complex conjugate of minus half the imaginary unit.** The complex conjugate of
$-i/2 \in \mathbb{C}$ is $i/2$, that is, $\overline{-i/2} = i/2$. -/
theorem starRingEnd_neg_I_div_two :
    starRingEnd ℂ (-(Complex.I / 2) : ℂ) = Complex.I / 2 := by
  rw [show (Complex.I : ℂ) = RCLike.I from rfl, map_neg, map_div₀, RCLike.conj_I,
    map_ofNat]
  ring

/-- **The real Cartesian part is symmetric.** For every bounded linear operator $T$ on a complex
Hilbert space $H$ with adjoint $T^*$, the real Cartesian part $A = (T + T^*)/2$ is symmetric:
$\langle Ax, y\rangle = \langle x, Ay\rangle$ for all $x, y \in H$. -/
theorem isSymmetric_cartesianRealPart (T : H →L[ℂ] H) :
    LinearMap.IsSymmetric (cartesianRealPart T : H →ₗ[ℂ] H) := by
  exact (show IsSelfAdjoint (cartesianRealPart T) from (realPart T).property).isSymmetric

/-- **The imaginary Cartesian part is symmetric.** For every bounded linear operator $T$ on a
complex Hilbert space $H$ with adjoint $T^*$, the imaginary Cartesian part $B = (T - T^*)/(2i)$ is
symmetric: $\langle Bx, y\rangle = \langle x, By\rangle$ for all $x, y \in H$. -/
theorem isSymmetric_cartesianImagPart (T : H →L[ℂ] H) :
    LinearMap.IsSymmetric (cartesianImagPart T : H →ₗ[ℂ] H) := by
  exact (show IsSelfAdjoint (cartesianImagPart T) from (imaginaryPart T).property).isSymmetric

/-- **Quadratic form of the real Cartesian part.** Let $T$ be a bounded operator on a complex
Hilbert space $H$ and let $A = (T + T^*)/2$ be the real Cartesian part of $T$. Then for every
$x \in H$ one has $\langle A x, x \rangle = \operatorname{Re} \langle T x, x \rangle$. -/
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

/-- **Quadratic form of the imaginary Cartesian part.** Let $T$ be a bounded operator on a complex
Hilbert space $H$, whose inner product $\langle \cdot, \cdot \rangle$ is conjugate-linear in its
first argument, and let $B = (T - T^*)/(2i)$ be the imaginary Cartesian part of $T$. Then for
every $x \in H$ one has $\langle B x, x \rangle = -\operatorname{Im} \langle T x, x \rangle$.

The sign comes from the convention on the inner product: writing $T = A + iB$ with
$A = (T + T^*)/2$, one has
$\langle T x, x \rangle = \langle A x, x \rangle - i \langle B x, x \rangle$. -/
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

/-- **Cartesian decomposition.** Every bounded linear operator $T$ on a complex Hilbert space
satisfies $T = A + iB$, where $A = (T + T^*)/2$ and $B = (T - T^*)/(2i)$ are the real and
imaginary Cartesian parts of $T$ and $T^*$ is the adjoint of $T$. -/
theorem cartesian_decomposition (T : H →L[ℂ] H) :
    T = cartesianRealPart T + Complex.I • cartesianImagPart T := by
  exact (realPart_add_I_smul_imaginaryPart T).symm

/-- **Norm of the real part is at most the numerical radius.** Let $T$ be a bounded
operator on a complex Hilbert space, with adjoint $T^*$, and let $A = (T + T^*)/2$ be its real
Cartesian part. Then $\|A\| \le w(T)$, where $\|A\|$ is the operator norm of $A$ and $w(T)$ is
the numerical radius of $T$. -/
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

/-- **Norm of the imaginary part is at most the numerical radius.** Let $T$ be a
bounded operator on a complex Hilbert space, with adjoint $T^*$, and let $B = (T - T^*)/(2i)$ be
its imaginary Cartesian part. Then $\|B\| \le w(T)$, where $\|B\|$ is the operator norm of $B$
and $w(T)$ is the numerical radius of $T$. -/
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

/-- **Operator norm at most twice the numerical radius.** For every bounded operator $T$ on a
complex Hilbert space, $\|T\| \le 2\,w(T)$, where $\|T\|$ is the operator norm and $w(T)$ is the
numerical radius of $T$. -/
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

/-- **Numerical radius of a self-adjoint operator.** If $T$ is a self-adjoint bounded operator
on a complex Hilbert space, then its numerical radius equals its operator norm:
$w(T) = \|T\|$. -/
theorem numericalRadius_eq_norm_of_isSelfAdjoint {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) :
    numericalRadius T = ‖T‖ := by
  apply le_antisymm (numericalRadius_le_norm T)
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient T hT.isSymmetric]
  exact Real.iSup_le (fun x => abs_rayleighQuotient_le_numericalRadius T x)
    (numericalRadius_nonneg T)

/-- **The quadratic form of the adjoint has the same modulus.** Let $T$ be a bounded operator
on a complex Hilbert space $H$, with adjoint $T^*$. For every $x \in H$,
$|\langle T^* x, x\rangle| = |\langle T x, x\rangle|$, since $\langle T^* x, x\rangle$ is the
complex conjugate of $\langle T x, x\rangle$. -/
theorem norm_quadForm_adjoint (T : H →L[ℂ] H) (x : H) :
    ‖⟪ContinuousLinearMap.adjoint T x, x⟫_ℂ‖ = ‖⟪T x, x⟫_ℂ‖ := by
  rw [ContinuousLinearMap.adjoint_inner_left,
    show ⟪x, T x⟫_ℂ = starRingEnd ℂ ⟪T x, x⟫_ℂ from (inner_conj_symm x (T x)).symm,
    starRingEnd_apply, norm_star]

/-- **Numerical radius of the adjoint.** For every bounded operator $T$ on a complex Hilbert
space, the numerical radius of its adjoint $T^*$ equals the numerical radius of $T$:
$w(T^*) = w(T)$. -/
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
