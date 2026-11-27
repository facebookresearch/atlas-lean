/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.ArgumentPrincipleCurve
public import MathlibExt.Analysis.SpecialFunctions.Elliptic.ArgumentPrincipleSteps
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# The argument principle for a parallelogram

Let $\omega_1, \omega_2 \in \mathbb{C}$ be linearly independent over $\mathbb{R}$, that is,
$\operatorname{Im}(\omega_2/\omega_1) \ne 0$, let $z_0 \in \mathbb{C}$, and let
$D = \{z_0 + t_1\omega_1 + t_2\omega_2 : 0 < t_1, t_2 < 1\}$ be the open parallelogram with vertices
$z_0$, $z_0 + \omega_1$, $z_0 + \omega_1 + \omega_2$, $z_0 + \omega_2$. For $f$ meromorphic near the
closed parallelogram $\overline{D}$ with no zero or pole on its boundary,

$$\oint_{\partial D} \frac{f'(z)}{f(z)}\,dz = 2\pi i\,\sigma \sum_{P \in D} \mathrm{ord}_P f,$$

where $\sigma = 1$ if $\operatorname{Im}(\omega_2/\omega_1) > 0$ and $\sigma = -1$ otherwise
(`MeromorphicOn.parallelogramBoundaryIntegral_logDeriv`, and
`MeromorphicOn.parallelogramBoundaryIntegral_logDeriv_of_im_pos` for $\sigma = 1$). The boundary
integral is `parallelogramBoundaryIntegral`, the sum of four interval integrals over the sides.

Main declarations:
* `parallelogramPath z₀ ω₁ ω₂`: the boundary as a closed piecewise $C^1$ path
  (`isPiecewiseC1_parallelogramPath`), with its range (`mem_range_parallelogramPath_iff`), the
  curve integral along it, which is `parallelogramBoundaryIntegral` when the four side integrands
  are interval-integrable (`curveIntegral_parallelogramPath`), for instance for an integrand
  continuous on the boundary (`curveIntegral_parallelogramPath_of_continuousOn`), its inside
  (`inside_range_parallelogramPath`) and its winding number (`windingNumber_parallelogramPath`);
* `parallelogramBoundaryIntegral_inv_sub`: $\oint_{\partial D} dz/(z - w) = 2\pi i\,\sigma$ for
  $w \in D$;
* `parallelogramBoundaryIntegral_eq_zero_of_differentiableOn`: Cauchy's theorem for a
  parallelogram;
* `parallelogramBoundaryIntegral_swap`: swapping $\omega_1, \omega_2$ reverses the orientation;
* `PeriodPair.im_ω₂_div_ω₁_ne_zero`: the periods of a period pair satisfy the independence
  hypothesis.

Mathlib has Cauchy's theorem for rectangles but no residue theorem or argument principle for a
rectangle or parallelogram. The proof applies the argument principle for a closed piecewise $C^1$
curve, `MeromorphicOn.argument_principle`, to `parallelogramPath`. Its hypotheses are checked in
coordinates: the real coordinates of $z - z_0$ in the basis $\omega_1, \omega_2$ identify the range
of the path with $\overline{D} \setminus D$, the path is injective on $[0, 1)$, $D$ is a bounded
component of the complement while the ray from the centre through any point outside $\overline{D}$
stays outside, so the inside of the path is $D$, and the winding number is computed at the centre
with the principal logarithm and is constant on the convex set $D$. Mathlib's meromorphic functions
may take arbitrary values on a discrete set, so along each side $f'/f$ agrees with a continuous
function only off a finite set; this is enough for the side integrals to be the curve integral.

## References

* J. S. Milne, *Elliptic Curves*, 2nd ed., World Scientific, 2021; author's version at
  <https://jmilne.org/math/Books/EC2.pdf>, Chapter III, §2, Proposition 2.1 and its proof,
  pp. 86–87.
-/

@[expose] public section

set_option autoImplicit false

open Complex ComplexConjugate Filter MeasureTheory Metric Set Topology
open scoped Real

/-! ### Coordinates with respect to two independent periods -/

/-- `Im(conj ω₁ · ω₂)`, nonzero exactly when `ω₁, ω₂` are linearly independent over `ℝ`. -/
private noncomputable def pdet (ω₁ ω₂ : ℂ) : ℝ := (conj ω₁ * ω₂).im

/-- The first real coordinate of `z - z₀` in the basis `ω₁, ω₂`. -/
private noncomputable def pc₁ (z₀ ω₁ ω₂ z : ℂ) : ℝ := (conj (z - z₀) * ω₂).im / pdet ω₁ ω₂

/-- The second real coordinate of `z - z₀` in the basis `ω₁, ω₂`. -/
private noncomputable def pc₂ (z₀ ω₁ ω₂ z : ℂ) : ℝ := (conj ω₁ * (z - z₀)).im / pdet ω₁ ω₂

private theorem continuous_pc₁ (z₀ ω₁ ω₂ : ℂ) : Continuous (pc₁ z₀ ω₁ ω₂) := by
  unfold pc₁; fun_prop

private theorem continuous_pc₂ (z₀ ω₁ ω₂ : ℂ) : Continuous (pc₂ z₀ ω₁ ω₂) := by
  unfold pc₂; fun_prop

private theorem pc₁_combo {z₀ ω₁ ω₂ : ℂ} (h : pdet ω₁ ω₂ ≠ 0) (a b : ℝ) :
    pc₁ z₀ ω₁ ω₂ (z₀ + a • ω₁ + b • ω₂) = a := by
  have : (conj (z₀ + a • ω₁ + b • ω₂ - z₀) * ω₂).im = a * pdet ω₁ ω₂ := by
    rw [show z₀ + a • ω₁ + b • ω₂ - z₀ = a • ω₁ + b • ω₂ by abel]
    simp only [pdet, Complex.real_smul, map_add, map_mul, Complex.conj_ofReal, Complex.mul_im,
      Complex.add_im, Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [pc₁, this, mul_div_assoc, div_self h, mul_one]

private theorem pc₂_combo {z₀ ω₁ ω₂ : ℂ} (h : pdet ω₁ ω₂ ≠ 0) (a b : ℝ) :
    pc₂ z₀ ω₁ ω₂ (z₀ + a • ω₁ + b • ω₂) = b := by
  have : (conj ω₁ * (z₀ + a • ω₁ + b • ω₂ - z₀)).im = b * pdet ω₁ ω₂ := by
    rw [show z₀ + a • ω₁ + b • ω₂ - z₀ = a • ω₁ + b • ω₂ by abel]
    simp only [pdet, Complex.real_smul, Complex.mul_im, Complex.add_im, Complex.add_re,
      Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [pc₂, this, mul_div_assoc, div_self h, mul_one]

private theorem eq_combo {z₀ ω₁ ω₂ : ℂ} (h : pdet ω₁ ω₂ ≠ 0) (z : ℂ) :
    z = z₀ + pc₁ z₀ ω₁ ω₂ z • ω₁ + pc₂ z₀ ω₁ ω₂ z • ω₂ := by
  have key : (pdet ω₁ ω₂ : ℂ) * (z - z₀) = ((conj (z - z₀) * ω₂).im : ℂ) * ω₁ +
      ((conj ω₁ * (z - z₀)).im : ℂ) * ω₂ := by
    apply Complex.ext <;>
    · simp only [pdet, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Complex.sub_re,
        Complex.sub_im]
      ring
  have hd : (pdet ω₁ ω₂ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 h
  simp only [pc₁, pc₂, Complex.real_smul, Complex.ofReal_div]
  field_simp
  rw [mul_comm (z - z₀) (conj ω₁)]
  linear_combination key

/-- The open parallelogram `{z₀ + t₁ ω₁ + t₂ ω₂ : 0 < t₁, t₂ < 1}`. -/
private def pInt (z₀ ω₁ ω₂ : ℂ) : Set ℂ :=
  {P | ∃ t₁ t₂ : ℝ, 0 < t₁ ∧ t₁ < 1 ∧ 0 < t₂ ∧ t₂ < 1 ∧ P = z₀ + t₁ • ω₁ + t₂ • ω₂}

/-- The closed parallelogram `{z₀ + t₁ ω₁ + t₂ ω₂ : 0 ≤ t₁, t₂ ≤ 1}`. -/
private def pCl (z₀ ω₁ ω₂ : ℂ) : Set ℂ :=
  {P | ∃ t₁ t₂ : ℝ, 0 ≤ t₁ ∧ t₁ ≤ 1 ∧ 0 ≤ t₂ ∧ t₂ ≤ 1 ∧ P = z₀ + t₁ • ω₁ + t₂ • ω₂}

private theorem mem_pInt_iff {z₀ ω₁ ω₂ : ℂ} (h : pdet ω₁ ω₂ ≠ 0) {z : ℂ} :
    z ∈ pInt z₀ ω₁ ω₂ ↔ 0 < pc₁ z₀ ω₁ ω₂ z ∧ pc₁ z₀ ω₁ ω₂ z < 1 ∧
      0 < pc₂ z₀ ω₁ ω₂ z ∧ pc₂ z₀ ω₁ ω₂ z < 1 := by
  constructor
  · rintro ⟨a, b, h1, h2, h3, h4, rfl⟩
    rw [pc₁_combo h, pc₂_combo h]
    exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨_, _, h1, h2, h3, h4, eq_combo h z⟩

private theorem mem_pCl_iff {z₀ ω₁ ω₂ : ℂ} (h : pdet ω₁ ω₂ ≠ 0) {z : ℂ} :
    z ∈ pCl z₀ ω₁ ω₂ ↔ 0 ≤ pc₁ z₀ ω₁ ω₂ z ∧ pc₁ z₀ ω₁ ω₂ z ≤ 1 ∧
      0 ≤ pc₂ z₀ ω₁ ω₂ z ∧ pc₂ z₀ ω₁ ω₂ z ≤ 1 := by
  constructor
  · rintro ⟨a, b, h1, h2, h3, h4, rfl⟩
    rw [pc₁_combo h, pc₂_combo h]
    exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨_, _, h1, h2, h3, h4, eq_combo h z⟩

private theorem pInt_subset_pCl (z₀ ω₁ ω₂ : ℂ) : pInt z₀ ω₁ ω₂ ⊆ pCl z₀ ω₁ ω₂ := by
  rintro z ⟨a, b, h1, h2, h3, h4, rfl⟩
  exact ⟨a, b, h1.le, h2.le, h3.le, h4.le, rfl⟩

private theorem pInt_eq_image (z₀ ω₁ ω₂ : ℂ) : pInt z₀ ω₁ ω₂ =
    (fun p : ℝ × ℝ => z₀ + p.1 • ω₁ + p.2 • ω₂) '' (Ioo 0 1 ×ˢ Ioo 0 1) := by
  ext z
  simp only [pInt, mem_ofPred_eq, mem_image, mem_prod, mem_Ioo, Prod.exists]
  constructor
  · rintro ⟨a, b, h1, h2, h3, h4, rfl⟩
    exact ⟨a, b, ⟨⟨h1, h2⟩, h3, h4⟩, rfl⟩
  · rintro ⟨a, b, ⟨⟨h1, h2⟩, h3, h4⟩, rfl⟩
    exact ⟨a, b, h1, h2, h3, h4, rfl⟩

private theorem pCl_eq_image (z₀ ω₁ ω₂ : ℂ) : pCl z₀ ω₁ ω₂ =
    (fun p : ℝ × ℝ => z₀ + p.1 • ω₁ + p.2 • ω₂) '' (Icc 0 1 ×ˢ Icc 0 1) := by
  ext z
  simp only [pCl, mem_ofPred_eq, mem_image, mem_prod, mem_Icc, Prod.exists]
  constructor
  · rintro ⟨a, b, h1, h2, h3, h4, rfl⟩
    exact ⟨a, b, ⟨⟨h1, h2⟩, h3, h4⟩, rfl⟩
  · rintro ⟨a, b, ⟨⟨h1, h2⟩, h3, h4⟩, rfl⟩
    exact ⟨a, b, h1, h2, h3, h4, rfl⟩

private theorem isCompact_pCl (z₀ ω₁ ω₂ : ℂ) : IsCompact (pCl z₀ ω₁ ω₂) := by
  rw [pCl_eq_image]
  exact (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)

private theorem isPreconnected_pCl (z₀ ω₁ ω₂ : ℂ) : IsPreconnected (pCl z₀ ω₁ ω₂) := by
  rw [pCl_eq_image]
  exact (isPreconnected_Icc.prod isPreconnected_Icc).image _
    (by fun_prop : Continuous _).continuousOn

private theorem isPreconnected_pInt (z₀ ω₁ ω₂ : ℂ) : IsPreconnected (pInt z₀ ω₁ ω₂) := by
  rw [pInt_eq_image]
  exact (isPreconnected_Ioo.prod isPreconnected_Ioo).image _
    (by fun_prop : Continuous _).continuousOn

private theorem isOpen_pInt {z₀ ω₁ ω₂ : ℂ} (h : pdet ω₁ ω₂ ≠ 0) : IsOpen (pInt z₀ ω₁ ω₂) := by
  have : pInt z₀ ω₁ ω₂ = pc₁ z₀ ω₁ ω₂ ⁻¹' Ioo 0 1 ∩ pc₂ z₀ ω₁ ω₂ ⁻¹' Ioo 0 1 := by
    ext z
    rw [mem_pInt_iff h]
    simp only [mem_inter_iff, mem_preimage, mem_Ioo, and_assoc]
  rw [this]
  exact (isOpen_Ioo.preimage (continuous_pc₁ _ _ _)).inter
    (isOpen_Ioo.preimage (continuous_pc₂ _ _ _))

/-- The parameters of a combination swap with the two sides. -/
private theorem pInt_swap (z₀ ω₁ ω₂ : ℂ) : pInt z₀ ω₂ ω₁ = pInt z₀ ω₁ ω₂ := by
  ext z
  constructor <;>
  · rintro ⟨a, b, h1, h2, h3, h4, rfl⟩
    exact ⟨b, a, h3, h4, h1, h2, add_right_comm _ _ _⟩

private theorem pCl_swap (z₀ ω₁ ω₂ : ℂ) : pCl z₀ ω₂ ω₁ = pCl z₀ ω₁ ω₂ := by
  ext z
  constructor <;>
  · rintro ⟨a, b, h1, h2, h3, h4, rfl⟩
    exact ⟨b, a, h3, h4, h1, h2, add_right_comm _ _ _⟩

/-- `Im(ω₂ / ω₁) · |ω₁|² = Im(conj ω₁ · ω₂)`. -/
private theorem pdet_eq (ω₁ ω₂ : ℂ) : pdet ω₁ ω₂ = (ω₂ / ω₁).im * normSq ω₁ := by
  rcases eq_or_ne ω₁ 0 with rfl | h
  · simp [pdet]
  · have h' : normSq ω₁ ≠ 0 := normSq_eq_zero.not.2 h
    rw [div_im, pdet]
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    field_simp
    ring

private theorem pdet_pos {ω₁ ω₂ : ℂ} (h : 0 < (ω₂ / ω₁).im) : 0 < pdet ω₁ ω₂ := by
  have hω₁ : ω₁ ≠ 0 := by rintro rfl; simp at h
  rw [pdet_eq]
  exact mul_pos h (normSq_pos.2 hω₁)

private theorem pdet_ne_zero {ω₁ ω₂ : ℂ} (h : (ω₂ / ω₁).im ≠ 0) : pdet ω₁ ω₂ ≠ 0 := by
  have hω₁ : ω₁ ≠ 0 := by rintro rfl; simp at h
  rw [pdet_eq]
  exact mul_ne_zero h (normSq_pos.2 hω₁).ne'

private theorem ne_zero_left {ω₁ ω₂ : ℂ} (h : pdet ω₁ ω₂ ≠ 0) : ω₁ ≠ 0 := by
  rintro rfl; simp [pdet] at h

private theorem ne_zero_right {ω₁ ω₂ : ℂ} (h : pdet ω₁ ω₂ ≠ 0) : ω₂ ≠ 0 := by
  rintro rfl; simp [pdet] at h

private theorem pAdd_ne_zero {ω₁ ω₂ : ℂ} (h : pdet ω₁ ω₂ ≠ 0) : ω₁ + ω₂ ≠ 0 := by
  intro h0
  apply h
  rw [show ω₂ = -ω₁ by linear_combination h0]
  simp only [pdet, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im]
  ring

private theorem pSub_ne_zero {ω₁ ω₂ : ℂ} (h : pdet ω₁ ω₂ ≠ 0) : ω₁ - ω₂ ≠ 0 := by
  intro h0
  apply h
  rw [show ω₂ = ω₁ by linear_combination -h0]
  simp only [pdet, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-! ### The boundary path -/

/-- **The boundary of a parallelogram as a closed path.** For
$z_0, \omega_1, \omega_2 \in \mathbb{C}$, the closed path
$z_0 \to z_0 + \omega_1 \to z_0 + \omega_1 + \omega_2 \to z_0 + \omega_2 \to z_0$ made of four
segments, each traversed in a quarter of the parameter interval. It is
piecewise $C^1$ (`isPiecewiseC1_parallelogramPath`) and its range is the boundary of the
parallelogram (`mem_range_parallelogramPath_iff`). When the four side integrands
$t \mapsto g(z_0 + t\omega_1)\,\omega_1$, $t \mapsto g(z_0 + \omega_1 + t\omega_2)\,\omega_2$,
$t \mapsto g(z_0 + \omega_2 + t\omega_1)\,\omega_1$ and $t \mapsto g(z_0 + t\omega_2)\,\omega_2$ are
interval-integrable on $[0, 1]$, the curve integral of $g(z)\,dz$ along it is
`parallelogramBoundaryIntegral g z₀ ω₁ ω₂` (`curveIntegral_parallelogramPath`); this holds in
particular when $g$ is continuous on the boundary
(`curveIntegral_parallelogramPath_of_continuousOn`). Without integrability the two can differ, as
each is a Bochner integral that is $0$ when its integrand is not integrable. -/
noncomputable def parallelogramPath (z₀ ω₁ ω₂ : ℂ) : Path z₀ z₀ :=
  ((Path.segment z₀ (z₀ + ω₁)).trans (Path.segment (z₀ + ω₁) (z₀ + ω₁ + ω₂))).trans
    ((Path.segment (z₀ + ω₂) (z₀ + ω₁ + ω₂)).symm.trans (Path.segment z₀ (z₀ + ω₂)).symm)

/-- **The boundary path of a parallelogram is piecewise $C^1$.** For all
$z_0, \omega_1, \omega_2 \in \mathbb{C}$, `parallelogramPath z₀ ω₁ ω₂` is a piecewise $C^1$ path:
it is a concatenation of four segments. -/
theorem isPiecewiseC1_parallelogramPath (z₀ ω₁ ω₂ : ℂ) :
    (parallelogramPath z₀ ω₁ ω₂).IsPiecewiseC1 :=
  ((Path.isPiecewiseC1_segment _ _).trans (Path.isPiecewiseC1_segment _ _)).trans
    ((Path.isPiecewiseC1_segment _ _).symm.trans (Path.isPiecewiseC1_segment _ _).symm)

/-- **The range of the boundary path of a parallelogram.** For
$z_0, \omega_1, \omega_2, z \in \mathbb{C}$, the point $z$ lies on `parallelogramPath z₀ ω₁ ω₂` if
and only if $z = z_0 + t_1\omega_1 + t_2\omega_2$ for some $t_1, t_2 \in [0, 1]$ with
$t_1 \in \{0, 1\}$ or $t_2 \in \{0, 1\}$. No independence of $\omega_1, \omega_2$ is assumed. -/
theorem mem_range_parallelogramPath_iff {z₀ ω₁ ω₂ z : ℂ} :
    z ∈ range (parallelogramPath z₀ ω₁ ω₂) ↔
      ∃ t₁ t₂ : ℝ, 0 ≤ t₁ ∧ t₁ ≤ 1 ∧ 0 ≤ t₂ ∧ t₂ ≤ 1 ∧ (t₁ = 0 ∨ t₁ = 1 ∨ t₂ = 0 ∨ t₂ = 1) ∧
        z = z₀ + t₁ • ω₁ + t₂ • ω₂ := by
  simp only [parallelogramPath, Path.trans_range, Path.symm_range, Path.range_segment,
    segment_eq_image', mem_union, mem_image, mem_Icc]
  constructor
  · rintro ((⟨t, ⟨h0, h1⟩, rfl⟩ | ⟨t, ⟨h0, h1⟩, rfl⟩) | (⟨t, ⟨h0, h1⟩, rfl⟩ | ⟨t, ⟨h0, h1⟩, rfl⟩))
    · exact ⟨t, 0, h0, h1, le_rfl, zero_le_one, Or.inr (Or.inr (Or.inl rfl)), by module⟩
    · exact ⟨1, t, zero_le_one, le_rfl, h0, h1, Or.inr (Or.inl rfl), by module⟩
    · exact ⟨t, 1, h0, h1, zero_le_one, le_rfl, Or.inr (Or.inr (Or.inr rfl)), by module⟩
    · exact ⟨0, t, le_rfl, zero_le_one, h0, h1, Or.inl rfl, by module⟩
  · rintro ⟨a, b, h1, h2, h3, h4, hab, rfl⟩
    rcases hab with rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inr ⟨b, ⟨h3, h4⟩, by module⟩)
    · exact Or.inl (Or.inr ⟨b, ⟨h3, h4⟩, by module⟩)
    · exact Or.inl (Or.inl ⟨a, ⟨h1, h2⟩, by module⟩)
    · exact Or.inr (Or.inl ⟨a, ⟨h1, h2⟩, by module⟩)

private theorem range_eq {z₀ ω₁ ω₂ : ℂ} (h : pdet ω₁ ω₂ ≠ 0) :
    range (parallelogramPath z₀ ω₁ ω₂) = pCl z₀ ω₁ ω₂ \ pInt z₀ ω₁ ω₂ := by
  ext z
  rw [mem_range_parallelogramPath_iff, Set.mem_sdiff, mem_pCl_iff h, mem_pInt_iff h]
  constructor
  · rintro ⟨a, b, h1, h2, h3, h4, hab, rfl⟩
    rw [pc₁_combo h, pc₂_combo h]
    refine ⟨⟨h1, h2, h3, h4⟩, ?_⟩
    rintro ⟨g1, g2, g3, g4⟩
    rcases hab with rfl | rfl | rfl | rfl <;> linarith
  · rintro ⟨⟨h1, h2, h3, h4⟩, hn⟩
    refine ⟨_, _, h1, h2, h3, h4, ?_, eq_combo h z⟩
    by_contra hc
    push Not at hc
    exact hn ⟨lt_of_le_of_ne h1 (Ne.symm hc.1), lt_of_le_of_ne h2 hc.2.1,
      lt_of_le_of_ne h3 (Ne.symm hc.2.2.1), lt_of_le_of_ne h4 hc.2.2.2⟩

/-- The value of the boundary path at a parameter, in coordinates. -/
private theorem parallelogramPath_apply (z₀ ω₁ ω₂ : ℂ) (t : unitInterval) :
    parallelogramPath z₀ ω₁ ω₂ t = z₀ +
      (if (t : ℝ) ≤ 1 / 2 then (if 2 * (t : ℝ) ≤ 1 / 2 then 4 * (t : ℝ) else 1)
        else (if 2 * (t : ℝ) - 1 ≤ 1 / 2 then 3 - 4 * (t : ℝ) else 0)) • ω₁ +
      (if (t : ℝ) ≤ 1 / 2 then (if 2 * (t : ℝ) ≤ 1 / 2 then 0 else 4 * (t : ℝ) - 1)
        else (if 2 * (t : ℝ) - 1 ≤ 1 / 2 then 1 else 4 - 4 * (t : ℝ))) • ω₂ := by
  rw [parallelogramPath, Path.trans_apply]
  split_ifs with h1 h2 h3
  · rw [Path.trans_apply, dite_eq_left h2]
    simp only [Path.segment_apply, AffineMap.lineMap_apply_module']
    module
  · rw [Path.trans_apply, dite_eq_right h2]
    simp only [Path.segment_apply, AffineMap.lineMap_apply_module']
    module
  · rw [Path.trans_apply, dite_eq_left h3]
    simp only [Path.symm_apply, Function.comp_apply, unitInterval.coe_symm_eq, Path.segment_apply,
      AffineMap.lineMap_apply_module']
    module
  · rw [Path.trans_apply, dite_eq_right h3]
    simp only [Path.symm_apply, Function.comp_apply, unitInterval.coe_symm_eq, Path.segment_apply,
      AffineMap.lineMap_apply_module']
    module

/-- The boundary path of a nondegenerate parallelogram is injective on `[0, 1)`. -/
private theorem injOn_parallelogramPath {z₀ ω₁ ω₂ : ℂ} (h : pdet ω₁ ω₂ ≠ 0) :
    InjOn (parallelogramPath z₀ ω₁ ω₂) (Iio 1) := by
  intro s hs t ht hst
  have h1 := congrArg (pc₁ z₀ ω₁ ω₂) hst
  have h2 := congrArg (pc₂ z₀ ω₁ ω₂) hst
  rw [parallelogramPath_apply, parallelogramPath_apply, pc₁_combo h, pc₁_combo h] at h1
  rw [parallelogramPath_apply, parallelogramPath_apply, pc₂_combo h, pc₂_combo h] at h2
  have hs1 : (s : ℝ) < 1 := hs
  have ht1 : (t : ℝ) < 1 := ht
  have hs0 : 0 ≤ (s : ℝ) := s.2.1
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  apply Subtype.ext
  split_ifs at h1 h2 <;> linarith

/-! ### Curve integrals along the boundary -/

private theorem curveIntegral_seg {φ : ℂ → ℂ} {a b v : ℂ} (hb : b = a + v) :
    ∫ᶜ z in Path.segment a b, φ z • ContinuousLinearMap.id ℂ ℂ =
      ∫ t in (0 : ℝ)..1, φ (a + t • v) * v := by
  subst hb
  rw [curveIntegral_segment]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [AffineMap.lineMap_apply_module', add_sub_cancel_left]
  rw [add_comm (t • v) a]
  rfl

private theorem curveIntegrable_seg {φ : ℂ → ℂ} {a b v : ℂ} (hb : b = a + v)
    (h : IntervalIntegrable (fun t : ℝ => φ (a + t • v) * v) volume 0 1) :
    CurveIntegrable (fun z => φ z • ContinuousLinearMap.id ℂ ℂ) (Path.segment a b) := by
  subst hb
  rw [curveIntegrable_segment]
  refine h.congr fun t _ => ?_
  simp only [AffineMap.lineMap_apply_module', add_sub_cancel_left]
  rw [add_comm (t • v) a]
  rfl

/-- **Curve integral along the boundary of a parallelogram.** Let
$\varphi : \mathbb{C} \to \mathbb{C}$ and $z_0, \omega_1, \omega_2 \in \mathbb{C}$, and suppose that
the four functions $t \mapsto \varphi(z_0 + t\omega_1)\,\omega_1$,
$t \mapsto \varphi(z_0 + \omega_1 + t\omega_2)\,\omega_2$,
$t \mapsto \varphi(z_0 + \omega_2 + t\omega_1)\,\omega_1$ and
$t \mapsto \varphi(z_0 + t\omega_2)\,\omega_2$ are integrable on $[0, 1]$. Then the curve integral
of $\varphi(z)\,dz$ along `parallelogramPath z₀ ω₁ ω₂` is
`parallelogramBoundaryIntegral φ z₀ ω₁ ω₂`. -/
theorem curveIntegral_parallelogramPath {φ : ℂ → ℂ} {z₀ ω₁ ω₂ : ℂ}
    (h₁ : IntervalIntegrable (fun t : ℝ => φ (z₀ + t • ω₁) * ω₁) volume 0 1)
    (h₂ : IntervalIntegrable (fun t : ℝ => φ (z₀ + ω₁ + t • ω₂) * ω₂) volume 0 1)
    (h₃ : IntervalIntegrable (fun t : ℝ => φ (z₀ + ω₂ + t • ω₁) * ω₁) volume 0 1)
    (h₄ : IntervalIntegrable (fun t : ℝ => φ (z₀ + t • ω₂) * ω₂) volume 0 1) :
    ∫ᶜ z in parallelogramPath z₀ ω₁ ω₂, φ z • ContinuousLinearMap.id ℂ ℂ =
      parallelogramBoundaryIntegral φ z₀ ω₁ ω₂ := by
  have i₁ := curveIntegrable_seg (b := z₀ + ω₁) rfl h₁
  have i₂ := curveIntegrable_seg (b := z₀ + ω₁ + ω₂) rfl h₂
  have i₃ := curveIntegrable_seg (b := z₀ + ω₁ + ω₂) (add_right_comm _ _ _) h₃
  have i₄ := curveIntegrable_seg (b := z₀ + ω₂) rfl h₄
  rw [parallelogramPath, curveIntegral_trans (i₁.trans i₂)
      ((curveIntegrable_symm.2 i₃).trans (curveIntegrable_symm.2 i₄)),
    curveIntegral_trans i₁ i₂, curveIntegral_trans (curveIntegrable_symm.2 i₃)
      (curveIntegrable_symm.2 i₄), curveIntegral_symm, curveIntegral_symm,
    curveIntegral_seg rfl, curveIntegral_seg rfl, curveIntegral_seg (add_right_comm _ _ _),
    curveIntegral_seg rfl, parallelogramBoundaryIntegral]
  ring

/-! ### The inside of the boundary path -/

private theorem inside_eq {z₀ ω₁ ω₂ : ℂ} (h : pdet ω₁ ω₂ ≠ 0) :
    (range (parallelogramPath z₀ ω₁ ω₂)).inside = pInt z₀ ω₁ ω₂ := by
  set K := range (parallelogramPath z₀ ω₁ ω₂) with hK
  have hrange : K = pCl z₀ ω₁ ω₂ \ pInt z₀ ω₁ ω₂ := range_eq h
  have hD : IsOpen (pInt z₀ ω₁ ω₂) := isOpen_pInt h
  have hE : IsOpen (pCl z₀ ω₁ ω₂)ᶜ := (isCompact_pCl z₀ ω₁ ω₂).isClosed.isOpen_compl
  have hKc : Kᶜ ⊆ pInt z₀ ω₁ ω₂ ∪ (pCl z₀ ω₁ ω₂)ᶜ := fun z hz => by
    by_cases hz' : z ∈ pCl z₀ ω₁ ω₂
    · left
      by_contra hn
      exact hz (hrange ▸ ⟨hz', hn⟩)
    · exact Or.inr hz'
  have hdisj : Disjoint (pInt z₀ ω₁ ω₂) (pCl z₀ ω₁ ω₂)ᶜ :=
    disjoint_compl_right.mono_left (pInt_subset_pCl z₀ ω₁ ω₂)
  have hKcl : K ⊆ pCl z₀ ω₁ ω₂ := hrange ▸ sdiff_subset
  ext x
  rw [mem_inside]
  constructor
  · rintro ⟨hxK, hb⟩
    by_contra hxD
    have hxE : x ∉ pCl z₀ ω₁ ω₂ := (hKc hxK).resolve_left hxD
    set m : ℂ := z₀ + (1 / 2 : ℝ) • ω₁ + (1 / 2 : ℝ) • ω₂
    have hm : m ∈ pInt z₀ ω₁ ω₂ := ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num,
      by norm_num, rfl⟩
    have hxm : x - m ≠ 0 := sub_ne_zero.2 fun hxm => hxD (hxm ▸ hm)
    set R := (fun s : ℝ => x + s • (x - m)) '' Ici 0
    -- The ray from `x` away from the centre stays outside the closed parallelogram.
    have hRE : R ⊆ (pCl z₀ ω₁ ω₂)ᶜ := by
      rintro _ ⟨s, hs, rfl⟩ hz
      apply hxE
      have hs : 0 ≤ s := hs
      simp only at hz
      rw [mem_pCl_iff h] at hz ⊢
      have e : x + s • (x - m) = z₀ + (pc₁ z₀ ω₁ ω₂ x + s * (pc₁ z₀ ω₁ ω₂ x - 1 / 2)) • ω₁ +
          (pc₂ z₀ ω₁ ω₂ x + s * (pc₂ z₀ ω₁ ω₂ x - 1 / 2)) • ω₂ := by
        conv_lhs => rw [eq_combo (z₀ := z₀) (ω₁ := ω₁) (ω₂ := ω₂) h x]
        simp only [m]
        module
      rw [e, pc₁_combo h, pc₂_combo h] at hz
      obtain ⟨h1, h2, h3, h4⟩ := hz
      refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
    have hRc : R ⊆ connectedComponentIn Kᶜ x :=
      (isPreconnected_Ici.image _
        (by fun_prop : Continuous fun s : ℝ => x + s • (x - m)).continuousOn
        ).subset_connectedComponentIn ⟨0, (Set.mem_Ici.2 le_rfl), by simp⟩
        (hRE.trans (compl_subset_compl.2 hKcl))
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (hb.subset hRc)
    set s : ℝ := (C + ‖x‖ + 1) / ‖x - m‖
    have hn : 0 < ‖x - m‖ := norm_pos_iff.2 hxm
    have hC0 : 0 ≤ C := (norm_nonneg x).trans (hC x ⟨0, (Set.mem_Ici.2 le_rfl), by simp⟩)
    have hs0 : 0 ≤ s := by positivity
    have h1 := hC _ ⟨s, hs0, rfl⟩
    have h2 : ‖s • (x - m)‖ ≤ ‖x + s • (x - m)‖ + ‖x‖ := by
      have := norm_sub_le (x + s • (x - m)) x
      rwa [add_sub_cancel_left] at this
    rw [norm_smul, Real.norm_of_nonneg hs0, div_mul_cancel₀ _ hn.ne'] at h2
    linarith
  · intro hx
    have hxK : x ∉ K := fun hxK => (hrange ▸ hxK : x ∈ pCl z₀ ω₁ ω₂ \ pInt z₀ ω₁ ω₂).2 hx
    refine ⟨hxK, (isCompact_pCl z₀ ω₁ ω₂).isBounded.subset (Subset.trans ?_
      (pInt_subset_pCl z₀ ω₁ ω₂))⟩
    exact isPreconnected_connectedComponentIn.subset_left_of_subset_union hD hE hdisj
      ((connectedComponentIn_subset _ _).trans hKc) ⟨x, mem_connectedComponentIn hxK, hx⟩

/-- **The inside of the boundary of a parallelogram.** Let $z_0, \omega_1, \omega_2 \in \mathbb{C}$
with $\operatorname{Im}(\omega_2/\omega_1) \ne 0$, that is, $\omega_1, \omega_2$ linearly
independent over $\mathbb{R}$. Then the inside of the range of `parallelogramPath z₀ ω₁ ω₂`
(the union of the bounded components of its complement, `Set.inside`) is the open parallelogram
$\{z_0 + t_1\omega_1 + t_2\omega_2 : 0 < t_1 < 1,\ 0 < t_2 < 1\}$. -/
theorem inside_range_parallelogramPath {z₀ ω₁ ω₂ : ℂ} (hω : (ω₂ / ω₁).im ≠ 0) :
    (range (parallelogramPath z₀ ω₁ ω₂)).inside =
      {P | ∃ t₁ t₂ : ℝ, 0 < t₁ ∧ t₁ < 1 ∧ 0 < t₂ ∧ t₂ < 1 ∧ P = z₀ + t₁ • ω₁ + t₂ • ω₂} :=
  inside_eq (pdet_ne_zero hω)

/-! ### The winding number of the boundary path -/

/-- Integral of `(p + t q)⁻¹ q` over `[0, 1]`, by the principal logarithm. -/
private theorem integral_inv_mul {p q : ℂ} (h : ∀ t ∈ Icc (0 : ℝ) 1, p + t • q ≠ 0) :
    IntervalIntegrable (fun t : ℝ => (p + t • q)⁻¹ * q) volume 0 1 ∧
      ∫ t in (0 : ℝ)..1, (p + t • q)⁻¹ * q = log ((p + q) / p) := by
  have hp : p ≠ 0 := by simpa using h 0 ⟨le_rfl, zero_le_one⟩
  set r := q / p with hr
  have hq : q = p * r := by rw [hr]; field_simp
  have hslit : ∀ t ∈ Icc (0 : ℝ) 1, (1 : ℂ) + (t : ℂ) * r ∈ slitPlane := by
    intro t ht
    rw [mem_slitPlane_iff]
    by_contra hcon
    push Not at hcon
    obtain ⟨hre, him⟩ := hcon
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.add_im, Complex.one_im, Complex.mul_im,
      zero_add] at hre him
    have ht0 : t ≠ 0 := by rintro rfl; simp at hre; linarith
    have hrim : r.im = 0 := by
      rcases mul_eq_zero.1 (by simpa using him : t * r.im = 0) with h0 | h0
      · exact absurd h0 ht0
      · exact h0
    have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have hrre : r.re < 0 := by nlinarith
    set s : ℝ := -1 / r.re
    have hs0 : 0 ≤ s := div_nonneg_of_nonpos (by norm_num) hrre.le
    have hst : s ≤ t := by
      rw [div_le_iff_of_neg hrre]
      linarith
    apply h s ⟨hs0, hst.trans ht.2⟩
    have hsr : (1 : ℂ) + (s : ℂ) * r = 0 := by
      apply Complex.ext
      · simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero, Complex.zero_re, s]
        have hre0 : r.re ≠ 0 := hrre.ne
        field_simp
        ring
      · simp [hrim]
    calc p + s • q = p * (1 + (s : ℂ) * r) := by rw [hq, Complex.real_smul]; ring
      _ = 0 := by rw [hsr, mul_zero]
  have hcont : ContinuousOn (fun t : ℝ => (p + t • q)⁻¹ * q) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    exact ((continuousOn_const.add (by fun_prop)).inv₀ h).mul continuousOn_const
  have hint := hcont.intervalIntegrable (μ := volume)
  refine ⟨hint, ?_⟩
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => log (1 + (t : ℂ) * r))
      ((p + t • q)⁻¹ * q) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have h1 : HasDerivAt (fun t : ℝ => (1 : ℂ) + (t : ℂ) * r) r t := by
      simpa using ((hasDerivAt_id t).ofReal_comp.mul_const r).const_add 1
    convert h1.clog_real (hslit t ht) using 1
    have hne : (1 : ℂ) + (t : ℂ) * r ≠ 0 := slitPlane_ne_zero (hslit t ht)
    rw [hq, Complex.real_smul]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, add_zero, log_one,
    sub_zero]
  congr 1
  rw [hr]
  field_simp

/-- `log (-r) + log r⁻¹ - log (-r⁻¹) - log r = 2πi` when `Im r < 0`. -/
private theorem log_combo {r : ℂ} (hr : r.im < 0) :
    log (-r) + log r⁻¹ - log (-r⁻¹) - log r = 2 * π * I := by
  have hr0 : r ≠ 0 := by rintro rfl; simp at hr
  have hinv : 0 < r⁻¹.im := by
    rw [inv_im]
    exact div_pos (by linarith) (normSq_pos.2 hr0)
  have hpi : r.arg ≠ π := fun h' => by
    have := (arg_eq_pi_iff.1 h').2
    linarith
  apply Complex.ext
  · simp [log_re, norm_neg]
  · simp only [Complex.sub_im, Complex.add_im, log_im, arg_neg_eq_arg_add_pi_of_im_neg hr,
      arg_neg_eq_arg_sub_pi_of_im_pos hinv, arg_inv, hpi, ↓reduceIte]
    simp
    ring

/-- The winding number of the boundary path about the centre of the parallelogram. -/
private theorem windingNumber_center {z₀ ω₁ ω₂ : ℂ} (hpos : 0 < pdet ω₁ ω₂) :
    Complex.windingNumber (parallelogramPath z₀ ω₁ ω₂)
      (z₀ + (1 / 2 : ℝ) • ω₁ + (1 / 2 : ℝ) • ω₂) = 1 := by
  have h := hpos.ne'
  set m : ℂ := z₀ + (1 / 2 : ℝ) • ω₁ + (1 / 2 : ℝ) • ω₂ with hm_def
  have hm : m ∉ range (parallelogramPath z₀ ω₁ ω₂) := by
    rw [range_eq h]
    exact fun hm => hm.2 ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by norm_num, rfl⟩
  have hne : ∀ z ∈ range (parallelogramPath z₀ ω₁ ω₂), z - m ≠ 0 := fun z hz =>
    sub_ne_zero.2 fun hzm => hm (hzm ▸ hz)
  have hs₁ : ∀ t ∈ Icc (0 : ℝ) 1, (z₀ - m) + t • ω₁ ≠ 0 := fun t ht => by
    rw [sub_add_eq_add_sub]
    exact hne _ (mem_range_parallelogramPath_iff.2
      ⟨t, 0, ht.1, ht.2, le_rfl, zero_le_one, Or.inr (Or.inr (Or.inl rfl)), by module⟩)
  have hs₂ : ∀ t ∈ Icc (0 : ℝ) 1, (z₀ + ω₁ - m) + t • ω₂ ≠ 0 := fun t ht => by
    rw [sub_add_eq_add_sub]
    exact hne _ (mem_range_parallelogramPath_iff.2
      ⟨1, t, zero_le_one, le_rfl, ht.1, ht.2, Or.inr (Or.inl rfl), by module⟩)
  have hs₃ : ∀ t ∈ Icc (0 : ℝ) 1, (z₀ + ω₂ - m) + t • ω₁ ≠ 0 := fun t ht => by
    rw [sub_add_eq_add_sub]
    exact hne _ (mem_range_parallelogramPath_iff.2
      ⟨t, 1, ht.1, ht.2, zero_le_one, le_rfl, Or.inr (Or.inr (Or.inr rfl)), by module⟩)
  have hs₄ : ∀ t ∈ Icc (0 : ℝ) 1, (z₀ - m) + t • ω₂ ≠ 0 := fun t ht => by
    rw [sub_add_eq_add_sub]
    exact hne _ (mem_range_parallelogramPath_iff.2
      ⟨0, t, le_rfl, zero_le_one, ht.1, ht.2, Or.inl rfl, by module⟩)
  obtain ⟨i₁, e₁⟩ := integral_inv_mul hs₁
  obtain ⟨i₂, e₂⟩ := integral_inv_mul hs₂
  obtain ⟨i₃, e₃⟩ := integral_inv_mul hs₃
  obtain ⟨i₄, e₄⟩ := integral_inv_mul hs₄
  have f₁ : (fun t : ℝ => (z₀ + t • ω₁ - m)⁻¹ * ω₁) = fun t : ℝ => ((z₀ - m) + t • ω₁)⁻¹ * ω₁ := by
    funext t; rw [sub_add_eq_add_sub]
  have f₂ : (fun t : ℝ => (z₀ + ω₁ + t • ω₂ - m)⁻¹ * ω₂) =
      fun t : ℝ => ((z₀ + ω₁ - m) + t • ω₂)⁻¹ * ω₂ := by
    funext t; rw [sub_add_eq_add_sub]
  have f₃ : (fun t : ℝ => (z₀ + ω₂ + t • ω₁ - m)⁻¹ * ω₁) =
      fun t : ℝ => ((z₀ + ω₂ - m) + t • ω₁)⁻¹ * ω₁ := by
    funext t; rw [sub_add_eq_add_sub]
  have f₄ : (fun t : ℝ => (z₀ + t • ω₂ - m)⁻¹ * ω₂) = fun t : ℝ => ((z₀ - m) + t • ω₂)⁻¹ * ω₂ := by
    funext t; rw [sub_add_eq_add_sub]
  rw [Complex.windingNumber, curveIntegral_parallelogramPath (φ := fun ζ => (ζ - m)⁻¹)
    (by simpa only [f₁] using i₁) (by simpa only [f₂] using i₂) (by simpa only [f₃] using i₃)
    (by simpa only [f₄] using i₄), parallelogramBoundaryIntegral]
  rw [f₁, f₂, f₃, f₄, e₁, e₂, e₃, e₄]
  -- The four ratios are `-r`, `r⁻¹`, `-r⁻¹` and `r` for `r = (ω₁ - ω₂) / (ω₁ + ω₂)`.
  have hA := pAdd_ne_zero h
  have hB := pSub_ne_zero h
  have hp₁ : z₀ - m = -(ω₁ + ω₂) / 2 := by
    rw [hm_def]; simp only [Complex.real_smul]; push_cast; ring
  have hp₂ : z₀ + ω₁ - m = (ω₁ - ω₂) / 2 := by
    rw [hm_def]; simp only [Complex.real_smul]; push_cast; ring
  have hp₃ : z₀ + ω₂ - m = -(ω₁ - ω₂) / 2 := by
    rw [hm_def]; simp only [Complex.real_smul]; push_cast; ring
  set r := (ω₁ - ω₂) / (ω₁ + ω₂) with hr
  have r₁ : (z₀ - m + ω₁) / (z₀ - m) = -r := by rw [hp₁, hr]; field_simp; ring
  have r₂ : (z₀ + ω₁ - m + ω₂) / (z₀ + ω₁ - m) = r⁻¹ := by rw [hp₂, hr, inv_div]; field_simp; ring
  have r₃ : (z₀ + ω₂ - m + ω₁) / (z₀ + ω₂ - m) = -r⁻¹ := by
    rw [hp₃, hr, inv_div]; field_simp; ring
  have r₄ : (z₀ - m + ω₂) / (z₀ - m) = r := by rw [hp₁, hr]; field_simp; ring
  have hrim : r.im < 0 := by
    have hn : 0 < normSq (ω₁ + ω₂) := normSq_pos.2 hA
    have : r.im = -2 * pdet ω₁ ω₂ / normSq (ω₁ + ω₂) := by
      rw [hr, div_im, pdet]
      simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_im,
        Complex.conj_re, Complex.conj_im]
      field_simp
      ring
    rw [this]
    exact div_neg_of_neg_of_pos (by linarith) hn
  rw [r₁, r₂, r₃, r₄, log_combo hrim, inv_mul_cancel₀ two_pi_I_ne_zero]

private theorem windingNumber_eq_one {z₀ ω₁ ω₂ : ℂ} (hpos : 0 < pdet ω₁ ω₂) {w : ℂ}
    (hw : w ∈ pInt z₀ ω₁ ω₂) : Complex.windingNumber (parallelogramPath z₀ ω₁ ω₂) w = 1 := by
  have h := hpos.ne'
  have hsub : pInt z₀ ω₁ ω₂ ⊆ (range (parallelogramPath z₀ ω₁ ω₂))ᶜ := fun z hz hzK =>
    ((range_eq h ▸ hzK : z ∈ pCl z₀ ω₁ ω₂ \ pInt z₀ ω₁ ω₂).2 hz)
  rw [Complex.windingNumber_eq_of_isPreconnected (isPiecewiseC1_parallelogramPath z₀ ω₁ ω₂)
    (isPreconnected_pInt z₀ ω₁ ω₂) hsub
    (⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by norm_num, rfl⟩ :
      z₀ + (1 / 2 : ℝ) • ω₁ + (1 / 2 : ℝ) • ω₂ ∈ pInt z₀ ω₁ ω₂) hw]
  exact windingNumber_center hpos

/-- **The boundary of a positively oriented parallelogram winds once around its interior.** Let
$z_0, \omega_1, \omega_2 \in \mathbb{C}$ with $\operatorname{Im}(\omega_2/\omega_1) > 0$, and let
$w = z_0 + t_1\omega_1 + t_2\omega_2$ with $0 < t_1, t_2 < 1$. Then the winding number of
`parallelogramPath z₀ ω₁ ω₂` about $w$, that is,
$(2\pi i)^{-1}\oint (\zeta - w)^{-1}\,d\zeta$, is $1$. -/
theorem windingNumber_parallelogramPath {z₀ ω₁ ω₂ : ℂ} (hω : 0 < (ω₂ / ω₁).im) {w : ℂ}
    (hw : ∃ t₁ t₂ : ℝ, 0 < t₁ ∧ t₁ < 1 ∧ 0 < t₂ ∧ t₂ < 1 ∧ w = z₀ + t₁ • ω₁ + t₂ • ω₂) :
    Complex.windingNumber (parallelogramPath z₀ ω₁ ω₂) w = 1 :=
  windingNumber_eq_one (pdet_pos hω) hw

/-! ### Integrability of the logarithmic derivative on a side -/

/-- If `f` is meromorphic on `Ω` and has order `0` at every point of the segment
`{a + t v : t ∈ [0, 1]} ⊆ Ω`, `v ≠ 0`, then `t ↦ (f'/f)(a + t v) v` is integrable on `[0, 1]`:
it agrees with a continuous function off a finite set. -/
private theorem intervalIntegrable_logDeriv_side {Ω : Set ℂ} {f : ℂ → ℂ} (hf : MeromorphicOn f Ω)
    {a v : ℂ} (hv : v ≠ 0) (hS : ∀ t ∈ Icc (0 : ℝ) 1, a + t • v ∈ Ω)
    (hord : ∀ t ∈ Icc (0 : ℝ) 1, meromorphicOrderAt f (a + t • v) = 0) :
    IntervalIntegrable (fun t : ℝ => logDeriv f (a + t • v) * v) volume 0 1 := by
  set g := toMeromorphicNFOn f Ω
  have hg : MeromorphicNFOn g Ω := meromorphicNFOn_toMeromorphicNFOn f Ω
  set S := (fun t : ℝ => a + t • v) '' Icc 0 1
  have hSΩ : S ⊆ Ω := by rintro _ ⟨t, ht, rfl⟩; exact hS t ht
  have hSc : IsCompact S := isCompact_Icc.image (by fun_prop)
  have hF : (S \ {z | f z = g z}).Finite :=
    hSc.finite_sdiff_of_mem_codiscreteWithin
      (codiscreteWithin_mono hSΩ (toMeromorphicNFOn_eqOn_codiscrete hf))
  -- `g'/g` is continuous along the segment.
  have hcont : ContinuousOn (fun t : ℝ => logDeriv g (a + t • v) * v) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    refine ContinuousOn.mul (fun t ht => ?_) continuousOn_const
    have hz := hS t ht
    have h0 : meromorphicOrderAt g (a + t • v) = 0 := by
      rw [meromorphicOrderAt_toMeromorphicNFOn hf hz]; exact hord t ht
    have han : AnalyticAt ℂ g (a + t • v) :=
      (hg hz).meromorphicOrderAt_nonneg_iff_analyticAt.1 h0.ge
    have hne : g (a + t • v) ≠ 0 := (hg hz).meromorphicOrderAt_eq_zero_iff.1 h0
    have hc : ContinuousAt (logDeriv g) (a + t • v) :=
      (han.deriv.div han hne).differentiableAt.continuousAt
    exact (hc.comp_of_eq (by fun_prop : Continuous fun t : ℝ => a + t • v).continuousAt
      rfl).continuousWithinAt
  -- The parameters where `f ≠ g` form a finite set.
  have hT : ((fun t : ℝ => a + t • v) ⁻¹' (S \ {z | f z = g z})).Finite :=
    hF.preimage fun t₁ _ t₂ _ h => by
      have : (t₁ : ℂ) * v = (t₂ : ℂ) * v := by simpa [Complex.real_smul] using h
      exact_mod_cast mul_right_cancel₀ hv this
  refine (hcont.intervalIntegrable (μ := volume)).congr_ae ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hT.countable.measure_zero volume)] with t htT htI
  rw [uIoc_of_le zero_le_one] at htI
  have htS : a + t • v ∈ S := ⟨t, Ioc_subset_Icc_self htI, rfl⟩
  have hfg : f (a + t • v) = g (a + t • v) := by
    by_contra hne
    exact htT ⟨htS, hne⟩
  have hev : f =ᶠ[𝓝 (a + t • v)] g := eventuallyEq_nhds_of_eventuallyEq_nhdsNE
    (hf.toMeromorphicNFOn_eq_self_on_nhdsNE (hSΩ htS)).symm hfg
  rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hfg]

/-! ### The argument principle -/

/-- **Argument principle for a positively oriented parallelogram.** Let
$\Omega \subseteq \mathbb{C}$ be open, $f : \mathbb{C} \to \mathbb{C}$ meromorphic at every
point of $\Omega$, and $z_0, \omega_1, \omega_2 \in \mathbb{C}$ with
$\operatorname{Im}(\omega_2 / \omega_1) > 0$. Let
$D = \{z_0 + t_1\omega_1 + t_2\omega_2 : 0 < t_1, t_2 < 1\}$ be the open parallelogram and
$\overline{D} = \{z_0 + t_1\omega_1 + t_2\omega_2 : 0 \le t_1, t_2 \le 1\}$ the closed one.
Suppose that $\overline{D} \subseteq \Omega$ and that the meromorphic order
$\operatorname{ord}_P f$ is $0$ at every $P \in \overline{D} \setminus D$. Then only finitely many
$P \in D$ have $\operatorname{ord}_P f \ne 0$, and

$$\oint_{\partial D} \frac{f'(z)}{f(z)}\,dz = 2\pi i \sum_{P \in D} \operatorname{ord}_P f,$$

where the left side is `parallelogramBoundaryIntegral (logDeriv f) z₀ ω₁ ω₂`, the integral along
$z_0 \to z_0 + \omega_1 \to z_0 + \omega_1 + \omega_2 \to z_0 + \omega_2 \to z_0$, and
$\operatorname{ord}_P f$ is `(meromorphicOrderAt f P).untop₀`.

The order of $f$ is finite at every point of $\overline{D}$: this follows from the hypotheses, as
$\overline{D}$ is connected and meets the boundary, where the order is $0$. The finiteness of the
zeros and poles in $D$ is part of the conclusion. The proof applies the argument principle for a
closed curve (`MeromorphicOn.argument_principle`) to `parallelogramPath z₀ ω₁ ω₂`, which is
injective on $[0, 1)$, has inside $D$ (`inside_range_parallelogramPath`) and winds once around
every point of $D$ (`windingNumber_parallelogramPath`).

Source: J. S. Milne, *Elliptic Curves*, 2nd ed., Chapter III, §2, proof of Proposition 2.1, p. 87:
the residue theorem applied to $f'/f$ over the boundary of the period parallelogram $D$, with
$\operatorname{Res}_P(f'/f) = \operatorname{ord}_P(f)$. -/
theorem MeromorphicOn.parallelogramBoundaryIntegral_logDeriv_of_im_pos {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {f : ℂ → ℂ} (hf : MeromorphicOn f Ω) {z₀ ω₁ ω₂ : ℂ} (hω : 0 < (ω₂ / ω₁).im)
    (hPΩ : {P | ∃ t₁ t₂ : ℝ, 0 ≤ t₁ ∧ t₁ ≤ 1 ∧ 0 ≤ t₂ ∧ t₂ ≤ 1 ∧ P = z₀ + t₁ • ω₁ + t₂ • ω₂} ⊆ Ω)
    (hbd : ∀ P ∈ {P | ∃ t₁ t₂ : ℝ, 0 ≤ t₁ ∧ t₁ ≤ 1 ∧ 0 ≤ t₂ ∧ t₂ ≤ 1 ∧
        P = z₀ + t₁ • ω₁ + t₂ • ω₂},
      P ∉ {P | ∃ t₁ t₂ : ℝ, 0 < t₁ ∧ t₁ < 1 ∧ 0 < t₂ ∧ t₂ < 1 ∧ P = z₀ + t₁ • ω₁ + t₂ • ω₂} →
        meromorphicOrderAt f P = 0) :
    {P | (∃ t₁ t₂ : ℝ, 0 < t₁ ∧ t₁ < 1 ∧ 0 < t₂ ∧ t₂ < 1 ∧ P = z₀ + t₁ • ω₁ + t₂ • ω₂) ∧
        meromorphicOrderAt f P ≠ 0}.Finite ∧
      parallelogramBoundaryIntegral (logDeriv f) z₀ ω₁ ω₂ =
        2 * π * I * ((∑ᶠ P ∈ {P | ∃ t₁ t₂ : ℝ, 0 < t₁ ∧ t₁ < 1 ∧ 0 < t₂ ∧ t₂ < 1 ∧
          P = z₀ + t₁ • ω₁ + t₂ • ω₂}, (meromorphicOrderAt f P).untop₀ : ℤ) : ℂ) := by
  have hpos := pdet_pos hω
  have h := hpos.ne'
  change pCl z₀ ω₁ ω₂ ⊆ Ω at hPΩ
  change ∀ P ∈ pCl z₀ ω₁ ω₂, P ∉ pInt z₀ ω₁ ω₂ → meromorphicOrderAt f P = 0 at hbd
  change {P | P ∈ pInt z₀ ω₁ ω₂ ∧ meromorphicOrderAt f P ≠ 0}.Finite ∧
    parallelogramBoundaryIntegral (logDeriv f) z₀ ω₁ ω₂ =
      2 * π * I * ((∑ᶠ P ∈ pInt z₀ ω₁ ω₂, (meromorphicOrderAt f P).untop₀ : ℤ) : ℂ)
  set γ := parallelogramPath z₀ ω₁ ω₂
  have hγ := isPiecewiseC1_parallelogramPath z₀ ω₁ ω₂
  have hrange : range γ = pCl z₀ ω₁ ω₂ \ pInt z₀ ω₁ ω₂ := range_eq h
  have hins : (range γ).inside = pInt z₀ ω₁ ω₂ := inside_eq h
  have hγΩ : range γ ⊆ Ω := hrange ▸ sdiff_subset.trans hPΩ
  have hinsΩ : (range γ).inside ⊆ Ω := hins ▸ (pInt_subset_pCl z₀ ω₁ ω₂).trans hPΩ
  have hγf : ∀ z ∈ range γ, meromorphicOrderAt f z = 0 := fun z hz => by
    rw [hrange] at hz; exact hbd z hz.1 hz.2
  obtain ⟨hfin, hres⟩ := MeromorphicOn.argument_principle hΩ hf hγ (injOn_parallelogramPath h)
    (fun w hw => windingNumber_eq_one hpos (hins ▸ hw)) hγΩ hinsΩ hγf
  rw [hins] at hfin hres
  set D := MeromorphicOn.divisor f Ω
  -- The order is finite on the closed parallelogram, which is connected and meets the boundary.
  have hz₀ : z₀ ∈ range γ := mem_range_parallelogramPath_iff.2
    ⟨0, 0, le_rfl, zero_le_one, le_rfl, zero_le_one, Or.inl rfl, by simp⟩
  have htop : ∀ P ∈ pCl z₀ ω₁ ω₂, meromorphicOrderAt f P ≠ ⊤ := fun P hP =>
    (hf.mono_set hPΩ).meromorphicOrderAt_ne_top_of_isPreconnected (isPreconnected_pCl z₀ ω₁ ω₂)
      (hrange ▸ hz₀).1 hP (by rw [hγf z₀ hz₀]; exact WithTop.zero_ne_top)
  have hDP : ∀ P ∈ pInt z₀ ω₁ ω₂, D P = (meromorphicOrderAt f P).untop₀ := fun P hP =>
    MeromorphicOn.divisor_apply hf (hPΩ (pInt_subset_pCl z₀ ω₁ ω₂ hP))
  refine ⟨hfin.subset fun P ⟨hP, hne⟩ => ⟨?_, hP⟩, ?_⟩
  · rw [Function.mem_support, hDP P hP]
    intro h0
    rcases WithTop.untop₀_eq_zero.1 h0 with h0 | h0
    · exact hne h0
    · exact htop P (pInt_subset_pCl z₀ ω₁ ω₂ hP) h0
  -- The boundary integral is the curve integral along the boundary path.
  have hside : ∀ a v : ℂ, v ≠ 0 → (∀ t ∈ Icc (0 : ℝ) 1, a + t • v ∈ range γ) →
      IntervalIntegrable (fun t : ℝ => logDeriv f (a + t • v) * v) volume 0 1 :=
    fun a v hv hav => intervalIntegrable_logDeriv_side hf hv (fun t ht => hγΩ (hav t ht))
      (fun t ht => hγf _ (hav t ht))
  have hint : ∫ᶜ z in γ, logDeriv f z • ContinuousLinearMap.id ℂ ℂ =
      parallelogramBoundaryIntegral (logDeriv f) z₀ ω₁ ω₂ :=
    curveIntegral_parallelogramPath
      (hside _ _ (ne_zero_left h) fun t ht => mem_range_parallelogramPath_iff.2
        ⟨t, 0, ht.1, ht.2, le_rfl, zero_le_one, Or.inr (Or.inr (Or.inl rfl)), by module⟩)
      (hside _ _ (ne_zero_right h) fun t ht => mem_range_parallelogramPath_iff.2
        ⟨1, t, zero_le_one, le_rfl, ht.1, ht.2, Or.inr (Or.inl rfl), by module⟩)
      (hside _ _ (ne_zero_left h) fun t ht => mem_range_parallelogramPath_iff.2
        ⟨t, 1, ht.1, ht.2, zero_le_one, le_rfl, Or.inr (Or.inr (Or.inr rfl)), by module⟩)
      (hside _ _ (ne_zero_right h) fun t ht => mem_range_parallelogramPath_iff.2
        ⟨0, t, le_rfl, zero_le_one, ht.1, ht.2, Or.inl rfl, by module⟩)
  rw [hint, inv_mul_eq_iff_eq_mul₀ two_pi_I_ne_zero] at hres
  rw [hres]
  congr 2
  -- Sums over the open parallelogram reduce to sums over the finitely many zeros and poles.
  have hsum : ∀ φ : ℤ → ℤ, φ 0 = 0 →
      ∑ᶠ z ∈ pInt z₀ ω₁ ω₂, φ (D z) = ∑ z ∈ hfin.toFinset, φ (D z) := by
    intro φ hφ
    rw [← finsum_mem_eq_finite_toFinset_sum _ hfin]
    refine finsum_mem_inter_support_eq _ _ _ ?_
    ext z
    simp only [mem_inter_iff, Function.mem_support]
    exact ⟨fun h => ⟨⟨fun hz => h.2 (by rw [hz, hφ]), h.1⟩, h.2⟩, fun h => ⟨h.1.2, h.2⟩⟩
  simp only [Function.locallyFinsuppWithin.posPart_apply,
    Function.locallyFinsuppWithin.negPart_apply]
  rw [hsum (·⁺) posPart_zero, hsum (·⁻) negPart_zero, ← Finset.sum_sub_distrib,
    finsum_mem_congr rfl fun P hP => (hDP P hP).symm,
    show ∑ᶠ z ∈ pInt z₀ ω₁ ω₂, D z = ∑ z ∈ hfin.toFinset, D z from hsum id rfl]
  exact Finset.sum_congr rfl fun z _ => posPart_sub_negPart (D z)

/-! ### Orientation, winding and Cauchy's theorem -/

/-- **Swapping the sides of a parallelogram reverses its boundary integral.** For
$g : \mathbb{C} \to \mathbb{C}$ and $z_0, \omega_1, \omega_2 \in \mathbb{C}$,
`parallelogramBoundaryIntegral g z₀ ω₂ ω₁ = -parallelogramBoundaryIntegral g z₀ ω₁ ω₂`: the two
integrals run over the same four sides in opposite directions. -/
theorem parallelogramBoundaryIntegral_swap (g : ℂ → ℂ) (z₀ ω₁ ω₂ : ℂ) :
    parallelogramBoundaryIntegral g z₀ ω₂ ω₁ = -parallelogramBoundaryIntegral g z₀ ω₁ ω₂ := by
  unfold parallelogramBoundaryIntegral
  ring

/-- **Curve integral of a continuous function along the boundary of a parallelogram.** Let
$z_0, \omega_1, \omega_2 \in \mathbb{C}$ and let $\varphi : \mathbb{C} \to \mathbb{C}$ be continuous
on the range of `parallelogramPath z₀ ω₁ ω₂`. Then the curve integral of $\varphi(z)\,dz$ along
`parallelogramPath z₀ ω₁ ω₂` is `parallelogramBoundaryIntegral φ z₀ ω₁ ω₂`. -/
theorem curveIntegral_parallelogramPath_of_continuousOn {φ : ℂ → ℂ} {z₀ ω₁ ω₂ : ℂ}
    (hφ : ContinuousOn φ (range (parallelogramPath z₀ ω₁ ω₂))) :
    ∫ᶜ z in parallelogramPath z₀ ω₁ ω₂, φ z • ContinuousLinearMap.id ℂ ℂ =
      parallelogramBoundaryIntegral φ z₀ ω₁ ω₂ := by
  have hside : ∀ a v : ℂ, (∀ t ∈ Icc (0 : ℝ) 1, a + t • v ∈ range (parallelogramPath z₀ ω₁ ω₂)) →
      IntervalIntegrable (fun t : ℝ => φ (a + t • v) * v) volume 0 1 := by
    intro a v hav
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact (hφ.comp (by fun_prop) hav).mul continuousOn_const
  exact curveIntegral_parallelogramPath
    (hside _ _ fun t ht => mem_range_parallelogramPath_iff.2
      ⟨t, 0, ht.1, ht.2, le_rfl, zero_le_one, Or.inr (Or.inr (Or.inl rfl)), by module⟩)
    (hside _ _ fun t ht => mem_range_parallelogramPath_iff.2
      ⟨1, t, zero_le_one, le_rfl, ht.1, ht.2, Or.inr (Or.inl rfl), by module⟩)
    (hside _ _ fun t ht => mem_range_parallelogramPath_iff.2
      ⟨t, 1, ht.1, ht.2, zero_le_one, le_rfl, Or.inr (Or.inr (Or.inr rfl)), by module⟩)
    (hside _ _ fun t ht => mem_range_parallelogramPath_iff.2
      ⟨0, t, le_rfl, zero_le_one, ht.1, ht.2, Or.inl rfl, by module⟩)

private theorem im_div_swap_pos {ω₁ ω₂ : ℂ} (h : (ω₂ / ω₁).im < 0) : 0 < (ω₁ / ω₂).im := by
  have hne : ω₂ / ω₁ ≠ 0 := by rintro h0; rw [h0] at h; simp at h
  rw [← inv_div, inv_im]
  exact div_pos (neg_pos.2 h) (normSq_pos.2 hne)

private theorem boundaryIntegral_inv_sub_of_pos {z₀ ω₁ ω₂ w : ℂ} (hpos : 0 < pdet ω₁ ω₂)
    (hw : w ∈ pInt z₀ ω₁ ω₂) :
    parallelogramBoundaryIntegral (fun z => (z - w)⁻¹) z₀ ω₁ ω₂ = 2 * π * I := by
  have h := hpos.ne'
  have hwK : w ∉ range (parallelogramPath z₀ ω₁ ω₂) := fun hwK =>
    (range_eq h ▸ hwK : w ∈ pCl z₀ ω₁ ω₂ \ pInt z₀ ω₁ ω₂).2 hw
  have hcont : ContinuousOn (fun z => (z - w)⁻¹) (range (parallelogramPath z₀ ω₁ ω₂)) :=
    (continuousOn_id.sub continuousOn_const).inv₀ fun z hz => by
      refine sub_ne_zero.2 fun hzw => hwK ?_
      rw [← show z = w from hzw]
      exact hz
  have hwind := windingNumber_eq_one hpos hw
  rw [Complex.windingNumber, curveIntegral_parallelogramPath_of_continuousOn hcont,
    inv_mul_eq_iff_eq_mul₀ two_pi_I_ne_zero, mul_one] at hwind
  exact hwind

/-- **The boundary integral of $1/(z - w)$ over a parallelogram.** Let
$z_0, \omega_1, \omega_2 \in \mathbb{C}$ with $\operatorname{Im}(\omega_2/\omega_1) \ne 0$ (that is,
$\omega_1, \omega_2$ linearly independent over $\mathbb{R}$), and let
$w = z_0 + t_1\omega_1 + t_2\omega_2$ with $0 < t_1, t_2 < 1$. Then

$$\oint_{\partial D} \frac{dz}{z - w} = 2\pi i\,\sigma,$$

where the left side is `parallelogramBoundaryIntegral (fun z ↦ (z - w)⁻¹) z₀ ω₁ ω₂`, and
$\sigma = 1$ if $\operatorname{Im}(\omega_2/\omega_1) > 0$ (the boundary
$z_0 \to z_0 + \omega_1 \to z_0 + \omega_1 + \omega_2 \to z_0 + \omega_2 \to z_0$ runs
counterclockwise) and $\sigma = -1$ otherwise. -/
theorem parallelogramBoundaryIntegral_inv_sub {z₀ ω₁ ω₂ w : ℂ} (hω : (ω₂ / ω₁).im ≠ 0)
    (hw : ∃ t₁ t₂ : ℝ, 0 < t₁ ∧ t₁ < 1 ∧ 0 < t₂ ∧ t₂ < 1 ∧ w = z₀ + t₁ • ω₁ + t₂ • ω₂) :
    parallelogramBoundaryIntegral (fun z => (z - w)⁻¹) z₀ ω₁ ω₂ =
      2 * π * I * (if 0 < (ω₂ / ω₁).im then 1 else -1) := by
  change w ∈ pInt z₀ ω₁ ω₂ at hw
  rcases lt_or_gt_of_ne hω with hneg | hpos
  · have hn : ¬ 0 < (ω₂ / ω₁).im := not_lt.2 hneg.le
    simp only [hn, ↓reduceIte]
    rw [← neg_neg (parallelogramBoundaryIntegral _ z₀ ω₁ ω₂),
      ← parallelogramBoundaryIntegral_swap,
      boundaryIntegral_inv_sub_of_pos (pdet_pos (im_div_swap_pos hneg)) (pInt_swap z₀ ω₁ ω₂ ▸ hw)]
    ring
  · simp only [hpos, ↓reduceIte, mul_one]
    exact boundaryIntegral_inv_sub_of_pos (pdet_pos hpos) hw

/-- **Cauchy's theorem for a parallelogram.** Let $\Omega \subseteq \mathbb{C}$ be open,
$f : \mathbb{C} \to \mathbb{C}$ complex differentiable on $\Omega$, and
$z_0, \omega_1, \omega_2 \in \mathbb{C}$ with $\operatorname{Im}(\omega_2/\omega_1) \ne 0$, such
that the closed parallelogram $\{z_0 + t_1\omega_1 + t_2\omega_2 : 0 \le t_1, t_2 \le 1\}$ lies in
$\Omega$. Then `parallelogramBoundaryIntegral f z₀ ω₁ ω₂ = 0`.

The proof applies Cauchy's theorem for a path homologous to zero
(`Complex.curveIntegral_eq_zero_of_differentiableOn`) to `parallelogramPath z₀ ω₁ ω₂`: its winding
number vanishes off the closed parallelogram, whose complement is the unbounded component of the
complement of the path. -/
theorem parallelogramBoundaryIntegral_eq_zero_of_differentiableOn {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω) {z₀ ω₁ ω₂ : ℂ} (hω : (ω₂ / ω₁).im ≠ 0)
    (hPΩ : {P | ∃ t₁ t₂ : ℝ, 0 ≤ t₁ ∧ t₁ ≤ 1 ∧ 0 ≤ t₂ ∧ t₂ ≤ 1 ∧ P = z₀ + t₁ • ω₁ + t₂ • ω₂} ⊆ Ω) :
    parallelogramBoundaryIntegral f z₀ ω₁ ω₂ = 0 := by
  have h := pdet_ne_zero hω
  change pCl z₀ ω₁ ω₂ ⊆ Ω at hPΩ
  set γ := parallelogramPath z₀ ω₁ ω₂
  have hγ := isPiecewiseC1_parallelogramPath z₀ ω₁ ω₂
  have hKcl : range γ ⊆ pCl z₀ ω₁ ω₂ := range_eq h ▸ sdiff_subset
  have hγΩ : range γ ⊆ Ω := hKcl.trans hPΩ
  have hhom : Complex.IsHomologousToZero γ Ω := by
    refine ⟨hγΩ, fun a ha => Complex.windingNumber_eq_zero_of_not_isBounded hγ fun hb => ?_⟩
    have haK : a ∉ range γ := fun haK => ha (hγΩ haK)
    have hains : a ∈ (range γ).inside := mem_inside.2 ⟨haK, hb⟩
    rw [inside_eq h] at hains
    exact ha (hPΩ (pInt_subset_pCl z₀ ω₁ ω₂ hains))
  rw [← curveIntegral_parallelogramPath_of_continuousOn (hf.continuousOn.mono hγΩ)]
  exact (Complex.curveIntegral_eq_zero_of_differentiableOn hΩ hf).1 γ hγ hhom

/-- **Argument principle for a parallelogram.** Let $\Omega \subseteq \mathbb{C}$ be open,
$f : \mathbb{C} \to \mathbb{C}$ meromorphic at every point of $\Omega$, and
$z_0, \omega_1, \omega_2 \in \mathbb{C}$ with $\operatorname{Im}(\omega_2 / \omega_1) \ne 0$, that
is, $\omega_1, \omega_2$ linearly independent over $\mathbb{R}$. Let
$D = \{z_0 + t_1\omega_1 + t_2\omega_2 : 0 < t_1, t_2 < 1\}$ be the open parallelogram and
$\overline{D} = \{z_0 + t_1\omega_1 + t_2\omega_2 : 0 \le t_1, t_2 \le 1\}$ the closed one. Suppose
that $\overline{D} \subseteq \Omega$ and that the meromorphic order $\operatorname{ord}_P f$ is
$0$ at every $P \in \overline{D} \setminus D$. Then only finitely many $P \in D$ have
$\operatorname{ord}_P f \ne 0$, and

$$\oint_{\partial D} \frac{f'(z)}{f(z)}\,dz = 2\pi i\,\sigma \sum_{P \in D} \mathrm{ord}_P f,$$

where the left side is `parallelogramBoundaryIntegral (logDeriv f) z₀ ω₁ ω₂`, the integral along
$z_0 \to z_0 + \omega_1 \to z_0 + \omega_1 + \omega_2 \to z_0 + \omega_2 \to z_0$,
$\operatorname{ord}_P f$ is `(meromorphicOrderAt f P).untop₀`, and $\sigma = 1$ if
$\operatorname{Im}(\omega_2/\omega_1) > 0$ (the path runs counterclockwise) and $\sigma = -1$
otherwise.

Neither the finiteness of $\operatorname{ord}_P f$ on $\overline{D}$ nor the finiteness of the
set of zeros and poles in $D$ is assumed. The first follows from the hypotheses, because
$\overline{D}$ is connected and meets the boundary, where the order is $0$; the second is part of
the conclusion.

Source: J. S. Milne, *Elliptic Curves*, 2nd ed., Chapter III, §2, proof of Proposition 2.1, p. 87:
the residue theorem applied to $f'/f$ over the boundary of the period parallelogram $D$, with
$\operatorname{Res}_P(f'/f) = \operatorname{ord}_P(f)$. -/
theorem MeromorphicOn.parallelogramBoundaryIntegral_logDeriv {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {f : ℂ → ℂ} (hf : MeromorphicOn f Ω) {z₀ ω₁ ω₂ : ℂ} (hω : (ω₂ / ω₁).im ≠ 0)
    (hPΩ : {P | ∃ t₁ t₂ : ℝ, 0 ≤ t₁ ∧ t₁ ≤ 1 ∧ 0 ≤ t₂ ∧ t₂ ≤ 1 ∧ P = z₀ + t₁ • ω₁ + t₂ • ω₂} ⊆ Ω)
    (hbd : ∀ P ∈ {P | ∃ t₁ t₂ : ℝ, 0 ≤ t₁ ∧ t₁ ≤ 1 ∧ 0 ≤ t₂ ∧ t₂ ≤ 1 ∧
        P = z₀ + t₁ • ω₁ + t₂ • ω₂},
      P ∉ {P | ∃ t₁ t₂ : ℝ, 0 < t₁ ∧ t₁ < 1 ∧ 0 < t₂ ∧ t₂ < 1 ∧ P = z₀ + t₁ • ω₁ + t₂ • ω₂} →
        meromorphicOrderAt f P = 0) :
    {P | (∃ t₁ t₂ : ℝ, 0 < t₁ ∧ t₁ < 1 ∧ 0 < t₂ ∧ t₂ < 1 ∧ P = z₀ + t₁ • ω₁ + t₂ • ω₂) ∧
        meromorphicOrderAt f P ≠ 0}.Finite ∧
      parallelogramBoundaryIntegral (logDeriv f) z₀ ω₁ ω₂ =
        2 * π * I * (if 0 < (ω₂ / ω₁).im then 1 else -1) *
          ((∑ᶠ P ∈ {P | ∃ t₁ t₂ : ℝ, 0 < t₁ ∧ t₁ < 1 ∧ 0 < t₂ ∧ t₂ < 1 ∧
            P = z₀ + t₁ • ω₁ + t₂ • ω₂}, (meromorphicOrderAt f P).untop₀ : ℤ) : ℂ) := by
  change pCl z₀ ω₁ ω₂ ⊆ Ω at hPΩ
  change ∀ P ∈ pCl z₀ ω₁ ω₂, P ∉ pInt z₀ ω₁ ω₂ → meromorphicOrderAt f P = 0 at hbd
  change {P | P ∈ pInt z₀ ω₁ ω₂ ∧ meromorphicOrderAt f P ≠ 0}.Finite ∧
    parallelogramBoundaryIntegral (logDeriv f) z₀ ω₁ ω₂ =
      2 * π * I * (if 0 < (ω₂ / ω₁).im then 1 else -1) *
        ((∑ᶠ P ∈ pInt z₀ ω₁ ω₂, (meromorphicOrderAt f P).untop₀ : ℤ) : ℂ)
  rcases lt_or_gt_of_ne hω with hneg | hpos
  · have hPΩ' : pCl z₀ ω₂ ω₁ ⊆ Ω := by rw [pCl_swap]; exact hPΩ
    have hbd' : ∀ P ∈ pCl z₀ ω₂ ω₁, P ∉ pInt z₀ ω₂ ω₁ → meromorphicOrderAt f P = 0 := by
      rw [pCl_swap, pInt_swap]; exact hbd
    obtain ⟨hfin, heq⟩ := MeromorphicOn.parallelogramBoundaryIntegral_logDeriv_of_im_pos hΩ hf
      (im_div_swap_pos hneg) hPΩ' hbd'
    change {P | P ∈ pInt z₀ ω₂ ω₁ ∧ meromorphicOrderAt f P ≠ 0}.Finite at hfin
    change _ = 2 * π * I * ((∑ᶠ P ∈ pInt z₀ ω₂ ω₁, (meromorphicOrderAt f P).untop₀ : ℤ) : ℂ)
      at heq
    rw [pInt_swap] at hfin heq
    refine ⟨hfin, ?_⟩
    have hn : ¬ 0 < (ω₂ / ω₁).im := not_lt.2 hneg.le
    simp only [hn, ↓reduceIte]
    rw [← neg_neg (parallelogramBoundaryIntegral _ z₀ ω₁ ω₂),
      ← parallelogramBoundaryIntegral_swap, heq]
    ring
  · obtain ⟨hfin, heq⟩ :=
      MeromorphicOn.parallelogramBoundaryIntegral_logDeriv_of_im_pos hΩ hf hpos hPΩ hbd
    exact ⟨hfin, by simp only [hpos, ↓reduceIte, mul_one]; exact heq⟩

/-- **The periods of a period pair span a nondegenerate parallelogram.** For a period pair $L$
with periods $\omega_1, \omega_2$, $\operatorname{Im}(\omega_2 / \omega_1) \ne 0$: this is the
linear independence of $\omega_1, \omega_2$ over $\mathbb{R}$. -/
theorem PeriodPair.im_ω₂_div_ω₁_ne_zero (L : PeriodPair) : (L.ω₂ / L.ω₁).im ≠ 0 := by
  intro h0
  have hω₁ : L.ω₁ ≠ 0 := by simpa using L.indep.ne_zero 0
  have hr : L.ω₂ / L.ω₁ = ((L.ω₂ / L.ω₁).re : ℂ) := Complex.ext (by simp) (by simp [h0])
  have hω₂ : L.ω₂ = (L.ω₂ / L.ω₁).re • L.ω₁ := by
    rw [Complex.real_smul, ← hr]; field_simp
  have := (LinearIndependent.pair_iff.1 L.indep) ((L.ω₂ / L.ω₁).re) (-1) (by
    rw [← hω₂]; simp)
  norm_num at this

end
