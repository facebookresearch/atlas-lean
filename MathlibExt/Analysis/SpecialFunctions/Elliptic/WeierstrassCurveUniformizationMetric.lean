/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.Elliptic.FundamentalParallelogramArea
public import MathlibExt.Analysis.SpecialFunctions.Elliptic.HomothetyClasses
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The archimedean metric of a complex Weierstrass curve through a uniformization datum

For a Weierstrass curve `W` over `ℂ`, the archimedean contribution to Silverman's formula for
the height of an elliptic curve is the squared norm `(i/2) ∫_{E(ℂ)} α_W ∧ ᾱ_W` of the invariant
differential `α_W = dx / (2y + a₁x + a₃)`. This file computes that quantity through a
*uniformization datum*: a period pair `L` with lattice `Λ` together with a variable change `C`
taking `W` to the curve `Y² = 4X³ - g₂(Λ)X - g₃(Λ)` of `Λ` (in Mathlib's form
`y² = x³ - (g₂/4)x - g₃/4`, with `X = x`, `Y = 2y`). The analytic identifications behind the
formula (the parametrization `z ↦ (℘(z), ℘'(z)/2)` pulls `dx/(2y)` back to `dz`, and
`(i/2) ∫_{ℂ/Λ} dz ∧ dz̄` is the area of a fundamental parallelogram) are *not* formalized: the
value `‖u‖⁻² · covol(Λ)` is taken as the definition of the squared norm.

## Main definitions

* `PeriodPair.covolume`: `|Im(conj ω₁ · ω₂)|`, the area of a fundamental parallelogram.
* `PeriodPair.weierstrassCurve`: the Weierstrass curve `⟨0, 0, 0, -g₂/4, -g₃/4⟩` of a period pair.
* `WeierstrassCurve.UniformizationDatum`: a period pair with a variable change from `W` to its
  Weierstrass curve.
* `WeierstrassCurve.UniformizationDatum.normSq`: `‖u‖⁻² · covol(Λ)`.

## Main results

* `PeriodPair.volume_fundamentalParallelogram_eq_covolume`, `PeriodPair.covolume_pos`,
  `PeriodPair.covolume_ofTau`, `PeriodPair.covolume_eq_of_lattice_eq_smul` (`covol(cΛ) =
  |c|² covol(Λ)`, for any period pairs with these lattices).
* `PeriodPair.weierstrassCurve_Δ`, `PeriodPair.isElliptic_weierstrassCurve`,
  `PeriodPair.equation_weierstrassP_derivWeierstrassP` (the point `(℘(z), ℘'(z)/2)` lies on the
  curve).
* `PeriodPair.norm_discriminant_mul_covolume_pow_six_eq_of_lattice_eq_smul`:
  `‖Δ(Λ)‖ covol(Λ)⁶` is a homothety invariant.
* `WeierstrassCurve.UniformizationDatum.normSq_pow_six`, `log_normSq`: the closed formula
  `normSq⁶ = ‖Δ(Λ)‖ covol(Λ)⁶ / ‖Δ(W)‖`.
* `WeierstrassCurve.UniformizationDatum.normSq_eq_of_lattice_eq_smul`: two data for `W` with
  homothetic lattices give the same value.
* `WeierstrassCurve.UniformizationDatum.normSq_pow_six_of_isHomothetic_ofTau`: the value through
  `τ` in the upper half-plane, `normSq⁶ = ‖Δ(τ)‖ (Im τ)⁶ / ‖Δ(W)‖`.
* `WeierstrassCurve.UniformizationDatum.normSq_variableChange`: a datum for `W` gives one for
  `C' • W`, and `normSq` is multiplied by `‖u'‖²`.

## What is missing for a canonical metric

The value `normSq` is shown here to depend only on the homothety class of the lattice of the
datum. Two further facts, neither available here, would make it an invariant of `W` alone:

1. *Lattices with isomorphic Weierstrass curves are homothetic*: if `C • L.weierstrassCurve =
   L'.weierstrassCurve`, then `Λ' = cΛ` (`c = u⁻¹`). Over `ℂ` the variable change must have
   `r = s = t = 0`, so `g₂(Λ') = u⁻⁴ g₂(Λ)` and `g₃(Λ') = u⁻⁶ g₃(Λ)`; then `℘_{Λ'}(z)` and
   `u⁻² ℘_Λ(u⁻¹ z)` have the same Laurent expansion at `0` (its coefficients are polynomials in
   `g₂`, `g₃`), hence agree, and their pole sets are `Λ'` and `uΛ`.
2. *Existence of a datum for every `W` over `ℂ` with `Δ(W) ≠ 0`*: this is the uniformization
   theorem, i.e. surjectivity of `j : ℍ → ℂ` (J. S. Milne, *Elliptic Curves*, 2nd ed., Chapter
   III, Theorem 3.10, p. 96, with Chapter V, 2.2), together with the classification of Weierstrass
   curves over an algebraically closed field by `j`.

Also not on main: `Δ(Λ) = g₂³ - 27 g₃² ≠ 0` for every lattice (Milne, Chapter III, Lemma 3.6,
p. 95); results needing it take `Δ(W) ≠ 0` as a hypothesis.

## References

* J. H. Silverman, *Heights and elliptic curves*, in: *Arithmetic Geometry* (G. Cornell,
  J. H. Silverman, eds.), Springer, 1986, pp. 255–256.
* J. S. Milne, *Elliptic Curves*, 2nd ed., World Scientific, 2021, Chapter III, §§1–3
  (Proposition 2.6, p. 89; Lemma 3.6 and Proposition 3.7, p. 95; Theorem 3.10, p. 96).
* P. Deligne, *Preuve des conjectures de Tate et Shafarevitch (d'après G. Faltings)*, Séminaire
  Bourbaki, exp. 616, Astérisque 121–122 (1985), §1.2 (b), p. 26 (the Hermitian metric on the
  space of invariant differentials defined by integrating `α ∧ ᾱ`).
-/

@[expose] public section

open MeasureTheory
open scoped Pointwise UpperHalfPlane

namespace PeriodPair

/-! ### The covolume of a period pair -/

/-- The **covolume** of a period pair `(ω₁, ω₂)`: the real number `|Im(conj ω₁ · ω₂)|`, which is
the Lebesgue measure of a fundamental parallelogram
(`PeriodPair.volume_fundamentalParallelogram_eq_covolume`). -/
noncomputable def covolume (L : PeriodPair) : ℝ :=
  |(starRingEnd ℂ L.ω₁ * L.ω₂).im|

/-- **Area of a fundamental parallelogram as the covolume.** For a period pair `L` and
`α ∈ ℂ`, the fundamental parallelogram `{α + t₁ω₁ + t₂ω₂ : t₁, t₂ ∈ [0, 1)}` has Lebesgue measure
`L.covolume`.

Source: J. S. Milne, *Elliptic Curves*, 2nd ed., World Scientific, 2021, Chapter III, §1, p. 86
(the period parallelogram); this is `PeriodPair.volume_fundamentalParallelogram` restated. -/
theorem volume_fundamentalParallelogram_eq_covolume (L : PeriodPair) (α : ℂ) :
    volume (L.fundamentalParallelogram α) = ENNReal.ofReal L.covolume :=
  L.volume_fundamentalParallelogram α

/-- The covolume of a period pair is positive: `ω₁`, `ω₂` are `ℝ`-linearly independent. -/
theorem covolume_pos (L : PeriodPair) : 0 < L.covolume := by
  rw [covolume, ← basisOneI_det_basis]
  exact abs_pos.mpr (Complex.basisOneI.isUnit_det L.basis).ne_zero

/-- The covolume of the period pair `(1, τ)` is `|Im τ|`. -/
theorem covolume_ofTau (τ : ℂ) (hτ : τ.im ≠ 0) : (ofTau τ hτ).covolume = |τ.im| := by
  simp [covolume, ofTau_ω₁, ofTau_ω₂]

/-- The covolume of the period pair `(1, τ)` with `τ` in the upper half-plane is `Im τ`. -/
theorem covolume_ofTau_upperHalfPlane (τ : ℍ) :
    (ofTau τ τ.im_pos.ne').covolume = τ.im := by
  exact (covolume_ofTau (τ : ℂ) τ.im_pos.ne').trans (abs_of_pos τ.im_pos)

private lemma im_conj_intComb_mul_intComb (x y : ℂ) (a b c d : ℤ) :
    (starRingEnd ℂ (a * x + b * y) * (c * x + d * y)).im =
      ((a * d - b * c : ℤ) : ℝ) * (starRingEnd ℂ x * y).im := by
  simp only [map_add, map_mul, map_intCast, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.conj_re,
    Complex.conj_im]
  push_cast
  ring

private lemma im_conj_mul_mul (c u v : ℂ) :
    (starRingEnd ℂ (c * u) * (c * v)).im = ‖c‖ ^ 2 * (starRingEnd ℂ u * v).im := by
  have h : starRingEnd ℂ (c * u) * (c * v) = (starRingEnd ℂ c * c) * (starRingEnd ℂ u * v) := by
    rw [map_mul]; ring
  rw [h, Complex.conj_mul', ← Complex.ofReal_pow, Complex.im_ofReal_mul]

/-- If every period of `L'` is `c` times a period of `L`, the covolume of `L'` is
`‖c‖² |k|` times that of `L` for an integer `k` (the determinant of the integer matrix). -/
private lemma exists_covolume_eq {L L' : PeriodPair} {c : ℂ}
    (h : ∀ x ∈ L'.lattice, ∃ y ∈ L.lattice, x = c * y) :
    ∃ k : ℤ, L'.covolume = ‖c‖ ^ 2 * |(k : ℝ)| * L.covolume := by
  obtain ⟨y₁, hy₁, e₁⟩ := h _ (ω₁_mem_lattice (L := L'))
  obtain ⟨y₂, hy₂, e₂⟩ := h _ (ω₂_mem_lattice (L := L'))
  obtain ⟨a, b, rfl⟩ := mem_lattice.mp hy₁
  obtain ⟨c', d, rfl⟩ := mem_lattice.mp hy₂
  refine ⟨a * d - b * c', ?_⟩
  rw [covolume, covolume, e₁, e₂, im_conj_mul_mul, im_conj_intComb_mul_intComb, abs_mul,
    abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖c‖ ^ 2)]
  push_cast
  ring

/-- **Covolume of homothetic lattices.** Let `L`, `L'` be period pairs whose lattices satisfy
`Λ' = cΛ` with `c ≠ 0`. Then `covol(L') = ‖c‖² covol(L)`.

The periods of `L'` need not be `c` times those of `L`: the two bases of `Λ'` differ by an
integer matrix of determinant `±1`, which leaves `|Im(conj ω₁ · ω₂)|` unchanged.

Source: J. S. Milne, *Elliptic Curves*, 2nd ed., World Scientific, 2021, Chapter III, §1, p. 86
(period parallelograms); the computation is done here. -/
theorem covolume_eq_of_lattice_eq_smul {L L' : PeriodPair} {c : ℂ} (hc : c ≠ 0)
    (h : (L'.lattice : Set ℂ) = c • (L.lattice : Set ℂ)) :
    L'.covolume = ‖c‖ ^ 2 * L.covolume := by
  obtain ⟨k, hk⟩ := exists_covolume_eq (L := L) (L' := L') (c := c) fun x hx => by
    have hx' : x ∈ c • (L.lattice : Set ℂ) := h ▸ hx
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hx'
    exact ⟨y, hy, rfl⟩
  obtain ⟨k', hk'⟩ := exists_covolume_eq (L := L') (L' := L) (c := c⁻¹) fun x hx => by
    have hx' : c * x ∈ (L'.lattice : Set ℂ) := h ▸ Set.smul_mem_smul_set hx
    exact ⟨c * x, hx', by field_simp⟩
  have hpos := L.covolume_pos
  have hcn : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  have e : (|(k : ℝ)| * |(k' : ℝ)|) * L.covolume = 1 * L.covolume := by
    calc (|(k : ℝ)| * |(k' : ℝ)|) * L.covolume
        = ‖c⁻¹‖ ^ 2 * |(k' : ℝ)| * (‖c‖ ^ 2 * |(k : ℝ)| * L.covolume) := by
          rw [norm_inv]; field_simp
      _ = 1 * L.covolume := by rw [← hk, ← hk', one_mul]
  have hkk : |(k : ℝ)| * |(k' : ℝ)| = 1 := mul_right_cancel₀ hpos.ne' e
  have hkkZ : |k| * |k'| = 1 := by
    have : ((|k| * |k'| : ℤ) : ℝ) = 1 := by push_cast; exact hkk
    exact_mod_cast this
  have hk1 : |k| = 1 := Int.eq_one_of_mul_eq_one_right (abs_nonneg k) hkkZ
  have hk1' : |(k : ℝ)| = 1 := by
    rw [← Int.cast_abs, hk1, Int.cast_one]
  rw [hk, hk1', mul_one]

/-! ### The Weierstrass curve of a period pair -/

/-- The **Weierstrass curve of a period pair** `L`: the curve `y² = x³ - (g₂/4) x - g₃/4`, i.e.
`⟨a₁, a₂, a₃, a₄, a₆⟩ = ⟨0, 0, 0, -g₂/4, -g₃/4⟩`. With `X = x`, `Y = 2y` it is Milne's curve
`Y² = 4X³ - g₂X - g₃` (J. S. Milne, *Elliptic Curves*, 2nd ed., Chapter III, §3, p. 95). -/
noncomputable def weierstrassCurve (L : PeriodPair) : WeierstrassCurve ℂ :=
  ⟨0, 0, 0, -L.g₂ / 4, -L.g₃ / 4⟩

/-- **The discriminant of the Weierstrass curve of a period pair.** The discriminant of the curve
`y² = x³ - (g₂/4) x - g₃/4` is `g₂³ - 27 g₃²`.

Source: J. S. Milne, *Elliptic Curves*, 2nd ed., World Scientific, 2021, Chapter III, proof of
Theorem 3.10, p. 96 (for the model `Y² = 4X³ - g₂X - g₃`); with Mathlib's normalization of `Δ`
the value is the same, computed here. -/
theorem weierstrassCurve_Δ (L : PeriodPair) :
    L.weierstrassCurve.Δ = L.g₂ ^ 3 - 27 * L.g₃ ^ 2 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, weierstrassCurve]
  ring

/-- **The Weierstrass curve of a period pair is elliptic when `g₂³ - 27 g₃² ≠ 0`.** The
hypothesis always holds (J. S. Milne, *Elliptic Curves*, 2nd ed., Chapter III, Lemma 3.6, p. 95),
but that lemma is not available here, so it is assumed. -/
theorem isElliptic_weierstrassCurve (L : PeriodPair) (h : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ≠ 0) :
    L.weierstrassCurve.IsElliptic :=
  ⟨by rw [weierstrassCurve_Δ]; exact h.isUnit⟩

/-- **The Weierstrass parametrization lands on the curve.** For a period pair `L` and
`z ∉ Λ`, the point `(℘(z), ℘'(z)/2)` satisfies the equation `y² = x³ - (g₂/4) x - g₃/4` of
`L.weierstrassCurve`.

Source: J. S. Milne, *Elliptic Curves*, 2nd ed., World Scientific, 2021, Chapter III,
Proposition 2.6, p. 89 (`℘'² = 4℘³ - g₂℘ - g₃`), via `PeriodPair.derivWeierstrassP_sq`. -/
theorem equation_weierstrassP_derivWeierstrassP (L : PeriodPair) (z : ℂ) (hz : z ∉ L.lattice) :
    L.weierstrassCurve.toAffine.Equation (L.weierstrassP z) (L.derivWeierstrassP z / 2) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  have h := L.derivWeierstrassP_sq z hz
  simp only [weierstrassCurve]
  linear_combination h / 4

/-! ### Homothety invariance of `‖Δ‖ covol⁶` -/

/-- **`‖Δ(Λ)‖ covol(Λ)⁶` is a homothety invariant.** If the lattices of the period pairs `L`, `L'`
satisfy `Λ' = cΛ` with `c ≠ 0`, then, with `Δ = g₂³ - 27 g₃²`,
`‖Δ(L')‖ covol(L')⁶ = ‖Δ(L)‖ covol(L)⁶`: `Δ` scales by `c⁻¹²` and the covolume by `‖c‖²`.

Source: J. S. Milne, *Elliptic Curves*, 2nd ed., World Scientific, 2021, Chapter III, proof of
Theorem 3.10, p. 96 (scaling of `g₂`, `g₃`); the combination with the covolume is done here. -/
theorem norm_discriminant_mul_covolume_pow_six_eq_of_lattice_eq_smul {L L' : PeriodPair}
    {c : ℂ} (hc : c ≠ 0) (h : (L'.lattice : Set ℂ) = c • (L.lattice : Set ℂ)) :
    ‖L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2‖ * L'.covolume ^ 6 =
      ‖L.g₂ ^ 3 - 27 * L.g₃ ^ 2‖ * L.covolume ^ 6 := by
  rw [discriminant_eq_of_lattice_eq_smul hc h, covolume_eq_of_lattice_eq_smul hc h, norm_mul,
    norm_pow, norm_inv]
  have hcn : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  field_simp

end PeriodPair

namespace WeierstrassCurve

/-- A **uniformization datum** for a Weierstrass curve `W` over `ℂ`: a period pair `L` and a
variable change `C` with `C • W = L.weierstrassCurve`, the curve `Y² = 4X³ - g₂X - g₃` of the
lattice of `L` (with `X = x`, `Y = 2y`). -/
structure UniformizationDatum (W : WeierstrassCurve ℂ) where
  /-- The period pair. -/
  L : PeriodPair
  /-- The variable change from `W` to the Weierstrass curve of `L`. -/
  C : VariableChange ℂ
  /-- The variable change takes `W` to the Weierstrass curve of `L`. -/
  eq : C • W = L.weierstrassCurve

namespace UniformizationDatum

variable {W : WeierstrassCurve ℂ}

/-- The **squared norm of the invariant differential** of `W` computed through a uniformization
datum `D = (L, C)`: `‖u‖⁻² · covol(Λ)`, where `u` is the scaling factor of `C` and `Λ` the lattice
of `L`.

This is the value of `(i/2) ∫_{ℂ/Λ} α_W ∧ ᾱ_W`, where `α_W` is the invariant differential of `W`,
computed as follows (J. H. Silverman, *Heights and elliptic curves*, in: *Arithmetic Geometry*,
Springer, 1986, pp. 255–256): under the parametrization `z ↦ (℘(z), ℘'(z)/2)` the invariant
differential `dx/(2y)` of `L.weierstrassCurve` pulls back to `dz`, `α_{C•W} = u·α_W`
(variable-change law), and `(i/2) ∫ dz ∧ dz̄` over `ℂ/Λ` is the area of a fundamental
parallelogram; these analytic identifications are the definition here, not formalized. -/
noncomputable def normSq (D : W.UniformizationDatum) : ℝ :=
  ‖(D.C.u : ℂ)‖ ^ (-2 : ℤ) * D.L.covolume

/-- The squared norm computed through a uniformization datum is positive. -/
theorem normSq_pos (D : W.UniformizationDatum) : 0 < D.normSq :=
  mul_pos (zpow_pos (norm_pos_iff.mpr D.C.u.ne_zero) _) D.L.covolume_pos

/-- **The discriminant of the lattice of a uniformization datum.** For a uniformization datum
`D = (L, C)` of `W`, `g₂(L)³ - 27 g₃(L)² = u⁻¹² Δ(W)`, from the transformation law of the
discriminant under a variable change (`WeierstrassCurve.variableChange_Δ`). -/
theorem discriminant_eq (D : W.UniformizationDatum) :
    D.L.g₂ ^ 3 - 27 * D.L.g₃ ^ 2 = ((D.C.u⁻¹ : ℂˣ) : ℂ) ^ 12 * W.Δ := by
  rw [← PeriodPair.weierstrassCurve_Δ, ← D.eq, variableChange_Δ]

/-- **Closed formula for the squared norm.** For a uniformization datum `D = (L, C)` of a
Weierstrass curve `W` over `ℂ` with `Δ(W) ≠ 0`,
`normSq(D)⁶ = ‖g₂(L)³ - 27 g₃(L)²‖ · covol(L)⁶ / ‖Δ(W)‖`.

Source: J. H. Silverman, *Heights and elliptic curves*, in: *Arithmetic Geometry*, Springer,
1986, pp. 255–256; derived here from `WeierstrassCurve.variableChange_Δ`. -/
theorem normSq_pow_six (D : W.UniformizationDatum) (hW : W.Δ ≠ 0) :
    D.normSq ^ 6 =
      ‖D.L.g₂ ^ 3 - 27 * D.L.g₃ ^ 2‖ * D.L.covolume ^ 6 / ‖W.Δ‖ := by
  rw [discriminant_eq, norm_mul, norm_pow, Units.val_inv_eq_inv_val, norm_inv, normSq, mul_pow,
    zpow_neg, zpow_ofNat]
  have hu : ‖(D.C.u : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr D.C.u.ne_zero
  have hΔ : ‖W.Δ‖ ≠ 0 := norm_ne_zero_iff.mpr hW
  field_simp

/-- **Logarithm of the squared norm.** For a uniformization datum `D = (L, C)` of a Weierstrass
curve `W` over `ℂ` with `Δ(W) ≠ 0`,
`log normSq(D) = (1/6) (log (‖g₂(L)³ - 27 g₃(L)²‖ · covol(L)⁶) - log ‖Δ(W)‖)`.

Source: J. H. Silverman, *Heights and elliptic curves*, in: *Arithmetic Geometry*, Springer,
1986, pp. 255–256; derived here from `normSq_pow_six`. -/
theorem log_normSq (D : W.UniformizationDatum) (hW : W.Δ ≠ 0) :
    Real.log D.normSq =
      1 / 6 * (Real.log (‖D.L.g₂ ^ 3 - 27 * D.L.g₃ ^ 2‖ * D.L.covolume ^ 6) -
        Real.log ‖W.Δ‖) := by
  have hΔL : D.L.g₂ ^ 3 - 27 * D.L.g₃ ^ 2 ≠ 0 := by
    rw [discriminant_eq]
    exact mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) hW
  have hA : ‖D.L.g₂ ^ 3 - 27 * D.L.g₃ ^ 2‖ * D.L.covolume ^ 6 ≠ 0 :=
    mul_ne_zero (norm_ne_zero_iff.mpr hΔL) (pow_ne_zero _ D.L.covolume_pos.ne')
  have hB : ‖W.Δ‖ ≠ 0 := norm_ne_zero_iff.mpr hW
  have h6 : Real.log (D.normSq ^ 6) = 6 * Real.log D.normSq := by
    rw [Real.log_pow]; norm_num
  rw [normSq_pow_six D hW, Real.log_div hA hB] at h6
  linarith

/-- **Independence of the datum within a homothety class.** Let `D = (L, C)` and `D' = (L', C')`
be uniformization data for a Weierstrass curve `W` over `ℂ` with `Δ(W) ≠ 0`, whose lattices
satisfy `Λ' = cΛ` with `c ≠ 0`. Then `normSq(D') = normSq(D)`.

Proved from `normSq_pow_six` and the homothety invariance of `‖Δ‖ covol⁶`, without comparing the
variable changes. -/
theorem normSq_eq_of_lattice_eq_smul (hW : W.Δ ≠ 0) (D D' : W.UniformizationDatum) {c : ℂ}
    (hc : c ≠ 0) (h : (D'.L.lattice : Set ℂ) = c • (D.L.lattice : Set ℂ)) :
    D'.normSq = D.normSq := by
  have h6 : D'.normSq ^ 6 = D.normSq ^ 6 := by
    rw [normSq_pow_six D' hW, normSq_pow_six D hW,
      PeriodPair.norm_discriminant_mul_covolume_pow_six_eq_of_lattice_eq_smul hc h]
  exact (pow_left_inj₀ D'.normSq_pos.le D.normSq_pos.le (by norm_num)).mp h6

/-- **Independence of the datum within a homothety class**, stated with
`PeriodPair.IsHomothetic`: uniformization data `D`, `D'` for `W` with `Δ(W) ≠ 0` whose period
pairs are homothetic give the same squared norm. -/
theorem normSq_eq_of_isHomothetic (hW : W.Δ ≠ 0) (D D' : W.UniformizationDatum)
    (h : D.L.IsHomothetic D'.L) : D'.normSq = D.normSq := by
  obtain ⟨c, hc, hcL⟩ := h
  exact normSq_eq_of_lattice_eq_smul hW D D' hc hcL

/-- **The squared norm through `τ`.** Let `D = (L, C)` be a uniformization datum for a
Weierstrass curve `W` over `ℂ` with `Δ(W) ≠ 0`, and let `τ` be in the upper half-plane with `L`
homothetic to `(1, τ)`. Then, with `Δ(τ) = g₂(1, τ)³ - 27 g₃(1, τ)²`,
`normSq(D)⁶ = ‖Δ(τ)‖ (Im τ)⁶ / ‖Δ(W)‖`.

Source: J. H. Silverman, *Heights and elliptic curves*, in: *Arithmetic Geometry*, Springer,
1986, pp. 255–256; derived here. Every period pair is homothetic to some `(1, τ)`
(`PeriodPair.exists_isHomothetic_ofTau`). -/
theorem normSq_pow_six_of_isHomothetic_ofTau (hW : W.Δ ≠ 0) (D : W.UniformizationDatum)
    (τ : ℍ) (h : D.L.IsHomothetic (PeriodPair.ofTau τ τ.im_pos.ne')) :
    D.normSq ^ 6 =
      ‖(PeriodPair.ofTau τ τ.im_pos.ne').g₂ ^ 3 - 27 * (PeriodPair.ofTau τ τ.im_pos.ne').g₃ ^ 2‖ *
        τ.im ^ 6 / ‖W.Δ‖ := by
  obtain ⟨c, hc, hcL⟩ := h
  rw [normSq_pow_six D hW,
    ← PeriodPair.norm_discriminant_mul_covolume_pow_six_eq_of_lattice_eq_smul hc hcL,
    PeriodPair.covolume_ofTau_upperHalfPlane]

/-- **Transport of a uniformization datum along a variable change.** A uniformization datum
`D = (L, C)` for `W` gives the datum `(L, C * C'⁻¹)` for `C' • W`. -/
def variableChange (D : W.UniformizationDatum) (C' : VariableChange ℂ) :
    (C' • W).UniformizationDatum where
  L := D.L
  C := D.C * C'⁻¹
  eq := by rw [mul_smul, inv_smul_smul, D.eq]

/-- **The squared norm under a variable change.** For a uniformization datum `D` of `W` and a
variable change `C'` with scaling factor `u'`, the transported datum for `C' • W` has squared
norm `‖u'‖² · normSq(D)`, matching `α_{C'•W} = u' α_W`. -/
theorem normSq_variableChange (D : W.UniformizationDatum) (C' : VariableChange ℂ) :
    (D.variableChange C').normSq = ‖(C'.u : ℂ)‖ ^ 2 * D.normSq := by
  have hu : (D.C * C'⁻¹).u = D.C.u * C'.u⁻¹ := by
    rw [VariableChange.mul_def, VariableChange.inv_def]
  simp only [normSq, variableChange, hu, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul,
    norm_inv, zpow_neg, zpow_ofNat]
  have h1 : ‖(D.C.u : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr D.C.u.ne_zero
  have h2 : ‖(C'.u : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr C'.u.ne_zero
  field_simp

end UniformizationDatum

end WeierstrassCurve
