/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Rényi divergence between measures

For probability measures `μ` and `ν` and an order `α > 1`, the Rényi moment `renyiMoment μ ν α`
is `∫⁻ x, (∂μ/∂ν) x ^ α ∂ν` when `μ ≪ ν`, and the Rényi divergence `renyiDiv μ ν α` is
`(α - 1)⁻¹ * log (renyiMoment μ ν α)` in `EReal`, with the natural logarithm (Mironov, *Rényi
Differential Privacy*, IEEE CSF 2017, arXiv:1702.07476v3, Definition 3, where the moment is
`E_{x ∼ Q} (P(x) / Q(x)) ^ α`). Both are `⊤` when `μ` is not absolutely continuous with respect
to `ν`. At every order `α ≤ 1` both are `⊤` too, a convention of this file rather than of the
source: Mironov sets orders `α < 1` aside (Remark 2) and defines order `1` after Definition 3 by
continuity as the KL divergence, so for a probability measure his `D₁(μ ‖ μ)` is `0`.

Lean accepts arbitrary measures and uses Mathlib's total `μ.rnDeriv ν`. This function is zero
if the pair has no Lebesgue decomposition; in that case it need not recover `μ` as a density
against `ν`, even when `μ ≪ ν`.

## Main results

* `renyiMoment_withDensity`: for densities `f`, `g` against a σ-finite base `ρ`, with `g`
  positive and finite and `f` finite almost everywhere, the moment is
  `∫⁻ x, f x ^ α * g x ^ (1 - α) ∂ρ` above order `1`.
* `renyiDiv_self`, `renyiDiv_nonneg`: the divergence of a probability measure from itself is
  `0` above order `1`, and between probability measures it is nonnegative (Mironov,
  Proposition 8).
* `renyiMoment_gaussianReal`, `renyiDiv_gaussianReal`: for real Gaussians with a common nonzero
  variance `v` (a variance, not a standard deviation) and `1 < α`, the moment is
  `exp (α (α - 1) (m - n)² / (2 v))` and the divergence is `α (m - n)² / (2 v)` (Mironov,
  Proposition 7, with `v = σ²`).
* `renyiDiv_gaussianReal_le`: when `|m - n| ≤ Δ` and `1 < α`, the divergence is at most
  `α Δ² / (2 v)`, the privacy curve of the Gaussian mechanism (Mironov, Corollary 3, there for
  `Δ = 1`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MathlibExt.InformationTheory.RenyiDivergence

open scoped Classical in
/-- **Rényi moment** of order `α` of `μ` with respect to `ν`: `∫⁻ x, (μ.rnDeriv ν x) ^ α ∂ν`
when `μ ≪ ν` and `1 < α`, and `∞` otherwise. For absolutely continuous probability laws this
is the moment in Mironov, arXiv:1702.07476v3, Definition 3. For arbitrary measures the formula
uses Mathlib's total `rnDeriv`, which is zero without a Lebesgue decomposition. The value `∞`
at `α ≤ 1` is a convention of this file, not part of the cited definition. -/
noncomputable def renyiMoment {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω) (α : ℝ) :
    ℝ≥0∞ :=
  if μ ≪ ν ∧ 1 < α then ∫⁻ x, μ.rnDeriv ν x ^ α ∂ν else ∞

/-- **Rényi divergence** of order `α` of `μ` from `ν`: `(α - 1)⁻¹ * log (renyiMoment μ ν α)`
for `1 < α` (Mironov, arXiv:1702.07476v3, Definition 3), with `ENNReal.log`, so an infinite
moment gives `⊤`. At `α ≤ 1` it is `⊤`, a convention of this file: Mironov defines order `1`
by continuity as the KL divergence, which is `0` between equal probability measures, and sets
orders below `1` aside. Meant for probability measures. -/
noncomputable def renyiDiv {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω) (α : ℝ) : EReal :=
  if 1 < α then (((α - 1)⁻¹ : ℝ) : EReal) * ENNReal.log (renyiMoment μ ν α) else ⊤

/-- Under `μ ≪ ν` and `1 < α`, the moment integrates the `α`-th power of Mathlib's
`μ.rnDeriv ν`. With a Lebesgue decomposition of `μ` with respect to `ν`, this function is a
density of `μ` against `ν`. -/
theorem renyiMoment_of_ac {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω} {α : ℝ}
    (hμν : μ ≪ ν) (hα : 1 < α) :
    renyiMoment μ ν α = ∫⁻ x, μ.rnDeriv ν x ^ α ∂ν := by
  unfold renyiMoment
  exact ite_eq_left ⟨hμν, hα⟩

/-- **Moment without absolute continuity.** Without absolute continuity the moment is `∞`, at
every order; at `α ≤ 1` this is the convention of `renyiMoment`. -/
theorem renyiMoment_of_not_ac {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω} {α : ℝ}
    (hμν : ¬ μ ≪ ν) : renyiMoment μ ν α = ∞ := by
  unfold renyiMoment
  exact ite_eq_right fun h => hμν h.1

/-- **Moment at orders up to one.** At orders `α ≤ 1` the moment is `∞`, a convention of this
file; the cited definition covers only `α > 1`. -/
theorem renyiMoment_of_le_one {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω} {α : ℝ}
    (hα : α ≤ 1) : renyiMoment μ ν α = ∞ := by
  unfold renyiMoment
  exact ite_eq_right fun h => not_lt_of_ge hα h.2

/-- Above order `1` the divergence is `(α - 1)⁻¹ * log (renyiMoment μ ν α)`. -/
theorem renyiDiv_of_one_lt {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω} {α : ℝ}
    (hα : 1 < α) :
    renyiDiv μ ν α = (((α - 1)⁻¹ : ℝ) : EReal) * ENNReal.log (renyiMoment μ ν α) := by
  unfold renyiDiv
  exact ite_eq_left hα

/-- **Divergence at orders up to one.** At orders `α ≤ 1` the divergence is `⊤`, a convention
of this file; Mironov's order-`1` divergence is instead the KL divergence. -/
theorem renyiDiv_of_le_one {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω} {α : ℝ}
    (hα : α ≤ 1) : renyiDiv μ ν α = ⊤ := by
  unfold renyiDiv
  exact ite_eq_right (not_lt_of_ge hα)

/-- **Divergence without absolute continuity.** Without absolute continuity the divergence is
`⊤`, at every order; at `α ≤ 1` this is the convention of `renyiDiv`. -/
theorem renyiDiv_of_not_ac {Ω : Type*} [MeasurableSpace Ω] {μ ν : Measure Ω} {α : ℝ}
    (hμν : ¬ μ ≪ ν) : renyiDiv μ ν α = ⊤ := by
  by_cases hα : 1 < α
  · rw [renyiDiv_of_one_lt hα, renyiMoment_of_not_ac hμν, ENNReal.log_top]
    exact EReal.coe_mul_top_of_pos (inv_pos.mpr (sub_pos.mpr hα))
  · exact renyiDiv_of_le_one (le_of_not_gt hα)

/-- **Real divergence from a finite moment.** Above order `1`, a finite positive moment
`ENNReal.ofReal r` gives the real divergence `log r / (α - 1)`. -/
theorem renyiDiv_eq_of_renyiMoment_eq_ofReal {Ω : Type*} [MeasurableSpace Ω]
    {μ ν : Measure Ω} {α r : ℝ} (hα : 1 < α) (hr : 0 < r)
    (h : renyiMoment μ ν α = ENNReal.ofReal r) :
    renyiDiv μ ν α = ((Real.log r / (α - 1) : ℝ) : EReal) := by
  rw [renyiDiv_of_one_lt hα, h, ENNReal.log_ofReal_of_pos hr, ← EReal.coe_mul, inv_mul_eq_div]

/-- **Moment of a measure with respect to itself.** The moment of a σ-finite measure with
respect to itself is its total mass, above order `1`. -/
theorem renyiMoment_self {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]
    {α : ℝ} (hα : 1 < α) : renyiMoment μ μ α = μ Set.univ := by
  rw [renyiMoment_of_ac Measure.AbsolutelyContinuous.rfl hα,
    lintegral_congr_ae (g := fun _ => (1 : ℝ≥0∞))
      (by filter_upwards [Measure.rnDeriv_self μ] with x hx; rw [hx, ENNReal.one_rpow])]
  simp

/-- The divergence of a probability measure from itself is `0`, above order `1`. -/
theorem renyiDiv_self {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {α : ℝ} (hα : 1 < α) : renyiDiv μ μ α = 0 := by
  rw [renyiDiv_of_one_lt hα, renyiMoment_self μ hα, measure_univ, ENNReal.log_one, mul_zero]

/-- **The moment is at least one.** Above order `1`, the moment between probability measures is
at least `1`: when `μ ≪ ν` by Hölder's inequality with exponents `α` and `α / (α - 1)` applied
to `∂μ/∂ν` and `1`, and otherwise because the moment is then `∞`, the fallback of
`renyiMoment`. -/
theorem one_le_renyiMoment {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {α : ℝ} (hα : 1 < α) :
    1 ≤ renyiMoment μ ν α := by
  by_cases hμν : μ ≪ ν
  swap
  · rw [renyiMoment_of_not_ac hμν]
    exact le_top
  rw [renyiMoment_of_ac hμν hα]
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν (Real.HolderConjugate.conjExponent hα)
    (Measure.measurable_rnDeriv μ ν).aemeasurable (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ] at h
  rw [Measure.lintegral_rnDeriv hμν, measure_univ] at h
  have hα0 : 0 < α := by linarith
  have h' : (1 : ℝ≥0∞) ≤ (∫⁻ x, μ.rnDeriv ν x ^ α ∂ν) ^ (1 / α) := by simpa using h
  calc (1 : ℝ≥0∞) = 1 ^ α := (ENNReal.one_rpow α).symm
    _ ≤ ((∫⁻ x, μ.rnDeriv ν x ^ α ∂ν) ^ (1 / α)) ^ α := ENNReal.rpow_le_rpow h' hα0.le
    _ = ∫⁻ x, μ.rnDeriv ν x ^ α ∂ν := by
      rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hα0.ne', ENNReal.rpow_one]

/-- **Nonnegativity.** The divergence between probability measures is nonnegative, at every
order: for `1 < α` this is Mironov, arXiv:1702.07476v3, Proposition 8, and at `α ≤ 1` the
value is `⊤` by the convention of `renyiDiv`. -/
theorem renyiDiv_nonneg {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (α : ℝ) : 0 ≤ renyiDiv μ ν α := by
  by_cases hα : 1 < α
  · rw [renyiDiv_of_one_lt hα]
    have h1 : 0 ≤ ENNReal.log (renyiMoment μ ν α) := by
      rw [← ENNReal.log_one]
      exact ENNReal.log_monotone (one_le_renyiMoment μ ν hα)
    exact EReal.mul_nonneg (EReal.coe_nonneg.mpr (inv_nonneg.mpr (sub_nonneg.mpr hα.le))) h1
  · rw [renyiDiv_of_le_one (le_of_not_gt hα)]
    exact le_top

/-- **Density form of the moment.** For a σ-finite base `ρ`, measurable densities `f`, `g`
with `f` finite and `g` positive and finite `ρ`-almost everywhere, and `1 < α`, the moment of
`ρ.withDensity f` with respect to `ρ.withDensity g` is `∫⁻ x, f x ^ α * g x ^ (1 - α) ∂ρ`. -/
theorem renyiMoment_withDensity {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure Ω) [SigmaFinite ρ]
    {f g : Ω → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) (hf_top : ∀ᵐ x ∂ρ, f x ≠ ∞)
    (hg_zero : ∀ᵐ x ∂ρ, g x ≠ 0) (hg_top : ∀ᵐ x ∂ρ, g x ≠ ∞) {α : ℝ} (hα : 1 < α) :
    renyiMoment (ρ.withDensity f) (ρ.withDensity g) α = ∫⁻ x, f x ^ α * g x ^ (1 - α) ∂ρ := by
  have : SigmaFinite (ρ.withDensity f) := SigmaFinite.withDensity_of_ne_top hf_top
  have hac : ρ.withDensity f ≪ ρ.withDensity g :=
    (withDensity_absolutelyContinuous ρ f).trans
      (withDensity_absolutelyContinuous' hg.aemeasurable hg_zero)
  rw [renyiMoment_of_ac hac hα, lintegral_withDensity_eq_lintegral_mul₀ hg.aemeasurable
    ((Measure.measurable_rnDeriv _ _).pow_const α).aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [Measure.rnDeriv_withDensity_right (ρ.withDensity f) ρ hg.aemeasurable hg_zero
    hg_top, Measure.rnDeriv_withDensity ρ hf, hg_zero, hg_top] with x hx1 hx2 hx0 hxt
  simp only [Pi.mul_apply]
  rw [hx1, hx2, ENNReal.mul_rpow_of_nonneg _ _ (by linarith : (0 : ℝ) ≤ α), ENNReal.inv_rpow,
    ENNReal.rpow_sub _ _ hx0 hxt, ENNReal.rpow_one, div_eq_mul_inv]
  ring

/-- Completing the square: for a common nonzero variance `v`,
`p_m(x) ^ α * p_n(x) ^ (1 - α) = exp (α (α - 1) (m - n)² / (2 v)) * p_{α m + (1 - α) n}(x)`,
where `p_m` is the Gaussian density with mean `m` and variance `v`. -/
theorem gaussianPDFReal_rpow_mul_rpow (m n : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (α x : ℝ) :
    gaussianPDFReal m v x ^ α * gaussianPDFReal n v x ^ (1 - α) =
      Real.exp (α * (α - 1) * (m - n) ^ 2 / (2 * v)) *
        gaussianPDFReal (α * m + (1 - α) * n) v x := by
  have hv' : (0 : ℝ) < v := by exact_mod_cast pos_iff_ne_zero.mpr hv
  have hc : 0 < (√(2 * Real.pi * v))⁻¹ :=
    inv_pos.mpr (Real.sqrt_pos.mpr (mul_pos (mul_pos two_pos Real.pi_pos) hv'))
  rw [Real.rpow_def_of_pos (gaussianPDFReal_pos _ _ _ hv),
    Real.rpow_def_of_pos (gaussianPDFReal_pos _ _ _ hv), ← Real.exp_add]
  simp only [gaussianPDFReal]
  rw [Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_mul hc.ne' (Real.exp_pos _).ne',
    Real.log_exp, Real.log_exp]
  conv_rhs => rw [← Real.exp_log hc, ← Real.exp_add, ← Real.exp_add]
  congr 1
  field_simp
  ring

/-- **Rényi moment of shifted Gaussians.** For a common nonzero variance `v` and `1 < α`,
the moment of `N(m, v)` with respect to `N(n, v)` is `exp (α (α - 1) (m - n)² / (2 v))`. -/
theorem renyiMoment_gaussianReal (m n : ℝ) {v : ℝ≥0} (hv : v ≠ 0) {α : ℝ} (hα : 1 < α) :
    renyiMoment (gaussianReal m v) (gaussianReal n v) α =
      ENNReal.ofReal (Real.exp (α * (α - 1) * (m - n) ^ 2 / (2 * v))) := by
  rw [gaussianReal_of_var_ne_zero m hv, gaussianReal_of_var_ne_zero n hv,
    renyiMoment_withDensity volume (measurable_gaussianPDF m v) (measurable_gaussianPDF n v)
      (ae_of_all _ fun _ => gaussianPDF_ne_top)
      (ae_of_all _ fun x => (gaussianPDF_pos n hv x).ne')
      (ae_of_all _ fun _ => gaussianPDF_ne_top) hα]
  have hpt : ∀ x, gaussianPDF m v x ^ α * gaussianPDF n v x ^ (1 - α) =
      ENNReal.ofReal (Real.exp (α * (α - 1) * (m - n) ^ 2 / (2 * v))) *
        gaussianPDF (α * m + (1 - α) * n) v x := by
    intro x
    simp only [gaussianPDF]
    rw [ENNReal.ofReal_rpow_of_pos (gaussianPDFReal_pos _ _ _ hv),
      ENNReal.ofReal_rpow_of_pos (gaussianPDFReal_pos _ _ _ hv),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (gaussianPDFReal_nonneg _ _ _) _),
      gaussianPDFReal_rpow_mul_rpow m n hv α x, ENNReal.ofReal_mul (Real.exp_pos _).le]
  simp_rw [hpt]
  rw [lintegral_const_mul _ (measurable_gaussianPDF _ _), lintegral_gaussianPDF_eq_one _ hv,
    mul_one]

/-- **Rényi divergence of shifted Gaussians** (Mironov, arXiv:1702.07476v3, Proposition 7,
`D_α(N(0, σ²) ‖ N(μ, σ²)) = α μ² / (2 σ²)`, here with variance `v = σ²` and general means):
for a common nonzero variance `v` and `1 < α`, the divergence of `N(m, v)` from `N(n, v)` is
`α (m - n)² / (2 v)`. -/
theorem renyiDiv_gaussianReal (m n : ℝ) {v : ℝ≥0} (hv : v ≠ 0) {α : ℝ} (hα : 1 < α) :
    renyiDiv (gaussianReal m v) (gaussianReal n v) α =
      ((α * (m - n) ^ 2 / (2 * v) : ℝ) : EReal) := by
  rw [renyiDiv_eq_of_renyiMoment_eq_ofReal hα (Real.exp_pos _)
    (renyiMoment_gaussianReal m n hv hα), Real.log_exp]
  have h1 : α - 1 ≠ 0 := (sub_pos.mpr hα).ne'
  congr 1
  field_simp

/-- **Gaussian Rényi bound** (Mironov, arXiv:1702.07476v3, Corollary 3, there for
sensitivity `1`): if `|m - n| ≤ Δ`, the divergence of `N(m, v)` from `N(n, v)` is at most
`α Δ² / (2 v)`, for a nonzero variance `v` and `1 < α`. -/
theorem renyiDiv_gaussianReal_le (m n : ℝ) {v : ℝ≥0} (hv : v ≠ 0) {α Δ : ℝ} (hα : 1 < α)
    (hΔ : |m - n| ≤ Δ) :
    renyiDiv (gaussianReal m v) (gaussianReal n v) α ≤ ((α * Δ ^ 2 / (2 * v) : ℝ) : EReal) := by
  rw [renyiDiv_gaussianReal m n hv hα, EReal.coe_le_coe_iff]
  have hv' : (0 : ℝ) < v := by exact_mod_cast pos_iff_ne_zero.mpr hv
  have hsq : (m - n) ^ 2 ≤ Δ ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hΔ 2
  have hα0 : 0 ≤ α := by linarith
  gcongr

end MathlibExt.InformationTheory.RenyiDivergence
