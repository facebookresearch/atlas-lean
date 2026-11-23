/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
public import MathlibExt.InformationTheory.MeasurePinsker

/-!
# The Hellinger distance between measures

For finite measures `μ` and `ν` on the same space (in practice probability measures), the
Hellinger distance is

`d_Hell(μ, ν) = (½ ∫ (√(dμ/dζ) - √(dν/dζ))² dζ)^{1/2}`,

where `ζ` is a measure dominating both. Here `ζ = μ + ν`, which makes the definition free of
choices. The normalising constant `½` is the one of Dashti and Stuart, *The Bayesian Approach to
Inverse Problems* (arXiv:1302.6989v4, 2015), Section 7.2.4, Definition 7.11; with it the distance
between probability measures lies in `[0, 1]` (their remark after (7.21)). The definition below
accepts any measures, but it is meaningful only for finite ones: for infinite measures the integral
can diverge, and Mathlib's convention that a non-integrable function has integral `0` then gives a
meaningless value (Lebesgue measure and twice Lebesgue measure on `ℝ` are at "distance" `0`).

## Main results

* `hellingerDist`: the definition, with reference measure `μ + ν`.
* `hellingerDist_withDensity`: if `μ = ρ.withDensity f` and `ν = ρ.withDensity g` for a
  σ-finite `ρ` and almost everywhere finite measurable densities, then
  `d_Hell(μ, ν)² = ½ ∫ (√f - √g)² dρ`. So any common dominating measure gives the same value,
  which is the form used by Dashti and Stuart (their Definition 7.11 with reference measure `ρ`,
  and (7.21) when `ρ = μ`).
* `hellingerDist_nonneg`, `hellingerDist_comm`, `hellingerDist_self`.
* `hellingerDist_le_sqrt_totalVariationDist`: for probability measures,
  `d_Hell(μ, ν) ≤ d_TV(μ, ν)^{1/2}` (Dashti and Stuart, Lemma 7.12, second inequality), with
  `d_TV = sup_B |μ(B) - ν(B)|` the supremum distance
  `MathlibExt.Probability.TotalVariationDistance.totalVariationDist`; hence
  `hellingerDist_le_one`; and `totalVariationDist_div_sqrt_two_le_hellingerDist`, the reverse
  comparison `d_TV(μ, ν)/√2 ≤ d_Hell(μ, ν)` (Lemma 7.12, first inequality).
* `norm_integral_sub_integral_le_hellingerDist`: the Hellinger distance controls differences of
  expectations, `‖E^μ f - E^ν f‖ ≤ 2 (E^μ ‖f‖² + E^ν ‖f‖²)^{1/2} d_Hell(μ, ν)` (Lemma 7.14).
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.HellingerDistance

open MeasureTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Hellinger distance.** For finite measures `μ` and `ν` (in practice probability measures),
`d_Hell(μ, ν)` is the square root of
`½ ∫ (√(dμ/dζ) - √(dν/dζ))² dζ` with `ζ = μ + ν` (Dashti and Stuart, *The Bayesian Approach to
Inverse Problems*, arXiv:1302.6989v4, Section 7.2.4, Definition 7.11, with reference measure
`μ + ν`). The definition accepts any measures, but for infinite ones the integral may diverge
and the value, which then follows Mathlib's convention for non-integrable functions, is not
meaningful. -/
noncomputable def hellingerDist (μ ν : Measure Ω) : ℝ :=
  √((1 / 2 : ℝ) * ∫ x, (√((μ.rnDeriv (μ + ν) x).toReal) - √((ν.rnDeriv (μ + ν) x).toReal)) ^ 2
    ∂(μ + ν))

/-- **The Hellinger distance is nonnegative.** -/
theorem hellingerDist_nonneg (μ ν : Measure Ω) : 0 ≤ hellingerDist μ ν :=
  Real.sqrt_nonneg _

/-- **The Hellinger distance is symmetric.** `d_Hell(μ, ν) = d_Hell(ν, μ)`. -/
theorem hellingerDist_comm (μ ν : Measure Ω) : hellingerDist μ ν = hellingerDist ν μ := by
  unfold hellingerDist
  rw [add_comm ν μ]
  congr 2
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only
  ring

/-- **The Hellinger distance from a measure to itself is zero.** -/
theorem hellingerDist_self (μ : Measure Ω) : hellingerDist μ μ = 0 := by
  simp [hellingerDist]

/-- Pointwise identity behind the change of reference measure: with `h ≥ 0`,
`h (√a - √b)² = (√(h a) - √(h b))²` (for any real `a`, `b`). -/
private lemma mul_sqrt_sub_sq {h : ℝ} (a b : ℝ) (hh : 0 ≤ h) :
    h * (√a - √b) ^ 2 = (√(h * a) - √(h * b)) ^ 2 := by
  rw [Real.sqrt_mul hh, Real.sqrt_mul hh]
  have : (√h) ^ 2 = h := Real.sq_sqrt hh
  nlinarith [this]

/-- **Hellinger distance through densities against any dominating measure.** If
`μ = ρ.withDensity f` and `ν = ρ.withDensity g`, with `ρ` σ-finite and `f`, `g` measurable and
finite `ρ`-almost everywhere, then `d_Hell(μ, ν) = (½ ∫ (√f - √g)² dρ)^{1/2}`. This is
Definition 7.11 of Dashti and Stuart (arXiv:1302.6989v4, Section 7.2.4) with reference measure
`ρ`, and shows that the value does not depend on the dominating measure. The identity holds for
every σ-finite `ρ`; it is meaningful when `μ` and `ν` are finite measures. -/
theorem hellingerDist_withDensity {ρ : Measure Ω} [SigmaFinite ρ] {f g : Ω → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hf_top : ∀ᵐ x ∂ρ, f x ≠ ∞)
    (hg_top : ∀ᵐ x ∂ρ, g x ≠ ∞) :
    hellingerDist (ρ.withDensity f) (ρ.withDensity g) =
      √((1 / 2 : ℝ) * ∫ x, (√((f x).toReal) - √((g x).toReal)) ^ 2 ∂ρ) := by
  have hfg_top : ∀ᵐ x ∂ρ, (f + g) x ≠ ∞ := by
    filter_upwards [hf_top, hg_top] with x h1 h2
    simp [Pi.add_apply, ENNReal.add_eq_top, h1, h2]
  have hsum : ρ.withDensity f + ρ.withDensity g = ρ.withDensity (f + g) :=
    (withDensity_add_left hf g).symm
  have : SigmaFinite (ρ.withDensity (f + g)) := SigmaFinite.withDensity_of_ne_top hfg_top
  have : SigmaFinite (ρ.withDensity f) := SigmaFinite.withDensity_of_ne_top hf_top
  have : SigmaFinite (ρ.withDensity g) := SigmaFinite.withDensity_of_ne_top hg_top
  set a := (ρ.withDensity f).rnDeriv (ρ.withDensity (f + g))
  set b := (ρ.withDensity g).rnDeriv (ρ.withDensity (f + g))
  -- densities of `μ` and `ν` with respect to `ρ`, recovered from those against `ζ`
  have hacf : ρ.withDensity f ≪ ρ.withDensity (f + g) := by
    rw [← hsum]; exact Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hacg : ρ.withDensity g ≪ ρ.withDensity (f + g) := by
    rw [← hsum]; exact Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  have hfa : (f + g) * a =ᵐ[ρ] f := by
    have h1 : ρ.withDensity ((f + g) * a) = ρ.withDensity f := by
      rw [withDensity_mul ρ (hf.add hg) (Measure.measurable_rnDeriv _ _)]
      exact Measure.withDensity_rnDeriv_eq _ _ hacf
    exact (withDensity_eq_iff_of_sigmaFinite
      ((hf.add hg).mul (Measure.measurable_rnDeriv _ _)).aemeasurable hf.aemeasurable).1 h1
  have hgb : (f + g) * b =ᵐ[ρ] g := by
    have h1 : ρ.withDensity ((f + g) * b) = ρ.withDensity g := by
      rw [withDensity_mul ρ (hf.add hg) (Measure.measurable_rnDeriv _ _)]
      exact Measure.withDensity_rnDeriv_eq _ _ hacg
    exact (withDensity_eq_iff_of_sigmaFinite
      ((hf.add hg).mul (Measure.measurable_rnDeriv _ _)).aemeasurable hg.aemeasurable).1 h1
  unfold hellingerDist
  rw [hsum]
  congr 2
  rw [integral_withDensity_eq_integral_toReal_smul (hf.add hg)
    (by filter_upwards [hfg_top] with x hx using lt_top_iff_ne_top.2 hx)]
  refine integral_congr_ae ?_
  filter_upwards [hfa, hgb] with x h1 h2
  simp only [smul_eq_mul]
  rw [mul_sqrt_sub_sq _ _ ENNReal.toReal_nonneg,
    ← ENNReal.toReal_mul, ← ENNReal.toReal_mul]
  have e1 : (f + g) x * a x = f x := h1
  have e2 : (f + g) x * b x = g x := h2
  rw [e1, e2]

open MathlibExt.Probability.TotalVariationDistance MathlibExt.InformationTheory.MeasurePinsker in
/-- **Hellinger is at most the square root of total variation.** For probability measures,
`d_Hell(μ, ν) ≤ d_TV(μ, ν)^{1/2}`, where `d_TV(μ, ν) = sup_B |μ(B) - ν(B)|` (Dashti and Stuart,
*The Bayesian Approach to Inverse Problems*, arXiv:1302.6989v4, Lemma 7.12, second inequality;
their `d_TV = ½ ∫ |dμ/dζ - dν/dζ| dζ` is at most this supremum, which is all the proof needs).
The proof bounds `(√a - √b)²` by `|a - b|` and splits `∫ |a - b|` along `{a ≤ b}`. -/
theorem hellingerDist_le_sqrt_totalVariationDist (μ ν : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : hellingerDist μ ν ≤ √(totalVariationDist μ ν) := by
  set ζ := μ + ν
  have hμ : μ ≪ ζ := Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hν : ν ≪ ζ := Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  set a : Ω → ℝ := fun x ↦ (μ.rnDeriv ζ x).toReal
  set b : Ω → ℝ := fun x ↦ (ν.rnDeriv ζ x).toReal
  have ha : Integrable a ζ := Measure.integrable_toReal_rnDeriv
  have hb : Integrable b ζ := Measure.integrable_toReal_rnDeriv
  have key : ∀ p q : ℝ, 0 ≤ p → 0 ≤ q → (p - q) ^ 2 ≤ |p ^ 2 - q ^ 2| := by
    intro p q hp hq
    rw [show p ^ 2 - q ^ 2 = (p - q) * (p + q) by ring, abs_mul,
      abs_of_nonneg (add_nonneg hp hq), ← sq_abs]
    have h : |p - q| ≤ p + q := by rw [abs_le]; constructor <;> linarith
    calc |p - q| ^ 2 = |p - q| * |p - q| := sq _
      _ ≤ |p - q| * (p + q) := mul_le_mul_of_nonneg_left h (abs_nonneg _)
  have hpt : ∀ x, (√(a x) - √(b x)) ^ 2 ≤ |a x - b x| := by
    intro x
    have := key (√(a x)) (√(b x)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    rwa [Real.sq_sqrt ENNReal.toReal_nonneg, Real.sq_sqrt ENNReal.toReal_nonneg] at this
  have hint : Integrable (fun x ↦ |a x - b x|) ζ := (ha.sub hb).abs
  -- `∫ |a - b| dζ ≤ 2 d_TV`
  set s : Set Ω := {x | a x ≤ b x}
  have hs : MeasurableSet s := measurableSet_le (by fun_prop) (by fun_prop)
  have hsplit : ∫ x, |a x - b x| ∂ζ =
      (ν.real s - μ.real s) + (μ.real sᶜ - ν.real sᶜ) := by
    rw [← integral_add_compl hs hint]
    congr 1
    · rw [setIntegral_congr_fun hs (g := fun x ↦ b x - a x)
        (fun x hx ↦ by simp only; rw [abs_of_nonpos (by simp [s] at hx; linarith)]; ring),
        integral_sub hb.integrableOn ha.integrableOn, Measure.setIntegral_toReal_rnDeriv hν,
        Measure.setIntegral_toReal_rnDeriv hμ]
    · rw [setIntegral_congr_fun hs.compl (g := fun x ↦ a x - b x)
        (fun x hx ↦ by simp only; rw [abs_of_nonneg (by simp [s] at hx; linarith)]),
        integral_sub ha.integrableOn hb.integrableOn, Measure.setIntegral_toReal_rnDeriv hμ,
        Measure.setIntegral_toReal_rnDeriv hν]
  have hTV : ∫ x, |a x - b x| ∂ζ ≤ 2 * totalVariationDist μ ν := by
    rw [hsplit]
    have h1 := abs_sub_le_totalVariationDist (μ := μ) (ν := ν) hs
    have h2 := abs_sub_le_totalVariationDist (μ := μ) (ν := ν) hs.compl
    rw [abs_le] at h1 h2
    linarith [h1.1, h2.2]
  unfold hellingerDist
  refine Real.sqrt_le_sqrt ?_
  calc (1 / 2 : ℝ) * ∫ x, (√(a x) - √(b x)) ^ 2 ∂ζ ≤ (1 / 2) * ∫ x, |a x - b x| ∂ζ := by
        exact mul_le_mul_of_nonneg_left (integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _) hint
          (Filter.Eventually.of_forall hpt)) (by norm_num)
    _ ≤ totalVariationDist μ ν := by linarith

open MathlibExt.Probability.TotalVariationDistance in
/-- **Total variation is at most `√2` times Hellinger.** For probability measures,
`d_TV(μ, ν) / √2 ≤ d_Hell(μ, ν)`, where `d_TV(μ, ν) = sup_B |μ(B) - ν(B)|` (Dashti and Stuart,
*The Bayesian Approach to Inverse Problems*, arXiv:1302.6989v4, Lemma 7.12, first inequality).
Instead of the Cauchy–Schwarz inequality of the source, the proof integrates the pointwise bound
`|√a - √b| (√a + √b) ≤ (t/2)(√a - √b)² + (1/(2t))(√a + √b)²` and optimises over `t > 0`. -/
theorem totalVariationDist_div_sqrt_two_le_hellingerDist (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    totalVariationDist μ ν / √2 ≤ hellingerDist μ ν := by
  set ζ := μ + ν
  have hμ : μ ≪ ζ := Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hν : ν ≪ ζ := Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  set a : Ω → ℝ := fun x ↦ (μ.rnDeriv ζ x).toReal
  set b : Ω → ℝ := fun x ↦ (ν.rnDeriv ζ x).toReal
  have ha : Integrable a ζ := Measure.integrable_toReal_rnDeriv
  have hb : Integrable b ζ := Measure.integrable_toReal_rnDeriv
  have ha0 : ∀ x, 0 ≤ a x := fun _ ↦ ENNReal.toReal_nonneg
  have hb0 : ∀ x, 0 ≤ b x := fun _ ↦ ENNReal.toReal_nonneg
  have hint : Integrable (fun x ↦ |a x - b x|) ζ := (ha.sub hb).abs
  set X := ∫ x, (√(a x) - √(b x)) ^ 2 ∂ζ
  have hH : hellingerDist μ ν = √((1 / 2 : ℝ) * X) := rfl
  have hX0 : 0 ≤ X := integral_nonneg fun _ ↦ sq_nonneg _
  -- squares of `√a ± √b` are dominated by `2 (a + b)`
  have hdom : ∀ x, (√(a x) - √(b x)) ^ 2 ≤ 2 * (a x + b x) ∧
      (√(a x) + √(b x)) ^ 2 ≤ 2 * (a x + b x) := by
    intro x
    have e1 := Real.sq_sqrt (ha0 x); have e2 := Real.sq_sqrt (hb0 x)
    constructor <;> nlinarith [sq_nonneg (√(a x) + √(b x)), sq_nonneg (√(a x) - √(b x))]
  have hab : Integrable (fun x ↦ 2 * (a x + b x)) ζ := (ha.add hb).const_mul 2
  have hm : Integrable (fun x ↦ (√(a x) - √(b x)) ^ 2) ζ :=
    hab.mono' (by fun_prop) (Filter.Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact (hdom x).1)
  have hp : Integrable (fun x ↦ (√(a x) + √(b x)) ^ 2) ζ :=
    hab.mono' (by fun_prop) (Filter.Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact (hdom x).2)
  have hsumab : ∫ x, 2 * (a x + b x) ∂ζ = 4 := by
    rw [integral_const_mul, integral_add ha hb, Measure.integral_toReal_rnDeriv hμ,
      Measure.integral_toReal_rnDeriv hν]
    simp; norm_num
  -- `d_TV ≤ ½ ∫ |a - b|`
  have hTV : totalVariationDist μ ν ≤ (1 / 2) * ∫ x, |a x - b x| ∂ζ := by
    refine ciSup_le fun B ↦ ?_
    have hB := B.2
    have e1 : (μ B.1).toReal - (ν B.1).toReal = ∫ x in B.1, (a x - b x) ∂ζ := by
      rw [integral_sub ha.integrableOn hb.integrableOn, Measure.setIntegral_toReal_rnDeriv hμ,
        Measure.setIntegral_toReal_rnDeriv hν]; rfl
    have e2 : (μ B.1).toReal - (ν B.1).toReal = -∫ x in B.1ᶜ, (a x - b x) ∂ζ := by
      rw [integral_sub ha.integrableOn hb.integrableOn, Measure.setIntegral_toReal_rnDeriv hμ,
        Measure.setIntegral_toReal_rnDeriv hν, probReal_compl_eq_one_sub hB,
        probReal_compl_eq_one_sub hB]; simp [measureReal_def]
    have i1 : |∫ x in B.1, (a x - b x) ∂ζ| ≤ ∫ x in B.1, |a x - b x| ∂ζ :=
      abs_integral_le_integral_abs
    have i2 : |∫ x in B.1ᶜ, (a x - b x) ∂ζ| ≤ ∫ x in B.1ᶜ, |a x - b x| ∂ζ :=
      abs_integral_le_integral_abs
    have hsplit := integral_add_compl hB hint
    have j1 : |(μ B.1).toReal - (ν B.1).toReal| ≤ ∫ x in B.1, |a x - b x| ∂ζ := by rw [e1]; exact i1
    have j2 : |(μ B.1).toReal - (ν B.1).toReal| ≤ ∫ x in B.1ᶜ, |a x - b x| ∂ζ := by
      rw [e2, abs_neg]; exact i2
    linarith
  -- `∫ |a - b| ≤ t X / 2 + 2 / t` for every `t > 0`
  have hAMGM : ∀ t > 0, ∫ x, |a x - b x| ∂ζ ≤ t / 2 * X + 1 / (2 * t) * 4 := by
    intro t ht
    have hpt : ∀ x, |a x - b x| ≤ t / 2 * (√(a x) - √(b x)) ^ 2 +
        1 / (2 * t) * (√(a x) + √(b x)) ^ 2 := by
      intro x
      have e1 := Real.sq_sqrt (ha0 x); have e2 := Real.sq_sqrt (hb0 x)
      have hfac : a x - b x = (√(a x) - √(b x)) * (√(a x) + √(b x)) := by nlinarith
      rw [hfac, abs_mul, abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
      set u := |√(a x) - √(b x)|
      set v := √(a x) + √(b x)
      have hu : (√(a x) - √(b x)) ^ 2 = u ^ 2 := (sq_abs _).symm
      rw [hu]
      have h2t : 0 < 2 * t := by positivity
      rw [show t / 2 * u ^ 2 + 1 / (2 * t) * v ^ 2 = ((t * u) ^ 2 + v ^ 2) / (2 * t) by
        field_simp, le_div_iff₀ h2t]
      nlinarith [sq_nonneg (t * u - v)]
    calc ∫ x, |a x - b x| ∂ζ
        ≤ ∫ x, (t / 2 * (√(a x) - √(b x)) ^ 2 + 1 / (2 * t) * (√(a x) + √(b x)) ^ 2) ∂ζ :=
          integral_mono hint ((hm.const_mul _).add (hp.const_mul _)) hpt
      _ = t / 2 * X + 1 / (2 * t) * ∫ x, (√(a x) + √(b x)) ^ 2 ∂ζ := by
          rw [integral_add (hm.const_mul _) (hp.const_mul _), integral_const_mul,
            integral_const_mul]
      _ ≤ t / 2 * X + 1 / (2 * t) * 4 := by
          gcongr
          rw [← hsumab]
          exact integral_mono hp hab fun x ↦ (hdom x).2
  -- optimise over `t`
  rw [hH, div_le_iff₀ (by positivity)]
  rcases hX0.eq_or_lt with hX | hX
  · -- `X = 0`: `d_TV ≤ 1 / t` for all `t > 0`
    rw [← hX]; simp only [mul_zero, Real.sqrt_zero, zero_mul]
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    have := hAMGM (1 / ε) (by positivity)
    rw [← hX] at this
    have h4 : 1 / (2 * (1 / ε)) * 4 = 2 * ε := by field_simp; ring
    linarith
  · have hs : 0 < √X := Real.sqrt_pos.2 hX
    have := hAMGM (2 / √X) (by positivity)
    have hsq : √X ^ 2 = X := Real.sq_sqrt hX0
    have h1 : 2 / √X / 2 * X + 1 / (2 * (2 / √X)) * 4 = 2 * √X := by
      field_simp; nlinarith [hsq]
    have h2 : √((1 / 2 : ℝ) * X) * √2 = √X := by
      rw [← Real.sqrt_mul (by positivity)]; congr 1; ring
    rw [h2]
    linarith

/-- **The Hellinger distance controls expectations.** For probability measures `μ`, `ν` and
`f` with values in a real Banach space and finite second moments under both,
`‖E^μ f - E^ν f‖ ≤ 2 (E^μ ‖f‖² + E^ν ‖f‖²)^{1/2} d_Hell(μ, ν)` (Dashti and Stuart,
*The Bayesian Approach to Inverse Problems*, arXiv:1302.6989v4, Lemma 7.14, first statement;
there the underlying space is a separable Banach space, which the proof does not use). Instead of
the Cauchy–Schwarz inequality of the source, the proof integrates
`|√a - √b| (√a + √b) ‖f‖ ≤ (t/2)(√a - √b)² + (1/(2t))(√a + √b)² ‖f‖²` and optimises over
`t > 0`. -/
theorem norm_integral_sub_integral_le_hellingerDist {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (μ ν : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (f : Ω → E) (hμf : MemLp f 2 μ) (hνf : MemLp f 2 ν) :
    ‖∫ x, f x ∂μ - ∫ x, f x ∂ν‖ ≤
      2 * √(∫ x, ‖f x‖ ^ 2 ∂μ + ∫ x, ‖f x‖ ^ 2 ∂ν) * hellingerDist μ ν := by
  set ζ := μ + ν
  have hμ : μ ≪ ζ := Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hν : ν ≪ ζ := Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  set a : Ω → ℝ := fun x ↦ (μ.rnDeriv ζ x).toReal
  set b : Ω → ℝ := fun x ↦ (ν.rnDeriv ζ x).toReal
  have ha : Integrable a ζ := Measure.integrable_toReal_rnDeriv
  have hb : Integrable b ζ := Measure.integrable_toReal_rnDeriv
  have ha0 : ∀ x, 0 ≤ a x := fun _ ↦ ENNReal.toReal_nonneg
  have hb0 : ∀ x, 0 ≤ b x := fun _ ↦ ENNReal.toReal_nonneg
  set X := ∫ x, (√(a x) - √(b x)) ^ 2 ∂ζ
  have hH : hellingerDist μ ν = √((1 / 2 : ℝ) * X) := rfl
  have hX0 : 0 ≤ X := integral_nonneg fun _ ↦ sq_nonneg _
  have hdom : ∀ x, (√(a x) - √(b x)) ^ 2 ≤ 2 * (a x + b x) ∧
      (√(a x) + √(b x)) ^ 2 ≤ 2 * (a x + b x) := by
    intro x
    have e1 := Real.sq_sqrt (ha0 x); have e2 := Real.sq_sqrt (hb0 x)
    constructor <;> nlinarith [sq_nonneg (√(a x) + √(b x)), sq_nonneg (√(a x) - √(b x))]
  have hab : Integrable (fun x ↦ 2 * (a x + b x)) ζ := (ha.add hb).const_mul 2
  have hm : Integrable (fun x ↦ (√(a x) - √(b x)) ^ 2) ζ :=
    hab.mono' (by fun_prop) (Filter.Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact (hdom x).1)
  -- second moments
  set S := ∫ x, ‖f x‖ ^ 2 ∂μ + ∫ x, ‖f x‖ ^ 2 ∂ν
  have hfμ : Integrable (fun x ↦ ‖f x‖ ^ 2) μ := hμf.integrable_norm_pow two_ne_zero
  have hfν : Integrable (fun x ↦ ‖f x‖ ^ 2) ν := hνf.integrable_norm_pow two_ne_zero
  have hS0 : 0 ≤ S := add_nonneg (integral_nonneg fun _ ↦ by positivity)
    (integral_nonneg fun _ ↦ by positivity)
  have haf : Integrable (fun x ↦ a x * ‖f x‖ ^ 2) ζ :=
    (integrable_toReal_rnDeriv_mul_iff hμ).2 hfμ
  have hbf : Integrable (fun x ↦ b x * ‖f x‖ ^ 2) ζ :=
    (integrable_toReal_rnDeriv_mul_iff hν).2 hfν
  have hSζ : ∫ x, (a x * ‖f x‖ ^ 2 + b x * ‖f x‖ ^ 2) ∂ζ = S := by
    rw [integral_add haf hbf, integral_toReal_rnDeriv_mul hμ,
      integral_toReal_rnDeriv_mul hν]
  -- the difference of expectations as an integral against `ζ`
  have haf1 : Integrable (fun x ↦ a x • f x) ζ :=
    (integrable_rnDeriv_smul_iff hμ).2 (hμf.integrable one_le_two)
  have hbf1 : Integrable (fun x ↦ b x • f x) ζ :=
    (integrable_rnDeriv_smul_iff hν).2 (hνf.integrable one_le_two)
  have hnorm : ‖∫ x, f x ∂μ - ∫ x, f x ∂ν‖ ≤ ∫ x, |a x - b x| * ‖f x‖ ∂ζ := by
    rw [← integral_rnDeriv_smul hμ, ← integral_rnDeriv_smul hν,
      ← integral_sub haf1 hbf1]
    refine (norm_integral_le_integral_norm _).trans_eq (integral_congr_ae ?_)
    filter_upwards with x
    rw [← sub_smul, norm_smul, Real.norm_eq_abs]
  have hG2 : Integrable (fun x ↦ a x * ‖f x‖ ^ 2 + b x * ‖f x‖ ^ 2) ζ := haf.add hbf
  -- `∫ |a - b| ‖f‖ ≤ (t/2) X + S/t` for every `t > 0`
  have hAMGM : ∀ t > 0, ∫ x, |a x - b x| * ‖f x‖ ∂ζ ≤ t / 2 * X + 1 / t * S := by
    intro t ht
    have hpt : ∀ x, |a x - b x| * ‖f x‖ ≤ t / 2 * (√(a x) - √(b x)) ^ 2 +
        1 / t * (a x * ‖f x‖ ^ 2 + b x * ‖f x‖ ^ 2) := by
      intro x
      have e1 := Real.sq_sqrt (ha0 x); have e2 := Real.sq_sqrt (hb0 x)
      have hfac : a x - b x = (√(a x) - √(b x)) * (√(a x) + √(b x)) := by nlinarith
      rw [hfac, abs_mul, abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
      set u := |√(a x) - √(b x)|
      set v := (√(a x) + √(b x)) * ‖f x‖
      have hu : (√(a x) - √(b x)) ^ 2 = u ^ 2 := (sq_abs _).symm
      have hv : v ^ 2 ≤ 2 * (a x * ‖f x‖ ^ 2 + b x * ‖f x‖ ^ 2) := by
        have := mul_le_mul_of_nonneg_right (hdom x).2 (sq_nonneg ‖f x‖)
        calc v ^ 2 = (√(a x) + √(b x)) ^ 2 * ‖f x‖ ^ 2 := by ring
          _ ≤ 2 * (a x + b x) * ‖f x‖ ^ 2 := this
          _ = _ := by ring
      rw [hu, show u * (√(a x) + √(b x)) * ‖f x‖ = u * v by ring]
      have h2t : 0 < 2 * t := by positivity
      calc u * v ≤ ((t * u) ^ 2 + v ^ 2) / (2 * t) := by
            rw [le_div_iff₀ h2t]; nlinarith [sq_nonneg (t * u - v)]
        _ ≤ ((t * u) ^ 2 + 2 * (a x * ‖f x‖ ^ 2 + b x * ‖f x‖ ^ 2)) / (2 * t) := by gcongr
        _ = t / 2 * u ^ 2 + 1 / t * (a x * ‖f x‖ ^ 2 + b x * ‖f x‖ ^ 2) := by
            field_simp
    calc ∫ x, |a x - b x| * ‖f x‖ ∂ζ
        ≤ ∫ x, (t / 2 * (√(a x) - √(b x)) ^ 2 +
            1 / t * (a x * ‖f x‖ ^ 2 + b x * ‖f x‖ ^ 2)) ∂ζ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ ↦ by positivity)
            ((hm.const_mul _).add (hG2.const_mul _)) (Filter.Eventually.of_forall hpt)
      _ = t / 2 * X + 1 / t * S := by
          rw [integral_add (hm.const_mul _) (hG2.const_mul _), integral_const_mul,
            integral_const_mul, hSζ]
  -- optimise over `t`
  set N := ‖∫ x, f x ∂μ - ∫ x, f x ∂ν‖
  have hbound : ∀ t > 0, N ≤ t / 2 * X + 1 / t * S := fun t ht ↦ hnorm.trans (hAMGM t ht)
  rw [hH]
  rcases hX0.eq_or_lt with hX | hX
  · rw [← hX]; simp only [mul_zero, Real.sqrt_zero, mul_zero]
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    have := hbound ((S + 1) / ε) (by positivity)
    rw [← hX] at this
    have : 1 / ((S + 1) / ε) * S ≤ ε := by
      rw [one_div_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
    linarith
  rcases hS0.eq_or_lt with hS | hS
  · rw [← hS]; simp only [Real.sqrt_zero, mul_zero, zero_mul]
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    have := hbound (ε / (X + 1)) (by positivity)
    rw [← hS] at this
    have : ε / (X + 1) / 2 * X ≤ ε := by
      rw [div_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
    linarith
  set h := √((1 / 2 : ℝ) * X)
  set σ := √S
  have hh : 0 < h := Real.sqrt_pos.2 (by positivity)
  have hσ : 0 < σ := Real.sqrt_pos.2 hS
  have eh : h ^ 2 = (1 / 2) * X := Real.sq_sqrt (by positivity)
  have eσ : σ ^ 2 = S := Real.sq_sqrt hS0
  have := hbound (σ / h) (by positivity)
  have hval : σ / h / 2 * X + 1 / (σ / h) * S = 2 * σ * h := by
    rw [← eσ, show X = 2 * h ^ 2 by linarith]; field_simp; ring
  linarith

open MathlibExt.Probability.TotalVariationDistance in
/-- **The Hellinger distance between probability measures is at most one** (Dashti and Stuart,
arXiv:1302.6989v4, the remark after (7.21)). -/
theorem hellingerDist_le_one (μ ν : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : hellingerDist μ ν ≤ 1 :=
  (hellingerDist_le_sqrt_totalVariationDist μ ν).trans
    (Real.sqrt_le_one.2 (totalVariationDist_le_one))

end MathlibExt.Probability.HellingerDistance
