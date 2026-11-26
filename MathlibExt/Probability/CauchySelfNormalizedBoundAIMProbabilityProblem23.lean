/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Cauchy
public import Mathlib.Probability.Independence.Basic

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.CondVar
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.Filtration
import MathlibExt.Probability.Statistics.Sequential.Ville

/-!
# A time-uniform self-normalized bound for Cauchy sums (AimPL Stein's method, Problem 1.15)

This module proves `cauchySelfNormalizedBound_holds`: for i.i.d. standard Cauchy `X₁, X₂, …`
with `S_t = ∑_{i ≤ t} X_i` and `V_t = ∑_{i ≤ t} X_i²`, and all `m, x ≥ 0`,
`P(∃ t, S_t / (V_t + m) > x) ≤ exp(-2 m x²)`. The bound follows from de la Peña's
exponential inequality for symmetric increments via a nonnegative supermartingale and Ville's
maximal inequality.

## References

* AimPL: Stein's method and applications in high-dimensional statistics, Problem 1.15,
  http://aimpl.org/steinhd/1/.
* S. R. Howard, A. Ramdas, J. McAuliffe and J. Sekhon, Time-uniform Chernoff bounds via
  nonnegative supermartingales, Probab. Surv. 17 (2020), 257-317, arXiv:1808.03204,
  https://doi.org/10.1214/18-PS321.
* V. H. de la Peña, A general class of exponential inequalities for martingales and ratios,
  Ann. Probab. 27 (1999), no. 1, 537-564, https://doi.org/10.1214/aop/1022677271.
-/

@[expose] public section

namespace MathlibExt.Probability.CauchySelfNormalizedBoundAIMProbabilityProblem23Wanted

/-!
Source: AimPL: Stein's method and applications in high-dimensional statistics, Problem 1.15,
http://aimpl.org/steinhd/1/ (remark: the inequality is Example 4 of arXiv:1808.03204 and holds for
any symmetric increments). UnsolvedMath record UM-20002581 (`AIM-PROBABILITY-0023`), dataset
ulamai/UnsolvedMath v1.8.0.

The variables are i.i.d. standard Cauchy (location `0`, scale `1`; Mathlib's `cauchyMeasure 0 1`),
as in Howard et al.'s example; scaling the variables by `γ > 0` turns the event for `(m, x)` into
the event for `(m / γ², γ x)`, which has the same bound `e^{-2 m x²}`, so scale `1` loses nothing.
`S_t` and `V_t` sum the first `t` variables (`t = 0` gives `0`, which never exceeds `x ≥ 0`). When
`m = 0` or `x = 0` the bound is `1`. The request to use Stein's method is a proof-method requirement
and is not formalized; the AimPL remark records that the inequality itself is known.
-/

open MeasureTheory ProbabilityTheory

/-- AimPL Stein's method and applications in high-dimensional statistics, Problem 1.15, as a
claim: for i.i.d. standard Cauchy `X₁, X₂, …` with `S_t = ∑_{i ≤ t} X_i` and
`V_t = ∑_{i ≤ t} X_i²`, and all `m, x ≥ 0`, `P(∃ t, S_t / (V_t + m) > x) ≤ exp(-2 m x²)`. -/
def cauchySelfNormalizedBound : Prop :=
  ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)] (X : ℕ → Ω → ℝ),
    (∀ i, Measurable (X i)) → iIndepFun X → (∀ i, volume.map (X i) = cauchyMeasure 0 1) →
    ∀ m x : ℝ, 0 ≤ m → 0 ≤ x →
      volume {ω | ∃ t : ℕ,
        x < (∑ i ∈ Finset.range t, X i ω) / (∑ i ∈ Finset.range t, X i ω ^ 2 + m)} ≤
        ENNReal.ofReal (Real.exp (-2 * m * x ^ 2))

/-- The quadratic `λ u - (λ² / 2) u²` is at most `1 / 2`. -/
private lemma quad_le_half (lam u : ℝ) : lam * u - (lam ^ 2 / 2) * u ^ 2 ≤ 1 / 2 := by
  have h : lam * u - (lam ^ 2 / 2) * u ^ 2 = 1 / 2 - (lam * u - 1) ^ 2 / 2 := by ring
  rw [h]
  linarith [sq_nonneg (lam * u - 1)]

/-- The one-step exponential factor `exp (λ u - (λ² / 2) u²)`. -/
private noncomputable def stepFactor (lam : ℝ) (u : ℝ) : ℝ :=
  Real.exp (lam * u - (lam ^ 2 / 2) * u ^ 2)

private lemma stepFactor_nonneg (lam u : ℝ) : 0 ≤ stepFactor lam u := Real.exp_nonneg _

private lemma stepFactor_le (lam u : ℝ) : stepFactor lam u ≤ Real.exp (1 / 2) :=
  Real.exp_le_exp.mpr (quad_le_half lam u)

private lemma stepFactor_norm_le (lam u : ℝ) : ‖stepFactor lam u‖ ≤ Real.exp (1 / 2) := by
  rw [Real.norm_eq_abs, abs_of_nonneg (stepFactor_nonneg lam u)]
  exact stepFactor_le lam u

private lemma continuous_stepFactor (lam : ℝ) : Continuous (stepFactor lam) := by
  unfold stepFactor
  exact Real.continuous_exp.comp
    ((continuous_const.mul continuous_id).sub (continuous_const.mul (continuous_id.pow 2)))

/-- The standard Cauchy density is an even function. -/
private lemma cauchyPDF_neg (x : ℝ) : cauchyPDF 0 1 (-x) = cauchyPDF 0 1 x := by
  simp [cauchyPDF, cauchyPDFReal, sub_zero]

/-- The standard Cauchy law is invariant under negation. -/
private lemma map_neg_cauchyMeasure :
    (cauchyMeasure 0 1).map Neg.neg = cauchyMeasure 0 1 := by
  have h1 : (1 : NNReal) ≠ 0 := one_ne_zero
  rw [cauchyMeasure_of_scale_ne_zero 0 h1]
  rw [MeasureTheory.Measure.ext_iff]
  intro s hs
  rw [Measure.map_apply measurable_neg hs, withDensity_apply _ hs,
    withDensity_apply _ (measurable_neg hs)]
  have hsub : ∫⁻ x in Neg.neg ⁻¹' s, cauchyPDF 0 1 x ∂volume
      = ∫⁻ x in s, cauchyPDF 0 1 (-x) ∂volume := by
    rw [← lintegral_indicator (measurable_neg hs) _, ← lintegral_indicator hs _]
    have hind : (Neg.neg ⁻¹' s).indicator (cauchyPDF 0 1)
        = fun x => s.indicator (fun x => cauchyPDF 0 1 (-x)) (-x) := by
      ext x
      by_cases hx : -x ∈ s <;> simp [Set.indicator, hx]
    rw [hind]
    have hmap := MeasureTheory.Measure.map_neg_eq_self (volume : Measure ℝ)
    have hbase : ∫⁻ x, s.indicator (fun x => cauchyPDF 0 1 (-x)) x
          ∂(Measure.map Neg.neg volume)
        = ∫⁻ x, s.indicator (fun x => cauchyPDF 0 1 (-x)) (-x) ∂volume :=
      MeasureTheory.lintegral_map
        (((measurable_cauchyPDF 0 1).comp measurable_neg).indicator hs) measurable_neg
    rw [hmap] at hbase
    exact hbase.symm
  rw [hsub]
  exact setLIntegral_congr_fun hs (fun x _ => cauchyPDF_neg x)

/-- The symmetrized one-step factor is pointwise at most `1`. -/
private lemma stepFactor_avg_le_one (lam u : ℝ) :
    (stepFactor lam u + stepFactor lam (-u)) / 2 ≤ 1 := by
  have hcosh : Real.cosh (lam * u) ≤ Real.exp ((lam * u) ^ 2 / 2) :=
    Real.cosh_le_exp_half_sq _
  have hexp_nonneg : 0 ≤ Real.exp (-((lam ^ 2 / 2) * u ^ 2)) := Real.exp_nonneg _
  have hfactor : (stepFactor lam u + stepFactor lam (-u)) / 2
      = Real.cosh (lam * u) * Real.exp (-((lam ^ 2 / 2) * u ^ 2)) := by
    have e1 : Real.exp (lam * u - (lam ^ 2 / 2) * u ^ 2)
        = Real.exp (lam * u) * Real.exp (-((lam ^ 2 / 2) * u ^ 2)) := by
      rw [← Real.exp_add, sub_eq_add_neg]
    have e2 : Real.exp (lam * (-u) - (lam ^ 2 / 2) * (-u) ^ 2)
        = Real.exp (-(lam * u)) * Real.exp (-((lam ^ 2 / 2) * u ^ 2)) := by
      rw [← Real.exp_add]; congr 1; ring
    unfold stepFactor
    rw [e1, e2, Real.cosh_eq]
    ring
  rw [hfactor]
  calc Real.cosh (lam * u) * Real.exp (-((lam ^ 2 / 2) * u ^ 2))
      ≤ Real.exp ((lam * u) ^ 2 / 2) * Real.exp (-((lam ^ 2 / 2) * u ^ 2)) :=
        mul_le_mul_of_nonneg_right hcosh hexp_nonneg
    _ = 1 := by
        rw [← Real.exp_add]
        have hexp0 : (lam * u) ^ 2 / 2 + -((lam ^ 2 / 2) * u ^ 2) = 0 := by ring
        rw [hexp0, Real.exp_zero]

/-- De la Peña's one-step bound: the one-step factor has mean at most `1` under the standard
Cauchy law. -/
private lemma integral_stepFactor_cauchy (lam : ℝ) :
    ∫ u, stepFactor lam u ∂(cauchyMeasure 0 1) ≤ 1 := by
  have hgcont : Continuous (stepFactor lam) := continuous_stepFactor lam
  have hgsm : StronglyMeasurable (stepFactor lam) := hgcont.stronglyMeasurable
  have hgbdd : ∀ u, ‖stepFactor lam u‖ ≤ Real.exp (1 / 2) := stepFactor_norm_le lam
  have hgint : Integrable (stepFactor lam) (cauchyMeasure 0 1) :=
    Integrable.of_bound hgsm.aestronglyMeasurable _ (ae_of_all _ hgbdd)
  have hgncont : Continuous (fun u => stepFactor lam (-u)) := hgcont.comp continuous_neg
  have hgnsm : StronglyMeasurable (fun u => stepFactor lam (-u)) := hgncont.stronglyMeasurable
  have hgnbdd : ∀ u, ‖stepFactor lam (-u)‖ ≤ Real.exp (1 / 2) :=
    fun u => stepFactor_norm_le lam (-u)
  have hgnint : Integrable (fun u => stepFactor lam (-u)) (cauchyMeasure 0 1) :=
    Integrable.of_bound hgnsm.aestronglyMeasurable _ (ae_of_all _ hgnbdd)
  have hsymm : ∫ u, stepFactor lam (-u) ∂(cauchyMeasure 0 1)
      = ∫ u, stepFactor lam u ∂(cauchyMeasure 0 1) := by
    have h := MeasureTheory.integral_map (μ := cauchyMeasure 0 1) (φ := Neg.neg)
      (f := stepFactor lam) measurable_neg.aemeasurable hgsm.aestronglyMeasurable
    rw [map_neg_cauchyMeasure] at h
    exact h.symm
  have havg : ∫ u, stepFactor lam u ∂(cauchyMeasure 0 1)
      = ∫ u, (stepFactor lam u + stepFactor lam (-u)) / 2 ∂(cauchyMeasure 0 1) := by
    rw [integral_div, integral_add hgint hgnint, hsymm]
    ring
  rw [havg]
  calc ∫ u, (stepFactor lam u + stepFactor lam (-u)) / 2 ∂(cauchyMeasure 0 1)
      ≤ ∫ u, 1 ∂(cauchyMeasure 0 1) :=
        integral_mono ((hgint.add hgnint).div_const 2) (integrable_const 1)
          (fun u => stepFactor_avg_le_one lam u)
    _ = 1 := by simp

/-- The exponential process `exp (λ S_t - (λ² / 2) (V_t + m))`. -/
private noncomputable def expProcess {Ω : Type*} (X : ℕ → Ω → ℝ) (lam m : ℝ) (t : ℕ)
    (ω : Ω) : ℝ :=
  Real.exp (lam * (∑ i ∈ Finset.range t, X i ω)
    - (lam ^ 2 / 2) * ((∑ i ∈ Finset.range t, X i ω ^ 2) + m))

/-- One-step multiplicative splitting of the exponential process. -/
private lemma expProcess_succ {Ω : Type*} (X : ℕ → Ω → ℝ) (lam m : ℝ) (t : ℕ) (ω : Ω) :
    expProcess X lam m (t + 1) ω = expProcess X lam m t ω * stepFactor lam (X t ω) := by
  unfold expProcess stepFactor
  rw [Finset.sum_range_succ, Finset.sum_range_succ, ← Real.exp_add]
  congr 1
  ring

/-- The exponential process is strongly measurable whenever the first `t` variables are. -/
private lemma stronglyMeasurable_expProcess_of {Ω : Type*} {mσ : MeasurableSpace Ω}
    (X : ℕ → Ω → ℝ) (lam m : ℝ) (t : ℕ)
    (hX : ∀ i ∈ Finset.range t, StronglyMeasurable[mσ] (X i)) :
    StronglyMeasurable[mσ] (expProcess X lam m t) := by
  have hS : StronglyMeasurable[mσ] (fun ω => ∑ i ∈ Finset.range t, X i ω) :=
    Finset.stronglyMeasurable_fun_sum _ hX
  have hXsq : ∀ i ∈ Finset.range t,
      StronglyMeasurable[mσ] (fun ω => X i ω ^ 2) := by
    intro i hi
    have h := (hX i hi).mul (hX i hi)
    have heq : (fun ω => X i ω ^ 2) = (X i * X i) := by
      ext ω
      simp [Pi.mul_apply, pow_two]
    rw [heq]
    exact h
  have hV : StronglyMeasurable[mσ] (fun ω => ∑ i ∈ Finset.range t, X i ω ^ 2) :=
    Finset.stronglyMeasurable_fun_sum _ hXsq
  have hlamS : StronglyMeasurable[mσ]
      (fun ω => lam * (∑ i ∈ Finset.range t, X i ω)) := hS.const_mul lam
  have hVm : StronglyMeasurable[mσ]
      (fun ω => (∑ i ∈ Finset.range t, X i ω ^ 2) + m) := hV.add_const m
  have hcVm : StronglyMeasurable[mσ]
      (fun ω => (lam ^ 2 / 2) * ((∑ i ∈ Finset.range t, X i ω ^ 2) + m)) :=
    hVm.const_mul (lam ^ 2 / 2)
  have hinner : StronglyMeasurable[mσ] (fun ω => lam * (∑ i ∈ Finset.range t, X i ω)
      - (lam ^ 2 / 2) * ((∑ i ∈ Finset.range t, X i ω ^ 2) + m)) := hlamS.sub hcVm
  exact Real.continuous_exp.comp_stronglyMeasurable hinner

/-- The shifted exponential process is adapted to the natural filtration. The shift matches
the inclusive natural filtration: `M (t + 1)` uses `X₀, …, X_t`. -/
private lemma stronglyAdapted_expProcess_shift {Ω : Type*} {m0 : MeasurableSpace Ω}
    (X : ℕ → Ω → ℝ) (hXstrong : ∀ i, StronglyMeasurable (X i)) (lam m : ℝ) :
    StronglyAdapted (Filtration.natural X hXstrong)
      (fun t => expProcess X lam m (t + 1)) := by
  intro t
  show StronglyMeasurable[Filtration.natural X hXstrong t] (expProcess X lam m (t + 1))
  apply stronglyMeasurable_expProcess_of
  intro i hi
  simp only [Finset.mem_range] at hi
  have hij : i ≤ t := Nat.le_of_lt_succ hi
  have h := (Filtration.stronglyAdapted_natural hXstrong) i
  exact h.mono ((Filtration.natural X hXstrong).mono hij)

/-- The exponential process is integrable, since it is bounded. -/
private lemma integrable_expProcess {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ) (hXmeas : ∀ i, Measurable (X i))
    (lam m : ℝ) (hm : 0 ≤ m) (t : ℕ) :
    Integrable (expProcess X lam m t) μ := by
  have hsm : StronglyMeasurable (expProcess X lam m t) := by
    apply stronglyMeasurable_expProcess_of
    intro i _
    exact (hXmeas i).stronglyMeasurable
  apply Integrable.of_bound hsm.aestronglyMeasurable (Real.exp ((t : ℝ) / 2))
  filter_upwards with ω
  have hMnonneg : 0 ≤ expProcess X lam m t ω := Real.exp_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hMnonneg]
  unfold expProcess
  apply Real.exp_le_exp.mpr
  have hterm : ∀ i ∈ Finset.range t,
      lam * X i ω - (lam ^ 2 / 2) * (X i ω) ^ 2 ≤ 1 / 2 :=
    fun i _ => quad_le_half lam (X i ω)
  have hle : ∑ i ∈ Finset.range t, (lam * X i ω - (lam ^ 2 / 2) * (X i ω) ^ 2)
      ≤ ∑ i ∈ Finset.range t, (1 / 2 : ℝ) := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
  have hsplit : ∑ i ∈ Finset.range t, (lam * X i ω - (lam ^ 2 / 2) * (X i ω) ^ 2)
      = lam * (∑ i ∈ Finset.range t, X i ω)
        - (lam ^ 2 / 2) * (∑ i ∈ Finset.range t, (X i ω) ^ 2) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hsplit] at hle
  have hcm : 0 ≤ (lam ^ 2 / 2) * m := mul_nonneg (by positivity) hm
  linarith [hle, hcm]

/-- One-step conditional expectation bound for the shifted exponential process. -/
private lemma condExp_expProcess_succ_le {Ω : Type*} {m0 : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hXstrong : ∀ i, StronglyMeasurable (X i))
    (hXindep : iIndepFun X μ) (hlaw : ∀ i, μ.map (X i) = cauchyMeasure 0 1)
    (lam m : ℝ) (hm : 0 ≤ m) (t : ℕ) :
    μ[expProcess X lam m (t + 1 + 1) | Filtration.natural X hXstrong t]
      ≤ᵐ[μ] expProcess X lam m (t + 1) := by
  have hMmeas : StronglyMeasurable[Filtration.natural X hXstrong t]
      (expProcess X lam m (t + 1)) :=
    stronglyAdapted_expProcess_shift X hXstrong lam m t
  have hZsm : StronglyMeasurable (fun ω => stepFactor lam (X (t + 1) ω)) :=
    (continuous_stepFactor lam).comp_stronglyMeasurable (hXstrong (t + 1))
  have hZint : Integrable (fun ω => stepFactor lam (X (t + 1) ω)) μ :=
    Integrable.of_bound hZsm.aestronglyMeasurable _
      (ae_of_all _ fun ω => stepFactor_norm_le lam _)
  have hMint : Integrable (expProcess X lam m (t + 1 + 1)) μ :=
    integrable_expProcess μ X (fun i => (hXstrong i).measurable) lam m hm (t + 1 + 1)
  have hZmean : ∫ ω, stepFactor lam (X (t + 1) ω) ∂μ ≤ 1 := by
    have h := MeasureTheory.integral_map (μ := μ) (φ := X (t + 1))
      (f := stepFactor lam) (hXstrong (t + 1)).measurable.aemeasurable
      (continuous_stepFactor lam).stronglyMeasurable.aestronglyMeasurable
    rw [hlaw (t + 1)] at h
    rw [← h]
    exact integral_stepFactor_cauchy lam
  have hfg : Integrable ((expProcess X lam m (t + 1))
      * (fun ω => stepFactor lam (X (t + 1) ω))) μ := by
    have heq : (expProcess X lam m (t + 1)) * (fun ω => stepFactor lam (X (t + 1) ω))
        = expProcess X lam m (t + 1 + 1) := by
      ext ω
      simp only [Pi.mul_apply]
      exact (expProcess_succ X lam m (t + 1) ω).symm
    rw [heq]
    exact hMint
  have hpull : μ[(expProcess X lam m (t + 1)) * (fun ω => stepFactor lam (X (t + 1) ω))
      | Filtration.natural X hXstrong t]
      =ᵐ[μ] (expProcess X lam m (t + 1))
        * μ[(fun ω => stepFactor lam (X (t + 1) ω)) | Filtration.natural X hXstrong t] :=
    condExp_mul_of_stronglyMeasurable_left (m := Filtration.natural X hXstrong t) hMmeas hfg
      hZint
  have hindep : Indep (MeasurableSpace.comap (X (t + 1)) inferInstance)
      (Filtration.natural X hXstrong t) μ := by
    have hdis : Disjoint ({t + 1} : Set ℕ) {k | k ≤ t} := by
      rw [Set.disjoint_singleton_left]
      intro h
      simp only [Set.mem_ofPred_eq] at h
      omega
    have hfull : Indep
        (⨆ k ∈ ({t + 1} : Set ℕ), MeasurableSpace.comap (X k) inferInstance)
        (⨆ k ∈ {k | k ≤ t}, MeasurableSpace.comap (X k) inferInstance) μ :=
      ProbabilityTheory.indep_iSup_of_disjoint
        (fun k => (hXstrong k).measurable.comap_le) hXindep hdis
    rwa [iSup_singleton] at hfull
  have hZmeas : StronglyMeasurable[MeasurableSpace.comap (X (t + 1)) inferInstance]
      (fun ω => stepFactor lam (X (t + 1) ω)) := by
    have hmeas : Measurable (stepFactor lam) := (continuous_stepFactor lam).measurable
    have hXmeas : Measurable[MeasurableSpace.comap (X (t + 1)) inferInstance] (X (t + 1)) :=
      comap_measurable (X (t + 1))
    exact (hmeas.comp hXmeas).stronglyMeasurable
  have hcondZ : μ[(fun ω => stepFactor lam (X (t + 1) ω)) | Filtration.natural X hXstrong t]
      =ᵐ[μ] fun _ => ∫ ω, stepFactor lam (X (t + 1) ω) ∂μ := by
    have hle1 : MeasurableSpace.comap (X (t + 1)) inferInstance ≤ m0 :=
      (hXstrong (t + 1)).measurable.comap_le
    have hle2 : (Filtration.natural X hXstrong t) ≤ m0 :=
      (Filtration.natural X hXstrong).le t
    have h := condExp_indep_eq (m₁ := MeasurableSpace.comap (X (t + 1)) inferInstance)
      (m₂ := Filtration.natural X hXstrong t) (m := m0) (μ := μ)
      (f := fun ω => stepFactor lam (X (t + 1) ω)) hle1 hle2 hZmeas hindep
    simpa using h
  have hsplit_ae : μ[expProcess X lam m (t + 1 + 1) | Filtration.natural X hXstrong t]
      =ᵐ[μ] μ[(expProcess X lam m (t + 1)) * (fun ω => stepFactor lam (X (t + 1) ω))
        | Filtration.natural X hXstrong t] := by
    apply condExp_congr_ae
    filter_upwards with ω
    simp only [Pi.mul_apply]
    exact expProcess_succ X lam m (t + 1) ω
  filter_upwards [hsplit_ae, hpull, hcondZ] with ω h1 h2 h3
  rw [h1, h2]
  simp only [Pi.mul_apply] at h2 ⊢
  rw [h3]
  have hMnonneg : 0 ≤ expProcess X lam m (t + 1) ω := Real.exp_nonneg _
  calc expProcess X lam m (t + 1) ω * (∫ ω, stepFactor lam (X (t + 1) ω) ∂μ)
      ≤ expProcess X lam m (t + 1) ω * 1 :=
        mul_le_mul_of_nonneg_left hZmean hMnonneg
    _ = expProcess X lam m (t + 1) ω := mul_one _

/-- The shifted exponential process is a supermartingale for the natural filtration. -/
private lemma supermartingale_expProcess_shift {Ω : Type*} {m0 : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hXstrong : ∀ i, StronglyMeasurable (X i))
    (hXindep : iIndepFun X μ) (hlaw : ∀ i, μ.map (X i) = cauchyMeasure 0 1)
    (lam m : ℝ) (hm : 0 ≤ m) :
    Supermartingale (fun t => expProcess X lam m (t + 1)) (Filtration.natural X hXstrong)
      μ := by
  apply supermartingale_nat (stronglyAdapted_expProcess_shift X hXstrong lam m)
    (fun t => integrable_expProcess μ X (fun i => (hXstrong i).measurable) lam m hm (t + 1))
  intro t
  exact condExp_expProcess_succ_le μ X hXstrong hXindep hlaw lam m hm t

/--
Resolved true: Howard, Ramdas, McAuliffe and Sekhon prove that i.i.d. standard Cauchy increments
satisfy `P(∃ t, S_t / (V_t + m) ≥ x) ≤ exp(-2 m x²)` for all `x, m > 0` (de la Peña's
self-normalized bound for symmetric increments needs no moments), and the AimPL remark records the
inequality as known; for `m = 0` or `x = 0` the bound is `1`. Source: AimPL: Stein's method and
applications in high-dimensional statistics, Problem 1.15, http://aimpl.org/steinhd/1/ (remark: the
inequality is Example 4 of arXiv:1808.03204 and holds for any symmetric increments); resolution: S.
R. Howard, A. Ramdas, J. McAuliffe and J. Sekhon, Time-uniform Chernoff bounds via nonnegative
supermartingales, Probab. Surv. 17 (2020), 257-317, arXiv:1808.03204, Example 5 (Cauchy increments)
of arXiv v8, eq. (4.24) (Example 4 in the version the AimPL remark cites): for i.i.d. standard
Cauchy increments and any x, m > 0, P(∃ t ∈ ℕ : S_t / ([S]_t + m) ≥ x) ≤ exp(-2 m x²), [S]_t = ∑
ΔS_i², from de la Peña's bound for conditionally symmetric increments (Lemma 3(d)) and Corollary 6,
https://doi.org/10.1214/18-PS321.
-/
public theorem cauchySelfNormalizedBound_holds : cauchySelfNormalizedBound := by
  intro Ω _ _ X hmeas hindep hlaw m x hm hx
  by_cases hx0 : x = 0
  · subst hx0
    have hRHS : ENNReal.ofReal (Real.exp (-2 * m * (0 : ℝ) ^ 2)) = 1 := by simp
    rw [hRHS]
    exact prob_le_one
  · have hxpos : 0 < x := hx.lt_of_ne (Ne.symm hx0)
    have hXstrong : ∀ i, StronglyMeasurable (X i) := fun i => (hmeas i).stronglyMeasurable
    set M' : ℕ → Ω → ℝ := fun t => expProcess X (2 * x) m (t + 1) with hM'
    have hsup : Supermartingale M' (Filtration.natural X hXstrong) volume :=
      supermartingale_expProcess_shift volume X hXstrong hindep hlaw (2 * x) m hm
    have hnonneg : 0 ≤ M' := fun _ _ => Real.exp_nonneg _
    have hVille := Supermartingale.ville_maximal_ineq (μ := volume) hsup hnonneg
      (show (0 : ℝ) < 1 by norm_num)
    rw [one_mul] at hVille
    have hZ0mean : ∫ ω, stepFactor (2 * x) (X 0 ω) ∂volume ≤ 1 := by
      have h := MeasureTheory.integral_map (μ := volume) (φ := X 0)
        (f := stepFactor (2 * x)) (hXstrong 0).measurable.aemeasurable
        (continuous_stepFactor (2 * x)).stronglyMeasurable.aestronglyMeasurable
      rw [hlaw 0] at h
      rw [← h]
      exact integral_stepFactor_cauchy (2 * x)
    have hM0 : ∫ ω, M' 0 ω ∂volume ≤ Real.exp (-2 * m * x ^ 2) := by
      have hsplit0 : ∀ ω, M' 0 ω
          = stepFactor (2 * x) (X 0 ω) * Real.exp (-(((2 * x) ^ 2 / 2) * m)) := by
        intro ω
        have h1 := expProcess_succ X (2 * x) m 0 ω
        have hM0 : expProcess X (2 * x) m 0 ω
            = Real.exp (-(((2 * x) ^ 2 / 2) * m)) := by
          unfold expProcess
          simp only [Finset.sum_range_zero, mul_zero, zero_add, zero_sub]
        simp only [hM']
        rw [h1, hM0, mul_comm]
      have hconst : ∫ ω, M' 0 ω ∂volume
          = (∫ ω, stepFactor (2 * x) (X 0 ω) ∂volume)
            * Real.exp (-(((2 * x) ^ 2 / 2) * m)) := by
        have hfun : (fun ω => M' 0 ω)
            = fun ω => stepFactor (2 * x) (X 0 ω) * Real.exp (-(((2 * x) ^ 2 / 2) * m)) :=
          funext hsplit0
        rw [hfun, integral_mul_const]
      rw [hconst]
      have hexp_nonneg : 0 ≤ Real.exp (-(((2 * x) ^ 2 / 2) * m)) := Real.exp_nonneg _
      have hexp_eq : -(((2 * x) ^ 2 / 2) * m) = -2 * m * x ^ 2 := by ring
      rw [hexp_eq] at hexp_nonneg ⊢
      calc (∫ ω, stepFactor (2 * x) (X 0 ω) ∂volume) * Real.exp (-2 * m * x ^ 2)
          ≤ 1 * Real.exp (-2 * m * x ^ 2) :=
            mul_le_mul_of_nonneg_right hZ0mean hexp_nonneg
        _ = Real.exp (-2 * m * x ^ 2) := one_mul _
    have hsub : {ω | ∃ t : ℕ,
          x < (∑ i ∈ Finset.range t, X i ω) / (∑ i ∈ Finset.range t, X i ω ^ 2 + m)}
        ⊆ {ω | ∃ n, 1 ≤ M' n ω} := by
      intro ω h
      obtain ⟨t, ht⟩ := h
      by_cases ht0 : t = 0
      · subst ht0
        simp only [Finset.sum_range_zero] at ht
        rw [zero_div] at ht
        exact absurd ht (not_lt_of_ge hx)
      · have ht1 : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr ht0
        refine ⟨t - 1, ?_⟩
        have hMt : M' (t - 1) ω = expProcess X (2 * x) m t ω := by
          have hsub1 : t - 1 + 1 = t := Nat.sub_add_cancel ht1
          simp only [hM']
          rw [hsub1]
        rw [hMt]
        have hVnonneg : 0 ≤ (∑ i ∈ Finset.range t, X i ω ^ 2) :=
          Finset.sum_nonneg (fun i _ => sq_nonneg _)
        have hD : 0 < (∑ i ∈ Finset.range t, X i ω ^ 2) + m := by
          by_contra hD0
          have hDeq := le_antisymm (not_lt.mp hD0) (add_nonneg hVnonneg hm)
          rw [hDeq, div_zero] at ht
          exact absurd ht (not_lt_of_ge hx)
        have hSgt : x * ((∑ i ∈ Finset.range t, X i ω ^ 2) + m)
            < ∑ i ∈ Finset.range t, X i ω :=
          (lt_div_iff₀ hD).mp ht
        have hexp_pos : 0 < 2 * x * (∑ i ∈ Finset.range t, X i ω)
            - ((2 * x) ^ 2 / 2) * ((∑ i ∈ Finset.range t, X i ω ^ 2) + m) := by
          have h2x : (0 : ℝ) < 2 * x := by linarith [hxpos]
          have hfactor : 2 * x * (∑ i ∈ Finset.range t, X i ω)
              - ((2 * x) ^ 2 / 2) * ((∑ i ∈ Finset.range t, X i ω ^ 2) + m)
              = 2 * x * ((∑ i ∈ Finset.range t, X i ω)
                - x * ((∑ i ∈ Finset.range t, X i ω ^ 2) + m)) := by ring
          rw [hfactor]
          apply mul_pos h2x
          linarith [hSgt]
        unfold expProcess
        rw [← Real.exp_zero]
        apply Real.exp_le_exp.mpr
        linarith [hexp_pos]
    calc volume {ω | ∃ t : ℕ,
            x < (∑ i ∈ Finset.range t, X i ω) / (∑ i ∈ Finset.range t, X i ω ^ 2 + m)}
        ≤ volume {ω | ∃ n, 1 ≤ M' n ω} := measure_mono hsub
      _ = ENNReal.ofReal (volume.real {ω | ∃ n, 1 ≤ M' n ω}) := by
          rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
      _ ≤ ENNReal.ofReal (Real.exp (-2 * m * x ^ 2)) :=
          ENNReal.ofReal_le_ofReal (le_trans hVille hM0)

end MathlibExt.Probability.CauchySelfNormalizedBoundAIMProbabilityProblem23Wanted
