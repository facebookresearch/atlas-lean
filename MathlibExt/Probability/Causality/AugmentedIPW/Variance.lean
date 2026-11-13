/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.AugmentedIPW.Score
public import MathlibExt.Probability.Causality.AugmentedIPW.DoubleRobustness
public import MathlibExt.Probability.Statistics.Bootstrap
public import MathlibExt.Probability.Statistics.Slutsky
public import MathlibExt.Probability.Statistics.Survival.ProcessInference
public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Probability.StrongLaw

/-!
# Asymptotic variance, variance estimation and Wald intervals for the AIPW estimator

A single unit lives on a probability space `(Ω₁, μ₁)` carrying a treatment event `T`, a covariate
`X` and an observed outcome `Y`, as in `AugmentedIPW.Score`. An i.i.d. sample is a sequence
`O : ℕ → Ω → Ω₁` of independent random units with common law `μ₁` (`iIndepFun O P` and
`HasLaw (O i) μ₁ P`).

The nuisances used for unit `i` at sample size `n` are `e n i ω`, `m₀ n i ω`, `m₁ n i ω`:
arbitrary functions of the whole sample. This covers full-sample plug-in fits (no dependence on
`i`), cross-fitting (dependence on `i` only through its fold), and fixed nuisances (no
dependence on `n, i, ω`). With fixed true nuisances `e, m₀, m₁` the per-unit score
`ψ = aipwScore T X Y e m₀ m₁` has mean `τ` (the average treatment effect, see
`integral_aipwScore_eq_ate`), and `φ = ψ - τ` is the efficient influence function of the average
treatment effect (Hahn 1998); `Var(φ) = Var(ψ) = E[φ²]` (`variance_aipwScore_eq_integral_sq`).

## Main definitions

* `aipwFittedScore O T X Y e m₀ m₁ n i`: the AIPW score of unit `i` at sample size `n`, with its
  fitted nuisances.
* `aipwEstimator O T X Y e m₀ m₁ n`: the AIPW estimator, the sample mean of the fitted scores
  of units `0, …, n - 1`.
* `aipwVarianceEstimator O T X Y e m₀ m₁ n`: the plug-in variance estimator, the sample variance
  `n⁻¹ ∑ (ψ̂ᵢ - τ̂)²` of the estimated influence-function values `ψ̂ᵢ - τ̂`. It is the generic
  plug-in sample variance `ProbabilityTheory.Bootstrap.empiricalVar` of the fitted scores, whose
  center is the AIPW estimator (`aipwVarianceEstimator_eq`).

## Main results

* `tendstoInDistribution_aipwEstimator_oracle`: with fixed nuisances and `ψ ∈ L²`,
  `√n (τ̂ₙ - τ) →ᵈ N(0, Var ψ)` (central limit theorem).
* `tendstoInDistribution_aipwEstimator`: for fitted nuisances, if the estimator is
  asymptotically equivalent to the oracle one, `√n (τ̂ₙ - τ̂ₙ*) → 0` in probability, then
  `√n (τ̂ₙ - τ) →ᵈ N(0, Var φ)`: the asymptotic variance is the variance of the influence
  function.
* `tendstoInMeasure_aipwVarianceEstimator`: if the fitted scores are consistent in empirical
  `L²`, `n⁻¹ ∑ (ψ̂ₙᵢ - ψᵢ)² → 0` in probability, the variance estimator converges in probability
  to `Var φ`; with fixed nuisances the hypothesis holds trivially
  (`tendstoInMeasure_aipwVarianceEstimator_oracle`).
* `tendsto_coverage_aipwWaldInterval`: the Wald interval `τ̂ₙ ± z √(σ̂ₙ² / n)` has asymptotic
  coverage `P(|N(0, 1)| ≤ z)` for `τ = E[ψ]` when `Var φ ≠ 0`.
* `integral_aipwScore_eq_ate`: at the true propensity, `E[ψ] = E[Y₁ - Y₀]`, so the limit theorems
  above are centered at, and the Wald interval covers, the average treatment effect.

## Hypotheses taken from sibling results

The asymptotic equivalence `√n (τ̂ₙ - τ̂ₙ*) → 0` (from Neyman orthogonality, cross-fitting and a
product rate on the nuisance errors) and the empirical `L²` consistency of the fitted scores are
explicit hypotheses here; neither is proved in this file. The merged
`AugmentedIPW.Orthogonality` supplies the exact finite-covariate ingredients (zero Gateaux
derivative of the bias, the split-fold tower identity), not the rate statement, so it is not
imported. Semiparametric efficiency of `φ`
(that `Var φ` is the efficiency bound) is not proved here.

## Reuse search (API-00)

The score is `AugmentedIPW.Score.aipwScore`; the mean identity at the true nuisances is
`DoubleRobustness.integral_aipwScoreOfSigma_of_propensity`. The limit theorems are Mathlib's
`ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub` (CLT),
`ProbabilityTheory.strong_law_ae_real` (SLLN) and
`MeasureTheory.TendstoInDistribution.add_of_tendstoInMeasure_const` (Slutsky). The interval is
`ProcessInference.waldInterval` and its coverage limit is
`ProcessInference.tendsto_coverage_waldInterval`;
`MeasureTheory.TendstoInMeasure.comp_const_of_continuousAt` gives the square root. The variance
estimator is `ProbabilityTheory.Bootstrap.empiricalVar` of the fitted scores, and its
mean-of-squares form is `ProbabilityTheory.Bootstrap.empiricalVar_eq`.

## References

* J. Hahn, *On the role of the propensity score in efficient semiparametric estimation of
  average treatment effects*, Econometrica 66(2) (1998), 315–331.
* V. Chernozhukov, D. Chetverikov, M. Demirer, E. Duflo, C. Hansen, W. Newey and J. Robins,
  *Double/debiased machine learning for treatment and structural parameters*, Econometrics
  Journal 21(1) (2018), C1–C68, Theorems 3.1 and 3.2, Corollary 3.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Finset

namespace MathlibExt.Probability.Causality.AugmentedIPW.Variance

open MathlibExt.Probability.Causality
open MathlibExt.Probability.Statistics.ProcessInference

section Definitions

variable {Ω Ω₁ 𝒳 : Type*}

/-- The AIPW score of unit `i` at sample size `n`, evaluated at that unit's observation `O i ω`
with its fitted nuisances `e n i ω`, `m₀ n i ω`, `m₁ n i ω`. -/
noncomputable def aipwFittedScore (O : ℕ → Ω → Ω₁) (T : Set Ω₁) (X : Ω₁ → 𝒳) (Y : Ω₁ → ℝ)
    (e m₀ m₁ : ℕ → ℕ → Ω → 𝒳 → ℝ) (n i : ℕ) (ω : Ω) : ℝ :=
  aipwScore T X Y (e n i ω) (m₀ n i ω) (m₁ n i ω) (O i ω)

/-- The **AIPW estimator** of the average treatment effect at sample size `n`: the sample mean
`n⁻¹ ∑_{i < n} ψ̂ₙᵢ` of the fitted AIPW scores. -/
noncomputable def aipwEstimator (O : ℕ → Ω → Ω₁) (T : Set Ω₁) (X : Ω₁ → 𝒳) (Y : Ω₁ → ℝ)
    (e m₀ m₁ : ℕ → ℕ → Ω → 𝒳 → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i ∈ range n, aipwFittedScore O T X Y e m₀ m₁ n i ω

/-- The **plug-in variance estimator** for the AIPW estimator: the sample variance
`n⁻¹ ∑_{i < n} (ψ̂ₙᵢ - τ̂ₙ)²` of the estimated influence-function values `ψ̂ₙᵢ - τ̂ₙ`, defined as
the plug-in sample variance `Bootstrap.empiricalVar` of the fitted scores of units
`0, …, n - 1` (`aipwVarianceEstimator_eq` gives the centered form). -/
noncomputable def aipwVarianceEstimator (O : ℕ → Ω → Ω₁) (T : Set Ω₁) (X : Ω₁ → 𝒳)
    (Y : Ω₁ → ℝ) (e m₀ m₁ : ℕ → ℕ → Ω → 𝒳 → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Bootstrap.empiricalVar (fun i => aipwFittedScore O T X Y e m₀ m₁ n i ω) n

/-- The plug-in variance estimator is centered at the AIPW estimator:
`σ̂ₙ² = n⁻¹ ∑_{i < n} (ψ̂ₙᵢ - τ̂ₙ)²`, since the sample mean in `Bootstrap.empiricalVar` is
`aipwEstimator` (`Bootstrap.sampleMean_range`). -/
theorem aipwVarianceEstimator_eq (O : ℕ → Ω → Ω₁) (T : Set Ω₁) (X : Ω₁ → 𝒳) (Y : Ω₁ → ℝ)
    (e m₀ m₁ : ℕ → ℕ → Ω → 𝒳 → ℝ) (n : ℕ) (ω : Ω) :
    aipwVarianceEstimator O T X Y e m₀ m₁ n ω = (n : ℝ)⁻¹ * ∑ i ∈ range n,
      (aipwFittedScore O T X Y e m₀ m₁ n i ω - aipwEstimator O T X Y e m₀ m₁ n ω) ^ 2 := by
  simp only [aipwVarianceEstimator, Bootstrap.empiricalVar, Bootstrap.sampleMean_range,
    aipwEstimator]

end Definitions

section Basic

variable {Ω₁ 𝒳 : Type*} [MeasurableSpace Ω₁]

/-- The AIPW score is measurable when the treatment event, the covariate, the outcome and the
nuisances are. -/
theorem measurable_aipwScore [MeasurableSpace 𝒳] {T : Set Ω₁} (hT : MeasurableSet T) {X : Ω₁ → 𝒳}
    (hX : Measurable X) {Y : Ω₁ → ℝ} (hY : Measurable Y) {e m₀ m₁ : 𝒳 → ℝ} (he : Measurable e)
    (hm₀ : Measurable m₀) (hm₁ : Measurable m₁) : Measurable (aipwScore T X Y e m₀ m₁) := by
  have h : aipwScore T X Y e m₀ m₁ = fun ω => m₁ (X ω) - m₀ (X ω) +
      T.indicator (fun ω => (Y ω - m₁ (X ω)) / e (X ω)) ω -
        Tᶜ.indicator (fun ω => (Y ω - m₀ (X ω)) / (1 - e (X ω))) ω :=
    funext fun _ => aipwScore_eq
  rw [h]
  refine ((hm₁.comp hX).sub (hm₀.comp hX)).add (Measurable.indicator ?_ hT) |>.sub
    (Measurable.indicator ?_ hT.compl)
  · exact (hY.sub (hm₁.comp hX)).div (he.comp hX)
  · exact (hY.sub (hm₀.comp hX)).div (measurable_const.sub (he.comp hX))

/-- The variance of the AIPW score is the second moment of the centered score
`φ = ψ - τ`, where `τ = E[ψ]`: `Var(ψ) = Var(φ) = E[φ²]`. -/
theorem variance_aipwScore_eq_integral_sq {μ₁ : Measure Ω₁} {T : Set Ω₁} {X : Ω₁ → 𝒳}
    {Y : Ω₁ → ℝ} {e m₀ m₁ : 𝒳 → ℝ} (hψ : AEMeasurable (aipwScore T X Y e m₀ m₁) μ₁) {τ : ℝ}
    (hτ : ∫ ω, aipwScore T X Y e m₀ m₁ ω ∂μ₁ = τ) :
    Var[aipwScore T X Y e m₀ m₁; μ₁] = ∫ ω, (aipwScore T X Y e m₀ m₁ ω - τ) ^ 2 ∂μ₁ := by
  rw [variance_eq_integral hψ, hτ]

end Basic

section Helpers

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- `√n (n⁻¹ S - τ) = (√n)⁻¹ (S - n τ)`, including at `n = 0`. -/
private lemma sqrt_mul_inv_mul_sub (n : ℕ) (S τ : ℝ) :
    √(n : ℝ) * ((n : ℝ)⁻¹ * S - τ) = (√(n : ℝ))⁻¹ * (S - n * τ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have key : ∀ s : ℝ, 0 < s → s * ((s ^ 2)⁻¹ * S - τ) = s⁻¹ * (S - s ^ 2 * τ) := by
      intro s hs
      field_simp
    have h := key (√(n : ℝ)) (Real.sqrt_pos.2 (Nat.cast_pos.2 hn))
    rwa [Real.sq_sqrt (Nat.cast_nonneg n)] at h

/-- Convergence in probability of two sequences gives convergence in probability of the pair. -/
private lemma tendstoInMeasure_prodMk {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    {A : ℕ → Ω → E} {B : ℕ → Ω → F} {a : E} {b : F}
    (hA : TendstoInMeasure P A atTop fun _ => a) (hB : TendstoInMeasure P B atTop fun _ => b) :
    TendstoInMeasure P (fun n ω => (A n ω, B n ω)) atTop fun _ => (a, b) := by
  rw [tendstoInMeasure_iff_dist] at hA hB ⊢
  intro ε hε
  have hsum := (hA ε hε).add (hB ε hε)
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le)
    fun n => (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
  simp only [Set.mem_ofPred_eq, Prod.dist_eq, le_max_iff] at hω
  exact hω

/-- If `|f n - c| ≤ g n` eventually and `g n → 0` in probability, then `f n → c` in
probability. -/
private lemma tendstoInMeasure_of_abs_sub_le {f g : ℕ → Ω → ℝ} {c : ℝ}
    (hg : TendstoInMeasure P g atTop fun _ => 0)
    (hle : ∀ᶠ n in atTop, ∀ ω, |f n ω - c| ≤ g n ω) :
    TendstoInMeasure P f atTop fun _ => c := by
  rw [tendstoInMeasure_iff_dist] at hg ⊢
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hg ε hε)
    (Eventually.of_forall fun _ => zero_le) (hle.mono fun n hn => measure_mono fun ω hω => ?_)
  simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero] at hω ⊢
  exact hω.trans ((hn ω).trans (le_abs_self _))

/-- The real-number core of the perturbation bound for the sample variance. -/
private lemma abs_perturb_le {B₁ B₂ C D₁ D₂ : ℝ} (hB₂ : 0 ≤ B₂) (hD₂ : 0 ≤ D₂)
    (hC : C ^ 2 ≤ B₂ * D₂) (hD : D₁ ^ 2 ≤ D₂) :
    |2 * C + D₂ - 2 * B₁ * D₁ - D₁ ^ 2| ≤ 2 * (√B₂ * √D₂) + 2 * D₂ + 2 * (|B₁| * √D₂) := by
  have hC' : |C| ≤ √B₂ * √D₂ := (Real.abs_le_sqrt hC).trans_eq (Real.sqrt_mul hB₂ _)
  have hD' : |D₁| ≤ √D₂ := Real.abs_le_sqrt hD
  have hBD : |B₁ * D₁| ≤ |B₁| * √D₂ := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hD' (abs_nonneg _)
  rw [abs_le] at hC' hBD ⊢
  constructor <;> nlinarith [sq_nonneg D₁]

/-- **Perturbation bound for the sample variance.** For `n > 0` and reals `aᵢ = bᵢ + dᵢ`, the
`1/n` sample variance `Bootstrap.empiricalVar a n` differs from `B₂ - B₁²` (the sample variance
of `b`, with `B₁ = n⁻¹ ∑ bᵢ`, `B₂ = n⁻¹ ∑ bᵢ²`) by at most `2 √B₂ √D₂ + 2 D₂ + 2 |B₁| √D₂`,
where `D₂ = n⁻¹ ∑ dᵢ²`. -/
private lemma abs_empiricalVar_sub_le {n : ℕ} (hn : 0 < n) (a b : ℕ → ℝ) :
    |Bootstrap.empiricalVar a n -
        ((n : ℝ)⁻¹ * ∑ i ∈ range n, b i ^ 2 - ((n : ℝ)⁻¹ * ∑ i ∈ range n, b i) ^ 2)| ≤
      2 * (√((n : ℝ)⁻¹ * ∑ i ∈ range n, b i ^ 2) *
          √((n : ℝ)⁻¹ * ∑ i ∈ range n, (a i - b i) ^ 2)) +
        2 * ((n : ℝ)⁻¹ * ∑ i ∈ range n, (a i - b i) ^ 2) +
        2 * (|(n : ℝ)⁻¹ * ∑ i ∈ range n, b i| *
          √((n : ℝ)⁻¹ * ∑ i ∈ range n, (a i - b i) ^ 2)) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hni : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg n)
  set d : ℕ → ℝ := fun i => a i - b i with hd
  have ha : ∀ i, a i = b i + d i := fun i => by simp [hd]
  have hA2 : (n : ℝ)⁻¹ * ∑ i ∈ range n, a i ^ 2 = (n : ℝ)⁻¹ * ∑ i ∈ range n, b i ^ 2 +
      2 * ((n : ℝ)⁻¹ * ∑ i ∈ range n, b i * d i) + (n : ℝ)⁻¹ * ∑ i ∈ range n, d i ^ 2 := by
    simp only [ha, add_sq, sum_add_distrib, mul_add, ← mul_sum, mul_assoc]
    ring
  have hA1 : (n : ℝ)⁻¹ * ∑ i ∈ range n, a i =
      (n : ℝ)⁻¹ * ∑ i ∈ range n, b i + (n : ℝ)⁻¹ * ∑ i ∈ range n, d i := by
    simp only [ha, sum_add_distrib, mul_add]
  have hC : ((n : ℝ)⁻¹ * ∑ i ∈ range n, b i * d i) ^ 2 ≤
      ((n : ℝ)⁻¹ * ∑ i ∈ range n, b i ^ 2) * ((n : ℝ)⁻¹ * ∑ i ∈ range n, d i ^ 2) := by
    have := sum_mul_sq_le_sq_mul_sq (range n) b d
    calc _ = (n : ℝ)⁻¹ ^ 2 * (∑ i ∈ range n, b i * d i) ^ 2 := by ring
      _ ≤ (n : ℝ)⁻¹ ^ 2 * ((∑ i ∈ range n, b i ^ 2) * ∑ i ∈ range n, d i ^ 2) :=
        mul_le_mul_of_nonneg_left this (sq_nonneg _)
      _ = _ := by ring
  have hD : ((n : ℝ)⁻¹ * ∑ i ∈ range n, d i) ^ 2 ≤ (n : ℝ)⁻¹ * ∑ i ∈ range n, d i ^ 2 := by
    have := sum_mul_sq_le_sq_mul_sq (range n) d fun _ => 1
    simp only [mul_one, one_pow, sum_const, card_range, nsmul_eq_mul] at this
    rw [mul_comm] at this
    calc _ = (n : ℝ)⁻¹ ^ 2 * (∑ i ∈ range n, d i) ^ 2 := by ring
      _ ≤ (n : ℝ)⁻¹ ^ 2 * (n * ∑ i ∈ range n, d i ^ 2) :=
        mul_le_mul_of_nonneg_left this (sq_nonneg _)
      _ = _ := by field_simp
  have hB₂ : 0 ≤ (n : ℝ)⁻¹ * ∑ i ∈ range n, b i ^ 2 :=
    mul_nonneg hni (sum_nonneg fun _ _ => sq_nonneg _)
  have hD₂ : 0 ≤ (n : ℝ)⁻¹ * ∑ i ∈ range n, d i ^ 2 :=
    mul_nonneg hni (sum_nonneg fun _ _ => sq_nonneg _)
  rw [Bootstrap.empiricalVar_eq hn.ne', Bootstrap.sampleMean_range, hA2, hA1]
  convert abs_perturb_le hB₂ hD₂ hC hD using 2
  ring

end Helpers

section Asymptotics

variable {Ω Ω₁ Ω' 𝒳 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace Ω₁]
  {mΩ' : MeasurableSpace Ω'} {P : Measure Ω} [IsProbabilityMeasure P] {μ₁ : Measure Ω₁}
  {P' : Measure Ω'} [IsProbabilityMeasure P']
  {O : ℕ → Ω → Ω₁} {T : Set Ω₁} {X : Ω₁ → 𝒳} {Y : Ω₁ → ℝ}

omit [MeasurableSpace Ω₁] [IsProbabilityMeasure P] in
/-- With fixed nuisances, the fitted score of unit `i` is the score at its observation. -/
theorem aipwFittedScore_const (e m₀ m₁ : 𝒳 → ℝ) (n i : ℕ) (ω : Ω) :
    aipwFittedScore O T X Y (fun _ _ _ => e) (fun _ _ _ => m₀) (fun _ _ _ => m₁) n i ω =
      aipwScore T X Y e m₀ m₁ (O i ω) :=
  rfl

omit [IsProbabilityMeasure P] in
/-- The units of an i.i.d. sample are identically distributed. -/
private lemma identDistrib_of_hasLaw (hlaw : ∀ i, HasLaw (O i) μ₁ P) (i : ℕ) :
    IdentDistrib (O i) (O 0) P P :=
  ⟨(hlaw i).aemeasurable, (hlaw 0).aemeasurable, (hlaw i).map_eq.trans (hlaw 0).map_eq.symm⟩

/-- **Oracle central limit theorem for the AIPW estimator.** With fixed nuisances `e, m₀, m₁`
whose score `ψ = aipwScore T X Y e m₀ m₁` is square integrable under the unit law `μ₁`, and an
i.i.d. sample with law `μ₁`, `√n (τ̂ₙ - τ) →ᵈ N(0, Var ψ)`, where `τ = E[ψ]`. -/
theorem tendstoInDistribution_aipwEstimator_oracle {e m₀ m₁ : 𝒳 → ℝ}
    (hψ : Measurable (aipwScore T X Y e m₀ m₁)) (hψ2 : MemLp (aipwScore T X Y e m₀ m₁) 2 μ₁)
    (hind : iIndepFun O P) (hlaw : ∀ i, HasLaw (O i) μ₁ P) {τ : ℝ}
    (hτ : ∫ ω, aipwScore T X Y e m₀ m₁ ω ∂μ₁ = τ) {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 Var[aipwScore T X Y e m₀ m₁; μ₁].toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) *
      (aipwEstimator O T X Y (fun _ _ _ => e) (fun _ _ _ => m₀) (fun _ _ _ => m₁) n ω - τ))
      atTop Z (fun _ => P) P' := by
  set ψ := aipwScore T X Y e m₀ m₁
  have hindW : iIndepFun (fun i => ψ ∘ O i) P := hind.comp (fun _ => ψ) (fun _ => hψ)
  have hident : ∀ i, IdentDistrib (ψ ∘ O i) (ψ ∘ O 0) P P :=
    fun i => (identDistrib_of_hasLaw hlaw i).comp hψ
  have hvar : Var[ψ ∘ O 0; P] = Var[ψ; μ₁] := by
    rw [← variance_map hψ.aemeasurable (hlaw 0).aemeasurable, (hlaw 0).map_eq]
  have hmean : P[ψ ∘ O 0] = τ := by
    rw [(hlaw 0).integral_comp hψ.aestronglyMeasurable, hτ]
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub (X := fun i => ψ ∘ O i)
    (hvar ▸ hZ) ((hlaw 0).memLp_comp hψ2) hindW hident
  rw [hmean] at hclt
  refine hclt.congr (fun n => Eventually.of_forall fun ω => ?_) (Eventually.of_forall fun _ => rfl)
  simp only [aipwEstimator, aipwFittedScore_const, Function.comp_apply]
  exact (sqrt_mul_inv_mul_sub n _ τ).symm

/-- **Asymptotic variance of the AIPW estimator with fitted nuisances.** Let `ψ` be the score
at fixed nuisances `e, m₀, m₁` (the true ones in applications), square integrable, `τ = E[ψ]`,
and suppose the AIPW estimator with fitted nuisances `eₙ, m₀ₙ, m₁ₙ` is asymptotically equivalent
to the oracle estimator: `√n (τ̂ₙ - τ̂ₙ*) → 0` in probability (`hrem`, the conclusion of
Neyman orthogonality, cross-fitting and a product rate on the nuisance errors, taken as a
hypothesis). Then `√n (τ̂ₙ - τ) →ᵈ N(0, Var ψ)`: the asymptotic variance is `Var(φ)` for the
influence function `φ = ψ - τ`. -/
theorem tendstoInDistribution_aipwEstimator {e m₀ m₁ : 𝒳 → ℝ}
    {eₙ m₀ₙ m₁ₙ : ℕ → ℕ → Ω → 𝒳 → ℝ}
    (hψ : Measurable (aipwScore T X Y e m₀ m₁)) (hψ2 : MemLp (aipwScore T X Y e m₀ m₁) 2 μ₁)
    (hind : iIndepFun O P) (hlaw : ∀ i, HasLaw (O i) μ₁ P) {τ : ℝ}
    (hτ : ∫ ω, aipwScore T X Y e m₀ m₁ ω ∂μ₁ = τ) {Z : Ω' → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 Var[aipwScore T X Y e m₀ m₁; μ₁].toNNReal) P')
    (hfit : ∀ n i, AEMeasurable (aipwFittedScore O T X Y eₙ m₀ₙ m₁ₙ n i) P)
    (hrem : TendstoInMeasure P (fun (n : ℕ) ω => √(n : ℝ) *
      (aipwEstimator O T X Y eₙ m₀ₙ m₁ₙ n ω -
        aipwEstimator O T X Y (fun _ _ _ => e) (fun _ _ _ => m₀) (fun _ _ _ => m₁) n ω))
      atTop fun _ => 0) :
    TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) *
      (aipwEstimator O T X Y eₙ m₀ₙ m₁ₙ n ω - τ)) atTop Z (fun _ => P) P' := by
  have hA : ∀ n, AEMeasurable (aipwEstimator O T X Y eₙ m₀ₙ m₁ₙ n) P := fun n =>
    (Finset.aemeasurable_fun_sum _ fun i _ => hfit n i).const_mul _
  have hA' : ∀ n, AEMeasurable
      (aipwEstimator O T X Y (fun _ _ _ => e) (fun _ _ _ => m₀) (fun _ _ _ => m₁) n) P :=
    fun n => (Finset.aemeasurable_fun_sum _ fun i _ =>
      hψ.comp_aemeasurable (hlaw i).aemeasurable).const_mul _
  have hR : ∀ n : ℕ, AEMeasurable (fun ω => √(n : ℝ) * (aipwEstimator O T X Y eₙ m₀ₙ m₁ₙ n ω -
      aipwEstimator O T X Y (fun _ _ _ => e) (fun _ _ _ => m₀) (fun _ _ _ => m₁) n ω)) P :=
    fun n => ((hA n).sub (hA' n)).const_mul _
  refine ((tendstoInDistribution_aipwEstimator_oracle hψ hψ2 hind hlaw hτ
    hZ).add_of_tendstoInMeasure_const hrem hR).congr (fun n => Eventually.of_forall fun ω => ?_)
    (Eventually.of_forall fun ω => add_zero _)
  simp only [Pi.add_apply]
  ring

/-- **Consistency of the plug-in variance estimator.** Let `ψ` be the score at fixed nuisances
`e, m₀, m₁`, square integrable under the unit law `μ₁`, and suppose the fitted scores are
consistent for `ψ` in empirical `L²`: `n⁻¹ ∑_{i < n} (ψ̂ₙᵢ - ψ(Oᵢ))² → 0` in probability. Then the
sample variance of the estimated influence-function values converges in probability to
`Var ψ = Var φ`. -/
theorem tendstoInMeasure_aipwVarianceEstimator {e m₀ m₁ : 𝒳 → ℝ}
    {eₙ m₀ₙ m₁ₙ : ℕ → ℕ → Ω → 𝒳 → ℝ}
    (hψ : Measurable (aipwScore T X Y e m₀ m₁)) (hψ2 : MemLp (aipwScore T X Y e m₀ m₁) 2 μ₁)
    (hind : iIndepFun O P) (hlaw : ∀ i, HasLaw (O i) μ₁ P)
    (hL2 : TendstoInMeasure P (fun (n : ℕ) ω => (n : ℝ)⁻¹ * ∑ i ∈ range n,
      (aipwFittedScore O T X Y eₙ m₀ₙ m₁ₙ n i ω - aipwScore T X Y e m₀ m₁ (O i ω)) ^ 2)
      atTop fun _ => 0) :
    TendstoInMeasure P (aipwVarianceEstimator O T X Y eₙ m₀ₙ m₁ₙ) atTop
      fun _ => Var[aipwScore T X Y e m₀ m₁; μ₁] := by
  set ψ := aipwScore T X Y e m₀ m₁ with hψdef
  have : IsProbabilityMeasure μ₁ := (hlaw 0).isProbabilityMeasure_iff.1 inferInstance
  have hg : Measurable fun x => ψ x ^ 2 := hψ.pow_const 2
  have hident : ∀ i, IdentDistrib (ψ ∘ O i) (ψ ∘ O 0) P P :=
    fun i => (identDistrib_of_hasLaw hlaw i).comp hψ
  have hident2 : ∀ i, IdentDistrib ((fun x => ψ x ^ 2) ∘ O i) ((fun x => ψ x ^ 2) ∘ O 0) P P :=
    fun i => (identDistrib_of_hasLaw hlaw i).comp hg
  have hint : Integrable (ψ ∘ O 0) P := (hlaw 0).integrable_comp (hψ2.integrable one_le_two)
  have hint2 : Integrable ((fun x => ψ x ^ 2) ∘ O 0) P :=
    (hlaw 0).integrable_comp hψ2.integrable_sq
  have h1 := strong_law_ae_real (fun i => ψ ∘ O i) hint
    (fun i j hij => (hind.comp (fun _ => ψ) (fun _ => hψ)).indepFun hij) hident
  have h2 := strong_law_ae_real (fun i => (fun x => ψ x ^ 2) ∘ O i) hint2
    (fun i j hij => (hind.comp (fun _ => fun x => ψ x ^ 2) (fun _ => hg)).indepFun hij) hident2
  rw [(hlaw 0).integral_comp hψ.aestronglyMeasurable] at h1
  rw [(hlaw 0).integral_comp hg.aestronglyMeasurable] at h2
  set m := ∫ x, ψ x ∂μ₁
  set E₂ := ∫ x, ψ x ^ 2 ∂μ₁
  have hv : Var[ψ; μ₁] = E₂ - m ^ 2 := by
    rw [variance_eq_sub hψ2]; rfl
  have hb : ∀ i, AEMeasurable (fun ω => ψ (O i ω)) P := fun i =>
    hψ.comp_aemeasurable (hlaw i).aemeasurable
  have hBB : TendstoInMeasure P (fun (n : ℕ) ω => ((n : ℝ)⁻¹ * ∑ i ∈ range n, ψ (O i ω) ^ 2,
      (n : ℝ)⁻¹ * ∑ i ∈ range n, ψ (O i ω))) atTop fun _ => (E₂, m) := by
    refine tendstoInMeasure_of_tendsto_ae (fun n => ?_) ?_
    · exact (((Finset.aemeasurable_fun_sum _ fun i _ => (hb i).pow_const 2).const_mul _).prodMk
        ((Finset.aemeasurable_fun_sum _ fun i _ => hb i).const_mul _)).aestronglyMeasurable
    · filter_upwards [h1, h2] with ω hω1 hω2
      simp only [Function.comp_apply, div_eq_inv_mul] at hω1 hω2
      exact hω2.prodMk_nhds hω1
  set G : (ℝ × ℝ) × ℝ → ℝ := fun p => |p.1.1 - p.1.2 ^ 2 - Var[ψ; μ₁]| +
    (2 * (√p.1.1 * √p.2) + 2 * p.2 + 2 * (|p.1.2| * √p.2)) with hGdef
  have hGc : Continuous G := by
    simp only [hGdef]
    fun_prop
  have hG0 : G ((E₂, m), 0) = 0 := by simp [hGdef, hv]
  have hGlim := (tendstoInMeasure_prodMk hBB hL2).comp_const_of_continuousAt hGc.continuousAt
  rw [hG0] at hGlim
  refine tendstoInMeasure_of_abs_sub_le hGlim ?_
  filter_upwards [eventually_gt_atTop 0] with n hn ω
  have hW := abs_empiricalVar_sub_le hn (fun i => aipwFittedScore O T X Y eₙ m₀ₙ m₁ₙ n i ω)
    (fun i => ψ (O i ω))
  have htri := abs_sub_le (aipwVarianceEstimator O T X Y eₙ m₀ₙ m₁ₙ n ω)
    ((n : ℝ)⁻¹ * ∑ i ∈ range n, ψ (O i ω) ^ 2 - ((n : ℝ)⁻¹ * ∑ i ∈ range n, ψ (O i ω)) ^ 2)
    (Var[ψ; μ₁])
  simp only [aipwVarianceEstimator] at htri ⊢
  simp only [hGdef]
  linarith

/-- **Consistency of the variance estimator, fixed nuisances.** With fixed nuisances the
sample variance of the scores converges in probability to `Var ψ`. -/
theorem tendstoInMeasure_aipwVarianceEstimator_oracle {e m₀ m₁ : 𝒳 → ℝ}
    (hψ : Measurable (aipwScore T X Y e m₀ m₁)) (hψ2 : MemLp (aipwScore T X Y e m₀ m₁) 2 μ₁)
    (hind : iIndepFun O P) (hlaw : ∀ i, HasLaw (O i) μ₁ P) :
    TendstoInMeasure P
      (aipwVarianceEstimator O T X Y (fun _ _ _ => e) (fun _ _ _ => m₀) (fun _ _ _ => m₁)) atTop
      fun _ => Var[aipwScore T X Y e m₀ m₁; μ₁] := by
  refine tendstoInMeasure_aipwVarianceEstimator hψ hψ2 hind hlaw ?_
  simp only [aipwFittedScore_const, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, sum_const_zero, mul_zero]
  exact tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
    (ae_of_all _ fun _ => tendsto_const_nhds)

/-- **Asymptotic coverage of the AIPW Wald interval.** Under the hypotheses of
`tendstoInDistribution_aipwEstimator` and `tendstoInMeasure_aipwVarianceEstimator`, and
`Var φ ≠ 0`, the probability that the Wald interval `τ̂ₙ ± z √(σ̂ₙ²) / √n` contains `τ = E[ψ]`
tends to `P(-z ≤ N(0, 1) ≤ z)`. For `z` the `1 - α/2` standard-normal quantile this is
`1 - α`. -/
theorem tendsto_coverage_aipwWaldInterval {e m₀ m₁ : 𝒳 → ℝ}
    {eₙ m₀ₙ m₁ₙ : ℕ → ℕ → Ω → 𝒳 → ℝ}
    (hψ : Measurable (aipwScore T X Y e m₀ m₁)) (hψ2 : MemLp (aipwScore T X Y e m₀ m₁) 2 μ₁)
    (hind : iIndepFun O P) (hlaw : ∀ i, HasLaw (O i) μ₁ P) {τ : ℝ}
    (hτ : ∫ ω, aipwScore T X Y e m₀ m₁ ω ∂μ₁ = τ)
    (hvar : Var[aipwScore T X Y e m₀ m₁; μ₁] ≠ 0)
    (hfit : ∀ n i, AEMeasurable (aipwFittedScore O T X Y eₙ m₀ₙ m₁ₙ n i) P)
    (hrem : TendstoInMeasure P (fun (n : ℕ) ω => √(n : ℝ) *
      (aipwEstimator O T X Y eₙ m₀ₙ m₁ₙ n ω -
        aipwEstimator O T X Y (fun _ _ _ => e) (fun _ _ _ => m₀) (fun _ _ _ => m₁) n ω))
      atTop fun _ => 0)
    (hL2 : TendstoInMeasure P (fun (n : ℕ) ω => (n : ℝ)⁻¹ * ∑ i ∈ range n,
      (aipwFittedScore O T X Y eₙ m₀ₙ m₁ₙ n i ω - aipwScore T X Y e m₀ m₁ (O i ω)) ^ 2)
      atTop fun _ => 0) (z : ℝ) :
    Tendsto (fun n : ℕ => P.real {ω | τ ∈ waldInterval (aipwEstimator O T X Y eₙ m₀ₙ m₁ₙ n ω)
      (√(aipwVarianceEstimator O T X Y eₙ m₀ₙ m₁ₙ n ω) / √(n : ℝ)) z}) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Icc (-z) z))) := by
  set v := Var[aipwScore T X Y e m₀ m₁; μ₁]
  have hv0 : 0 ≤ v := variance_nonneg _ _
  have hv : v.toNNReal ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]; exact lt_of_le_of_ne hv0 (Ne.symm hvar)
  have hlim := tendstoInDistribution_aipwEstimator (Z := id) hψ hψ2 hind hlaw hτ HasLaw.id hfit hrem
  have hA : ∀ n, AEMeasurable (aipwEstimator O T X Y eₙ m₀ₙ m₁ₙ n) P := fun n =>
    (Finset.aemeasurable_fun_sum _ fun i _ => hfit n i).const_mul _
  have hse_meas : ∀ n, AEMeasurable (fun ω => √(aipwVarianceEstimator O T X Y eₙ m₀ₙ m₁ₙ n ω)) P :=
    fun n => by
      simp only [aipwVarianceEstimator_eq]
      exact ((Finset.aemeasurable_fun_sum _ fun i _ =>
        ((hfit n i).sub (hA n)).pow_const 2).const_mul _).sqrt
  have hse : TendstoInMeasure P (fun n ω => √(aipwVarianceEstimator O T X Y eₙ m₀ₙ m₁ₙ n ω))
      atTop fun _ => √(v.toNNReal : ℝ) := by
    rw [Real.coe_toNNReal _ hv0]
    exact (tendstoInMeasure_aipwVarianceEstimator hψ hψ2 hind hlaw hL2).comp_const_of_continuousAt
      Real.continuous_sqrt.continuousAt
  exact tendsto_coverage_waldInterval hv z hlim HasLaw.id hse hse_meas

end Asymptotics

section ATE

variable {Ω₁ 𝒳 : Type*} {mΩ₁ : MeasurableSpace Ω₁} [m𝒳 : MeasurableSpace 𝒳] {μ : Measure Ω₁}

/-- **The AIPW score at the true nuisances has mean the average treatment effect.** Under
consistency, mean exchangeability, integrability and `ε ≤ e(X) ≤ 1 - ε`, if the propensity is
correct, `e(X) = P(T | X)` a.e., then `E[ψ] = E[Y₁ - Y₀]` for any measurable integrable outcome
regressions. This discharges the centering hypothesis `hτ` of the limit theorems above with
`τ = E[Y₁ - Y₀]`; it is `DoubleRobustness.integral_aipwScoreOfSigma_of_propensity` with
`σ(X)`-measurable nuisances. -/
theorem integral_aipwScore_eq_ate [IsFiniteMeasure μ] {T : Set Ω₁} (hT : MeasurableSet T)
    {X : Ω₁ → 𝒳} (hX : Measurable X) {Y Y₀ Y₁ : Ω₁ → ℝ} (hcons : Y =ᵐ[μ] observed T Y₀ Y₁)
    (hY₀ : Integrable Y₀ μ) (hY₁ : Integrable Y₁ μ)
    (hex₁ : μ[T.indicator Y₁ | m𝒳.comap X] =ᵐ[μ]
      μ[T.indicator 1 | m𝒳.comap X] * μ[Y₁ | m𝒳.comap X])
    (hex₀ : μ[Tᶜ.indicator Y₀ | m𝒳.comap X] =ᵐ[μ]
      (1 - μ[T.indicator 1 | m𝒳.comap X]) * μ[Y₀ | m𝒳.comap X])
    {e m₀ m₁ : 𝒳 → ℝ} (he : Measurable e) (hm₀ : Measurable m₀) (hm₁ : Measurable m₁)
    (hm₀i : Integrable (fun ω => m₀ (X ω)) μ) (hm₁i : Integrable (fun ω => m₁ (X ω)) μ)
    {ε : ℝ} (hε : 0 < ε) (heε : ∀ᵐ ω ∂μ, ε ≤ e (X ω) ∧ e (X ω) ≤ 1 - ε)
    (hprop : (fun ω => e (X ω)) =ᵐ[μ] μ[T.indicator 1 | m𝒳.comap X]) :
    ∫ ω, aipwScore T X Y e m₀ m₁ ω ∂μ = ∫ ω, (Y₁ ω - Y₀ ω) ∂μ := by
  have hXm : Measurable[m𝒳.comap X] X := comap_measurable X
  exact integral_aipwScoreOfSigma_of_propensity hX.comap_le hT hcons hY₀ hY₁ hex₁ hex₀
    (he.comp hXm).stronglyMeasurable (hm₀.comp hXm).stronglyMeasurable
    (hm₁.comp hXm).stronglyMeasurable hm₀i hm₁i hε heε hprop

end ATE

end MathlibExt.Probability.Causality.AugmentedIPW.Variance
