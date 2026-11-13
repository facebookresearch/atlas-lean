/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.Adaptive.RandomizedEstimand
public import MathlibExt.Probability.Statistics.MultipleTesting.Holm

/-!
# Holm, BH under PRDS and Benjamini–Yekutieli for zero-ATE endpoints

`MathlibExt.Probability.Statistics.MultipleTesting.Adaptive.RandomizedEstimand` sets up `m`
endpoints sharing one binary treatment `T` and a finitely-valued covariate `X`. The true causal
nulls `ateNulls μ Y₀ Y₁` are the endpoints with zero, integrable average treatment effect, and
p-values calibrated for the observed-data IPW null (`IsIPWNullCalibrated`) are valid on every
causal null once each causal null is strongly ignorable given `X`
(`isValidPValue_of_mem_ateNulls`). That file connects Benjamini–Hochberg under independence and
Bonferroni to the causal nulls. This file connects the three remaining procedures of the
repository:

* **Holm** (Holm 1979): the step-down procedure controls the family-wise error rate over the
  causal nulls at `α`, with no assumption on the dependence of the p-values.
* **BH under PRDS** (Benjamini–Yekutieli 2001, Theorem 1.2): BH at level `q` controls the FDR over
  the causal nulls at `q |ateNulls| / m` when the p-value vector is PRDS on the causal nulls.
* **Benjamini–Yekutieli** (2001, Theorem 1.3): BH at level `q / H_m` controls the FDR over the
  causal nulls at `q |ateNulls| / m` under arbitrary dependence.

In each case the causal assumptions enter only through `isValidPValue_of_mem_ateNulls`; the merged
procedure theorems (`measure_holm_familywiseError_le`,
`integral_falseDiscoveryProportion_bhRejections_le_of_isPRDSOn`,
`integral_falseDiscoveryProportion_bhRejections_le_of_arbitrary_dependence`) are applied with the
null set `ateNulls μ Y₀ Y₁`. In particular the PRDS hypothesis is the merged `IsPRDSOn` on the
causal nulls, a condition on the joint law of the p-values; nothing here derives it from the
causal model.

## Main results

* `measure_holm_ateNulls_familywiseError_le`: Holm FWER over the causal nulls is at most `α`.
* `integral_falseDiscoveryProportion_bhRejections_ateNulls_le_of_isPRDSOn`: BH FDR over the
  causal nulls is at most `q |ateNulls| / m` under PRDS on the causal nulls.
* `integral_falseDiscoveryProportion_byRejections_ateNulls_le`: BH at level `q / H_m` has FDR
  over the causal nulls at most `q |ateNulls| / m` under arbitrary dependence.
* `measure_holm_ateNulls_familywiseError_le_of_indep`,
  `integral_falseDiscoveryProportion_bhRejections_ateNulls_le_of_isPRDSOn_of_indep`,
  `integral_falseDiscoveryProportion_byRejections_ateNulls_le_of_indep`: the same three bounds in a
  randomized trial (treatment independent of the potential outcomes, `0 < P(T) < 1`), via
  `stronglyIgnorable_of_indepFun` and the trivial covariate.
* Positivity failure (the example of `RandomizedEstimand`: one unit, nobody treated,
  `Y₀ = Y₁ = 1`): `holmRejections_untreated` and `measure_holm_familywiseError_untreated` (Holm
  FWER over the causal nulls is `1`), `isPRDSOn_untreated` (the always-reject p-value is PRDS, so
  PRDS does not substitute for positivity) and
  `integral_falseDiscoveryProportion_byRejections_untreated` (the Benjamini–Yekutieli FDR is `1`).

## Not covered

No power statement and no sample-size formula. The construction of calibrated p-values and the
verification of PRDS for a concrete test statistic (for example, one-sided Wald statistics of IPW
estimators with positively correlated errors) are hypotheses, not proved here.

## References

* S. Holm, *A simple sequentially rejective multiple test procedure*, Scand. J. Statist. 6
  (1979), 65–70.
* Y. Benjamini and D. Yekutieli, *The control of the false discovery rate in multiple testing
  under dependency*, Ann. Statist. 29 (2001), 1165–1188, Theorems 1.2 and 1.3.
* P. R. Rosenbaum and D. B. Rubin, *The central role of the propensity score in observational
  studies for causal effects*, Biometrika 70(1) (1983), 41–55.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.MultipleTesting

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Causality

variable {Ω 𝒳 : Type*} [MeasurableSpace Ω] {m : ℕ}

section Identification

variable [Finite 𝒳] [MeasurableSpace 𝒳] [MeasurableSingletonClass 𝒳] {μ : Measure Ω}

/-- **Holm controls the FWER over the causal nulls.** Under strong ignorability given `X` of
every endpoint with zero average treatment effect (nothing is assumed about the others), with
p-values calibrated for the observed-data IPW null and no assumption on their dependence, the
probability that Holm's step-down procedure at level `α ∈ [0, 1]` rejects some endpoint with zero
average treatment effect is at most `α`. The merged `measure_holm_familywiseError_le` is applied
to the causal nulls via `isValidPValue_of_mem_ateNulls`. No power claim is made.

Source: Holm (1979); identification as in Rosenbaum & Rubin (1983). -/
theorem measure_holm_ateNulls_familywiseError_le [IsProbabilityMeasure μ]
    {T : Set Ω} (hT : MeasurableSet T) {X : Ω → 𝒳} (hX : Measurable X)
    {Y₀ Y₁ : Fin m → Ω → ℝ} (hY₀ : ∀ j ∈ ateNulls μ Y₀ Y₁, Measurable (Y₀ j))
    (hY₁ : ∀ j ∈ ateNulls μ Y₀ Y₁, Measurable (Y₁ j))
    (hY₀i : ∀ j ∈ ateNulls μ Y₀ Y₁, Integrable (Y₀ j) μ)
    (hY₁i : ∀ j ∈ ateNulls μ Y₀ Y₁, Integrable (Y₁ j) μ)
    (hign : ∀ j ∈ ateNulls μ Y₀ Y₁, StronglyIgnorable μ T (fun ω => (Y₀ j ω, Y₁ j ω)) X)
    {p : Fin m → Ω → ℝ}
    (hcal : IsIPWNullCalibrated μ T X (fun j => observed T (Y₀ j) (Y₁ j)) p)
    {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    μ {ω | (holmRejections α (fun i => p i ω) ∩ ateNulls μ Y₀ Y₁).Nonempty} ≤
      ENNReal.ofReal α :=
  measure_holm_familywiseError_le μ p _
    (isValidPValue_of_mem_ateNulls hT hX hY₀ hY₁ hY₀i hY₁i hign hcal) hα₀ hα₁

/-- **BH under PRDS controls the FDR over the causal nulls.** Under strong ignorability given `X`
of every endpoint with zero average treatment effect, with measurable p-values calibrated for the
observed-data IPW null and PRDS on the causal nulls (`IsPRDSOn μ p (ateNulls μ Y₀ Y₁)`), the
Benjamini–Hochberg procedure at level `q ∈ [0, 1]` has false discovery rate at most
`q |ateNulls| / m`, the false discoveries being the rejected endpoints with zero average treatment
effect. This generalizes `integral_falseDiscoveryProportion_bhRejections_ateNulls_le`
(independent p-values are PRDS, `isPRDSOn_of_iIndepFun`). No power claim is made.

Source: Benjamini & Yekutieli (2001), Theorem 1.2. -/
theorem integral_falseDiscoveryProportion_bhRejections_ateNulls_le_of_isPRDSOn
    [IsProbabilityMeasure μ] {T : Set Ω} (hT : MeasurableSet T) {X : Ω → 𝒳} (hX : Measurable X)
    {Y₀ Y₁ : Fin m → Ω → ℝ} (hY₀ : ∀ j ∈ ateNulls μ Y₀ Y₁, Measurable (Y₀ j))
    (hY₁ : ∀ j ∈ ateNulls μ Y₀ Y₁, Measurable (Y₁ j))
    (hY₀i : ∀ j ∈ ateNulls μ Y₀ Y₁, Integrable (Y₀ j) μ)
    (hY₁i : ∀ j ∈ ateNulls μ Y₀ Y₁, Integrable (Y₁ j) μ)
    (hign : ∀ j ∈ ateNulls μ Y₀ Y₁, StronglyIgnorable μ T (fun ω => (Y₀ j ω, Y₁ j ω)) X)
    {p : Fin m → Ω → ℝ} (hp : ∀ i, Measurable (p i))
    (hprds : IsPRDSOn μ p (ateNulls μ Y₀ Y₁))
    (hcal : IsIPWNullCalibrated μ T X (fun j => observed T (Y₀ j) (Y₁ j)) p)
    (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∫ ω, falseDiscoveryProportion (ateNulls μ Y₀ Y₁) (bhRejections q fun i => p i ω) ∂μ ≤
      q * (ateNulls μ Y₀ Y₁).card / m :=
  integral_falseDiscoveryProportion_bhRejections_le_of_isPRDSOn μ p hp _ hprds
    (isValidPValue_of_mem_ateNulls hT hX hY₀ hY₁ hY₀i hY₁i hign hcal) q hq₀ hq₁

/-- **Benjamini–Yekutieli controls the FDR over the causal nulls under arbitrary dependence.**
Under strong ignorability given `X` of every endpoint with zero average treatment effect, with
measurable p-values calibrated for the observed-data IPW null and no assumption on their joint
law, the Benjamini–Hochberg procedure at the reduced level `q / H_m` (`H_m` the harmonic number)
has false discovery rate over the causal nulls at most `q |ateNulls| / m`, for `q ∈ [0, 1]`.
No power claim is made.

Source: Benjamini & Yekutieli (2001), Theorem 1.3. -/
theorem integral_falseDiscoveryProportion_byRejections_ateNulls_le [IsProbabilityMeasure μ]
    {T : Set Ω} (hT : MeasurableSet T) {X : Ω → 𝒳} (hX : Measurable X)
    {Y₀ Y₁ : Fin m → Ω → ℝ} (hY₀ : ∀ j ∈ ateNulls μ Y₀ Y₁, Measurable (Y₀ j))
    (hY₁ : ∀ j ∈ ateNulls μ Y₀ Y₁, Measurable (Y₁ j))
    (hY₀i : ∀ j ∈ ateNulls μ Y₀ Y₁, Integrable (Y₀ j) μ)
    (hY₁i : ∀ j ∈ ateNulls μ Y₀ Y₁, Integrable (Y₁ j) μ)
    (hign : ∀ j ∈ ateNulls μ Y₀ Y₁, StronglyIgnorable μ T (fun ω => (Y₀ j ω, Y₁ j ω)) X)
    {p : Fin m → Ω → ℝ} (hp : ∀ i, Measurable (p i))
    (hcal : IsIPWNullCalibrated μ T X (fun j => observed T (Y₀ j) (Y₁ j)) p)
    (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∫ ω, falseDiscoveryProportion (ateNulls μ Y₀ Y₁)
        (bhRejections (q / harmonic m) fun i => p i ω) ∂μ ≤
      q * (ateNulls μ Y₀ Y₁).card / m :=
  integral_falseDiscoveryProportion_bhRejections_le_of_arbitrary_dependence μ p hp _
    (isValidPValue_of_mem_ateNulls hT hX hY₀ hY₁ hY₀i hY₁i hign hcal) q hq₀ hq₁

end Identification

/-! ### Randomized trials (treatment independent of the potential outcomes)

Bernoulli-type assignment in a superpopulation, as in `RandomizedEstimand`: with the trivial
covariate, independence of the treatment indicator from the potential outcomes and
`0 < P(T) < 1` give strong ignorability (`stronglyIgnorable_of_indepFun`), and the observed-data
null is the Horvitz–Thompson null (`ipwContrast_const`). -/

section Randomized

variable {μ : Measure Ω}

/-- **Holm FWER control in a randomized trial.** If the treatment indicator is independent of the
potential outcomes of every endpoint with zero average treatment effect, `0 < P(T) < 1`, and the
p-values are calibrated for the observed-data Horvitz–Thompson null (arbitrary dependence),
Holm at level `α ∈ [0, 1]` rejects some endpoint with zero average treatment effect with
probability at most `α`. -/
theorem measure_holm_ateNulls_familywiseError_le_of_indep [IsProbabilityMeasure μ] {T : Set Ω}
    (hT : MeasurableSet T) (hT₀ : 0 < μ.real T) (hT₁ : μ.real T < 1) {Y₀ Y₁ : Fin m → Ω → ℝ}
    (hY₀ : ∀ j ∈ ateNulls μ Y₀ Y₁, Measurable (Y₀ j))
    (hY₁ : ∀ j ∈ ateNulls μ Y₀ Y₁, Measurable (Y₁ j))
    (hY₀i : ∀ j ∈ ateNulls μ Y₀ Y₁, Integrable (Y₀ j) μ)
    (hY₁i : ∀ j ∈ ateNulls μ Y₀ Y₁, Integrable (Y₁ j) μ)
    (hind : ∀ j ∈ ateNulls μ Y₀ Y₁,
      IndepFun (T.indicator (1 : Ω → ℝ)) (fun ω => (Y₀ j ω, Y₁ j ω)) μ)
    {p : Fin m → Ω → ℝ}
    (hcal : IsIPWNullCalibrated μ T (fun _ : Ω => ()) (fun j => observed T (Y₀ j) (Y₁ j)) p)
    {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    μ {ω | (holmRejections α (fun i => p i ω) ∩ ateNulls μ Y₀ Y₁).Nonempty} ≤
      ENNReal.ofReal α :=
  measure_holm_ateNulls_familywiseError_le hT measurable_const hY₀ hY₁ hY₀i hY₁i
    (fun j hj => stronglyIgnorable_of_indepFun (hind j hj) hT₀ hT₁) hcal hα₀ hα₁

/-- **BH under PRDS in a randomized trial.** With the treatment indicator independent of the
potential outcomes of every zero-ATE endpoint, `0 < P(T) < 1`, and measurable p-values that are
PRDS on the causal nulls and calibrated for the observed-data Horvitz–Thompson null, BH at level
`q ∈ [0, 1]` has FDR over the causal nulls at most `q |ateNulls| / m`. -/
theorem integral_falseDiscoveryProportion_bhRejections_ateNulls_le_of_isPRDSOn_of_indep
    [IsProbabilityMeasure μ] {T : Set Ω} (hT : MeasurableSet T) (hT₀ : 0 < μ.real T)
    (hT₁ : μ.real T < 1) {Y₀ Y₁ : Fin m → Ω → ℝ}
    (hY₀ : ∀ j ∈ ateNulls μ Y₀ Y₁, Measurable (Y₀ j))
    (hY₁ : ∀ j ∈ ateNulls μ Y₀ Y₁, Measurable (Y₁ j))
    (hY₀i : ∀ j ∈ ateNulls μ Y₀ Y₁, Integrable (Y₀ j) μ)
    (hY₁i : ∀ j ∈ ateNulls μ Y₀ Y₁, Integrable (Y₁ j) μ)
    (hind : ∀ j ∈ ateNulls μ Y₀ Y₁,
      IndepFun (T.indicator (1 : Ω → ℝ)) (fun ω => (Y₀ j ω, Y₁ j ω)) μ)
    {p : Fin m → Ω → ℝ} (hp : ∀ i, Measurable (p i))
    (hprds : IsPRDSOn μ p (ateNulls μ Y₀ Y₁))
    (hcal : IsIPWNullCalibrated μ T (fun _ : Ω => ()) (fun j => observed T (Y₀ j) (Y₁ j)) p)
    (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∫ ω, falseDiscoveryProportion (ateNulls μ Y₀ Y₁) (bhRejections q fun i => p i ω) ∂μ ≤
      q * (ateNulls μ Y₀ Y₁).card / m :=
  integral_falseDiscoveryProportion_bhRejections_ateNulls_le_of_isPRDSOn hT measurable_const hY₀
    hY₁ hY₀i hY₁i (fun j hj => stronglyIgnorable_of_indepFun (hind j hj) hT₀ hT₁) hp hprds hcal
    q hq₀ hq₁

/-- **Benjamini–Yekutieli in a randomized trial.** With the treatment indicator independent of the
potential outcomes of every zero-ATE endpoint, `0 < P(T) < 1`, and measurable p-values calibrated
for the observed-data Horvitz–Thompson null (arbitrary dependence), BH at level `q / H_m` has FDR
over the causal nulls at most `q |ateNulls| / m`. -/
theorem integral_falseDiscoveryProportion_byRejections_ateNulls_le_of_indep
    [IsProbabilityMeasure μ] {T : Set Ω} (hT : MeasurableSet T) (hT₀ : 0 < μ.real T)
    (hT₁ : μ.real T < 1) {Y₀ Y₁ : Fin m → Ω → ℝ}
    (hY₀ : ∀ j ∈ ateNulls μ Y₀ Y₁, Measurable (Y₀ j))
    (hY₁ : ∀ j ∈ ateNulls μ Y₀ Y₁, Measurable (Y₁ j))
    (hY₀i : ∀ j ∈ ateNulls μ Y₀ Y₁, Integrable (Y₀ j) μ)
    (hY₁i : ∀ j ∈ ateNulls μ Y₀ Y₁, Integrable (Y₁ j) μ)
    (hind : ∀ j ∈ ateNulls μ Y₀ Y₁,
      IndepFun (T.indicator (1 : Ω → ℝ)) (fun ω => (Y₀ j ω, Y₁ j ω)) μ)
    {p : Fin m → Ω → ℝ} (hp : ∀ i, Measurable (p i))
    (hcal : IsIPWNullCalibrated μ T (fun _ : Ω => ()) (fun j => observed T (Y₀ j) (Y₁ j)) p)
    (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∫ ω, falseDiscoveryProportion (ateNulls μ Y₀ Y₁)
        (bhRejections (q / harmonic m) fun i => p i ω) ∂μ ≤
      q * (ateNulls μ Y₀ Y₁).card / m :=
  integral_falseDiscoveryProportion_byRejections_ateNulls_le hT measurable_const hY₀ hY₁ hY₀i
    hY₁i (fun j hj => stronglyIgnorable_of_indepFun (hind j hj) hT₀ hT₁) hp hcal q hq₀ hq₁

end Randomized

/-! ### Positivity failure: the conclusions do not follow

The example of `RandomizedEstimand`: one unit, nobody treated, trivial covariate, one endpoint
with `Y₀ = Y₁ = 1`. The endpoint is a causal null (`ateNulls_untreated`) but positivity fails
(`not_stronglyIgnorable_untreated`), and the always-reject p-value `p ≡ 0` is calibrated for the
observed-data null (`isIPWNullCalibrated_untreated`). Holm's FWER and the FDR of BH at any level,
in particular the Benjamini–Yekutieli level `q / H_1`, are then `1`. The p-value is PRDS, so the
PRDS hypothesis does not replace positivity. -/

section PositivityFailure

/-- Holm at level `α ≥ 0` rejects the single endpoint when its p-value is `0`. -/
theorem holmRejections_untreated {α : ℝ} (hα : 0 ≤ α) :
    holmRejections α (fun _ : Fin 1 => (0 : ℝ)) = Finset.univ := by
  have hall : ∀ t : ℝ, 0 ≤ t → numBelow (fun _ : Fin 1 => (0 : ℝ)) t = 1 := fun t ht => by
    rw [numBelow, Finset.filter_true_of_mem fun _ _ => ht]
    rfl
  have h1 : 1 ≤ holmIndex α (fun _ : Fin 1 => (0 : ℝ)) := by
    refine le_holmIndex le_rfl fun k hk => ?_
    obtain rfl : k = 1 := le_antisymm (Finset.mem_Icc.1 hk).2 (Finset.mem_Icc.1 hk).1
    rw [hall _ (by norm_num [hα])]
  have hidx : holmIndex α (fun _ : Fin 1 => (0 : ℝ)) = 1 :=
    le_antisymm (holmIndex_le _ _) h1
  ext i
  simp only [holmRejections, hidx, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  norm_num [hα]

/-- **Holm error control fails without positivity**: in the example the probability that Holm
rejects a causal null is `1`, whatever the level `α ≥ 0`; for `α < 1` this exceeds `α`. -/
theorem measure_holm_familywiseError_untreated {α : ℝ} (hα : 0 ≤ α) :
    Measure.dirac () {_ω : Unit | (holmRejections α (fun _ => (0 : ℝ)) ∩
      ateNulls (Measure.dirac ()) untreatedOutcome untreatedOutcome).Nonempty} = 1 := by
  simp [ateNulls_untreated, holmRejections_untreated hα]

/-- The always-reject p-value of the example is PRDS on the causal nulls: the p-value vector is a
monotone function of each coordinate (`isPRDSOn_of_monotone_comp`). -/
theorem isPRDSOn_untreated :
    IsPRDSOn (Measure.dirac ()) (fun (_ : Fin 1) (_ : Unit) => (0 : ℝ))
      (ateNulls (Measure.dirac ()) untreatedOutcome untreatedOutcome) :=
  isPRDSOn_of_monotone_comp _ _ (fun _ => measurable_const) _ fun _ _ =>
    ⟨fun x _ => x, fun _ _ h _ => h, fun _ => rfl⟩

/-- **Benjamini–Yekutieli error control fails without positivity**: in the example the FDR over
the causal nulls of BH at level `q / H_1` is `1`, whatever `q ≥ 0`. -/
theorem integral_falseDiscoveryProportion_byRejections_untreated {q : ℝ} (hq : 0 ≤ q) :
    ∫ _, falseDiscoveryProportion (ateNulls (Measure.dirac ()) untreatedOutcome untreatedOutcome)
      (bhRejections (q / harmonic 1) fun _ => (0 : ℝ)) ∂(Measure.dirac ()) = 1 :=
  integral_falseDiscoveryProportion_bhRejections_untreated (by simpa using hq)

end PositivityFailure

end MathlibExt.Probability.Statistics.MultipleTesting
