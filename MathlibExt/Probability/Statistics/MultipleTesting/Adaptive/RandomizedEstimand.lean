/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.CausalIdentification
public import MathlibExt.Probability.Statistics.MultipleTesting.BenjaminiHochberg
public import MathlibExt.Probability.Statistics.MultipleTesting.Bonferroni

/-!
# Multiple testing of average treatment effects: error control through identification

`m` endpoints (or subgroup outcomes) `j` share one binary treatment `T` and one finitely-valued
covariate `X`; endpoint `j` has potential outcomes `Y₀ j, Y₁ j`. The causal null hypothesis for
`j` is that its average treatment effect vanishes, `E[Y₁ j - Y₀ j] = 0`; `ateNulls μ Y₀ Y₁` is the
set of endpoints for which it holds.

A test can only see the law of the observed data `(T, X, Y)`, `Y = observed T Y₀ Y₁`. What a test
can be calibrated for is therefore a null hypothesis about that law. We use the inverse
probability weighting (IPW) contrast of the observed outcome,
`ipwContrast μ T X Y = E[1_T Y / e(X) - 1_{Tᶜ} Y / (1 - e(X))]` with `e` the propensity score,
and call the p-values *calibrated for the observed-data null* (`IsIPWNullCalibrated`) when `p j`
is valid whenever the IPW contrast of endpoint `j`'s observed outcome vanishes.

The bridge from the causal null to the observed-data null is the identification theorem
`integral_ipw_ate` of `MathlibExt.Probability.Causality.CausalIdentification`: under consistency
(`Y = observed T Y₀ Y₁`), conditional exchangeability `T ⊥ (Y₀, Y₁) | X` and positivity
`0 < e(X) < 1` (together `StronglyIgnorable`), the IPW contrast equals the ATE. This is the only
place where the causal assumptions enter; once the true causal nulls are known to carry valid
p-values, the merged Benjamini–Hochberg and Bonferroni theorems are applied unchanged.

## Main definitions

* `ipwContrast μ T X Y`: the IPW contrast of an observed outcome `Y`, a functional of the
  observed-data law only.
* `ateNulls μ Y₀ Y₁`: the endpoints whose average treatment effect is zero.
* `IsIPWNullCalibrated μ T X Y p`: each `p j` is a valid p-value whenever the IPW contrast of the
  observed outcome `Y j` vanishes.

## Main results

* `ipwContrast_observed_eq_integral`: under strong ignorability the IPW contrast of the observed
  outcome is the ATE (a restatement of `integral_ipw_ate`).
* `isValidPValue_of_mem_ateNulls`: under strong ignorability for every endpoint with zero ATE
  (nothing assumed about the others), the p-values of the true causal nulls are valid.
* `integral_falseDiscoveryProportion_bhRejections_ateNulls_le`: BH at level `q` controls the
  FDR over the causal nulls at `q |ateNulls| / m` (independent p-values).
* `measure_bonferroni_ateNulls_familywiseError_le`: Bonferroni controls the FWER over the causal
  nulls at `α` (arbitrary dependence).
* Randomized trials: `stronglyIgnorable_of_indepFun` (a treatment independent of the potential
  outcomes, with `0 < P(T) < 1`, is strongly ignorable given the trivial covariate),
  `ipwContrast_const` (the IPW contrast is then the Horvitz–Thompson contrast with the design
  probability `π = P(T)`), and `integral_falseDiscoveryProportion_bhRejections_ateNulls_le_of_indep`
  (BH FDR control for a randomized trial, treatment independent of the potential outcomes).
* Positivity failure: `not_stronglyIgnorable_untreated` and
  `ipwContrast_untreated_eq_neg_one` (nobody treated: exchangeability holds, positivity fails,
  and the IPW contrast is `-1` while the ATE is `0`), `isIPWNullCalibrated_untreated` (the
  always-reject test is calibrated for the observed-data null there) and
  `integral_falseDiscoveryProportion_bhRejections_untreated` /
  `measure_bonferroni_familywiseError_untreated` (its FDR and FWER over the causal nulls are `1`,
  so neither conclusion holds at any level below `1`).

## Not covered

No power statement and no sample-size formula: power and sample-size optimization are kept
separate from validity, and nothing here depends on the false-null p-values beyond
measurability (and independence for BH). The construction of a p-value calibrated for the
observed-data null (for example by an asymptotic Wald test of the IPW estimator) is an explicit
hypothesis, not proved here.

The covariate `X` takes finitely many values, as `integral_ipw_ate` requires; the
general-covariate IPW identity `integral_ipw_treated_condExp` on main covers only the treated arm
and is not used. Only BH under independence and Bonferroni are connected to the causal nulls;
Holm, BH under PRDS and Benjamini–Yekutieli follow by the same one-line application of
`isValidPValue_of_mem_ateNulls` but are not stated here.

## References

* P. R. Rosenbaum and D. B. Rubin, *The central role of the propensity score in observational
  studies for causal effects*, Biometrika 70(1) (1983), 41–55.
* D. G. Horvitz and D. J. Thompson, *A generalization of sampling without replacement from a
  finite universe*, JASA 47(260) (1952), 663–685.
* Y. Benjamini and Y. Hochberg, *Controlling the false discovery rate: a practical and powerful
  approach to multiple testing*, J. Roy. Statist. Soc. Ser. B 57(1) (1995), 289–300.
* M. A. Hernán and J. M. Robins, *Causal Inference: What If*, Chapman & Hall/CRC (2020),
  Chapters 3 and 12 (identification conditions, positivity).
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.MultipleTesting

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Causality

variable {Ω 𝒳 : Type*} [MeasurableSpace Ω] {m : ℕ}

/-- The **inverse probability weighting contrast** of an observed outcome `Y`,
`E[1_T Y / e(X) - 1_{Tᶜ} Y / (1 - e(X))]`, where `e = propensity μ T X` is the propensity score.
It depends on the law of the observed data `(T, X, Y)` only, so a null hypothesis
`ipwContrast μ T X Y = 0` is one a test can be calibrated for.

Source: the left-hand side of `integral_ipw_ate` (Horvitz & Thompson 1952; Rosenbaum 1987). -/
noncomputable def ipwContrast (μ : Measure Ω) (T : Set Ω) (X : Ω → 𝒳) (Y : Ω → ℝ) : ℝ :=
  ∫ ω, (T.indicator (fun ω => Y ω / propensity μ T X (X ω)) ω -
      Tᶜ.indicator (fun ω => Y ω / (1 - propensity μ T X (X ω))) ω) ∂μ

open Classical in
/-- The **true causal nulls**: the endpoints `j` whose average treatment effect
`E[Y₁ j - Y₀ j]` is zero. -/
noncomputable def ateNulls (μ : Measure Ω) (Y₀ Y₁ : Fin m → Ω → ℝ) : Finset (Fin m) :=
  Finset.univ.filter fun j => ∫ ω, (Y₁ j ω - Y₀ j ω) ∂μ = 0

/-- The p-values `p` are **calibrated for the observed-data IPW null** of the observed outcomes
`Y`: `p j` is a valid p-value whenever the IPW contrast of `Y j` vanishes. This is a property of
the test and of the observed-data law; it says nothing about potential outcomes. -/
def IsIPWNullCalibrated (μ : Measure Ω) (T : Set Ω) (X : Ω → 𝒳) (Y : Fin m → Ω → ℝ)
    (p : Fin m → Ω → ℝ) : Prop :=
  ∀ j, ipwContrast μ T X (Y j) = 0 → IsValidPValue μ (p j)

/-- Membership in the causal nulls: `j ∈ ateNulls μ Y₀ Y₁ ↔ E[Y₁ j - Y₀ j] = 0`. -/
theorem mem_ateNulls_iff {μ : Measure Ω} {Y₀ Y₁ : Fin m → Ω → ℝ} {j : Fin m} :
    j ∈ ateNulls μ Y₀ Y₁ ↔ ∫ ω, (Y₁ j ω - Y₀ j ω) ∂μ = 0 := by
  simp [ateNulls]

section Identification

variable [Finite 𝒳] [MeasurableSpace 𝒳] [MeasurableSingletonClass 𝒳] {μ : Measure Ω}

/-- **Identification**: under strong ignorability of `T` given `X` for `(Y₀, Y₁)` (consistency
is built into `observed`), the IPW contrast of the observed outcome is the average treatment
effect `E[Y₁ - Y₀]`. A restatement of `integral_ipw_ate`. -/
theorem ipwContrast_observed_eq_integral [IsProbabilityMeasure μ] {T : Set Ω}
    (hT : MeasurableSet T) {X : Ω → 𝒳} (hX : Measurable X) {Y₀ Y₁ : Ω → ℝ}
    (hY₀ : Measurable Y₀) (hY₁ : Measurable Y₁) (hY₀i : Integrable Y₀ μ)
    (hY₁i : Integrable Y₁ μ) (h : StronglyIgnorable μ T (fun ω => (Y₀ ω, Y₁ ω)) X) :
    ipwContrast μ T X (observed T Y₀ Y₁) = ∫ ω, (Y₁ ω - Y₀ ω) ∂μ :=
  integral_ipw_ate hT hX hY₀ hY₁ hY₀i hY₁i h

/-- **The causal nulls carry valid p-values.** If every endpoint with zero average treatment
effect is strongly ignorable given `X`
and the p-values are calibrated for the observed-data IPW null of the observed outcomes, then
`p j` is valid for every endpoint `j` with zero average treatment effect. Identification is the
step `ATE_j = 0 → ipwContrast_j = 0`. -/
theorem isValidPValue_of_mem_ateNulls [IsProbabilityMeasure μ] {T : Set Ω}
    (hT : MeasurableSet T) {X : Ω → 𝒳} (hX : Measurable X) {Y₀ Y₁ : Fin m → Ω → ℝ}
    (hY₀ : ∀ j ∈ ateNulls μ Y₀ Y₁, Measurable (Y₀ j))
    (hY₁ : ∀ j ∈ ateNulls μ Y₀ Y₁, Measurable (Y₁ j))
    (hY₀i : ∀ j ∈ ateNulls μ Y₀ Y₁, Integrable (Y₀ j) μ)
    (hY₁i : ∀ j ∈ ateNulls μ Y₀ Y₁, Integrable (Y₁ j) μ)
    (hign : ∀ j ∈ ateNulls μ Y₀ Y₁, StronglyIgnorable μ T (fun ω => (Y₀ j ω, Y₁ j ω)) X)
    {p : Fin m → Ω → ℝ}
    (hcal : IsIPWNullCalibrated μ T X (fun j => observed T (Y₀ j) (Y₁ j)) p) :
    ∀ j ∈ ateNulls μ Y₀ Y₁, IsValidPValue μ (p j) := fun j hj =>
  hcal j <| (ipwContrast_observed_eq_integral hT hX (hY₀ j hj) (hY₁ j hj) (hY₀i j hj)
    (hY₁i j hj) (hign j hj)).trans (mem_ateNulls_iff.1 hj)

/-- **BH controls the FDR over the causal nulls.** Under strong ignorability given `X` of every
endpoint with zero average treatment effect (nothing is assumed about the other endpoints), with
independent p-values calibrated for the observed-data IPW null, the Benjamini–Hochberg procedure at
level `q ∈ [0, 1]` has false discovery rate at most `q |ateNulls| / m`, the false discoveries being
the rejected endpoints with zero average treatment effect. The merged BH theorem
`integral_falseDiscoveryProportion_bhRejections_le_of_isValidPValue` is applied to the causal nulls
via `isValidPValue_of_mem_ateNulls`. No power claim is made. -/
theorem integral_falseDiscoveryProportion_bhRejections_ateNulls_le [IsProbabilityMeasure μ]
    {T : Set Ω} (hT : MeasurableSet T) {X : Ω → 𝒳} (hX : Measurable X)
    {Y₀ Y₁ : Fin m → Ω → ℝ} (hY₀ : ∀ j ∈ ateNulls μ Y₀ Y₁, Measurable (Y₀ j))
    (hY₁ : ∀ j ∈ ateNulls μ Y₀ Y₁, Measurable (Y₁ j))
    (hY₀i : ∀ j ∈ ateNulls μ Y₀ Y₁, Integrable (Y₀ j) μ)
    (hY₁i : ∀ j ∈ ateNulls μ Y₀ Y₁, Integrable (Y₁ j) μ)
    (hign : ∀ j ∈ ateNulls μ Y₀ Y₁, StronglyIgnorable μ T (fun ω => (Y₀ j ω, Y₁ j ω)) X)
    {p : Fin m → Ω → ℝ}
    (hp : ∀ i, Measurable (p i)) (hpind : iIndepFun p μ)
    (hcal : IsIPWNullCalibrated μ T X (fun j => observed T (Y₀ j) (Y₁ j)) p)
    (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∫ ω, falseDiscoveryProportion (ateNulls μ Y₀ Y₁) (bhRejections q fun i => p i ω) ∂μ ≤
      q * (ateNulls μ Y₀ Y₁).card / m :=
  integral_falseDiscoveryProportion_bhRejections_le_of_isValidPValue μ p hp hpind _
    (isValidPValue_of_mem_ateNulls hT hX hY₀ hY₁ hY₀i hY₁i hign hcal) q hq₀ hq₁

/-- **Bonferroni controls the FWER over the causal nulls.** Under strong ignorability given `X` of
every endpoint with zero average treatment effect, with p-values calibrated for the observed-data
IPW null (no assumption on their dependence), the probability that the Bonferroni procedure at level
`α ∈ [0, 1]` rejects some endpoint with zero average treatment effect is at most `α`. No power claim
is made. -/
theorem measure_bonferroni_ateNulls_familywiseError_le [IsProbabilityMeasure μ]
    {T : Set Ω} (hT : MeasurableSet T) {X : Ω → 𝒳} (hX : Measurable X)
    {Y₀ Y₁ : Fin m → Ω → ℝ} (hY₀ : ∀ j ∈ ateNulls μ Y₀ Y₁, Measurable (Y₀ j))
    (hY₁ : ∀ j ∈ ateNulls μ Y₀ Y₁, Measurable (Y₁ j))
    (hY₀i : ∀ j ∈ ateNulls μ Y₀ Y₁, Integrable (Y₀ j) μ)
    (hY₁i : ∀ j ∈ ateNulls μ Y₀ Y₁, Integrable (Y₁ j) μ)
    (hign : ∀ j ∈ ateNulls μ Y₀ Y₁, StronglyIgnorable μ T (fun ω => (Y₀ j ω, Y₁ j ω)) X)
    {p : Fin m → Ω → ℝ}
    (hcal : IsIPWNullCalibrated μ T X (fun j => observed T (Y₀ j) (Y₁ j)) p)
    {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    μ {ω | (bonferroniRejections α (fun i => p i ω) ∩ ateNulls μ Y₀ Y₁).Nonempty} ≤
      ENNReal.ofReal α :=
  measure_bonferroni_familywiseError_le μ p _
    (isValidPValue_of_mem_ateNulls hT hX hY₀ hY₁ hY₀i hY₁i hign hcal) hα₀ hα₁

end Identification

/-! ### Randomized trials (treatment independent of the potential outcomes)

This is Bernoulli-type assignment in a superpopulation: the treatment indicator is a random
variable independent of the potential outcomes. It is not the *complete randomization* of
`randExp` (the uniform law on treated sets of a fixed size `n₁` in a finite population), and the
finite-population estimand `ate` / `diffInMeans` of `CausalIdentification` is not used here. -/

section Randomized

variable {μ : Measure Ω}

/-- With the trivial covariate the propensity score is the design probability `P(T)`. -/
theorem propensity_const [IsProbabilityMeasure μ] (T : Set Ω) :
    propensity μ T (fun _ : Ω => ()) () = μ.real T := by
  simp [propensity]

/-- With the trivial covariate the IPW contrast is the **Horvitz–Thompson contrast** with the
design probability `π = P(T)`: `E[1_T Y / π - 1_{Tᶜ} Y / (1 - π)]`. -/
theorem ipwContrast_const [IsProbabilityMeasure μ] (T : Set Ω) (Y : Ω → ℝ) :
    ipwContrast μ T (fun _ : Ω => ()) Y =
      ∫ ω, (T.indicator (fun ω => Y ω / μ.real T) ω -
        Tᶜ.indicator (fun ω => Y ω / (1 - μ.real T)) ω) ∂μ := by
  simp only [ipwContrast, propensity_const]

/-- **Randomization identifies the ATE.** If the treatment indicator is independent of the
potential outcomes `V` and the design probability satisfies `0 < P(T) < 1`, the treatment is
strongly ignorable given the trivial covariate: independence gives exchangeability, and
`0 < P(T) < 1` is positivity. -/
theorem stronglyIgnorable_of_indepFun [IsProbabilityMeasure μ] {β : Type*} [MeasurableSpace β]
    {T : Set Ω} {V : Ω → β} (hind : IndepFun (T.indicator (1 : Ω → ℝ)) V μ)
    (hT₀ : 0 < μ.real T) (hT₁ : μ.real T < 1) :
    StronglyIgnorable μ T V (fun _ : Ω => ()) := by
  refine ⟨fun B hB w => ?_, fun w _ => ?_⟩
  · have hpre : T.indicator (1 : Ω → ℝ) ⁻¹' {1} = T := by
      ext ω
      by_cases hω : ω ∈ T <;> simp [hω]
    have h := hind.measure_inter_preimage_eq_mul {1} B (measurableSet_singleton 1) hB
    rw [hpre] at h
    simp [measureReal_def, h, ENNReal.toReal_mul]
  · exact propensity_const (μ := μ) T ▸ ⟨hT₀, hT₁⟩

/-- **BH FDR control in a randomized trial (treatment independent of the potential outcomes).**
If the treatment indicator is independent of the potential outcomes of every endpoint with zero
average treatment effect, `0 < P(T) < 1`, and the independent p-values
are calibrated for the observed-data Horvitz–Thompson null (`ipwContrast_const`), BH at level
`q ∈ [0, 1]` has FDR at most `q |ateNulls| / m` over the endpoints with zero average treatment
effect. Randomization enters through `stronglyIgnorable_of_indepFun`. No power claim is made. -/
theorem integral_falseDiscoveryProportion_bhRejections_ateNulls_le_of_indep
    [IsProbabilityMeasure μ] {T : Set Ω} (hT : MeasurableSet T) (hT₀ : 0 < μ.real T)
    (hT₁ : μ.real T < 1) {Y₀ Y₁ : Fin m → Ω → ℝ}
    (hY₀ : ∀ j ∈ ateNulls μ Y₀ Y₁, Measurable (Y₀ j))
    (hY₁ : ∀ j ∈ ateNulls μ Y₀ Y₁, Measurable (Y₁ j))
    (hY₀i : ∀ j ∈ ateNulls μ Y₀ Y₁, Integrable (Y₀ j) μ)
    (hY₁i : ∀ j ∈ ateNulls μ Y₀ Y₁, Integrable (Y₁ j) μ)
    (hind : ∀ j ∈ ateNulls μ Y₀ Y₁,
      IndepFun (T.indicator (1 : Ω → ℝ)) (fun ω => (Y₀ j ω, Y₁ j ω)) μ)
    {p : Fin m → Ω → ℝ} (hp : ∀ i, Measurable (p i)) (hpind : iIndepFun p μ)
    (hcal : IsIPWNullCalibrated μ T (fun _ : Ω => ()) (fun j => observed T (Y₀ j) (Y₁ j)) p)
    (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∫ ω, falseDiscoveryProportion (ateNulls μ Y₀ Y₁) (bhRejections q fun i => p i ω) ∂μ ≤
      q * (ateNulls μ Y₀ Y₁).card / m :=
  integral_falseDiscoveryProportion_bhRejections_ateNulls_le hT measurable_const hY₀ hY₁ hY₀i
    hY₁i (fun j hj => stronglyIgnorable_of_indepFun (hind j hj) hT₀ hT₁) hp hpind hcal q hq₀ hq₁

end Randomized

/-! ### Positivity failure: the conclusion does not follow

One unit, nobody treated (`T = ∅`), trivial covariate, and a single endpoint with
`Y₀ = Y₁ = 1`. Exchangeability holds trivially and the ATE is `0`, so the endpoint is a true
causal null; positivity fails (`e = 0`). The IPW contrast is `-1 ≠ 0`, so the observed-data null
is false and the always-reject p-value `p ≡ 0` is calibrated for it; its FDR and FWER over the
causal nulls are both `1`. -/

section PositivityFailure

/-- The single-endpoint potential outcomes of the positivity-failure example: `Y₀ = Y₁ = 1`. -/
def untreatedOutcome : Fin 1 → Unit → ℝ := fun _ _ => 1

/-- Exchangeability holds when nobody is treated: both sides of `CondIndepDiscrete` vanish. -/
theorem condIndepDiscrete_untreated {β : Type*} [MeasurableSpace β] (V : Unit → β) :
    CondIndepDiscrete (Measure.dirac ()) (∅ : Set Unit) V (fun _ => ()) := by
  intro B _ w
  simp

/-- **Positivity fails** when nobody is treated, so strong ignorability fails. -/
theorem not_stronglyIgnorable_untreated {β : Type*} [MeasurableSpace β] (V : Unit → β) :
    ¬ StronglyIgnorable (Measure.dirac ()) (∅ : Set Unit) V (fun _ => ()) := by
  rintro ⟨-, hpos⟩
  have := (hpos () (by simp)).1
  simp [propensity] at this

/-- The endpoint of the example is a true causal null: its ATE is `0`. -/
theorem ateNulls_untreated :
    ateNulls (Measure.dirac ()) untreatedOutcome untreatedOutcome = Finset.univ := by
  ext j
  simp only [mem_ateNulls_iff, untreatedOutcome, sub_self, integral_zero, Finset.mem_univ]

/-- **The failure, computed**: the IPW contrast of the observed outcome is `-1`, while the ATE is
`0`. Identification fails, so the observed-data null is not the causal null. -/
theorem ipwContrast_untreated_eq_neg_one :
    ipwContrast (Measure.dirac ()) (∅ : Set Unit) (fun _ => ())
      (observed ∅ (untreatedOutcome 0) (untreatedOutcome 0)) = -1 := by
  simp [ipwContrast, propensity, observed, untreatedOutcome]

/-- The always-reject p-value `p ≡ 0` is calibrated for the observed-data IPW null in the
example, vacuously: that null is false (`ipwContrast_untreated_eq_neg_one`). -/
theorem isIPWNullCalibrated_untreated :
    IsIPWNullCalibrated (Measure.dirac ()) (∅ : Set Unit) (fun _ => ())
      (fun j => observed ∅ (untreatedOutcome j) (untreatedOutcome j)) (fun _ _ => 0) := by
  intro j hj
  rw [Subsingleton.elim j 0, ipwContrast_untreated_eq_neg_one] at hj
  norm_num at hj

/-- **BH error control fails without positivity**: in the example the FDR over the causal nulls
is `1`, whatever the level `q ≥ 0`; for `q < 1` this exceeds the bound `q |ateNulls| / m = q`. -/
theorem integral_falseDiscoveryProportion_bhRejections_untreated {q : ℝ} (hq : 0 ≤ q) :
    ∫ _, falseDiscoveryProportion (ateNulls (Measure.dirac ()) untreatedOutcome untreatedOutcome)
      (bhRejections q fun _ => (0 : ℝ)) ∂(Measure.dirac ()) = 1 := by
  have hR : bhRejections q (fun _ : Fin 1 => (0 : ℝ)) = Finset.univ := by
    ext i
    simp only [bhRejections, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    positivity
  simp [ateNulls_untreated, hR, falseDiscoveryProportion]

/-- **Bonferroni error control fails without positivity**: in the example the probability of
rejecting a causal null is `1`, whatever the level `α ≥ 0`; for `α < 1` this exceeds `α`. -/
theorem measure_bonferroni_familywiseError_untreated {α : ℝ} (hα : 0 ≤ α) :
    Measure.dirac () {_ω : Unit | (bonferroniRejections α (fun _ => (0 : ℝ)) ∩
      ateNulls (Measure.dirac ()) untreatedOutcome untreatedOutcome).Nonempty} = 1 := by
  have hR : bonferroniRejections α (fun _ : Fin 1 => (0 : ℝ)) = Finset.univ := by
    ext i
    simp only [bonferroniRejections, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    positivity
  simp [ateNulls_untreated, hR]

end PositivityFailure

end MathlibExt.Probability.Statistics.MultipleTesting
