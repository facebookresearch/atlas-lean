/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration

/-!
# Potential outcomes with a binary instrument and binary treatment

**Local average treatment effect** (Imbens & Angrist 1994, Theorem 1; Angrist, Imbens &
  Rubin 1996). A potential-outcomes model with a binary instrument `Z`, potential treatments
  `D(z)` and potential outcomes `Y(z, d)`. Under independence of `Z` from the potential
  variables, exclusion (`Y(0, d) = Y(1, d)`) and monotonicity (`D(0) ≤ D(1)`), the Wald
  estimand `(𝔼[Y | Z = 1] - 𝔼[Y | Z = 0]) / (𝔼[D | Z = 1] - 𝔼[D | Z = 0])` equals the average
  effect `𝔼[Y(1) - Y(0) | complier]`, assuming a nonzero proportion of compliers. The
  denominator is the complier proportion (`D(0) = 0`, `D(1) = 1`), so this relevance premise
  makes both the ratio and the conditional average meaningful. A separately named theorem records
  the totalized algebraic identity at zero complier mass without calling it identification.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MathlibExt.Biology.StatisticalGenetics.MendelianRandomization

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Under independence, conditioning on the instrument does not change the mean of a function of
the variables it is independent of. -/
private theorem integral_cond_eq_of_indepFun {μ : Measure Ω} [IsProbabilityMeasure μ]
    {β : Type*} [MeasurableSpace β] {Z : Ω → Bool} {V : Ω → β} (hZ : Measurable Z)
    (hV : Measurable V) (hind : IndepFun Z V μ) {f : β → ℝ} (hf : Measurable f) {z : Bool}
    (hz : μ (Z ⁻¹' {z}) ≠ 0) :
    ∫ ω, f (V ω) ∂μ[|Z ⁻¹' {z}] = ∫ ω, f (V ω) ∂μ := by
  have hA : MeasurableSet (Z ⁻¹' {z}) := hZ (measurableSet_singleton z)
  have hφ : Measurable (({z} : Set Bool).indicator fun _ => (1 : ℝ)) := measurable_of_countable _
  have hind' := hind.comp hφ hf
  have hmul : (Z ⁻¹' {z}).indicator (fun ω => f (V ω)) =
      fun ω => (({z} : Set Bool).indicator (fun _ => (1 : ℝ)) ∘ Z) ω * (f ∘ V) ω := by
    funext ω
    by_cases h : Z ω = z <;> simp [Set.indicator, h]
  have hone : (fun ω => (({z} : Set Bool).indicator (fun _ => (1 : ℝ)) ∘ Z) ω) =
      (Z ⁻¹' {z}).indicator 1 := by
    funext ω
    by_cases h : Z ω = z <;> simp [Set.indicator, h]
  rw [ProbabilityTheory.cond, integral_smul_measure, ← integral_indicator hA, hmul,
    IndepFun.integral_fun_mul_eq_mul_integral hind' (hφ.comp hZ).aestronglyMeasurable
      (hf.comp hV).aestronglyMeasurable]
  rw [show μ[({z} : Set Bool).indicator (fun _ => (1 : ℝ)) ∘ Z] = μ.real (Z ⁻¹' {z}) by
    rw [← integral_indicator_one hA]
    exact congrArg (fun g => ∫ ω, g ω ∂μ) hone]
  rw [smul_eq_mul, ← mul_assoc, ENNReal.toReal_inv, measureReal_def,
    inv_mul_cancel₀ (ENNReal.toReal_ne_zero.2 ⟨hz, measure_ne_top μ _⟩), one_mul]
  rfl

/-- Integrals against `μ[|A]` only see the values on `A`. -/
private theorem integral_cond_congr {μ : Measure Ω} {A : Set Ω} (hA : MeasurableSet A)
    {f g : Ω → ℝ} (h : Set.EqOn f g A) : ∫ ω, f ω ∂μ[|A] = ∫ ω, g ω ∂μ[|A] := by
  rw [ProbabilityTheory.cond, integral_smul_measure, integral_smul_measure,
    setIntegral_congr_fun hA h]

/-- The four compliance types of Angrist, Imbens & Rubin (1996), determined by the pair of
potential treatments `(D(0), D(1))`. -/
inductive ComplianceType
  /-- `D(0) = 0`, `D(1) = 1`: takes the treatment exactly when encouraged. -/
  | complier
  /-- `D(0) = D(1) = 1`. -/
  | alwaysTaker
  /-- `D(0) = D(1) = 0`. -/
  | neverTaker
  /-- `D(0) = 1`, `D(1) = 0`: takes the treatment exactly when not encouraged. -/
  | defier
  deriving DecidableEq

/-- The compliance type of the potential treatments `(D(0), D(1)) = (d₀, d₁)`. -/
def complianceType : Bool → Bool → ComplianceType
  | false, true => .complier
  | true, true => .alwaysTaker
  | false, false => .neverTaker
  | true, false => .defier

/-- A potential-outcomes model with a binary instrument and a binary treatment (Imbens &
Angrist 1994; Angrist, Imbens & Rubin 1996): the assigned instrument `Z`, the potential
treatments `D(z)` and the potential outcomes `Y(z, d)`, all measurable. The observed treatment
is `D(Z)` and the observed outcome `Y(Z, D(Z))`. The identifying assumptions (independence,
exclusion, monotonicity, relevance) are separate predicates. -/
structure PotentialOutcomes (Ω : Type*) [MeasurableSpace Ω] where
  /-- The assigned instrument `Z`. -/
  instrument : Ω → Bool
  /-- The potential treatment `D(z)` under assignment `z`. -/
  treatment : Bool → Ω → Bool
  /-- The potential outcome `Y(z, d)` under assignment `z` and treatment `d`. -/
  outcome : Bool → Bool → Ω → ℝ
  /-- The instrument is measurable. -/
  measurable_instrument : Measurable instrument
  /-- The potential treatments are measurable. -/
  measurable_treatment : ∀ z, Measurable (treatment z)
  /-- The potential outcomes are measurable. -/
  measurable_outcome : ∀ z d, Measurable (outcome z d)

namespace PotentialOutcomes

variable (P : PotentialOutcomes Ω)

/-- The observed treatment `D = D(Z)`. -/
def observedTreatment (ω : Ω) : Bool := P.treatment (P.instrument ω) ω

/-- The observed outcome `Y = Y(Z, D(Z))`. -/
def observedOutcome (ω : Ω) : ℝ := P.outcome (P.instrument ω) (P.observedTreatment ω) ω

/-- The compliance type of a unit. -/
def type (ω : Ω) : ComplianceType := complianceType (P.treatment false ω) (P.treatment true ω)

/-- The compliers, `D(0) = 0` and `D(1) = 1`. -/
def compliers : Set Ω := {ω | P.type ω = .complier}

/-- Independence (random assignment): the instrument is independent of the vector of all
potential treatments and potential outcomes. -/
def Independence (μ : Measure Ω) : Prop :=
  IndepFun P.instrument (fun ω => (fun z => P.treatment z ω, fun z d => P.outcome z d ω)) μ

/-- Exclusion: the instrument affects the outcome only through the treatment,
`Y(0, d) = Y(1, d)`. -/
def Exclusion : Prop := ∀ d ω, P.outcome false d ω = P.outcome true d ω

/-- Monotonicity: assignment never decreases the treatment, `D(0) ≤ D(1)`; there are no
defiers. -/
def Monotonicity : Prop := ∀ ω, P.treatment false ω ≤ P.treatment true ω

/-- The mean of `f` in the arm `Z = z`, `𝔼[f | Z = z]`, the expectation under the conditional
measure. It is the junk value `0` when `P(Z = z) = 0`. -/
noncomputable def armMean (μ : Measure Ω) (f : Ω → ℝ) (z : Bool) : ℝ :=
  ∫ ω, f ω ∂μ[|P.instrument ⁻¹' {z}]

/-- The observed treatment as a `0`/`1` real variable. -/
def treated (ω : Ω) : ℝ := if P.observedTreatment ω then 1 else 0

/-- The Wald (instrumental-variable) estimand
`(𝔼[Y | Z = 1] - 𝔼[Y | Z = 0]) / (𝔼[D | Z = 1] - 𝔼[D | Z = 0])`. -/
noncomputable def waldEstimand (μ : Measure Ω) : ℝ :=
  (P.armMean μ P.observedOutcome true - P.armMean μ P.observedOutcome false) /
    (P.armMean μ P.treated true - P.armMean μ P.treated false)

/-- The vector of potential treatments and potential outcomes of a unit. -/
private def potentials (ω : Ω) : (Bool → Bool) × (Bool → Bool → ℝ) :=
  (fun z => P.treatment z ω, fun z d => P.outcome z d ω)

private theorem measurable_potentials : Measurable P.potentials :=
  Measurable.prodMk (measurable_pi_iff.2 fun z => P.measurable_treatment z)
    (measurable_pi_iff.2 fun z => measurable_pi_iff.2 fun d => P.measurable_outcome z d)

/-- Under independence, an arm mean of a variable that on that arm is a function of the
potential vector equals the population mean of that function. -/
private theorem armMean_eq {μ : Measure Ω} [IsProbabilityMeasure μ] (hind : P.Independence μ)
    {z : Bool} (hz : μ (P.instrument ⁻¹' {z}) ≠ 0)
    {f : (Bool → Bool) × (Bool → Bool → ℝ) → ℝ} (hf : Measurable f) {g : Ω → ℝ}
    (hg : ∀ ω, P.instrument ω = z → g ω = f (P.potentials ω)) :
    P.armMean μ g z = ∫ ω, f (P.potentials ω) ∂μ := by
  rw [armMean, integral_cond_congr (P.measurable_instrument (measurableSet_singleton z))
    (fun ω hω => hg ω hω)]
  exact integral_cond_eq_of_indepFun P.measurable_instrument P.measurable_potentials hind hf hz

/-- The treatment rate in arm `z` is `P(D(z) = 1)`. -/
private theorem armMean_treated {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hind : P.Independence μ) {z : Bool} (hz : μ (P.instrument ⁻¹' {z}) ≠ 0) :
    P.armMean μ P.treated z = μ.real {ω | P.treatment z ω = true} := by
  rw [P.armMean_eq hind hz (f := fun v => if v.1 z then (1 : ℝ) else 0)
    ((measurable_of_countable (fun b : Bool => if b then (1 : ℝ) else 0)).comp
      ((measurable_pi_apply z).comp measurable_fst))
    (fun ω hω => by
      unfold treated observedTreatment potentials
      rw [hω])]
  change _ = μ.real (P.treatment z ⁻¹' {true})
  rw [← integral_indicator_one ((P.measurable_treatment z) (measurableSet_singleton true))]
  congr 1
  funext ω
  by_cases h : P.treatment z ω = true <;> simp [potentials, Set.indicator, h]

/-- The outcome under assignment `z` and the potential treatment `D(z)`, as a function of the
potential vector. -/
private def outcomeAt (z : Bool) (v : (Bool → Bool) × (Bool → Bool → ℝ)) : ℝ :=
  if v.1 z then v.2 z true else v.2 z false

private theorem measurable_outcomeAt (z : Bool) : Measurable (outcomeAt z) := by
  have hs : MeasurableSet {v : (Bool → Bool) × (Bool → Bool → ℝ) | v.1 z = true} :=
    measurableSet_eq_fun ((measurable_pi_apply z).comp measurable_fst) measurable_const
  exact Measurable.ite hs
    ((measurable_pi_apply true).comp ((measurable_pi_apply z).comp measurable_snd))
    ((measurable_pi_apply false).comp ((measurable_pi_apply z).comp measurable_snd))

private theorem integrable_outcomeAt {μ : Measure Ω} (hY : ∀ z d, Integrable (P.outcome z d) μ)
    (z : Bool) : Integrable (fun ω => outcomeAt z (P.potentials ω)) μ := by
  refine Integrable.mono' ((hY z true).norm.add (hY z false).norm)
    ((measurable_outcomeAt z).comp P.measurable_potentials).aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  simp only [outcomeAt, potentials, Pi.add_apply]
  by_cases h : P.treatment z ω = true <;> simp [h]

/-- The mean outcome in arm `z` is `𝔼[Y(z, D(z))]`. -/
private theorem armMean_observedOutcome {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hind : P.Independence μ) {z : Bool} (hz : μ (P.instrument ⁻¹' {z}) ≠ 0) :
    P.armMean μ P.observedOutcome z = ∫ ω, outcomeAt z (P.potentials ω) ∂μ :=
  P.armMean_eq hind hz (measurable_outcomeAt z) fun ω hω => by
    simp only [observedOutcome, observedTreatment, outcomeAt, potentials, hω]
    by_cases h : P.treatment z ω = true <;> simp [h]

private theorem measurableSet_compliers : MeasurableSet P.compliers := by
  have h : P.compliers = {ω | P.treatment false ω = false} ∩ {ω | P.treatment true ω = true} := by
    ext ω
    simp only [compliers, type, Set.mem_ofPred_eq, Set.mem_inter_iff]
    by_cases h0 : P.treatment false ω = true <;> by_cases h1 : P.treatment true ω = true <;>
      simp_all [complianceType]
  rw [h]
  exact ((P.measurable_treatment false) (measurableSet_singleton false)).inter
    ((P.measurable_treatment true) (measurableSet_singleton true))

/-- The first stage (Imbens & Angrist 1994): under independence and monotonicity, with both
arms of positive probability, the difference in treatment rates between the arms is the
proportion of compliers. -/
theorem armMean_treated_sub {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hind : P.Independence μ) (hmono : P.Monotonicity)
    (hZ : ∀ z, μ (P.instrument ⁻¹' {z}) ≠ 0) :
    P.armMean μ P.treated true - P.armMean μ P.treated false = μ.real P.compliers := by
  rw [P.armMean_treated hind (hZ true), P.armMean_treated hind (hZ false),
    ← measureReal_sdiff (s₁ := {ω | P.treatment true ω = true})
      (s₂ := {ω | P.treatment false ω = true}) (fun ω (h : P.treatment false ω = true) => by
        have := hmono ω
        rw [h] at this
        exact top_le_iff.1 this)
      ((P.measurable_treatment false) (measurableSet_singleton true))]
  congr 1
  ext ω
  simp only [compliers, type, Set.mem_sdiff, Set.mem_ofPred_eq]
  by_cases h0 : P.treatment false ω = true <;> by_cases h1 : P.treatment true ω = true <;>
    simp_all [complianceType]

/-- The reduced form (Imbens & Angrist 1994): under independence, exclusion and monotonicity,
with integrable potential outcomes and both arms of positive probability, the difference in
mean outcomes between the arms is `𝔼[(Y(z, 1) - Y(z, 0)) 1_complier]`, for either `z`. -/
theorem armMean_outcome_sub {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hind : P.Independence μ) (hexcl : P.Exclusion) (hmono : P.Monotonicity)
    (hY : ∀ z d, Integrable (P.outcome z d) μ) (hZ : ∀ z, μ (P.instrument ⁻¹' {z}) ≠ 0)
    (z : Bool) :
    P.armMean μ P.observedOutcome true - P.armMean μ P.observedOutcome false =
      ∫ ω in P.compliers, P.outcome z true ω - P.outcome z false ω ∂μ := by
  rw [P.armMean_observedOutcome hind (hZ true), P.armMean_observedOutcome hind (hZ false),
    ← integral_sub (P.integrable_outcomeAt hY true) (P.integrable_outcomeAt hY false),
    ← integral_indicator P.measurableSet_compliers]
  congr 1
  funext ω
  have hm := hmono ω
  rw [Bool.le_iff_imp] at hm
  have e0 := hexcl false ω
  have e1 := hexcl true ω
  simp only [outcomeAt, potentials, compliers, type, Set.indicator, Set.mem_ofPred_eq]
  cases z <;> by_cases h0 : P.treatment false ω = true <;>
    by_cases h1 : P.treatment true ω = true <;> simp_all [complianceType]

/-- The unrestricted algebraic identity behind LATE. If the complier set has measure zero, both
sides totalize to `0`; therefore this theorem is not an identification or complier-average claim
at that boundary. Use `waldEstimand_eq_late` for the source-faithful result with relevance. -/
theorem waldEstimand_eq_late_totalized {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hind : P.Independence μ) (hexcl : P.Exclusion) (hmono : P.Monotonicity)
    (hY : ∀ z d, Integrable (P.outcome z d) μ)
    (hZ : ∀ z, μ (P.instrument ⁻¹' {z}) ≠ 0) (z : Bool) :
    P.waldEstimand μ = ∫ ω, P.outcome z true ω - P.outcome z false ω ∂μ[|P.compliers] := by
  rw [waldEstimand, P.armMean_outcome_sub hind hexcl hmono hY hZ z,
    P.armMean_treated_sub hind hmono hZ, ProbabilityTheory.cond, integral_smul_measure,
    smul_eq_mul, ENNReal.toReal_inv, measureReal_def, div_eq_inv_mul]

/-- The local average treatment effect theorem (Imbens & Angrist 1994, Theorem 1; Angrist,
Imbens & Rubin 1996): under independence, exclusion, monotonicity and relevance, with integrable
potential outcomes and both arms of positive probability, the Wald estimand is the average
treatment effect among compliers, `𝔼[Y(1) - Y(0) | complier]` (read at either instrument value
`z`, which exclusion makes irrelevant). Relevance is the nonzero complier mass hypothesis; by
`armMean_treated_sub`, it is equivalent here to a nonzero Wald denominator. -/
theorem waldEstimand_eq_late {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hind : P.Independence μ) (hexcl : P.Exclusion) (hmono : P.Monotonicity)
    (hY : ∀ z d, Integrable (P.outcome z d) μ)
    (hZ : ∀ z, μ (P.instrument ⁻¹' {z}) ≠ 0) (hC : μ P.compliers ≠ 0) (z : Bool) :
    P.waldEstimand μ = ∫ ω, P.outcome z true ω - P.outcome z false ω ∂μ[|P.compliers] :=
  have _ := cond_isProbabilityMeasure hC
  P.waldEstimand_eq_late_totalized hind hexcl hmono hY hZ z

end PotentialOutcomes

end MathlibExt.Biology.StatisticalGenetics.MendelianRandomization
