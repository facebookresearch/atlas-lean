/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.Adaptive.RandomizedEstimand

/-!
# Tests for multiple testing of average treatment effects

* A completely randomized trial on two independent fair coins: the first coin assigns treatment,
  the second drives a heterogeneous individual effect `±1` with average zero (Neyman's weak null,
  not Fisher's sharp null). Every identification hypothesis of the randomized BH theorem is
  discharged, so that theorem is not vacuous.
* Computations of `ipwContrast`, `ateNulls`, `IsIPWNullCalibrated` on small examples.
* The positivity-failure boundary: the computed IPW contrast `-1` against the ATE `0`, and FDR /
  FWER equal to `1`, contradicting the bound at level `1/20`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Causality
  MathlibExt.Probability.Statistics.MultipleTesting

namespace MathlibExtTest.Probability.Statistics.MultipleTesting.Adaptive.RandomizedEstimand

/-! ### Two independent fair coins -/

/-- A fair coin. -/
noncomputable def coin : Measure Bool :=
  (2⁻¹ : ENNReal) • (Measure.dirac true + Measure.dirac false)

lemma coin_apply_singleton (b : Bool) : coin {b} = 2⁻¹ := by
  cases b <;> simp [coin]

instance : IsProbabilityMeasure coin := by
  constructor
  rw [show (Set.univ : Set Bool) = {true} ∪ {false} by ext b; cases b <;> simp,
    measure_union (by simp) (measurableSet_singleton _), coin_apply_singleton,
    coin_apply_singleton, ENNReal.inv_two_add_inv_two]

/-- Two independent fair coins: `ω.1` assigns treatment, `ω.2` is a baseline trait. -/
noncomputable def trial : Measure (Bool × Bool) := coin.prod coin

instance : IsProbabilityMeasure trial := by
  unfold trial; infer_instance

/-- Treated units: the first coin shows `true`. -/
def treated : Set (Bool × Bool) := {ω | ω.1 = true}

/-- Untreated potential outcome: `1` for every unit. -/
def y0 : Fin 1 → Bool × Bool → ℝ := fun _ _ => 1

/-- Treated potential outcome: `2` if the trait is `true`, `0` otherwise, so the individual effect
is `+1` or `-1` and the ATE is `0`. -/
def y1 : Fin 1 → Bool × Bool → ℝ := fun _ ω => if ω.2 then 2 else 0

lemma measurableSet_treated : MeasurableSet treated :=
  show MeasurableSet (Prod.fst ⁻¹' {true}) from
    (measurableSet_singleton true).preimage measurable_fst

lemma trial_real_treated : trial.real treated = 1 / 2 := by
  have : treated = {true} ×ˢ Set.univ := by ext ω; simp [treated]
  rw [measureReal_def, this, trial, Measure.prod_prod, coin_apply_singleton, measure_univ]
  norm_num

/-- Randomization: the treatment indicator is independent of the potential outcomes. -/
lemma indep_treated (j : Fin 1) :
    IndepFun (treated.indicator (1 : Bool × Bool → ℝ)) (fun ω => (y0 j ω, y1 j ω)) trial := by
  have h := indepFun_prod (μ := coin) (ν := coin)
    (X := fun b : Bool => if b then (1 : ℝ) else 0)
    (Y := fun b : Bool => ((1 : ℝ), if b then (2 : ℝ) else 0))
    (Measurable.of_discrete) (Measurable.of_discrete)
  have hT : treated.indicator (1 : Bool × Bool → ℝ) = fun ω => if ω.1 = true then 1 else 0 := by
    funext ω
    rcases ω with ⟨a, b⟩
    cases a <;> simp [treated]
  have hV : (fun ω => (y0 j ω, y1 j ω)) =
      fun ω : Bool × Bool => ((1 : ℝ), if ω.2 = true then (2 : ℝ) else 0) := by
    funext ω
    simp [y0, y1]
  rw [hT, hV]
  exact h

/-- The ATE of the single endpoint is `0`: it is a true causal null. -/
lemma ateNulls_trial : ateNulls trial y0 y1 = Finset.univ := by
  ext j
  simp only [mem_ateNulls_iff, Finset.mem_univ, iff_true]
  rw [integral_fintype Integrable.of_finite]
  simp [Fintype.sum_prod_type, y0, y1, measureReal_def, trial, ← Set.singleton_prod_singleton,
    Measure.prod_prod, coin_apply_singleton]
  norm_num

/-- The identification hypothesis of the main theorem holds in the randomized trial. -/
example (j : Fin 1) :
    StronglyIgnorable trial treated (fun ω => (y0 j ω, y1 j ω)) (fun _ => ()) :=
  stronglyIgnorable_of_indepFun (indep_treated j) (by rw [trial_real_treated]; norm_num)
    (by rw [trial_real_treated]; norm_num)

/-- `ipwContrast` on the trial: identification gives the ATE `0` for the observed outcome. -/
example : ipwContrast trial treated (fun _ => ()) (observed treated (y0 0) (y1 0)) = 0 := by
  rw [ipwContrast_observed_eq_integral measurableSet_treated measurable_const
    Measurable.of_discrete Measurable.of_discrete Integrable.of_finite Integrable.of_finite
    (stronglyIgnorable_of_indepFun (indep_treated 0) (by rw [trial_real_treated]; norm_num)
      (by rw [trial_real_treated]; norm_num))]
  exact mem_ateNulls_iff.1 (ateNulls_trial ▸ Finset.mem_univ 0)

/-- The p-value that never rejects, `p ≡ 1`, is valid. -/
lemma isValidPValue_one {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    IsValidPValue μ (fun _ : Ω => (1 : ℝ)) := by
  intro t ht
  rcases eq_or_lt_of_le ht.2 with rfl | hlt
  · simp
  · simp [not_le.2 hlt]

/-- `IsIPWNullCalibrated` holds for the never-reject p-value. -/
example : IsIPWNullCalibrated trial treated (fun _ => ())
    (fun j => observed treated (y0 j) (y1 j)) (fun _ _ => 1) :=
  fun _ _ => isValidPValue_one trial

/-- **Non-vacuity of the randomized BH theorem**: all of its hypotheses are discharged on the
two-coin trial with heterogeneous effects. -/
example (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∫ _, falseDiscoveryProportion (ateNulls trial y0 y1)
      (bhRejections q fun _ => (1 : ℝ)) ∂trial ≤
      q * (ateNulls trial y0 y1).card / ((1 : ℕ) : ℝ) :=
  integral_falseDiscoveryProportion_bhRejections_ateNulls_le_of_indep
    measurableSet_treated
    (by rw [trial_real_treated]; norm_num) (by rw [trial_real_treated]; norm_num)
    (fun _ => Measurable.of_discrete) (fun _ => Measurable.of_discrete)
    (fun _ => Integrable.of_finite) (fun _ => Integrable.of_finite) indep_treated
    (fun _ => measurable_const) (iIndepFun.of_subsingleton)
    (fun _ _ => isValidPValue_one trial) q hq₀ hq₁

/-! ### Small computations -/

/-- `ateNulls` drops an endpoint with a nonzero ATE: on a point mass, `Y₀ = 0`, `Y₁ = 3`. -/
example : ateNulls (Measure.dirac ()) (fun (_ : Fin 1) _ => (0 : ℝ)) (fun _ _ => 3) = ∅ := by
  ext j
  simp [mem_ateNulls_iff]

/-- `ipwContrast` with the trivial covariate is the Horvitz–Thompson contrast. -/
example (Y : Bool × Bool → ℝ) :
    ipwContrast trial treated (fun _ => ()) Y =
      ∫ ω, (treated.indicator (fun ω => Y ω / (1 / 2)) ω -
        treatedᶜ.indicator (fun ω => Y ω / (1 - 1 / 2)) ω) ∂trial := by
  rw [ipwContrast_const, trial_real_treated]

/-! ### Positivity failure -/

/-- The example's potential outcomes are the constant `1`. -/
example : untreatedOutcome 0 () = 1 := rfl

/-- Exchangeability holds but positivity fails. -/
example : CondIndepDiscrete (Measure.dirac ()) (∅ : Set Unit)
      (fun ω => (untreatedOutcome 0 ω, untreatedOutcome 0 ω)) (fun _ => ()) ∧
    ¬ StronglyIgnorable (Measure.dirac ()) (∅ : Set Unit)
      (fun ω => (untreatedOutcome 0 ω, untreatedOutcome 0 ω)) (fun _ => ()) :=
  ⟨condIndepDiscrete_untreated _, not_stronglyIgnorable_untreated _⟩

/-- The IPW contrast is `-1`, but the ATE is `0`. -/
example : ipwContrast (Measure.dirac ()) (∅ : Set Unit) (fun _ => ())
      (observed ∅ (untreatedOutcome 0) (untreatedOutcome 0)) = -1 ∧
    ∫ ω, (untreatedOutcome 0 ω - untreatedOutcome 0 ω) ∂(Measure.dirac ()) = 0 :=
  ⟨ipwContrast_untreated_eq_neg_one, by simp⟩

/-- **The BH conclusion fails without positivity**: at `q = 1/20` the bound would be `1/20`, but
the FDR is `1`, although the always-reject p-value is calibrated for the observed-data null. -/
example : ¬ (∫ _, falseDiscoveryProportion
      (ateNulls (Measure.dirac ()) untreatedOutcome untreatedOutcome)
      (bhRejections (1 / 20) fun _ => (0 : ℝ)) ∂(Measure.dirac ()) ≤
      1 / 20 * (ateNulls (Measure.dirac ()) untreatedOutcome untreatedOutcome).card /
        ((1 : ℕ) : ℝ)) := by
  rw [integral_falseDiscoveryProportion_bhRejections_untreated (by norm_num), ateNulls_untreated]
  norm_num

/-- **The Bonferroni conclusion fails without positivity**: FWER `1 > 1/20`. -/
example : ¬ (Measure.dirac () {_ω : Unit | (bonferroniRejections (1 / 20)
      (fun _ => (0 : ℝ)) ∩
      ateNulls (Measure.dirac ()) untreatedOutcome untreatedOutcome).Nonempty} ≤
      ENNReal.ofReal (1 / 20)) := by
  rw [measure_bonferroni_familywiseError_untreated (by norm_num), not_le]
  rw [← ENNReal.ofReal_one]
  exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (by norm_num)

/-- The always-reject p-value is calibrated in the positivity-failure example. -/
example := isIPWNullCalibrated_untreated

end MathlibExtTest.Probability.Statistics.MultipleTesting.Adaptive.RandomizedEstimand
