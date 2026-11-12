/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.Adaptive.RandomizedEstimand
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Tests for multiple testing of average treatment effects

* A randomized trial (treatment independent of the potential outcomes) on four independent fair
  coins, with two endpoints. Coin `0` assigns treatment and coin `1` is a baseline trait.
  Endpoint `0` has a heterogeneous individual effect `±1` with average zero (the superpopulation
  analogue of Neyman's weak null, not Fisher's sharp null); endpoint `1` has ATE `2`. Coins `2`
  and `3` drive two independent, non-constant p-values: the null one is valid, the non-null one
  is not, so calibration has to use the IPW contrast. `ateNulls` is the proper subset `{0}`, and
  every hypothesis of the randomized BH theorem is discharged.
* Computations of `ipwContrast`, `ateNulls`, `IsIPWNullCalibrated` on small examples.
* The positivity-failure boundary: the computed IPW contrast `-1` against the ATE `0`, and FDR /
  FWER equal to `1`, contradicting the bound at level `1/20`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Causality
  MathlibExt.Probability.Statistics.MultipleTesting

namespace MathlibExtTest.Probability.Statistics.MultipleTesting.Adaptive.RandomizedEstimand

/-! ### Four independent fair coins -/

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

lemma integral_coin (f : Bool → ℝ) : ∫ b, f b ∂coin = (f true + f false) / 2 := by
  rw [coin, integral_smul_measure, integral_add_measure Integrable.of_finite Integrable.of_finite,
    integral_dirac, integral_dirac]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
  ring

/-- Four independent fair coins: `ω 0` assigns treatment, `ω 1` is a baseline trait, `ω 2` and
`ω 3` drive the two p-values. -/
noncomputable def trial : Measure (Fin 4 → Bool) := Measure.pi fun _ => coin

instance : IsProbabilityMeasure trial := by
  unfold trial; infer_instance

/-- The four coordinates are independent under `trial`. -/
lemma iIndepFun_coords : iIndepFun (fun (i : Fin 4) (ω : Fin 4 → Bool) => ω i) trial :=
  iIndepFun_pi (μ := fun _ => coin) (X := fun _ b => b) fun _ => Measurable.of_discrete.aemeasurable

lemma trial_preimage_coord (k : Fin 4) (s : Set Bool) :
    trial {ω | ω k ∈ s} = coin s :=
  (measurePreserving_eval (fun _ : Fin 4 => coin) k).measure_preimage
    MeasurableSet.of_discrete.nullMeasurableSet

lemma integral_trial_coord (k : Fin 4) (f : Bool → ℝ) :
    ∫ ω, f (ω k) ∂trial = (f true + f false) / 2 := by
  rw [trial, integral_comp_eval (μ := fun _ => coin) Measurable.of_discrete.aestronglyMeasurable,
    integral_coin]

/-- Treated units: coin `0` shows `true`. -/
def treated : Set (Fin 4 → Bool) := {ω | ω 0 = true}

lemma measurableSet_treated : MeasurableSet treated := MeasurableSet.of_discrete

lemma trial_real_treated : trial.real treated = 1 / 2 := by
  rw [measureReal_def, treated,
    show {ω : Fin 4 → Bool | ω 0 = true} = {ω | ω 0 ∈ ({true} : Set Bool)} by rfl,
    trial_preimage_coord, coin_apply_singleton]
  simp

/-- Treated-arm effects driven by the trait: endpoint `0` gets `2` or `0`, endpoint `1` gets `3`. -/
def eff : Fin 2 → Bool → ℝ := ![fun b => if b then 2 else 0, fun _ => 3]

/-- Untreated potential outcome: `1` for every unit and endpoint. -/
def y0 : Fin 2 → (Fin 4 → Bool) → ℝ := fun _ _ => 1

/-- Treated potential outcome: endpoint `0` has individual effect `±1` (ATE `0`), endpoint `1`
has effect `2`. -/
def y1 : Fin 2 → (Fin 4 → Bool) → ℝ := fun j ω => eff j (ω 1)

lemma integral_y1_sub_y0 (j : Fin 2) :
    ∫ ω, (y1 j ω - y0 j ω) ∂trial = (eff j true + eff j false) / 2 - 1 := by
  have := integral_trial_coord 1 (fun b => eff j b - 1)
  simp only [y0, y1] at this ⊢
  rw [this]
  ring

/-- `ateNulls` picks out the proper subset `{0}`: endpoint `0` is a true causal null, endpoint `1`
is not. -/
lemma ateNulls_trial : ateNulls trial y0 y1 = {0} := by
  ext j
  rw [mem_ateNulls_iff, integral_y1_sub_y0, Finset.mem_singleton]
  fin_cases j <;> norm_num [eff]

/-- Randomization: the treatment indicator is independent of each endpoint's potential
outcomes, because they are functions of different coins. -/
lemma indep_treated (j : Fin 2) :
    IndepFun (treated.indicator (1 : (Fin 4 → Bool) → ℝ)) (fun ω => (y0 j ω, y1 j ω)) trial := by
  have h := (iIndepFun_coords.indepFun (show (0 : Fin 4) ≠ 1 by decide)).comp
    (φ := fun b : Bool => if b then (1 : ℝ) else 0) (ψ := fun b : Bool => ((1 : ℝ), eff j b))
    Measurable.of_discrete Measurable.of_discrete
  have hT : treated.indicator (1 : (Fin 4 → Bool) → ℝ) =
      (fun b : Bool => if b then (1 : ℝ) else 0) ∘ fun ω => ω 0 := by
    funext ω
    by_cases hω : ω 0 = true <;> simp [treated, hω]
  rw [hT]
  exact h

lemma stronglyIgnorable_trial (j : Fin 2) :
    StronglyIgnorable trial treated (fun ω => (y0 j ω, y1 j ω)) (fun _ => ()) :=
  stronglyIgnorable_of_indepFun (indep_treated j) (by rw [trial_real_treated]; norm_num)
    (by rw [trial_real_treated]; norm_num)

/-- `ipwContrast` on the trial: identification gives the ATE, `0` and `2`. -/
lemma ipwContrast_trial (j : Fin 2) :
    ipwContrast trial treated (fun _ => ()) (observed treated (y0 j) (y1 j)) =
      (eff j true + eff j false) / 2 - 1 := by
  rw [ipwContrast_observed_eq_integral measurableSet_treated measurable_const
    Measurable.of_discrete Measurable.of_discrete Integrable.of_finite Integrable.of_finite
    (stronglyIgnorable_trial j), integral_y1_sub_y0]

/-- The null endpoint's p-value distribution: `1/2` or `1`. -/
noncomputable def pv0 : Bool → ℝ := fun b => if b then 1 / 2 else 1

/-- The non-null endpoint's p-value distribution: `1/100` or `1`. -/
noncomputable def pv1 : Bool → ℝ := fun b => if b then 1 / 100 else 1

/-- The two p-values, driven by coins `2` and `3`. -/
noncomputable def pval : Fin 2 → (Fin 4 → Bool) → ℝ := ![fun ω => pv0 (ω 2), fun ω => pv1 (ω 3)]

/-- The p-values are independent. -/
lemma iIndepFun_pval : iIndepFun pval trial := by
  have hinj : Function.Injective (![2, 3] : Fin 2 → Fin 4) := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all
  have h := (iIndepFun_coords.precomp hinj).comp (fun i => ![pv0, pv1] i)
    fun _ => Measurable.of_discrete
  refine h.congr fun i => Filter.Eventually.of_forall fun ω => ?_
  fin_cases i <;> rfl

/-- The null p-value is valid (super-uniform) and not constant. -/
lemma isValidPValue_pval_zero : IsValidPValue trial (pval 0) := by
  intro t ht
  have hset : {ω : Fin 4 → Bool | pval 0 ω ≤ t} = {ω | ω 2 ∈ {b | pv0 b ≤ t}} := rfl
  rw [hset, trial_preimage_coord]
  rcases eq_or_lt_of_le ht.2 with rfl | h1
  · rw [ENNReal.ofReal_one]; exact prob_le_one
  rcases lt_or_ge t 2⁻¹ with h2 | h2
  · have : {b : Bool | pv0 b ≤ t} = ∅ := by
      ext b; cases b <;> simp [pv0, not_le.2 h1, h2]
    simp [this]
  · have : {b : Bool | pv0 b ≤ t} = {true} := by
      ext b; cases b <;> simp [pv0, not_le.2 h1, h2]
    rw [this, coin_apply_singleton]
    calc (2⁻¹ : ENNReal) = ENNReal.ofReal (1 / 2) := by
          rw [ENNReal.ofReal_div_of_pos two_pos]; simp
      _ ≤ ENNReal.ofReal t := ENNReal.ofReal_le_ofReal (by rwa [one_div])

/-- The non-null p-value is **not** valid: `P(p₁ ≤ 1/100) = 1/2`. So calibration for the
observed-data null must use that the IPW contrast of endpoint `1` is nonzero. -/
lemma not_isValidPValue_pval_one : ¬ IsValidPValue trial (pval 1) := by
  intro h
  have := h (1 / 100) ⟨by norm_num, by norm_num⟩
  have hset : {ω : Fin 4 → Bool | pval 1 ω ≤ 1 / 100} = {ω | ω 3 ∈ ({true} : Set Bool)} := by
    ext ω
    by_cases hω : ω 3 = true
    · simp [pval, pv1, hω]
    · simp [pval, pv1, hω]
      norm_num
  rw [hset, trial_preimage_coord, coin_apply_singleton,
    ← ENNReal.ofReal_toReal (a := 2⁻¹) (by simp)] at this
  have := (ENNReal.ofReal_le_ofReal_iff (by norm_num)).1 this
  norm_num at this

/-- The p-values are calibrated for the observed-data IPW null. Endpoint `1` needs the contrast:
its p-value is invalid, but its IPW contrast is `2 ≠ 0`. -/
lemma isIPWNullCalibrated_trial :
    IsIPWNullCalibrated trial treated (fun _ => ()) (fun j => observed treated (y0 j) (y1 j))
      pval := by
  intro j hj
  fin_cases j
  · exact isValidPValue_pval_zero
  · have := ipwContrast_trial 1
    simp only [Fin.mk_one] at hj
    rw [hj] at this
    norm_num [eff] at this

/-- **Non-vacuity of the randomized BH theorem**: two endpoints, one causal null and one with ATE
`2`, independent non-constant p-values, every hypothesis discharged. The bound is `q / 2`. -/
example (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∫ ω, falseDiscoveryProportion (ateNulls trial y0 y1)
      (bhRejections q fun i => pval i ω) ∂trial ≤ q / 2 := by
  have h := integral_falseDiscoveryProportion_bhRejections_ateNulls_le_of_indep
    measurableSet_treated (by rw [trial_real_treated]; norm_num)
    (by rw [trial_real_treated]; norm_num)
    (fun _ _ => Measurable.of_discrete) (fun _ _ => Measurable.of_discrete)
    (fun _ _ => Integrable.of_finite) (fun _ _ => Integrable.of_finite)
    (fun j _ => indep_treated j) (fun _ => Measurable.of_discrete) iIndepFun_pval
    isIPWNullCalibrated_trial q hq₀ hq₁
  rw [ateNulls_trial] at h ⊢
  simpa using h

/-! ### Small computations -/

/-- `ateNulls` drops an endpoint with a nonzero ATE: on a point mass, `Y₀ = 0`, `Y₁ = 3`. -/
example : ateNulls (Measure.dirac ()) (fun (_ : Fin 1) _ => (0 : ℝ)) (fun _ _ => 3) = ∅ := by
  ext j
  simp [mem_ateNulls_iff]

/-- `ipwContrast` with the trivial covariate is the Horvitz–Thompson contrast. -/
example (Y : (Fin 4 → Bool) → ℝ) :
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
