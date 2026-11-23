/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.CoxCountingProcessConditions

/-!
# Tests for `CoxCountingProcessConditions`

* Grid computations from the definitions on two subjects: the summed score and information
  increments, and Cox's `coxScore` / `coxInformation` computed directly from `riskMean` /
  `riskVar`, agree.
* The no-ties hypothesis of `sq_sum_mul_eq_of_sum_le_one` cannot be dropped.
* Non-vacuity of `IsCoxCountingProcess`: a fair-coin model in which one subject has its event at
  grid time `1` with probability `1 / 2` satisfies all conditions, with the Cox intensity checked
  by computing the conditional expectation from its definition.
* A two-subject model on `Fin 3` with covariates `1, 0`: it satisfies `IsCoxCountingProcess`
  (no ties with two subjects at risk), its step-`0` score increment is `±1/2`, nonzero with
  probability `2/3`, and `E[(ΔU)²] = 1/6` computed directly equals the information-compensator
  term `Δα V S⁽⁰⁾ = 1/3 · 1/4 · 2`.

No fixture shows the compensator hypothesis `hcomp` holding together with `v > 0` at large `n`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Real
open MathlibExt.Probability.Statistics.CoxPartialLikelihood
open MathlibExt.Probability.Statistics.CoxCountingProcessConditions
open scoped ENNReal

namespace MathlibExtTest.Probability.Statistics.CoxCountingProcessConditions

/-! ### Grid computations on two subjects -/

/-- Grid times: subject `0` at time `1`, subject `1` at time `2`. -/
def t₀ : Fin 2 → ℕ := ![1, 2]

/-- Both events are observed. -/
def d₀ : Fin 2 → Bool := ![true, true]

/-- Covariates `1` and `0`. -/
noncomputable def z₀ : Fin 2 → ℝ := ![1, 0]

/-- Step `0`: both at risk, mean `1/2`, subject `0` fails: increment `1/2`. Step `1`: only
subject `1` at risk, mean `0`, increment `0`. -/
theorem sum_range_scoreIncr_t₀ : ∑ k ∈ range 2, scoreIncr t₀ d₀ z₀ 0 k = 1 / 2 := by
  simp only [scoreIncr, wMean, wSum, atRiskInd, eventInd, sum_range_succ, range_zero, sum_empty,
    Fin.sum_univ_two, t₀, d₀, z₀]
  norm_num

/-- Step `0`: weighted variance `1/2 - (1/2)² = 1/4`, one event. Step `1`: variance `0`. -/
theorem sum_range_infoIncr_t₀ : ∑ k ∈ range 2, infoIncr t₀ d₀ z₀ 0 k = 1 / 4 := by
  simp only [infoIncr, eventCount, wVar, wMean, wSum, atRiskInd, eventInd, sum_range_succ,
    range_zero, sum_empty, Fin.sum_univ_two, t₀, d₀, z₀]
  norm_num

theorem riskSet_t₀_zero : riskSet (fun l => (t₀ l : ℝ)) 0 = univ := by
  ext l
  simp only [riskSet, mem_filter, mem_univ, true_and, iff_true]
  fin_cases l <;> norm_num [t₀]

theorem riskSet_t₀_one : riskSet (fun l => (t₀ l : ℝ)) 1 = {1} := by
  ext l
  simp only [riskSet, mem_filter, mem_univ, true_and, mem_singleton]
  fin_cases l <;> norm_num [t₀]

theorem filter_d₀ : univ.filter (fun i => d₀ i = true) = univ := by decide

/-- Cox's score of the same data, computed from `riskMean`. -/
theorem coxScore_t₀ : coxScore (fun l => (t₀ l : ℝ)) d₀ z₀ 0 = 1 / 2 := by
  rw [coxScore, filter_d₀, Fin.sum_univ_two, riskMean, riskMean, riskSet_t₀_zero, riskSet_t₀_one]
  simp [Fin.sum_univ_two, z₀]
  norm_num

/-- Cox's observed information of the same data, computed from `riskVar`. -/
theorem coxInformation_t₀ : coxInformation (fun l => (t₀ l : ℝ)) d₀ z₀ 0 = 1 / 4 := by
  rw [coxInformation, filter_d₀, Fin.sum_univ_two, riskVar, riskVar, riskMean, riskMean,
    riskSet_t₀_zero, riskSet_t₀_one]
  simp [Fin.sum_univ_two, z₀]
  norm_num

/-- The bridge hypothesis holds for these data. -/
theorem supp_t₀ : ∀ i, d₀ i = true → 1 ≤ t₀ i ∧ t₀ i ≤ 2 := by decide

example : ∑ k ∈ range 2, scoreIncr t₀ d₀ z₀ 0 k = coxScore (fun l => (t₀ l : ℝ)) d₀ z₀ 0 := by
  rw [sum_range_scoreIncr_t₀, coxScore_t₀]

example : ∑ k ∈ range 2, infoIncr t₀ d₀ z₀ 0 k = coxInformation (fun l => (t₀ l : ℝ)) d₀ z₀ 0 := by
  rw [sum_range_infoIncr_t₀, coxInformation_t₀]

/-- Each subject has at most one event: subject `1` jumps only at step `1`. -/
example : ∑ k ∈ range 3, eventInd t₀ d₀ k 1 = 1 := by
  simp [eventInd, t₀, d₀]

/-! ### The no-ties hypothesis is needed -/

/-- Two simultaneous unit jumps: `(∑ aᵢ xᵢ)² = 4` but `∑ aᵢ² xᵢ = 2`. -/
theorem sq_sum_ne_of_tie :
    (∑ _i : Fin 2, (1 : ℝ) * 1) ^ 2 ≠ ∑ _i : Fin 2, (1 : ℝ) ^ 2 * 1 := by
  norm_num

/-! ### A non-degenerate model satisfying `IsCoxCountingProcess` -/

/-- A fair coin. -/
noncomputable def coin : Measure Bool := (2 : ℝ≥0∞)⁻¹ • (Measure.dirac true + Measure.dirac false)

instance : IsProbabilityMeasure coin := by
  constructor
  rw [coin, Measure.smul_apply, Measure.add_apply, measure_univ, measure_univ, one_add_one_eq_two,
    smul_eq_mul, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

theorem integral_coin (f : Bool → ℝ) : ∫ ω, f ω ∂coin = (f true + f false) / 2 := by
  rw [coin, integral_smul_measure, integral_add_measure (Integrable.of_finite)
    (Integrable.of_finite), integral_dirac, integral_dirac]
  simp
  ring

/-- The σ-algebras of the coin filtration: trivial at step `0`, everything from step `1` on. -/
abbrev coinSeq (k : ℕ) : MeasurableSpace Bool := if k = 0 then ⊥ else ⊤

theorem monotone_coinSeq : Monotone coinSeq := by
  intro i j hij
  by_cases hi : i = 0
  · simp only [coinSeq, hi, ↓reduceIte]
    exact bot_le
  · have hj : j ≠ 0 := by omega
    simp only [coinSeq, hi, hj, ↓reduceIte, le_refl]

theorem coinSeq_le (k : ℕ) : coinSeq k ≤ Bool.instMeasurableSpace := by
  unfold coinSeq
  split_ifs
  · exact bot_le
  · exact le_rfl

/-- Nothing is known at step `0`; everything is known from step `1` on. -/
def coinFiltration : Filtration ℕ Bool.instMeasurableSpace :=
  ⟨coinSeq, monotone_coinSeq, coinSeq_le⟩

theorem coinFiltration_zero : (coinFiltration 0 : MeasurableSpace Bool) = ⊥ := rfl

theorem coinFiltration_of_ne_zero {k : ℕ} (hk : k ≠ 0) :
    (coinFiltration k : MeasurableSpace Bool) = Bool.instMeasurableSpace := by
  change coinSeq k = _
  simp only [coinSeq, hk, ↓reduceIte]
  rfl

theorem stronglyMeasurable_coinFiltration {k : ℕ} (hk : k ≠ 0) (f : Bool → ℝ) :
    StronglyMeasurable[coinFiltration k] f := by
  rw [coinFiltration_of_ne_zero hk]
  exact Measurable.of_discrete.stronglyMeasurable

/-- For `n = 1` the single subject has its event at grid time `1` if the coin shows `true`, and is
censored at grid time `2` otherwise; for `n ≠ 1` nobody is observed. -/
def tc (n : ℕ) (ω : Bool) (_i : Fin n) : ℕ := if n = 1 then (if ω then 1 else 2) else 0

/-- The event indicator: observed exactly when `n = 1` and the coin shows `true`. -/
def dc (n : ℕ) (ω : Bool) (_i : Fin n) : Bool := decide (n = 1) && ω

/-- Zero covariate. -/
def zc (n : ℕ) (_ω : Bool) (_i : Fin n) : ℝ := 0

/-- Baseline hazard: `1/2` at grid time `1` (for `n = 1`), `0` otherwise. -/
noncomputable def dαc (n k : ℕ) : ℝ := if n = 1 ∧ k = 0 then 1 / 2 else 0

theorem eventInd_tc_of_ne_zero {n k : ℕ} (hk : k ≠ 0) (i : Fin n) :
    (fun ω => eventInd (tc n ω) (dc n ω) k i) = 0 := by
  funext ω
  by_cases hn : n = 1
  · cases ω <;> simp [eventInd, tc, dc, hn, hk]
  · simp [eventInd, tc, hn]

theorem isCoxCountingProcess_coin :
    IsCoxCountingProcess coin (fun _ => coinFiltration) tc dc zc dαc 0 0 where
  atRisk_measurable n k l := by
    by_cases hk : k = 0
    · subst hk
      have hfun : (fun ω => atRiskInd (tc n ω) 0 l) = fun _ => if n = 1 then 1 else 0 := by
        funext ω
        by_cases hn : n = 1 <;> cases ω <;> simp [atRiskInd, tc, hn]
      rw [hfun]
      exact stronglyMeasurable_const
    · exact stronglyMeasurable_coinFiltration hk _
  event_measurable n k i := stronglyMeasurable_coinFiltration (Nat.succ_ne_zero k) _
  covariate_measurable n l := stronglyMeasurable_const
  bound_nonneg := le_rfl
  covariate_bound n ω l := by simp [zc]
  hazard_nonneg n k := by unfold dαc; split_ifs <;> norm_num
  intensity n k i := by
    by_cases hk : k = 0
    · subst hk
      rw [coinFiltration_zero, condExp_bot]
      refine Filter.Eventually.of_forall fun ω => ?_
      rw [integral_coin]
      by_cases hn : n = 1
      · subst hn
        cases ω <;> simp [eventInd, atRiskInd, tc, dc, zc, dαc]
      · simp [eventInd, atRiskInd, tc, dc, zc, dαc, hn]
    · rw [eventInd_tc_of_ne_zero hk i, condExp_zero]
      refine Filter.Eventually.of_forall fun ω => ?_
      simp [dαc, hk]
  no_ties n := by
    refine Filter.Eventually.of_forall fun ω k => ?_
    by_cases hn : n = 1
    · subst hn
      simp only [eventCount, Fin.sum_univ_one]
      exact eventInd_le_one _ _ _ _
    · simp [eventCount, eventInd, tc, hn]

/-- In the coin model the event at grid time `1` has probability `1 / 2`: the model is not
degenerate. -/
theorem coin_event_prob : coin {ω | eventInd (tc 1 ω) (dc 1 ω) 0 0 = 1} = 2⁻¹ := by
  have hset : {ω | eventInd (tc 1 ω) (dc 1 ω) 0 0 = 1} = {true} := by
    ext ω
    cases ω <;> simp [eventInd, tc, dc]
  rw [hset, coin, Measure.smul_apply, Measure.add_apply,
    Measure.dirac_apply_of_mem (Set.mem_singleton true),
    Measure.dirac_apply' _ (measurableSet_singleton true)]
  simp

/-! ### A two-subject model with a nonzero score -/

/-- The uniform probability on `Fin 3`. -/
noncomputable def unif3 : Measure (Fin 3) :=
  (3 : ℝ≥0∞)⁻¹ • (Measure.dirac 0 + Measure.dirac 1 + Measure.dirac 2)

instance : IsProbabilityMeasure unif3 := by
  constructor
  rw [unif3, Measure.smul_apply, Measure.add_apply, Measure.add_apply, measure_univ, measure_univ,
    measure_univ, smul_eq_mul, show (1 : ℝ≥0∞) + 1 + 1 = 3 by norm_num,
    ENNReal.inv_mul_cancel (by norm_num) ENNReal.ofNat_ne_top]

theorem integral_unif3 (f : Fin 3 → ℝ) : ∫ ω, f ω ∂unif3 = (f 0 + f 1 + f 2) / 3 := by
  rw [unif3, integral_smul_measure, integral_add_measure Integrable.of_finite Integrable.of_finite,
    integral_add_measure Integrable.of_finite Integrable.of_finite, integral_dirac, integral_dirac,
    integral_dirac]
  simp
  ring

/-- The σ-algebras of the `Fin 3` filtration: trivial at step `0`, everything from step `1` on. -/
abbrev seq3 (k : ℕ) : MeasurableSpace (Fin 3) := if k = 0 then ⊥ else ⊤

theorem monotone_seq3 : Monotone seq3 := by
  intro i j hij
  by_cases hi : i = 0
  · simp only [seq3, hi, ↓reduceIte]
    exact bot_le
  · have hj : j ≠ 0 := by omega
    simp only [seq3, hi, hj, ↓reduceIte, le_refl]

theorem seq3_le (k : ℕ) : seq3 k ≤ Fin.instMeasurableSpace 3 := by
  unfold seq3
  split_ifs
  · exact bot_le
  · exact le_rfl

/-- Nothing is known at step `0`; everything is known from step `1` on. -/
def filtration3 : Filtration ℕ (Fin.instMeasurableSpace 3) := ⟨seq3, monotone_seq3, seq3_le⟩

theorem filtration3_zero : (filtration3 0 : MeasurableSpace (Fin 3)) = ⊥ := rfl

theorem stronglyMeasurable_filtration3 {k : ℕ} (hk : k ≠ 0) (f : Fin 3 → ℝ) :
    StronglyMeasurable[filtration3 k] f := by
  have hF : (filtration3 k : MeasurableSpace (Fin 3)) = Fin.instMeasurableSpace 3 := by
    change seq3 k = _
    simp only [seq3, hk, ↓reduceIte]
    rfl
  rw [hF]
  exact Measurable.of_discrete.stronglyMeasurable

/-- For `n = 2` both subjects have grid time `1`; for `n ≠ 2` nobody is observed. -/
def t3 (n : ℕ) (_ω : Fin 3) (_i : Fin n) : ℕ := if n = 2 then 1 else 0

/-- For `n = 2`, subject `i` has its event exactly when `ω = i`; `ω = 2` means no event. -/
def d3 (n : ℕ) (ω : Fin 3) (i : Fin n) : Bool := decide (n = 2) && decide (ω.val = i.val)

/-- Covariates `1, 0` for `n = 2`. -/
def z3 (n : ℕ) (_ω : Fin 3) (i : Fin n) : ℝ := if n = 2 then (if i.val = 0 then 1 else 0) else 0

/-- Baseline hazard `1/3` at grid time `1` (for `n = 2`), `0` otherwise. -/
noncomputable def dα3 (n k : ℕ) : ℝ := if n = 2 ∧ k = 0 then 1 / 3 else 0

theorem eventInd_t3_of_ne_zero {n k : ℕ} (hk : k ≠ 0) (i : Fin n) :
    (fun ω => eventInd (t3 n ω) (d3 n ω) k i) = 0 := by
  funext ω
  by_cases hn : n = 2
  · simp [eventInd, t3, hn]
    omega
  · simp [eventInd, t3, hn]

theorem isCoxCountingProcess_fin3 :
    IsCoxCountingProcess unif3 (fun _ => filtration3) t3 d3 z3 dα3 0 1 where
  atRisk_measurable n k l := by
    by_cases hk : k = 0
    · subst hk
      have hfun : (fun ω => atRiskInd (t3 n ω) 0 l) = fun _ => if n = 2 then 1 else 0 := by
        funext ω
        by_cases hn : n = 2 <;> simp [atRiskInd, t3, hn]
      rw [hfun]
      exact stronglyMeasurable_const
    · exact stronglyMeasurable_filtration3 hk _
  event_measurable n k i := stronglyMeasurable_filtration3 (Nat.succ_ne_zero k) _
  covariate_measurable n l := stronglyMeasurable_const
  bound_nonneg := zero_le_one
  covariate_bound n ω l := by unfold z3; split_ifs <;> norm_num
  hazard_nonneg n k := by unfold dα3; split_ifs <;> norm_num
  intensity n k i := by
    by_cases hk : k = 0
    · subst hk
      rw [filtration3_zero, condExp_bot]
      refine Filter.Eventually.of_forall fun ω => ?_
      rw [integral_unif3]
      by_cases hn : n = 2
      · subst hn
        fin_cases i <;> simp [eventInd, atRiskInd, t3, d3, dα3]
      · simp [eventInd, atRiskInd, t3, dα3, hn]
    · rw [eventInd_t3_of_ne_zero hk i, condExp_zero]
      refine Filter.Eventually.of_forall fun ω => ?_
      simp [dα3, hk]
  no_ties n := by
    refine Filter.Eventually.of_forall fun ω k => ?_
    by_cases hn : n = 2
    · subst hn
      simp only [eventCount, Fin.sum_univ_two]
      fin_cases ω <;> by_cases hk : k = 0 <;> simp [eventInd, t3, d3, hk]
    · simp [eventCount, eventInd, t3, hn]

/-- The step-`0` score increment at `β₀ = 0`: both subjects are at risk with weighted mean
`1/2`, so it is `1 - 1/2` if subject `0` fails, `0 - 1/2` if subject `1` fails, `0` otherwise. -/
theorem scoreIncr_fin3 (ω : Fin 3) :
    scoreIncr (t3 2 ω) (d3 2 ω) (z3 2 ω) 0 0 =
      if ω = 0 then 1 / 2 else if ω = 1 then -1 / 2 else 0 := by
  fin_cases ω <;>
    simp [scoreIncr, wMean, wSum, atRiskInd, eventInd, t3, d3, z3, Fin.sum_univ_two] <;> norm_num

/-- The score increment is nonzero with probability `2/3`. -/
theorem prob_scoreIncr_fin3_ne_zero :
    unif3 {ω | scoreIncr (t3 2 ω) (d3 2 ω) (z3 2 ω) 0 0 ≠ 0} = 2 / 3 := by
  have hset : {ω | scoreIncr (t3 2 ω) (d3 2 ω) (z3 2 ω) 0 0 ≠ 0} = {0, 1} := by
    ext ω
    fin_cases ω <;> simp [scoreIncr_fin3]
  rw [hset, unif3, Measure.smul_apply, Measure.add_apply, Measure.add_apply]
  simp [Measure.dirac_apply', Set.indicator]
  rw [ENNReal.div_eq_inv_mul, one_add_one_eq_two, mul_comm]

/-- `E[(ΔU)²] = (1/4 + 1/4 + 0) / 3 = 1/6`, computed directly from the law. -/
theorem integral_scoreIncr_sq_fin3 :
    ∫ ω, scoreIncr (t3 2 ω) (d3 2 ω) (z3 2 ω) 0 0 ^ 2 ∂unif3 = 1 / 6 := by
  rw [integral_unif3]
  simp only [scoreIncr_fin3]
  norm_num

/-- The information-compensator term at step `0`: `Δα V S⁽⁰⁾ = 1/3 · 1/4 · 2 = 1/6`, the same
for every `ω`. -/
theorem compensator_term_fin3 (ω : Fin 3) :
    dα3 2 0 * (wVar (atRiskInd (t3 2 ω) 0) (z3 2 ω) 0 * wSum (atRiskInd (t3 2 ω) 0) (z3 2 ω) 0 0) =
      1 / 6 := by
  simp [dα3, wVar, wMean, wSum, atRiskInd, t3, z3]
  norm_num

/-- The predictable variation of the score (information identity) matches the direct second
moment in the two-subject model. -/
example (ω : Fin 3) :
    ∫ ω', scoreIncr (t3 2 ω') (d3 2 ω') (z3 2 ω') 0 0 ^ 2 ∂unif3 =
      dα3 2 0 * (wVar (atRiskInd (t3 2 ω) 0) (z3 2 ω) 0 *
        wSum (atRiskInd (t3 2 ω) 0) (z3 2 ω) 0 0) := by
  rw [integral_scoreIncr_sq_fin3, compensator_term_fin3]

end MathlibExtTest.Probability.Statistics.CoxCountingProcessConditions
