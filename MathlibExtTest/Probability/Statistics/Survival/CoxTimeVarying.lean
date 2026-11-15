/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.CoxTimeVarying
public import MathlibExtTest.Probability.Statistics.Survival.CoxAsymptotics

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Finset Real Matrix
open MathlibExt.Probability.Statistics.CoxPartialLikelihood
open MathlibExt.Probability.Statistics.CoxAsymptoticsVector
open MathlibExt.Probability.Statistics.CoxTimeVarying
open MathlibExtTest.Probability.Statistics.CoxAsymptotics

namespace MathlibExtTest.Probability.Statistics.CoxTimeVarying

/-! ### A two-subject example computed from the definitions

Subjects at times `1, 2`; subject `0` has an event, subject `1` is censored. Subject `0` has
covariate `0` at all times, subject `1` has covariate `t` at time `t`. At the one event time
`T₀ = 1` the risk set is `{0, 1}` with covariates `0, 1`, so the score is
`0 - exp b / (1 + exp b)`: `-1/2` at `b = 0`, with information `1/4`. Freezing the covariates at
baseline (`0, 0`) gives score `0`; freezing them at each subject's own observed time (`0, 2`)
gives `-1`. The time-dependent analysis differs from both. -/

/-- Observed times. -/
noncomputable def T₁ : Fin 2 → ℝ := ![1, 2]

/-- Subject `0` has an event, subject `1` is censored. -/
def δ₁ : Fin 2 → Bool := ![true, false]

/-- Covariate processes: `0` for subject `0`, `t ↦ t` for subject `1`. -/
noncomputable def z₁ : Fin 2 → ℝ → ℝ := ![fun _ => 0, fun t => t]

/-- The same covariate processes as one-dimensional vectors. -/
noncomputable def x₁ : Fin 2 → ℝ → Fin 1 → ℝ := fun l t _ => z₁ l t

theorem riskSet_T₁_zero : riskSet T₁ 0 = univ := by
  ext l
  simp only [riskSet, mem_filter, mem_univ, true_and, iff_true]
  fin_cases l <;> norm_num [T₁]

theorem filter_δ₁ : univ.filter (fun i => δ₁ i = true) = {0} := by decide

/-- The time-dependent score, computed from the definitions. -/
theorem tvScore_T₁ (b : ℝ) : tvScore T₁ δ₁ z₁ b = -(exp b / (1 + exp b)) := by
  rw [tvScore, filter_δ₁, sum_singleton, riskMean, riskSet_T₁_zero]
  simp [Fin.sum_univ_two, z₁, T₁]

example : tvScore T₁ δ₁ z₁ 0 = -1 / 2 := by
  rw [tvScore_T₁]; norm_num

/-- The time-dependent information at `0`, computed from the definitions. -/
example : tvInformation T₁ δ₁ z₁ 0 = 1 / 4 := by
  rw [tvInformation, filter_δ₁, sum_singleton, riskVar, riskMean, riskSet_T₁_zero]
  norm_num [Fin.sum_univ_two, z₁, T₁]

/-- The vector log partial likelihood at `0` is `-log 2`. -/
example : tvLogPartialLikelihood T₁ δ₁ x₁ 0 = -log 2 := by
  rw [tvLogPartialLikelihood, filter_δ₁, sum_singleton, riskSet_T₁_zero]
  norm_num [Fin.sum_univ_two]

/-- The partial likelihood at `0` is `1/2`. -/
example : tvPartialLikelihood T₁ δ₁ x₁ 0 = 1 / 2 := by
  rw [tvPartialLikelihood, filter_δ₁, prod_singleton, riskSet_T₁_zero]
  norm_num [Fin.sum_univ_two]

/-- The vector score at `0` is `-1/2`, computed from the definitions. -/
example : tvGradient T₁ δ₁ x₁ 0 = fun _ => -1 / 2 := by
  funext j
  rw [tvGradient, filter_δ₁, sum_singleton]
  simp only [Pi.sub_apply, riskMeanVec_apply, riskSet_T₁_zero, snapshot, zero_dotProduct,
    exp_zero, mul_one, Fin.sum_univ_two]
  norm_num [x₁, z₁, T₁]

/-- The information matrix at `0` is `[[1/4]]`, computed from the definitions. -/
example : tvInfoMatrix T₁ δ₁ x₁ 0 = !![1 / 4] := by
  ext j k
  rw [tvInfoMatrix, filter_δ₁, sum_singleton]
  simp only [riskCov, of_apply, riskMeanVec_apply, riskSet_T₁_zero, snapshot, zero_dotProduct,
    exp_zero, mul_one, Fin.sum_univ_two]
  fin_cases j; fin_cases k
  norm_num [x₁, z₁, T₁]

/-- Covariates frozen at baseline: the fixed-covariate score at `0` is `0`. -/
example : coxScore T₁ δ₁ (fun l => z₁ l 0) 0 = 0 := by
  rw [coxScore, filter_δ₁, sum_singleton, riskMean, riskSet_T₁_zero]
  simp [Fin.sum_univ_two, z₁]

/-- Covariates frozen at each subject's own observed time: the fixed-covariate score at `0` is
`-1`. -/
example : coxScore T₁ δ₁ (fun l => z₁ l (T₁ l)) 0 = -1 := by
  rw [coxScore, filter_δ₁, sum_singleton, riskMean, riskSet_T₁_zero]
  norm_num [Fin.sum_univ_two, z₁, T₁]

/-- **Monotone likelihood.** The score is negative everywhere, so the time-dependent log partial
likelihood has no maximizer. -/
example : ¬ ∃ b, IsMaxOn (tvLogPartialLikelihood₁ T₁ δ₁ z₁) Set.univ b := fun ⟨b, hb⟩ => by
  have h := (isConcaveScore_tv T₁ δ₁ z₁).score_eq_zero_of_isMaxOn hb
  rw [tvScore_T₁] at h
  have : 0 < exp b / (1 + exp b) := by positivity
  linarith

/-! ### No events -/

/-- No events: the log partial likelihood, score and information all vanish. -/
example (x : Fin 2 → ℝ → Fin 1 → ℝ) (β : Fin 1 → ℝ) :
    tvLogPartialLikelihood T₁ (fun _ => false) x β = 0 ∧
      tvGradient T₁ (fun _ => false) x β = 0 ∧ tvInfoMatrix T₁ (fun _ => false) x β = 0 := by
  simp [tvLogPartialLikelihood, tvGradient, tvInfoMatrix]

/-! ### Non-vacuity of the large-sample hypotheses: a balanced design with a switching covariate

The balanced tied design of the scalar test (`Tb`, `δb`, `zb`: events at the common time `1`,
half with covariate `1`), with the covariate *switching* to `1 - zb` at every time other than
`1`: every subject's covariate takes different values at time `0` and time `1`. Only the values
at the event time `1` enter the partial likelihood, so the score and information are those of
the fixed design, and all hypotheses of `tendstoInMeasure_tvMPLE` hold with `β₀ = 0`,
`v = 1 / 4`. -/

/-- The switching covariate process. -/
noncomputable def zv (n : ℕ) : Fin n → ℝ → ℝ := fun l t => if t = 1 then zb n l else 1 - zb n l

/-- Every subject's covariate is genuinely time-dependent. -/
theorem zv_zero_ne_one (n : ℕ) (l : Fin n) : zv n l 0 ≠ zv n l 1 := by
  simp only [zv, zero_ne_one, ite_false, ite_true, zb]
  split_ifs <;> norm_num

theorem zv_Tb {n : ℕ} (i : Fin n) (hi : δb n i = true) (l : Fin n) :
    zv n l (Tb n i) = zb n l := by
  simp only [δb, decide_eq_true_eq] at hi
  simp [zv, Tb, hi]

theorem tvScore_balanced (n : ℕ) (b : ℝ) :
    tvScore (Tb n) (δb n) (zv n) b = coxScore (Tb n) (δb n) (zb n) b :=
  tvScore_of_eq (fun i hi l => zv_Tb i hi l) b

theorem tvInformation_balanced (n : ℕ) (b : ℝ) :
    tvInformation (Tb n) (δb n) (zv n) b = coxInformation (Tb n) (δb n) (zb n) b :=
  tvInformation_of_eq (fun i hi l => zv_Tb i hi l) b

/-- **Non-vacuity of consistency.** Every maximum partial likelihood selection for the balanced
design with switching covariate is consistent for `β₀ = 0`. -/
example (βhat : ℕ → Unit → ℝ)
    (hβhat : ∀ n ω, (∃ b, IsMaxOn (tvLogPartialLikelihood₁ (Tb n) (δb n) (zv n)) Set.univ b) →
      IsMaxOn (tvLogPartialLikelihood₁ (Tb n) (δb n) (zv n)) Set.univ (βhat n ω)) :
    TendstoInMeasure (Measure.dirac ()) βhat atTop (fun _ => (0 : ℝ)) :=
  tendstoInMeasure_tvMPLE (T := fun n _ => Tb n) (δ := fun n _ => δb n)
    (z := fun n _ => zv n) (i := ibal) (v := 1 / 4) (r := 1) (by norm_num) hβhat
    (by simpa only [tvScore_balanced] using tendstoInDistribution_score_balanced)
    continuous_ibal.continuousAt ibal_zero
    (by simpa only [tvInformation_balanced] using info_hyp_balanced) one_pos

/-- Existence with probability tending to one, for the switching design. -/
example : Tendsto (fun n : ℕ => Measure.dirac () {_ω : Unit | ¬ ∃ b,
    IsMaxOn (tvLogPartialLikelihood₁ (Tb n) (δb n) (zv n)) Set.univ b}) atTop (𝓝 0) :=
  tendsto_measure_not_exists_isMaxOn_tv (T := fun n _ => Tb n) (δ := fun n _ => δb n)
    (z := fun n _ => zv n) (i := ibal) (v := 1 / 4) (r := 1) (by norm_num)
    (by simpa only [tvScore_balanced] using tendstoInDistribution_score_balanced)
    continuous_ibal.continuousAt ibal_zero
    (by simpa only [tvInformation_balanced] using info_hyp_balanced) one_pos

/-- The limit theorem with an arbitrary score limit applies to the switching design, whose score
limit is `Z = 0`: `√n βhat n ⟶ 0`. -/
example (βhat : ℕ → Unit → ℝ)
    (hβhat : ∀ n ω, (∃ b, IsMaxOn (tvLogPartialLikelihood₁ (Tb n) (δb n) (zv n)) Set.univ b) →
      IsMaxOn (tvLogPartialLikelihood₁ (Tb n) (δb n) (zv n)) Set.univ (βhat n ω)) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) * (βhat n ω - 0)) atTop
      (fun _ => (0 : ℝ) / ((1 / 4 : NNReal) : ℝ)) (fun _ ↦ Measure.dirac ()) (Measure.dirac ()) :=
  tendstoInDistribution_tvMPLE (T := fun n _ => Tb n) (δ := fun n _ => δb n)
    (z := fun n _ => zv n) (i := ibal) (v := 1 / 4) (r := 1) (by norm_num) hβhat
    (fun _ => (measurable_from_top (f := βhat _)).aemeasurable)
    (by simpa only [tvScore_balanced] using tendstoInDistribution_score_balanced)
    continuous_ibal.continuousAt ibal_zero
    (by simpa only [tvInformation_balanced] using info_hyp_balanced) one_pos

/-! ### Reduction to fixed covariates -/

/-- Constant covariate processes give exactly the fixed-covariate score vector. -/
example {n p : ℕ} (T : Fin n → ℝ) (δ : Fin n → Bool) (z : Fin n → Fin p → ℝ) (β : Fin p → ℝ) :
    tvGradient T δ (fun l _ => z l) β = coxGradient T δ z β :=
  tvGradient_of_eq (T := T) (δ := δ) (x := fun l _ => z l) (z := z) (fun _ _ _ => rfl) β

end MathlibExtTest.Probability.Statistics.CoxTimeVarying
