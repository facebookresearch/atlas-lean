/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.CoxAsymptotics

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Finset Real
open MathlibExt.Probability.Statistics.CoxPartialLikelihood
open MathlibExt.Probability.Statistics.CoxAsymptotics

namespace MathlibExtTest.Probability.Statistics.CoxAsymptotics

/-! ### Monotone likelihood: no maximizer exists

Two subjects at times `1` and `2`; only the first has an event, and it has the smaller
covariate. The score is `-exp b / (1 + exp b) < 0` for every `b`, so the partial likelihood
increases forever and has no maximizer. This is why the estimator hypothesis reads "a maximizer
whenever one exists" and why existence only holds with probability tending to one. -/

/-- Observed times of the monotone-likelihood data. -/
noncomputable def T₁ : Fin 2 → ℝ := ![1, 2]

/-- Only subject `0` has an observed event. -/
def δ₁ : Fin 2 → Bool := ![true, false]

/-- The event subject has covariate `0`, the censored one covariate `1`. -/
noncomputable def z₁ : Fin 2 → ℝ := ![0, 1]

theorem riskSet_T₁_zero : riskSet T₁ 0 = univ := by
  ext l
  simp only [riskSet, mem_filter, mem_univ, true_and, iff_true]
  fin_cases l <;> norm_num [T₁]

theorem filter_δ₁ : univ.filter (fun i => δ₁ i = true) = {0} := by decide

/-- The score of the monotone-likelihood data, computed from the definitions. -/
theorem coxScore_T₁ (b : ℝ) : coxScore T₁ δ₁ z₁ b = -(exp b / (1 + exp b)) := by
  rw [coxScore, filter_δ₁, sum_singleton, riskMean, riskSet_T₁_zero, Fin.sum_univ_two,
    Fin.sum_univ_two]
  norm_num [z₁]

theorem coxScore_T₁_neg (b : ℝ) : coxScore T₁ δ₁ z₁ b < 0 := by
  rw [coxScore_T₁]
  have := exp_pos b
  exact neg_neg_of_pos (by positivity)

/-- No maximizer: the estimator hypothesis is vacuous on this sample. -/
example : ¬ ∃ b, IsMaxOn (logPartialLikelihood₁ T₁ δ₁ z₁) Set.univ b := fun ⟨b, hb⟩ =>
  (coxScore_T₁_neg b).ne (coxScore_eq_zero_of_isMaxOn T₁ δ₁ z₁ hb)

/-- The weighted risk-set variance at `b = 0` over `{0, 1}` with covariates `0, 1` is
`1 / 2 - (1 / 2) ^ 2 = 1 / 4`, computed from the definitions. -/
example : riskVar T₁ z₁ 0 0 = 1 / 4 := by
  rw [riskVar, riskMean, riskSet_T₁_zero]
  simp only [Fin.sum_univ_two]
  norm_num [z₁]

/-! ### A sample with a root of the score at `0`

Three subjects at times `1, 2, 3`, events for the first two, covariates `1, 0, 4/5`. At `b = 0`
the first event contributes `1 - 3/5` and the second `0 - 2/5`, so the score vanishes and `0` is
the maximum partial likelihood estimate. -/

/-- Observed times. -/
noncomputable def T₂ : Fin 3 → ℝ := ![1, 2, 3]

/-- Subjects `0` and `1` have events, subject `2` is censored. -/
def δ₂ : Fin 3 → Bool := ![true, true, false]

/-- Covariates. -/
noncomputable def z₂ : Fin 3 → ℝ := ![1, 0, 4 / 5]

theorem riskSet_T₂_zero : riskSet T₂ 0 = univ := by
  ext l
  simp only [riskSet, mem_filter, mem_univ, true_and, iff_true]
  fin_cases l <;> norm_num [T₂]

theorem riskSet_T₂_one : riskSet T₂ 1 = {1, 2} := by
  ext l
  simp only [riskSet, mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
  fin_cases l <;> norm_num [T₂]

theorem filter_δ₂ : univ.filter (fun i => δ₂ i = true) = {0, 1} := by decide

theorem coxScore_T₂_zero : coxScore T₂ δ₂ z₂ 0 = 0 := by
  rw [coxScore, filter_δ₂, sum_pair (by decide)]
  simp only [riskMean, riskSet_T₂_zero, riskSet_T₂_one, Fin.sum_univ_three,
    sum_pair (show (1 : Fin 3) ≠ 2 by decide), zero_mul, exp_zero, mul_one]
  norm_num [z₂]

/-- `0` maximizes the log partial likelihood of this sample. -/
example : IsMaxOn (logPartialLikelihood₁ T₂ δ₂ z₂) Set.univ 0 :=
  isMaxOn_of_coxScore_eq_zero T₂ δ₂ z₂ coxScore_T₂_zero

/-- The deterministic location theorem on this sample: the score vanishes at `β₀ = 0`, so any
positive lower bound `m` on the information near `0` puts every maximizer within `ε` of `0`. -/
example {ε m bh : ℝ} (hε : 0 < ε) (hm : 0 < m)
    (hbh : (∃ b, IsMaxOn (logPartialLikelihood₁ T₂ δ₂ z₂) Set.univ b) →
      IsMaxOn (logPartialLikelihood₁ T₂ δ₂ z₂) Set.univ bh)
    (hI : ∀ b ∈ Set.Icc (0 - ε) (0 + ε), m < coxInformation T₂ δ₂ z₂ b) :
    coxScore T₂ δ₂ z₂ bh = 0 ∧ |bh - 0| < ε :=
  coxScore_eq_zero_and_abs_sub_lt T₂ δ₂ z₂ hε hI
    (by rw [coxScore_T₂_zero, abs_zero]; positivity) hbh

/-! ### `hasLaw_div_gaussianReal` on the standard normal -/

/-- `N(0, 4) / 4 ~ N(0, 1 / 4)`. -/
example : HasLaw (fun x : ℝ => x / ((4 : NNReal) : ℝ)) (gaussianReal 0 (4 : NNReal)⁻¹)
    (gaussianReal 0 4) :=
  hasLaw_div_gaussianReal (by norm_num) HasLaw.id

/-! ### Non-vacuity of the consistency hypotheses: a balanced tied design

At sample size `n`, with `k = n / 2`, subjects `l < 2k` have an event at the common time `1`,
covariate `1` for `l < k` and `0` for `k ≤ l < 2k`; when `n` is odd the last subject is censored
at time `0` and lies in no risk set. Every event sees the same risk set (the `2k` event
subjects, half with covariate `1`), so `Uₙ(0) = 0` and
`Iₙ(b) = 2k · exp b / (exp b + 1)²`, computed below from the definitions. Hence `Iₙ(b) / n`
converges uniformly to `ibal b = exp b / (exp b + 1)²`, with `ibal 0 = 1 / 4`, and all hypotheses
of the consistency theorem hold with `β₀ = 0`, `v = 1 / 4` and the deterministic score limit
`Z = 0`. -/

/-- Observed times of the balanced design. -/
noncomputable def Tb (n : ℕ) : Fin n → ℝ := fun l => if (l : ℕ) < 2 * (n / 2) then 1 else 0

/-- Event indicators of the balanced design. -/
def δb (n : ℕ) : Fin n → Bool := fun l => decide ((l : ℕ) < 2 * (n / 2))

/-- Covariates of the balanced design. -/
noncomputable def zb (n : ℕ) : Fin n → ℝ := fun l => if (l : ℕ) < n / 2 then 1 else 0

/-- The limiting information of the balanced design. -/
noncomputable def ibal (b : ℝ) : ℝ := exp b / (exp b + 1) ^ 2

theorem riskSet_Tb {n : ℕ} {i : Fin n} (hi : δb n i = true) :
    riskSet (Tb n) i = univ.filter (fun l => δb n l = true) := by
  simp only [δb, decide_eq_true_eq] at hi
  ext l
  simp only [riskSet, mem_filter, mem_univ, true_and, Tb, δb, decide_eq_true_eq, ite_eq_left hi]
  split_ifs with h <;> simp [h]

theorem sum_filter_δb (n : ℕ) (g : ℝ → ℝ) :
    ∑ l ∈ univ.filter (fun l => δb n l = true), g (zb n l) = ((n / 2 : ℕ) : ℝ) * (g 1 + g 0) := by
  rw [sum_filter]
  simp only [δb, zb, decide_eq_true_eq]
  rw [Fin.sum_univ_eq_sum_range (fun j => if j < 2 * (n / 2) then g (if j < n / 2 then 1 else 0)
    else 0) n]
  obtain ⟨k, hk⟩ : ∃ k, k = n / 2 := ⟨_, rfl⟩
  rw [← hk]
  obtain ⟨t, rfl⟩ : ∃ t, n = 2 * k + t := ⟨n - 2 * k, by omega⟩
  rw [sum_range_add, two_mul, sum_range_add]
  have h1 : ∑ x ∈ range k, (if x < k + k then g (if x < k then 1 else 0) else 0) =
      ∑ _x ∈ range k, g 1 :=
    sum_congr rfl fun x hx => by
      rw [mem_range] at hx; rw [ite_eq_left (by omega), ite_eq_left hx]
  have h2 : ∑ x ∈ range k, (if k + x < k + k then g (if k + x < k then 1 else 0) else 0) =
      ∑ _x ∈ range k, g 0 :=
    sum_congr rfl fun x hx => by
      rw [mem_range] at hx; rw [ite_eq_left (by omega), ite_eq_right (by omega)]
  have h3 : ∑ x ∈ range t, (if k + k + x < k + k then g (if k + k + x < k then 1 else 0)
      else 0) = 0 :=
    sum_eq_zero fun x _ => by rw [ite_eq_right (by omega)]
  rw [h1, h2, h3]
  simp only [sum_const, card_range, nsmul_eq_mul]
  ring

theorem coxScore_balanced (n : ℕ) : coxScore (Tb n) (δb n) (zb n) 0 = 0 := by
  have hmean : ∀ i ∈ univ.filter (fun l => δb n l = true),
      riskMean (Tb n) (zb n) 0 i = ((n / 2 : ℕ) : ℝ) / (2 * ((n / 2 : ℕ) : ℝ)) := by
    intro i hi
    rw [riskMean, riskSet_Tb (mem_filter.1 hi).2, sum_filter_δb n (fun x => x * exp (0 * x)),
      sum_filter_δb n (fun x => exp (0 * x))]
    simp only [zero_mul, exp_zero, mul_one]
    ring_nf
  rw [coxScore, sum_congr rfl fun i hi => by rw [hmean i hi],
    sum_filter_δb n (fun x => x - ((n / 2 : ℕ) : ℝ) / (2 * ((n / 2 : ℕ) : ℝ)))]
  rcases eq_or_ne ((n / 2 : ℕ) : ℝ) 0 with h | h
  · rw [h, zero_mul]
  · field_simp
    ring

theorem coxInformation_balanced (n : ℕ) (b : ℝ) :
    coxInformation (Tb n) (δb n) (zb n) b = 2 * ((n / 2 : ℕ) : ℝ) * ibal b := by
  rcases eq_or_ne ((n / 2 : ℕ) : ℝ) 0 with h | h
  · have hempty : univ.filter (fun l => δb n l = true) = ∅ := by
      rw [filter_eq_empty_iff]
      intro l _ hl
      simp only [δb, decide_eq_true_eq] at hl
      have : n / 2 = 0 := by exact_mod_cast h
      omega
    rw [coxInformation, hempty, sum_empty, h]; ring
  · have hvar : ∀ i ∈ univ.filter (fun l => δb n l = true), riskVar (Tb n) (zb n) b i = ibal b := by
      intro i hi
      rw [riskVar, riskMean, riskSet_Tb (mem_filter.1 hi).2,
        sum_filter_δb n (fun x => x ^ 2 * exp (b * x)), sum_filter_δb n (fun x => exp (b * x)),
        sum_filter_δb n (fun x => x * exp (b * x)), ibal]
      simp only [mul_zero, exp_zero, mul_one, one_mul, one_pow, add_zero,
        ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      have := exp_pos b
      field_simp
      ring
    rw [coxInformation, sum_congr rfl hvar, sum_const, nsmul_eq_mul]
    have hcard : ((univ.filter (fun l => δb n l = true)).card : ℝ) = 2 * ((n / 2 : ℕ) : ℝ) := by
      have := sum_filter_δb n (fun _ => 1)
      simp only [sum_const, nsmul_eq_mul, mul_one] at this
      rw [this]; ring
    rw [hcard]

theorem ibal_le_one (b : ℝ) : ibal b ≤ 1 := by
  rw [ibal, div_le_one (by positivity)]
  nlinarith [exp_pos b]

theorem ibal_nonneg (b : ℝ) : 0 ≤ ibal b := by rw [ibal]; positivity

theorem ibal_zero : ibal 0 = ((1 / 4 : NNReal) : ℝ) := by norm_num [ibal]

theorem continuous_ibal : Continuous ibal := by
  unfold ibal
  exact continuous_exp.div (by fun_prop) fun b => by positivity

/-- The uniform-information hypothesis holds for the balanced design (on any interval, with the
data deterministic): `|Iₙ(b) / n - ibal b| ≤ 1 / n`. -/
theorem abs_coxInformation_balanced_sub_le {n : ℕ} (hn : 0 < n) (b : ℝ) :
    |coxInformation (Tb n) (δb n) (zb n) b / n - ibal b| ≤ 1 / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (2 * ((n / 2 : ℕ) : ℝ)) ≤ n := by exact_mod_cast Nat.mul_div_le n 2
  have h2 : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by
    have : n ≤ 2 * (n / 2) + 1 := by omega
    exact_mod_cast this
  rw [coxInformation_balanced, show 2 * ((n / 2 : ℕ) : ℝ) * ibal b / n - ibal b =
    -(ibal b * ((n - 2 * ((n / 2 : ℕ) : ℝ)) / n)) by field_simp; ring, abs_neg,
    abs_of_nonneg (mul_nonneg (ibal_nonneg b) (div_nonneg (by linarith) hn'.le))]
  calc ibal b * ((n - 2 * ((n / 2 : ℕ) : ℝ)) / n) ≤ 1 * (1 / n) := by
        gcongr
        · exact ibal_le_one b
        · linarith
    _ = 1 / n := one_mul _

/-- The score hypothesis for the balanced design: `Uₙ(0) / √n = 0` for every `n`. -/
theorem tendstoInDistribution_score_balanced : TendstoInDistribution
    (fun (n : ℕ) (_ : Unit) ↦ coxScore (Tb n) (δb n) (zb n) 0 / √(n : ℝ)) atTop
    (fun _ => (0 : ℝ)) (fun _ ↦ Measure.dirac ()) (Measure.dirac ()) := by
  simp only [coxScore_balanced, zero_div]
  exact tendstoInDistribution_const aemeasurable_const

/-- The uniform-information hypothesis for the balanced design, on `[-1, 1]`. -/
theorem info_hyp_balanced : ∀ η > 0, Tendsto (fun n : ℕ => Measure.dirac () {_ω : Unit |
    ∃ b ∈ Set.Icc ((0 : ℝ) - 1) (0 + 1),
      η ≤ |coxInformation (Tb n) (δb n) (zb n) b / n - ibal b|}) atTop (𝓝 0) := by
  intro η hη
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 0, eventually_gt_atTop ⌈1 / η⌉₊] with n hn hnη
  symm
  convert measure_empty (μ := Measure.dirac ())
  rw [Set.eq_empty_iff_forall_notMem]
  rintro ω ⟨b, -, hb⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : 1 / η < n := lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hnη)
  have h2 : 1 / (n : ℝ) < η := by rw [div_lt_iff₀ hn']; rw [div_lt_iff₀ hη] at h1; linarith
  linarith [abs_coxInformation_balanced_sub_le hn b]

/-- **Non-vacuity of consistency.** On the one-point probability space, every maximum partial
likelihood selection for the balanced design is consistent for `β₀ = 0`; all hypotheses of
`tendstoInMeasure_coxMPLE` are discharged from the definitions. -/
example (βhat : ℕ → Unit → ℝ)
    (hβhat : ∀ n ω, (∃ b, IsMaxOn (logPartialLikelihood₁ (Tb n) (δb n) (zb n)) Set.univ b) →
      IsMaxOn (logPartialLikelihood₁ (Tb n) (δb n) (zb n)) Set.univ (βhat n ω)) :
    TendstoInMeasure (Measure.dirac ()) βhat atTop (fun _ => (0 : ℝ)) :=
  tendstoInMeasure_coxMPLE (T := fun n _ => Tb n) (δ := fun n _ => δb n)
    (z := fun n _ => zb n) (i := ibal) (v := 1 / 4) (r := 1) (by norm_num) hβhat
    tendstoInDistribution_score_balanced continuous_ibal.continuousAt ibal_zero
    info_hyp_balanced one_pos

/-- Existence with probability tending to one, for the balanced design. -/
example : Tendsto (fun n : ℕ => Measure.dirac () {_ω : Unit | ¬ ∃ b,
    IsMaxOn (logPartialLikelihood₁ (Tb n) (δb n) (zb n)) Set.univ b}) atTop (𝓝 0) :=
  tendsto_measure_not_exists_isMaxOn (T := fun n _ => Tb n) (δ := fun n _ => δb n)
    (z := fun n _ => zb n) (i := ibal) (v := 1 / 4) (r := 1) (by norm_num)
    tendstoInDistribution_score_balanced continuous_ibal.continuousAt ibal_zero
    info_hyp_balanced one_pos

/-- The limit theorem `tendstoInDistribution_coxMPLE` (arbitrary score limit) applies to the
balanced design, whose score limit is `Z = 0`: `√n βhat n ⟶ 0`. The Gaussian version needs a
design whose normalized score has a nondegenerate normal limit, which is not constructed here. -/
example (βhat : ℕ → Unit → ℝ)
    (hβhat : ∀ n ω, (∃ b, IsMaxOn (logPartialLikelihood₁ (Tb n) (δb n) (zb n)) Set.univ b) →
      IsMaxOn (logPartialLikelihood₁ (Tb n) (δb n) (zb n)) Set.univ (βhat n ω)) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) * (βhat n ω - 0)) atTop
      (fun _ => (0 : ℝ) / ((1 / 4 : NNReal) : ℝ)) (fun _ ↦ Measure.dirac ()) (Measure.dirac ()) :=
  tendstoInDistribution_coxMPLE (T := fun n _ => Tb n) (δ := fun n _ => δb n)
    (z := fun n _ => zb n) (i := ibal) (v := 1 / 4) (r := 1) (by norm_num) hβhat
    (fun _ => (measurable_from_top (f := βhat _)).aemeasurable)
    tendstoInDistribution_score_balanced continuous_ibal.continuousAt ibal_zero
    info_hyp_balanced one_pos

#print axioms riskVar_nonneg
#print axioms antitone_coxScore
#print axioms isMaxOn_of_coxScore_eq_zero
#print axioms coxScore_eq_zero_and_abs_sub_lt
#print axioms abs_sqrt_mul_sub_sub_le
#print axioms tendstoInMeasure_div_sqrt
#print axioms tendsto_measure_not_exists_isMaxOn
#print axioms tendstoInMeasure_coxMPLE
#print axioms tendstoInDistribution_coxMPLE
#print axioms tendstoInDistribution_coxMPLE_gaussian
#print axioms tendstoInMeasure_coxInformation_coxMPLE
#print axioms tendsto_coverage_cox_waldInterval_coxMPLE

end MathlibExtTest.Probability.Statistics.CoxAsymptotics
