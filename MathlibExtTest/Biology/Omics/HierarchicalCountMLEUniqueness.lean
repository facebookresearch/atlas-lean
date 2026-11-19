/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Omics.HierarchicalCountMLEUniqueness

import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

open Real Finset
open MathlibExt.Biology.Omics.HierarchicalCount

namespace MathlibExtTest.Biology.Omics.HierarchicalCountMLEUniqueness

/-! ### The sample `(0, 3)`: overdispersed -/

/-- Two counts `0, 3`. -/
abbrev k03 : Fin 2 → ℕ := ![0, 3]

/-- Its sample mean `3 / 2` and biased variance `9 / 4`, from the definitions. -/
theorem countMean_k03 : countMean k03 = 3 / 2 := by
  norm_num [countMean, Fin.sum_univ_two]

theorem countVar_k03 : countVar k03 = 9 / 4 := by
  rw [countVar, countMean_k03]; norm_num [Fin.sum_univ_two]

/-- **Non-vacuity of the hypotheses.** The sample `(0, 3)` satisfies `0 < M < V`. -/
theorem overdispersed_k03 : 0 < countMean k03 ∧ countMean k03 < countVar k03 := by
  rw [countMean_k03, countVar_k03]; norm_num

/-- Ramp sums from the definition: `R₃(1/2) = 1/2`, `R₃(3) = 3 + 2 + 1 = 6`, and the modified
Lemma 2.2 inequality at `x = 1/2`, `y = 2`: `(1/2)² R₃(2) = 3/4 ≤ 2 = 2² R₃(1/2)`. -/
example : rampSum 3 (1 / 2) = 1 / 2 ∧ rampSum 3 3 = 6 ∧
    (1 / 2 : ℝ) ^ 2 * rampSum 3 2 ≤ 2 ^ 2 * rampSum 3 (1 / 2) := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [rampSum, sum_range_succ]

/-- **`H` changes sign on this sample** (computed from the definition): `H(1/2) = 1/4 > 0` and
`H(3) = -3/4 < 0`, the value `n (M - V) / 2 = 2 (3/2 - 9/4) / 2` of
`smoothedDiscrepancy_eq_of_ge`. So the sign-change point of the proof is interior. -/
example : smoothedDiscrepancy k03 (1 / 2) = 1 / 4 ∧ smoothedDiscrepancy k03 3 = -3 / 4 := by
  refine ⟨?_, ?_⟩ <;>
    norm_num [smoothedDiscrepancy, countMean_k03, rampSum, Fin.sum_univ_two, sum_range_succ]

private lemma profileShapeScore_k03 (a : ℝ) :
    profileShapeScore a k03 = (a⁻¹ + (a + 1)⁻¹ + (a + 2)⁻¹) - 2 * (log (a + 3 / 2) - log a) := by
  rw [profileShapeScore, countMean_k03]
  norm_num [digammaIncrement, Fin.sum_univ_two, sum_range_succ]

/-- **The profile shape score changes sign, from the definition.** At `a = 1/2` it is
`46/15 - 4 log 2 > 0`; at `a = 2` it is `13/12 - 2 log (7/4) < 0` (`e¹³ < (7/4)²⁴`). -/
theorem profileShapeScore_k03_half_pos : 0 < profileShapeScore (1 / 2) k03 := by
  rw [profileShapeScore_k03]
  have h : log (1 / 2 + 3 / 2 : ℝ) - log (1 / 2) = 2 * log 2 := by
    rw [show (1 / 2 + 3 / 2 : ℝ) = 2 by norm_num, one_div, log_inv]; ring
  rw [h]
  have := log_two_lt_d9
  norm_num
  linarith

theorem profileShapeScore_k03_two_neg : profileShapeScore 2 k03 < 0 := by
  rw [profileShapeScore_k03]
  have h : log (2 + 3 / 2 : ℝ) - log 2 = log (7 / 4) := by
    rw [← log_div (by norm_num) (by norm_num)]; norm_num
  rw [h]
  have he : exp 1 ^ 13 < (7 / 4 : ℝ) ^ 24 :=
    (pow_lt_pow_left₀ exp_one_lt_d9 (exp_pos 1).le (by norm_num)).trans (by norm_num)
  have hl := log_lt_log (by positivity) he
  rw [log_pow, log_pow, log_exp] at hl
  norm_num at hl ⊢
  linarith

/-- **The concrete joint MLE: it exists, is unique, and is bracketed.** At `σ = 1` the log
marginal likelihood of `(0, 3)` has exactly one maximizer on `(0, ∞)²`. -/
example : ∃! p : ℝ × ℝ, 0 < p.1 ∧ 0 < p.2 ∧ ∀ q : ℝ × ℝ, 0 < q.1 → 0 < q.2 →
    logMarginalLik q.1 q.2 (fun _ => (1 : ℝ)) k03 ≤ logMarginalLik p.1 p.2 (fun _ => 1) k03 :=
  existsUnique_isMaxOn_logMarginalLik one_pos overdispersed_k03.1 overdispersed_k03.2

/-- Its shape lies in `(1/2, 2)` and its rate is `â / (3/2)` (numerically `â ≈ 1.0047`). The
bracket comes from the two sign evaluations above, which are computed from the definitions. -/
example {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hmax : ∀ q : ℝ × ℝ, 0 < q.1 → 0 < q.2 →
    logMarginalLik q.1 q.2 (fun _ => (1 : ℝ)) k03 ≤ logMarginalLik a b (fun _ => 1) k03) :
    1 / 2 < a ∧ a < 2 ∧ b = a / (3 / 2) := by
  obtain ⟨hM, hMV⟩ := overdispersed_k03
  have hs := score_eq_zero_of_isMaxOn one_pos hM hMV ha hb hmax
  obtain ⟨hb', hP⟩ := (score_eq_zero_iff_const ha hb one_pos hM).1 hs
  refine ⟨?_, ?_, by rw [hb', countMean_k03, one_mul]⟩
  · by_contra hc
    push Not at hc
    rcases hc.lt_or_eq with hlt | heq
    · exact absurd profileShapeScore_k03_half_pos
        (not_lt.2 (profileShapeScore_neg_of_gt hMV ha hlt hP).le)
    · rw [heq] at hP; exact absurd hP profileShapeScore_k03_half_pos.ne'
  · by_contra hc
    push Not at hc
    rcases hc.lt_or_eq with hlt | heq
    · exact absurd profileShapeScore_k03_two_neg
        (not_lt.2 (profileShapeScore_pos_of_lt hMV two_pos hlt hP).le)
    · rw [← heq] at hP; exact absurd hP profileShapeScore_k03_two_neg.ne

/-! ### Boundary: `V = M` (the overdispersion hypothesis fails) -/

/-- Two counts `0, 2`: `M = V = 1`, so `M < V` fails and no uniqueness theorem applies. -/
abbrev k02 : Fin 2 → ℕ := ![0, 2]

theorem countMean_k02 : countMean k02 = 1 := by
  norm_num [countMean, Fin.sum_univ_two]

example : countVar k02 = countMean k02 ∧ ¬ countMean k02 < countVar k02 := by
  have hV : countVar k02 = 1 := by rw [countVar, countMean_k02]; norm_num [Fin.sum_univ_two]
  rw [hV, countMean_k02]; norm_num

/-- At the boundary `H(T) = n (M - V) / 2 = 0` (from the definition, `T = 2`), so the strict
boundary term of the single-crossing proof vanishes. -/
example : smoothedDiscrepancy k02 2 = 0 := by
  norm_num [smoothedDiscrepancy, countMean_k02, rampSum, Fin.sum_univ_two, sum_range_succ]

/-- At the boundary the profile shape score at `a = 1` is `3/2 - 2 log 2 > 0`, from the
definition: the likelihood still increases in the shape there. -/
example : 0 < profileShapeScore 1 k02 := by
  rw [profileShapeScore, countMean_k02]
  norm_num [digammaIncrement, Fin.sum_univ_two, sum_range_succ]
  have := log_two_lt_d9
  linarith

/-- **The likelihood increases along the path `a ↦ (a, a)` at the boundary**, from the
definitions (`σ = 1`, `M = 1`): `ℓ(1, 1) = -4 log 2 < 4 log 2 - 5 log 3 = ℓ(2, 2)`, i.e.
`3⁵ = 243 < 256 = 2⁸`. -/
example : logMarginalLik 1 1 (fun _ => (1 : ℝ)) k02 < logMarginalLik 2 2 (fun _ => 1) k02 := by
  rw [logMarginalLik_eq one_pos one_pos (fun _ => one_pos),
    logMarginalLik_eq two_pos two_pos (fun _ => one_pos)]
  norm_num [Fin.sum_univ_two, sum_range_succ]
  have h3 : log ((3 : ℝ) ^ 5) < log ((2 : ℝ) ^ 8) := log_lt_log (by norm_num) (by norm_num)
  rw [log_pow, log_pow] at h3
  push_cast at h3
  linarith

/-- **No finite joint MLE at the boundary `V = M`** (the converse, at `σ = 1`). -/
example : ¬ ∃ p : ℝ × ℝ, 0 < p.1 ∧ 0 < p.2 ∧ ∀ q : ℝ × ℝ, 0 < q.1 → 0 < q.2 →
    logMarginalLik q.1 q.2 (fun _ => (1 : ℝ)) k02 ≤ logMarginalLik p.1 p.2 (fun _ => 1) k02 := by
  have hV : countVar k02 = 1 := by rw [countVar, countMean_k02]; norm_num [Fin.sum_univ_two]
  exact not_exists_isMaxOn_logMarginalLik one_pos (by rw [countMean_k02]; norm_num)
    (by rw [hV, countMean_k02])

/-! ### Underdispersed: `V < M`, no finite MLE (the converse of Theorem 2) -/

/-- Two counts `1, 1`: `M = 1`, `V = 0`. -/
abbrev k11 : Fin 2 → ℕ := ![1, 1]

theorem countMean_k11 : countMean k11 = 1 := by
  norm_num [countMean, Fin.sum_univ_two]

theorem countVar_k11 : countVar k11 = 0 := by
  rw [countVar, countMean_k11]; norm_num [Fin.sum_univ_two]

/-- **Non-vacuity of the converse's hypotheses**: `0 < M` and `V ≤ M` (strictly). -/
theorem underdispersed_k11 : 0 < countMean k11 ∧ countVar k11 < countMean k11 := by
  rw [countMean_k11, countVar_k11]; norm_num

/-- **The profile shape score is positive everywhere, from the definition** (independently of
`H`): it is `2 / a - 2 log ((a + 1) / a)`, positive since `log x < x - 1` for `x ≠ 1`. -/
example {a : ℝ} (ha : 0 < a) : 0 < profileShapeScore a k11 := by
  rw [profileShapeScore, countMean_k11]
  norm_num [digammaIncrement, Fin.sum_univ_two]
  have hx : log ((a + 1) / a) < (a + 1) / a - 1 :=
    log_lt_sub_one_of_pos (by positivity) (by rw [ne_eq, div_eq_one_iff_eq ha.ne']; linarith)
  rw [log_div (by positivity) ha.ne'] at hx
  have : (a + 1) / a - 1 = a⁻¹ := by field_simp; ring
  linarith

/-- **The likelihood increases along the path `a ↦ (a, a)`**, from the definitions (`σ = 1`,
`M = 1`): `ℓ(1, 1) = -4 log 2 < 6 log 2 - 6 log 3 = ℓ(2, 2)`, i.e. `3⁶ = 729 < 1024 = 2¹⁰`. -/
example : logMarginalLik 1 1 (fun _ => (1 : ℝ)) k11 < logMarginalLik 2 2 (fun _ => 1) k11 := by
  rw [logMarginalLik_eq one_pos one_pos (fun _ => one_pos),
    logMarginalLik_eq two_pos two_pos (fun _ => one_pos)]
  norm_num [Fin.sum_univ_two]
  have h3 : log ((3 : ℝ) ^ 6) < log ((2 : ℝ) ^ 10) := log_lt_log (by norm_num) (by norm_num)
  rw [log_pow, log_pow] at h3
  push_cast at h3
  linarith

/-- **No finite joint MLE for `(1, 1)`** (the converse, at `σ = 1`): `ℓ` has no maximizer on
`(0, ∞)²`, and the joint score equations have no positive root. -/
example : ¬ ∃ p : ℝ × ℝ, 0 < p.1 ∧ 0 < p.2 ∧ ∀ q : ℝ × ℝ, 0 < q.1 → 0 < q.2 →
    logMarginalLik q.1 q.2 (fun _ => (1 : ℝ)) k11 ≤ logMarginalLik p.1 p.2 (fun _ => 1) k11 :=
  not_exists_isMaxOn_logMarginalLik one_pos underdispersed_k11.1 underdispersed_k11.2.le

example {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ¬ (shapeScore a b (fun _ => (1 : ℝ)) k11 = 0 ∧ rateScore a b (fun _ => 1) k11 = 0) :=
  score_ne_zero_of_le one_pos underdispersed_k11.1 underdispersed_k11.2.le ha hb

/-- **Contrast: the overdispersed `(0, 3)` fails the converse's hypothesis**, and its finite MLE
exists and is unique (`existsUnique_isMaxOn_logMarginalLik`, exercised on `k03` above). -/
example : ¬ countVar k03 ≤ countMean k03 := not_le.2 overdispersed_k03.2

/-! ### Heterogeneous size factors (the common-size-factor hypothesis fails) -/

/-- With size factors `1, 3` (mean `2`) and counts `0, 3`, the common-size-factor rate root
`s̄ a / M = 2 · 1 / (3/2) = 4/3` at `a = 1` is not a root of the rate score
(`3/4 - 3/7 + 3/4 - 12/13 = 27/182 ≠ 0`), so the reduction to one profile equation
(`score_eq_zero_iff_const`) is unavailable and uniqueness is not claimed. -/
example : rateScore 1 (4 / 3) ![1, 3] k03 = 27 / 182 ∧ rateScore 1 (4 / 3) ![1, 3] k03 ≠ 0 := by
  refine ⟨?_, ?_⟩ <;> norm_num [rateScore, Fin.sum_univ_two]

/-! ### Axioms -/

#print axioms rampSum_mul_sq_le
#print axioms smoothedDiscrepancy_neg_of_le
#print axioms profileShapeScore_eq_integral
#print axioms profileShapeScore_neg_of_le
#print axioms existsUnique_score_root
#print axioms logMarginalLik_lt_of_score_root
#print axioms existsUnique_isMaxOn_logMarginalLik
#print axioms score_eq_zero_of_isMaxOn
#print axioms smoothedDiscrepancy_nonneg
#print axioms profileShapeScore_pos_of_le
#print axioms score_ne_zero_of_le
#print axioms strictMonoOn_logMarginalLik_rateRoot
#print axioms not_exists_isMaxOn_logMarginalLik

end MathlibExtTest.Biology.Omics.HierarchicalCountMLEUniqueness
