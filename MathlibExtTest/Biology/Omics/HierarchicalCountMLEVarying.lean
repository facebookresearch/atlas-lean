/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Omics.HierarchicalCountMLEVarying

import Mathlib.Analysis.Complex.ExponentialBounds
import MathlibExt.Biology.Omics.HierarchicalCountMLEUniqueness
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Independence.InfinitePi

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter Topology Finset Function
open MathlibExt.Biology.Omics.HierarchicalCount

namespace MathlibExtTest.Biology.Omics.HierarchicalCountMLEVarying

/-! ### The rate root and the profile at heterogeneous size factors -/

/-- Size factors `(1, 2)`, counts `(1, 2)`, shape `1`: the rate score at `b = 1` is
`2 - 2/2 - 3/3 = 0`, computed from the definition. -/
example : rateScore 1 1 ![(1 : ℝ), 2] ![1, 2] = 0 := by
  norm_num [rateScore, Fin.sum_univ_two]

/-- Hence the rate root is `b̂(1) = 1`; the rate score is `-(3b + 4)(b - 1) / (b (b + 1) (b + 2))`,
so `1` is its only positive root. -/
example : rateRoot 1 ![(1 : ℝ), 2] ![1, 2] = 1 :=
  rateRoot_eq one_pos one_pos (fun i => by fin_cases i <;> norm_num)
    (by norm_num [rateScore, Fin.sum_univ_two])

/-- The profile shape score there:
`shapeScore 1 1 = (1 + log 1 - log 2) + (3/2 + log 1 - log 3)`. -/
example : profileShapeScoreVarying 1 ![(1 : ℝ), 2] ![1, 2] = 5 / 2 - log 6 := by
  have h : rateRoot 1 ![(1 : ℝ), 2] ![1, 2] = 1 :=
    rateRoot_eq one_pos one_pos (fun i => by fin_cases i <;> norm_num)
      (by norm_num [rateScore, Fin.sum_univ_two])
  rw [profileShapeScoreVarying, h]
  simp only [shapeScore, digammaIncrement, Fin.sum_univ_two]
  norm_num
  rw [show (6 : ℝ) = 2 * 3 by norm_num, log_mul (by norm_num) (by norm_num)]
  ring

/-- **Boundary: all counts zero.** Then no positive rate root exists (the rate score is positive)
and `rateRoot` is the default `0`. -/
example : rateRoot 1 ![(1 : ℝ), 2] ![0, 0] = 0 := by
  have hs : ∀ i, 0 < ![(1 : ℝ), 2] i := fun i => by fin_cases i <;> norm_num
  rw [rateRoot, dite_eq_right]
  rintro ⟨b, hb, h⟩
  linarith [rateScore_pos_of_counts_eq_zero one_pos hb hs (k := ![0, 0])
    (fun i => by fin_cases i <;> rfl)]

/-- At a common size factor the rate root is the closed form `σ a / M`: here `1 · 2 / 1`. -/
example : rateRoot 2 (fun _ : Fin 2 => (1 : ℝ)) (fun _ => 1) = 2 := by
  rw [rateRoot_const two_pos one_pos (by norm_num [countMean])]
  norm_num [countMean]

/-! ### The overdispersion condition -/

/-- Size factors `(1, 2)`, counts `(0, 6)`: pooled rate `μ̂ = 6 / 3 = 2`, fitted means `(2, 4)`,
residual sum of squares `4 + 4 = 8 > 6 = ∑ kᵢ`. -/
example : pooledMean ![(1 : ℝ), 2] ![0, 6] = 2 ∧
    ∑ i, ((![0, 6] i : ℕ) : ℝ) < ∑ i, (((![0, 6] i : ℕ) : ℝ) -
      ![(1 : ℝ), 2] i * pooledMean ![(1 : ℝ), 2] ![0, 6]) ^ 2 := by
  norm_num [pooledMean, Fin.sum_univ_two]

/-- **Non-vacuity of the existence theorem.** The sample above satisfies its hypothesis, so the
joint score equations have a positive solution. -/
example : ∃ a b, 0 < a ∧ 0 < b ∧ shapeScore a b ![(1 : ℝ), 2] ![0, 6] = 0 ∧
    rateScore a b ![(1 : ℝ), 2] ![0, 6] = 0 :=
  exists_score_root_of_overdispersed_varying (fun i => by fin_cases i <;> norm_num)
    (by norm_num [pooledMean, Fin.sum_univ_two])

/-- **Heterogeneity matters.** Counts `(1, 10)` at size factors `(1, 10)` are exactly proportional
to the size factors: the residuals around the fitted Poisson means vanish and the condition fails,
although the same counts read at a common size factor look overdispersed (`M = 11/2 < V = 81/4`). -/
example : ¬ (∑ i, ((![1, 10] i : ℕ) : ℝ) < ∑ i, (((![1, 10] i : ℕ) : ℝ) -
      ![(1 : ℝ), 10] i * pooledMean ![(1 : ℝ), 10] ![1, 10]) ^ 2) ∧
    countMean ![1, 10] < countVar ![1, 10] := by
  norm_num [pooledMean, countMean, countVar, Fin.sum_univ_two]

/-- At a common size factor the condition is T86's `M < V`: counts `(0, 0, 3)`, `M = 1`, `V = 2`. -/
example : ∑ i, ((![0, 0, 3] i : ℕ) : ℝ) < ∑ i, (((![0, 0, 3] i : ℕ) : ℝ) -
    (fun _ : Fin 3 => (1 : ℝ)) i * pooledMean (fun _ : Fin 3 => (1 : ℝ)) ![0, 0, 3]) ^ 2 :=
  (overdispersed_const_iff one_pos _).2 (by norm_num [countMean, countVar, Fin.sum_univ_three])

/-! ### Uniqueness at a common size factor -/

/-- **Uniqueness, common size factor.** Size factor `2`, counts `(0, 0, 3)`: pooled rate
`μ̂ = 3 / 6`, fitted means `1`, residual sum of squares `1 + 1 + 4 = 6 > 3 = ∑ kᵢ`, computed from
the definition of `pooledMean`. The joint score equations have exactly one positive root. -/
example : ∃! p : ℝ × ℝ, 0 < p.1 ∧ 0 < p.2 ∧
    shapeScore p.1 p.2 (fun _ : Fin 3 => (2 : ℝ)) ![0, 0, 3] = 0 ∧
    rateScore p.1 p.2 (fun _ : Fin 3 => (2 : ℝ)) ![0, 0, 3] = 0 :=
  existsUnique_score_root_const_varying two_pos (by norm_num [pooledMean, Fin.sum_univ_three])

/-- The same sample has exactly one joint MLE over `(0, ∞)²`. -/
example : ∃! p : ℝ × ℝ, 0 < p.1 ∧ 0 < p.2 ∧ ∀ q : ℝ × ℝ, 0 < q.1 → 0 < q.2 →
    logMarginalLik q.1 q.2 (fun _ : Fin 3 => (2 : ℝ)) ![0, 0, 3] ≤
      logMarginalLik p.1 p.2 (fun _ : Fin 3 => (2 : ℝ)) ![0, 0, 3] :=
  existsUnique_isMaxOn_logMarginalLik_const_varying two_pos
    (by norm_num [pooledMean, Fin.sum_univ_three])

/-- **Boundary: equality in the overdispersion condition.** Size factor `1`, counts `(0, 2)`:
`μ̂ = 1`, residual sum of squares `1 + 1 = 2 = ∑ kᵢ`, so the strict condition fails (this is
`V = M = 1`), and then no positive root exists at all (`score_ne_zero_of_le`). -/
example : ¬ (∑ i, ((![0, 2] i : ℕ) : ℝ) < ∑ i, (((![0, 2] i : ℕ) : ℝ) -
      1 * pooledMean (fun _ : Fin 2 => (1 : ℝ)) ![0, 2]) ^ 2) ∧
    ∀ a b : ℝ, 0 < a → 0 < b →
      ¬ (shapeScore a b (fun _ : Fin 2 => (1 : ℝ)) ![0, 2] = 0 ∧
        rateScore a b (fun _ : Fin 2 => (1 : ℝ)) ![0, 2] = 0) := by
  refine ⟨by norm_num [pooledMean, Fin.sum_univ_two], fun a b ha hb => ?_⟩
  exact score_ne_zero_of_le one_pos (by norm_num [countMean, Fin.sum_univ_two])
    (by norm_num [countVar, countMean, Fin.sum_univ_two]) ha hb

/-! ### Heterogeneous size factors: two roots of the score equations -/

namespace TwoRoots

/-- Size factors `(100, 1)`. -/
abbrev s₀ : Fin 2 → ℝ := ![100, 1]

/-- Counts `(2, 1)`. -/
abbrev k₀ : Fin 2 → ℕ := ![2, 1]

private lemma hs₀ : ∀ i, 0 < s₀ i := fun i => by fin_cases i <;> norm_num

private lemma shapeScore_eq (a b : ℝ) :
    shapeScore a b s₀ k₀ = 2 * a⁻¹ + (a + 1)⁻¹ + 2 * log b - log (b + 100) - log (b + 1) := by
  simp [shapeScore, digammaIncrement, Fin.sum_univ_two, sum_range_succ, s₀, k₀]
  ring

/-- The rate score equation `-3 b² + (101 a - 102) b + 200 a = 0` (times `b (b + 100) (b + 1)`)
has the positive root `b = 1` at `a = 15/43`, from the definition. -/
private lemma rateRoot₁ : rateRoot (15 / 43) s₀ k₀ = 1 :=
  rateRoot_eq (by norm_num) one_pos hs₀ (by norm_num [rateScore, Fin.sum_univ_two, s₀, k₀])

/-- The rate root at `a = 12/11` is `10`. -/
private lemma rateRoot₂ : rateRoot (12 / 11) s₀ k₀ = 10 :=
  rateRoot_eq (by norm_num) (by norm_num) hs₀ (by norm_num [rateScore, Fin.sum_univ_two, s₀, k₀])

/-- The rate root at `a = 402/103` is `100`. -/
private lemma rateRoot₃ : rateRoot (402 / 103) s₀ k₀ = 100 :=
  rateRoot_eq (by norm_num) (by norm_num) hs₀ (by norm_num [rateScore, Fin.sum_univ_two, s₀, k₀])

/-- At `a = 15/43` the profile is `86/15 + 43/58 - log 202 > 0` (`log 101 < 5`). -/
private lemma profile₁_pos : 0 < profileShapeScoreVarying (15 / 43) s₀ k₀ := by
  rw [profileShapeScoreVarying, rateRoot₁, shapeScore_eq]
  have h101 : log 101 < 5 := by
    rw [log_lt_iff_lt_exp (by norm_num)]
    have : (101 : ℝ) < exp 1 ^ 5 :=
      lt_trans (by norm_num) (pow_lt_pow_left₀ exp_one_gt_d9 (by norm_num) (by norm_num))
    rwa [← exp_nat_mul, show ((5 : ℕ) : ℝ) * 1 = 5 by norm_num] at this
  have h2 := log_two_lt_d9
  norm_num
  linarith

/-- At `a = 12/11` the profile is `319/138 - log (121/10) < 0` (`e⁷ < (121/10)³`). -/
private lemma profile₂_neg : profileShapeScoreVarying (12 / 11) s₀ k₀ < 0 := by
  rw [profileShapeScoreVarying, rateRoot₂, shapeScore_eq]
  have e110 : log 110 = log 10 + log 11 := by
    rw [← log_mul (by norm_num) (by norm_num)]; norm_num
  have hlog : 7 / 3 < 2 * log 11 - log 10 := by
    have e : 2 * log 11 - log 10 = log (121 / 10) := by
      rw [log_div (by norm_num) (by norm_num), show (121 : ℝ) = 11 ^ 2 by norm_num, log_pow]
      push_cast; ring
    rw [e, lt_log_iff_exp_lt (by norm_num)]
    have h7 : exp (7 / 3) ^ 3 = exp 1 ^ 7 := by rw [← exp_nat_mul, ← exp_nat_mul]; norm_num
    have : exp (7 / 3) ^ 3 < (121 / 10 : ℝ) ^ 3 := by
      rw [h7]
      exact lt_trans (pow_lt_pow_left₀ exp_one_lt_d9 (exp_pos 1).le (by norm_num)) (by norm_num)
    exact lt_of_pow_lt_pow_left₀ 3 (by norm_num) this
  norm_num
  linarith

/-- At `a = 402/103` the profile is `103/201 + 103/505 - log (101/50) > 0`
(`log 2 + 1/100 < 0.7032 < 0.7164`). -/
private lemma profile₃_pos : 0 < profileShapeScoreVarying (402 / 103) s₀ k₀ := by
  rw [profileShapeScoreVarying, rateRoot₃, shapeScore_eq]
  have e200 : log 200 = log 2 + log 100 := by
    rw [← log_mul (by norm_num) (by norm_num)]; norm_num
  have e101 : log 101 = log 100 + log (101 / 100) := by
    rw [← log_mul (by norm_num) (by norm_num)]; norm_num
  have h1 : log (101 / 100 : ℝ) ≤ 101 / 100 - 1 := log_le_sub_one_of_pos (by norm_num)
  have h2 := log_two_lt_d9
  norm_num
  linarith

/-- **Heterogeneous size factors: two roots of the joint score equations.** Size factors
`(100, 1)`, counts `(2, 1)`. The profile shape score is positive at `a = 15/43`, negative at
`12/11` and positive at `402/103` (all from the definitions, with the rate roots `1, 10, 100`
checked exactly), so the joint score equations have two positive solutions with different
shapes. Numerically they are `(a, b) ≈ (0.550, 2.09)` and `(2.08, 39.5)`. -/
theorem two_score_roots : ∃ a b a' b', 0 < a ∧ 0 < b ∧ 0 < a' ∧ 0 < b' ∧ a < a' ∧
    shapeScore a b s₀ k₀ = 0 ∧ rateScore a b s₀ k₀ = 0 ∧
    shapeScore a' b' s₀ k₀ = 0 ∧ rateScore a' b' s₀ k₀ = 0 :=
  exists_two_score_roots hs₀ ⟨0, by simp [k₀]⟩ (by norm_num) (by norm_num) (by norm_num)
    (Set.mem_uIcc.2 (Or.inr ⟨profile₂_neg.le, profile₁_pos.le⟩))
    (Set.mem_uIcc.2 (Or.inl ⟨profile₂_neg.le, profile₃_pos.le⟩)) profile₂_neg.ne

/-- Hence the conclusion of `existsUnique_score_root_const_varying` fails at these
heterogeneous size factors. -/
example : ¬ ∃! p : ℝ × ℝ, 0 < p.1 ∧ 0 < p.2 ∧ shapeScore p.1 p.2 s₀ k₀ = 0 ∧
    rateScore p.1 p.2 s₀ k₀ = 0 := by
  rintro ⟨p, _, huniq⟩
  obtain ⟨a, b, a', b', ha, hb, ha', hb', hlt, h1, h2, h3, h4⟩ := two_score_roots
  have e := (huniq (a, b) ⟨ha, hb, h1, h2⟩).trans (huniq (a', b') ⟨ha', hb', h3, h4⟩).symm
  exact hlt.ne (Prod.mk.inj e).1

/-- **The overdispersion condition fails for this sample** (from the definitions): `μ̂ = 3/101`,
residuals `∓98/101`, residual sum of squares `19208/10201 < 3 = ∑ kᵢ`. So the sample says nothing
about uniqueness under the condition; at a common size factor the same failure would rule out any
root (`score_ne_zero_of_le`). -/
example : ¬ (∑ i, (k₀ i : ℝ) < ∑ i, ((k₀ i : ℝ) - s₀ i * pooledMean s₀ k₀) ^ 2) := by
  norm_num [pooledMean, Fin.sum_univ_two, s₀, k₀]

end TwoRoots

/-! ### Heterogeneous size factors: two roots under the overdispersion condition -/

namespace TwoRootsOverdispersed

/-- Size factors `(1000, 1/100, 100)`. -/
noncomputable abbrev s₁ : Fin 3 → ℝ := ![1000, 1 / 100, 100]

/-- Counts `(12, 1, 6)`. -/
abbrev k₁ : Fin 3 → ℕ := ![12, 1, 6]

private lemma hs₁ : ∀ i, 0 < s₁ i := fun i => by fin_cases i <;> norm_num

private lemma shapeScore_eq (a b : ℝ) :
    shapeScore a b s₁ k₁ = digammaIncrement a 12 + digammaIncrement a 1 + digammaIncrement a 6 -
      (log (b + 1000) + log (b + 1 / 100) + log (b + 100) - 3 * log b) := by
  simp [shapeScore, Fin.sum_univ_three, s₁, k₁]
  ring

private lemma log_sum_eq {b : ℝ} (hb : 0 < b) :
    log (b + 1000) + log (b + 1 / 100) + log (b + 100) - 3 * log b =
      log ((b + 1000) * (b + 1 / 100) * (b + 100) / b ^ 3) := by
  rw [log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity),
    log_mul (by positivity) (by positivity), log_pow]
  push_cast
  ring

/-- `log x < p / q` from `x^q < 2.7182818283^p ≤ e^p`. -/
private lemma log_lt_div_of_pow_lt {x : ℝ} (hx : 0 < x) {p q : ℕ} (hq : 0 < q)
    (h : x ^ q < 2.7182818283 ^ p) : log x < p / q := by
  rw [lt_div_iff₀ (by exact_mod_cast hq), mul_comm, ← log_pow,
    log_lt_iff_lt_exp (pow_pos hx q)]
  calc x ^ q < 2.7182818283 ^ p := h
    _ ≤ exp 1 ^ p := pow_le_pow_left₀ (by norm_num) exp_one_gt_d9.le p
    _ = exp p := by rw [← exp_nat_mul, mul_one]

/-- `p / q < log x` from `e^p ≤ 2.7182818286^p < x^q`. -/
private lemma div_lt_log_of_lt_pow {x : ℝ} (hx : 0 < x) {p q : ℕ} (hq : 0 < q)
    (h : 2.7182818286 ^ p < x ^ q) : (p : ℝ) / q < log x := by
  rw [div_lt_iff₀ (by exact_mod_cast hq), mul_comm, ← log_pow,
    lt_log_iff_exp_lt (pow_pos hx q)]
  calc exp p = exp 1 ^ p := by rw [← exp_nat_mul, mul_one]
    _ ≤ 2.7182818286 ^ p := pow_le_pow_left₀ (exp_pos 1).le exp_one_lt_d9.le p
    _ < x ^ q := h

/-- The rate score is linear in the shape, so every rate `b` is the rate root of one shape; at
`b = 4` the shape is `3339418/5129301`, checked from the definition. -/
private lemma rateRoot₁ : rateRoot (3339418 / 5129301) s₁ k₁ = 4 :=
  rateRoot_eq (by norm_num) (by norm_num) hs₁
    (by norm_num [rateScore, Fin.sum_univ_three, s₁, k₁])

/-- The rate root at the shape `168158/192111` is `10`. -/
private lemma rateRoot₂ : rateRoot (168158 / 192111) s₁ k₁ = 10 :=
  rateRoot_eq (by norm_num) (by norm_num) hs₁
    (by norm_num [rateScore, Fin.sum_univ_three, s₁, k₁])

/-- The rate root at the shape `1120090/310053` is `100`. -/
private lemma rateRoot₃ : rateRoot (1120090 / 310053) s₁ k₁ = 100 :=
  rateRoot_eq (by norm_num) (by norm_num) hs₁
    (by norm_num [rateScore, Fin.sum_univ_three, s₁, k₁])

/-- At `b = 4` the profile is `8.585… - log (1004 · 401/100 · 104 / 64) < 8.59 - 26/3 < 0`. -/
private lemma profile₁_neg : profileShapeScoreVarying (3339418 / 5129301) s₁ k₁ < 0 := by
  rw [profileShapeScoreVarying, rateRoot₁, shapeScore_eq, log_sum_eq (by norm_num)]
  have h := div_lt_log_of_lt_pow (x := (4 + 1000) * (4 + 1 / 100) * (4 + 100) / 4 ^ 3)
    (by norm_num) (p := 26) (q := 3) (by norm_num) (by norm_num)
  generalize log ((4 + 1000) * (4 + 1 / 100) * (4 + 100) / 4 ^ 3) = L at h ⊢
  norm_num [digammaIncrement, sum_range_succ] at h ⊢
  linarith

/-- At `b = 10` the profile is `7.118… - log (1010 · 1001/100 · 110 / 1000) > 7.11 - 106/15 > 0`. -/
private lemma profile₂_pos : 0 < profileShapeScoreVarying (168158 / 192111) s₁ k₁ := by
  rw [profileShapeScoreVarying, rateRoot₂, shapeScore_eq, log_sum_eq (by norm_num)]
  have h := log_lt_div_of_pow_lt (x := (10 + 1000) * (10 + 1 / 100) * (10 + 100) / 10 ^ 3)
    (by norm_num) (p := 106) (q := 15) (by norm_num) (by norm_num)
  generalize log ((10 + 1000) * (10 + 1 / 100) * (10 + 100) / 10 ^ 3) = L at h ⊢
  norm_num [digammaIncrement, sum_range_succ] at h ⊢
  linarith

/-- At `b = 100` the profile is `2.923… - log (1100 · 10001/100 · 200 / 10⁶) < 2.93 - 3 < 0`. -/
private lemma profile₃_neg : profileShapeScoreVarying (1120090 / 310053) s₁ k₁ < 0 := by
  rw [profileShapeScoreVarying, rateRoot₃, shapeScore_eq, log_sum_eq (by norm_num)]
  have h := div_lt_log_of_lt_pow (x := (100 + 1000) * (100 + 1 / 100) * (100 + 100) / 100 ^ 3)
    (by norm_num) (p := 3) (q := 1) (by norm_num) (by norm_num)
  generalize log ((100 + 1000) * (100 + 1 / 100) * (100 + 100) / 100 ^ 3) = L at h ⊢
  norm_num [digammaIncrement, sum_range_succ] at h ⊢
  linarith

/-- **The overdispersion condition holds** (from the definitions): `μ̂ = 19 / 1100.01`, and the
residual sum of squares exceeds `∑ kᵢ = 19` (by about `28`). -/
theorem overdispersed : ∑ i, (k₁ i : ℝ) < ∑ i, ((k₁ i : ℝ) - s₁ i * pooledMean s₁ k₁) ^ 2 := by
  norm_num [pooledMean, Fin.sum_univ_three, s₁, k₁]

/-- **Heterogeneous size factors: two roots under the overdispersion condition.** Size factors
`(1000, 1/100, 100)`, counts `(12, 1, 6)`. The profile shape score is negative at the shape with
rate root `4`, positive at the one with rate root `10` and negative at the one with rate root
`100`, so the joint score equations have two positive solutions with different shapes, although
the hypothesis of `exists_score_root_of_overdispersed_varying` holds. Numerically the profile
vanishes near `a ≈ 0.175, 0.723, 1.385`. Where the likelihood attains its maximum, and whether the
joint MLE is unique, is not decided here. -/
theorem two_score_roots : ∃ a b a' b', 0 < a ∧ 0 < b ∧ 0 < a' ∧ 0 < b' ∧ a < a' ∧
    shapeScore a b s₁ k₁ = 0 ∧ rateScore a b s₁ k₁ = 0 ∧
    shapeScore a' b' s₁ k₁ = 0 ∧ rateScore a' b' s₁ k₁ = 0 :=
  exists_two_score_roots hs₁ ⟨0, by simp [k₁]⟩ (by norm_num) (by norm_num) (by norm_num)
    (Set.mem_uIcc.2 (Or.inl ⟨profile₁_neg.le, profile₂_pos.le⟩))
    (Set.mem_uIcc.2 (Or.inr ⟨profile₃_neg.le, profile₂_pos.le⟩)) profile₂_pos.ne'

/-- Hence the conclusion of `existsUnique_score_root_const_varying` fails at these heterogeneous
size factors, under its hypothesis. -/
example : (∑ i, (k₁ i : ℝ) < ∑ i, ((k₁ i : ℝ) - s₁ i * pooledMean s₁ k₁) ^ 2) ∧
    ¬ ∃! p : ℝ × ℝ, 0 < p.1 ∧ 0 < p.2 ∧ shapeScore p.1 p.2 s₁ k₁ = 0 ∧
      rateScore p.1 p.2 s₁ k₁ = 0 := by
  refine ⟨overdispersed, ?_⟩
  rintro ⟨p, _, huniq⟩
  obtain ⟨a, b, a', b', ha, hb, ha', hb', hlt, h1, h2, h3, h4⟩ := two_score_roots
  have e := (huniq (a, b) ⟨ha, hb, h1, h2⟩).trans (huniq (a', b') ⟨ha', hb', h3, h4⟩).symm
  exact hlt.ne (Prod.mk.inj e).1

end TwoRootsOverdispersed

/-! ### Consistency: a degenerate model -/

/-- The population rate score of the constant pair `(S, K) ≡ (2, 1)` at `a = 1`, from the
definition: `1 - (1 + 1) · b / (b + 2)`, zero at `b = 2`. -/
example : popRateScoreLog (Measure.dirac ()) (fun _ => (2 : ℝ)) (fun _ => 1) 1 2 = 0 := by
  norm_num [popRateScoreLog]

/-- The conditional-mean hypothesis `E[K g(S)] = (a₀ / b₀) E[S g(S)]` holds for `(S, K) ≡ (2, 1)` at
`a₀ = 1`, `b₀ = 2`, and gives the same population root. -/
example : popRateScoreLog (Measure.dirac ()) (fun _ => (2 : ℝ)) (fun _ => 1) 1 2 = 0 :=
  popRateScoreLog_eq_zero_of_condMean two_pos measurable_const measurable_const
    (fun _ => two_pos) (integrable_const _) fun g _ _ => by simp

/-- **The rate consistency theorem is non-vacuous.** The constant pair sequence `(Sᵢ, Kᵢ) ≡ (2, 1)`
on a one-point space is pairwise independent and identically distributed, and `b₀ = 2` solves the
population rate equation at `a = 1`; the theorem gives `b̂ₙ(1) → 2`. -/
example : ∀ᵐ _ ∂(Measure.dirac ()),
    Tendsto (fun n => rateRoot 1 (fun _ : Fin n => (2 : ℝ)) fun _ => 1) atTop (𝓝 2) := by
  have h := ae_tendsto_rateRoot (μ := Measure.dirac ()) (S := fun _ _ => (2 : ℝ))
    (X := fun _ _ => 1) (a := 1) (b₀ := 2) one_pos two_pos
    (fun _ => ⟨measurable_const, measurable_const⟩) (fun _ _ => two_pos)
    (fun i j _ => indepFun_const_left _ _) (fun _ => IdentDistrib.refl aemeasurable_const)
    (integrable_const _) (by norm_num [popRateScoreLog])
  filter_upwards [h] with _ hω using hω.2

/-! ### Consistency: the joint theorem is non-vacuous -/

namespace TwoPoint

/-- The population profile shape score of the two-point law below at size factor `1`:
`(1/3) (1/a + 1/(a+1) + 1/(a+2)) - (log (a + 1) - log a)` (as in the `HierarchicalCountMLE`
tests). -/
noncomputable def q (a : ℝ) : ℝ :=
  (1 / 3) * (a⁻¹ + (a + 1)⁻¹ + (a + 2)⁻¹) - (log (a + 1) - log a)

private lemma hasDerivAt_q {a : ℝ} (ha : 0 < a) :
    HasDerivAt q ((1 / 3) * (-(a ^ 2)⁻¹ - ((a + 1) ^ 2)⁻¹ - ((a + 2) ^ 2)⁻¹) -
      ((a + 1)⁻¹ - a⁻¹)) a := by
  have h0 := hasDerivAt_inv ha.ne'
  have h1 := (hasDerivAt_inv (by positivity : a + 1 ≠ 0)).comp a ((hasDerivAt_id a).add_const 1)
  have h2 := (hasDerivAt_inv (by positivity : a + 2 ≠ 0)).comp a ((hasDerivAt_id a).add_const 2)
  have hl1 := ((hasDerivAt_id a).add_const (1 : ℝ)).log (by simp only [id]; positivity)
  have hl0 := (hasDerivAt_id a).log ha.ne'
  have := (((h0.add h1).add h2).const_mul (1 / 3)).sub (hl1.sub hl0)
  convert this using 1
  · funext x; simp [q, Function.comp_def]
  · simp only [id]; field_simp; ring

private lemma q_strictAnti : StrictAntiOn q (Set.Ioc 0 (1 / 2)) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioc 0 (1 / 2))
    (fun x hx => (hasDerivAt_q hx.1).continuousAt.continuousWithinAt) fun x hx => ?_
  rw [interior_Ioc] at hx
  obtain ⟨hx0, hx1⟩ := hx
  rw [(hasDerivAt_q hx0).deriv]
  have key : -(1 / 3) * (x ^ 2)⁻¹ - ((x + 1)⁻¹ - x⁻¹) = (2 * x - 1) / (3 * x ^ 2 * (x + 1)) := by
    field_simp; ring
  have hneg : (2 * x - 1) / (3 * x ^ 2 * (x + 1)) < 0 :=
    div_neg_of_neg_of_pos (by linarith) (by positivity)
  have : 0 < ((x + 1) ^ 2)⁻¹ + ((x + 2) ^ 2)⁻¹ := by positivity
  nlinarith

private lemma q_pos : 0 < q (3 / 10) := by
  have hlog : log (3 / 10 + 1) - log (3 / 10) < 3 / 2 := by
    rw [← log_div (by norm_num) (by norm_num), log_lt_iff_lt_exp (by norm_num)]
    have he := Real.exp_one_gt_d9
    have h3 : exp (3 / 2) ^ 2 = exp 1 ^ 3 := by
      rw [← exp_nat_mul, ← exp_nat_mul]; norm_num
    have : ((3 / 10 + 1) / (3 / 10) : ℝ) ^ 2 < exp (3 / 2) ^ 2 := by
      rw [h3]; nlinarith [pow_lt_pow_left₀ he (by norm_num) (three_ne_zero)]
    exact lt_of_pow_lt_pow_left₀ 2 (exp_pos _).le this
  unfold q; norm_num at hlog ⊢; linarith

private lemma q_neg : q (1 / 2) < 0 := by
  have h2 := Real.log_two_gt_d9
  have h32 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
  have hhalf : log (1 / 2 : ℝ) = -log 2 := by rw [one_div, log_inv]
  unfold q
  rw [hhalf]
  norm_num at h32 ⊢
  linarith

private lemma exists_root : ∃ a₀ ∈ Set.Ioo (3 / 10 : ℝ) (1 / 2), q a₀ = 0 := by
  have hcont : ContinuousOn q (Set.Icc (3 / 10) (1 / 2)) := fun x hx =>
    (hasDerivAt_q (by linarith [hx.1] : (0 : ℝ) < x)).continuousAt.continuousWithinAt
  obtain ⟨a₀, ha, h⟩ := intermediate_value_Icc' (by norm_num) hcont ⟨q_neg.le, q_pos.le⟩
  refine ⟨a₀, ⟨lt_of_le_of_ne ha.1 ?_, lt_of_le_of_ne ha.2 ?_⟩, h⟩
  · rintro rfl; linarith [q_pos]
  · rintro rfl; linarith [q_neg]

/-- The two-point count law on `Bool`: `false ↦ 0` with probability `2/3`, `true ↦ 3` with `1/3`. -/
noncomputable def ν : Measure Bool :=
  (2 / 3 : ENNReal) • Measure.dirac false + (1 / 3 : ENNReal) • Measure.dirac true

instance : IsProbabilityMeasure ν := ⟨by
  simp only [ν, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [ENNReal.div_add_div_same]; norm_num; exact ENNReal.div_self (by norm_num) (by norm_num)⟩

/-- The count read from one coordinate. -/
def g : Bool → ℕ := fun b => if b then 3 else 0

private lemma integral_ν (F : ℕ → ℝ) : ∫ b, F (g b) ∂ν = 2 / 3 * F 0 + 1 / 3 * F 3 := by
  rw [integral_fintype Integrable.of_finite]
  simp [ν, Measure.real, g, ENNReal.toReal_div]
  ring

/-- I.i.d. coordinates with law `ν`. -/
noncomputable abbrev μ : Measure (ℕ → Bool) := Measure.infinitePi (fun _ : ℕ => ν)

/-- The `i`-th count. -/
def X (i : ℕ) (ω : ℕ → Bool) : ℕ := g (ω i)

/-- The size factors, all equal to `1`. -/
def S (_ : ℕ) (_ : ℕ → Bool) : ℝ := 1

private lemma hg : Measurable g := measurable_of_finite g

private lemma hX (i : ℕ) : Measurable (X i) := hg.comp (measurable_pi_apply i)

private lemma integral_X (F : ℕ → ℝ) : ∫ ω, F (X 0 ω) ∂μ = 2 / 3 * F 0 + 1 / 3 * F 3 := by
  have hmp := measurePreserving_eval_infinitePi (μ := fun _ : ℕ => ν) 0
  rw [← integral_ν, ← hmp.map_eq, integral_map (measurable_pi_apply 0).aemeasurable
    (Integrable.of_finite).aestronglyMeasurable]
  rfl

private lemma hφ : Measurable fun k : ℕ => ((1 : ℝ), k) := measurable_of_countable _

private lemma indep : Pairwise ((· ⟂ᵢ[μ] ·) on fun i ω => (S i ω, X i ω)) := fun _ _ hij =>
  ((iIndepFun_infinitePi (P := fun _ : ℕ => ν) (X := fun _ => g) (fun _ => hg)).indepFun
    hij).comp hφ hφ

private lemma ident (i : ℕ) :
    IdentDistrib (fun ω => (S i ω, X i ω)) (fun ω => (S 0 ω, X 0 ω)) μ μ := by
  have h : ∀ j, MeasurePreserving (fun ω : ℕ → Bool => ω j) μ ν := fun j =>
    measurePreserving_eval_infinitePi (μ := fun _ : ℕ => ν) j
  exact ((⟨(measurable_pi_apply i).aemeasurable, (measurable_pi_apply 0).aemeasurable,
    by rw [(h i).map_eq, (h 0).map_eq]⟩ : IdentDistrib (fun ω : ℕ → Bool => ω i)
      (fun ω => ω 0) μ μ).comp hg).comp hφ

private lemma integrable_X : Integrable (fun ω => (X 0 ω : ℝ)) μ := by
  refine (integrable_const (3 : ℝ)).mono' ((measurable_from_nat.comp (hX 0)).aestronglyMeasurable)
    (ae_of_all _ fun ω => ?_)
  simp only [X, g]; split_ifs <;> norm_num

/-- The population rate score in closed form: `a - (a + 1) c / (c + 1) = (a - c) / (c + 1)`. -/
private lemma popRate_eq (a c : ℝ) (hc : 0 < c) :
    popRateScoreLog μ (S 0) (X 0) a c = (a - c) / (c + 1) := by
  simp only [popRateScoreLog, S]
  rw [integral_X (fun k => (a + k) * (c / (c + 1)))]
  field_simp
  ring

/-- The population shape score in closed form:
`(1/3) (1/a + 1/(a+1) + 1/(a+2)) - log (1 + 1/c)`. -/
private lemma popShape_eq (a c : ℝ) :
    popShapeScore μ (S 0) (X 0) a c =
      (1 / 3) * (a⁻¹ + (a + 1)⁻¹ + (a + 2)⁻¹) - log (1 + 1 / c) := by
  simp only [popShapeScore, S]
  rw [integral_X (fun k => digammaIncrement a k - log (1 + 1 / c))]
  simp [digammaIncrement, sum_range_succ]
  ring

private lemma q_eq {a : ℝ} (ha : 0 < a) :
    q a = (1 / 3) * (a⁻¹ + (a + 1)⁻¹ + (a + 2)⁻¹) - log (1 + 1 / a) := by
  rw [q, ← log_div (by positivity) ha.ne']
  congr 3
  field_simp

private lemma continuousAt_popShape {a c : ℝ} (hc : 0 < c) :
    ContinuousAt (fun c => (1 / 3) * (a⁻¹ + (a + 1)⁻¹ + (a + 2)⁻¹) - log (1 + 1 / c)) c :=
  continuousAt_const.sub ((continuousAt_const.add (continuousAt_const.div continuousAt_id
    hc.ne')).log (by
      have : (0 : ℝ) < 1 + 1 / c := by positivity
      exact this.ne'))

/-- **The joint consistency theorem is non-vacuous.** For i.i.d. pairs `(1, Kᵢ)` with the
two-point count law (`0` w.p. `2/3`, `3` w.p. `1/3`, mean `1`) the population rate root at the
shape `a` is `a`, and along it the population shape score is `q a`, strictly decreasing on
`(0, 1/2]` with a root `a₀ ∈ (3/10, 1/2)`. Below `a₀` the rates `c` slightly below the root, and
above `a₀` the rates slightly above it, witness the sign hypothesis; every hypothesis of
`ae_eventually_exists_score_root_varying` holds with `b₀ = a₀`. The size factors are constant and
the law is not negative binomial. -/
example : ∃ a₀ ∈ Set.Ioo (3 / 10 : ℝ) (1 / 2), ∀ᵐ ω ∂μ, ∀ ε > 0, ∀ᶠ n in atTop,
    ∃ a b, 0 < a ∧ 0 < b ∧ |a - a₀| < ε ∧ |b - a₀| < ε ∧
      shapeScore a b (fun i : Fin n => S i ω) (fun i => X i ω) = 0 ∧
      rateScore a b (fun i : Fin n => S i ω) (fun i => X i ω) = 0 := by
  obtain ⟨a₀, ⟨ha₁, ha₂⟩, hq⟩ := exists_root
  have ha₀ : 0 < a₀ := by linarith
  refine ⟨a₀, ⟨ha₁, ha₂⟩, ae_eventually_exists_score_root_varying ha₀ ha₀
    (fun i => ⟨measurable_const, hX i⟩) (fun _ _ => one_pos) indep ident integrable_X
    (integrable_const _) (by rw [popRate_eq _ _ ha₀]; simp) ?_⟩
  have hu : (0 : ℝ) < min a₀ (1 / 2 - a₀) := lt_min ha₀ (by linarith)
  refine mem_nhdsGT_iff_exists_Ioo_subset.2 ⟨_, hu, fun η hη => ?_⟩
  obtain ⟨hη0, hηu⟩ := hη
  have h1 := lt_of_lt_of_le hηu (min_le_left _ _)
  have h2 := lt_of_lt_of_le hηu (min_le_right _ _)
  have ham : 0 < a₀ - η := by linarith
  have hap : 0 < a₀ + η := by linarith
  have hqm : 0 < q (a₀ - η) := by
    rw [← hq]; exact q_strictAnti ⟨ham, by linarith⟩ ⟨ha₀, ha₂.le⟩ (by linarith)
  have hqp : q (a₀ + η) < 0 := by
    rw [← hq]; exact q_strictAnti ⟨ha₀, ha₂.le⟩ ⟨hap, by linarith⟩ (by linarith)
  rw [q_eq ham] at hqm
  rw [q_eq hap] at hqp
  constructor
  · obtain ⟨c, hcpos, hc⟩ := (((continuousAt_popShape (a := a₀ - η) ham).eventually
      (lt_mem_nhds hqm)).filter_mono nhdsWithin_le_nhds |>.and
        (Ioo_mem_nhdsLT (by linarith : (a₀ - η) / 2 < a₀ - η))).exists
    have hc0 : 0 < c := by linarith [hc.1, ham]
    refine ⟨c, hc0, ?_, ?_⟩
    · rw [popRate_eq _ _ hc0]; exact div_pos (by linarith [hc.2]) (by linarith)
    · rw [popShape_eq]; exact hcpos
  · obtain ⟨c, hcneg, hc⟩ := (((continuousAt_popShape (a := a₀ + η) hap).eventually
      (gt_mem_nhds hqp)).filter_mono nhdsWithin_le_nhds |>.and
        (self_mem_nhdsWithin (s := Set.Ioi (a₀ + η)))).exists
    have hc : a₀ + η < c := hc
    have hc0 : 0 < c := by linarith
    refine ⟨c, hc0, ?_, ?_⟩
    · rw [popRate_eq _ _ hc0]; exact div_neg_of_neg_of_pos (by linarith) (by linarith)
    · rw [popShape_eq]; exact hcneg

end TwoPoint

end MathlibExtTest.Biology.Omics.HierarchicalCountMLEVarying
