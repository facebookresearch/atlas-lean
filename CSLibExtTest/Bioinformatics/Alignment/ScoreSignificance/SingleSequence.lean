/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Alignment.ScoreSignificance.SingleSequence
public import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# Maximal segment score tests

Pathwise fixtures for the walk maximum, the maximal segment score, the Lindley walk and the first
ladder epoch; then the score law `+1` / `-2` with probability `1/2` each (`E[X] = -1/2`), whose
Cramér root is `θ = log φ` (golden ratio), exercising every probabilistic statement; a positive
drift law for the divergence of the walk maximum; and a nonpositive score for the trivial case.
-/

namespace Cslib.Bioinformatics.Alignment.ScoreSignificance.SingleSequence

open Real Cslib.MachineLearning.LatentVariable.ExpectationMaximization

/-! ## Pathwise fixtures -/

-- prefix sums `0, 1, -1, 2`
example : walkMax [1, -2, 3] = 2 := by norm_num [walkMax]
-- best run `[3]`
example : maxSegScore [1, -2, 3] = 3 := by norm_num [maxSegScore, walkMax]
-- best run the whole list
example : maxSegScore [2, -1, 2] = 3 := by norm_num [maxSegScore, walkMax]
-- reflected walk `0, 1, 0, 3`
example : lindley [1, -2, 3] = 3 := by norm_num [lindley]
example : lindley [1, -2, 3] = walkMax [3, -2, 1] := lindley_eq_walkMax_reverse _
example : maxSegScore [] = 0 := rfl
-- boundary: no positive score
example : maxSegScore [-1, -2, 0] = 0 :=
  maxSegScore_eq_zero_of_nonpos (by norm_num)
-- a nonempty input whose best run is negative: the empty run wins
example : maxSegScore [-3, -1] = 0 := by norm_num [maxSegScore, walkMax]
-- agreement with Kadane: a real `IsMaxSubarraySum` witness from the Kadane scan
example : maxSegScore [-3, -1] = max 0 (-1) := by
  have hk : (Cslib.Algorithms.Lean.TimeM.maxSubarraySum [(-3 : ℝ), -1]).ret = some (-1) := by
    norm_num [Cslib.Algorithms.Lean.TimeM.maxSubarraySum, Cslib.Algorithms.Lean.TimeM.kadaneScan]
  exact maxSegScore_eq_max_zero
    ((Cslib.Algorithms.Lean.TimeM.maxSubarraySum_ret_eq_some_iff _ _).1 hk)
-- `Mₙ` is the maximum of the reflected walk over prefixes
example : ∃ p, p <+: [1, -2, 3] ∧ lindley p = maxSegScore [1, -2, 3] :=
  (maxSegScore_eq_max_lindley _).2

-- first ladder epoch `τ₊ = 2`, height `1`
example : IsFirstLadder [-1, 2] := by
  refine ⟨by norm_num, fun j hj => ?_⟩
  simp only [List.length_cons, List.length_nil] at hj
  interval_cases j <;> norm_num
example : ¬ IsFirstLadder [1, 1] := fun h => by
  have := h.2 1 (by norm_num); norm_num at this
example : ¬ IsFirstLadder [] := fun h => by have := h.1; simp at this
-- ladder decomposition: `walkMax ([-1, 2] ++ [3, -5]) = 1 + walkMax [3, -5]`
example : walkMax ([-1, 2] ++ [3, -5]) = 1 + walkMax [3, -5] := by
  have h : IsFirstLadder [-1, 2] := ⟨by norm_num, fun j hj => by
    simp only [List.length_cons, List.length_nil] at hj
    interval_cases j <;> norm_num⟩
  rw [walkMax_append_of_isFirstLadder h]; norm_num

/-! ## The score law `+1` / `-2` -/

/-- Fair coin letters. -/
noncomputable def q₀ : Bool → ℝ := fun _ => 1 / 2

/-- Score `+1` for `true`, `-2` for `false`. -/
def f₀ : Bool → ℝ := fun b => if b then 1 else -2

theorem hq₀ : IsDist q₀ := ⟨fun _ => by norm_num [q₀], by norm_num [q₀]⟩

theorem mean_f₀ : ∑ b, q₀ b * f₀ b = -1 / 2 := by norm_num [q₀, f₀]

/-- The Cramér root of `+1` / `-2` is `log φ`: `(φ + φ⁻²) / 2 = 1`. -/
theorem scoreMGF_log_goldenRatio : scoreMGF q₀ f₀ (log goldenRatio) = 1 := by
  have hφ : 0 < goldenRatio := goldenRatio_pos
  simp only [scoreMGF, Fintype.univ_bool, Finset.sum_insert, Finset.mem_singleton,
    Finset.sum_singleton, q₀, f₀, ↓reduceIte, Bool.false_eq_true, reduceCtorEq,
    not_false_eq_true]
  rw [mul_one, exp_log hφ, show log goldenRatio * -2 = -(2 * log goldenRatio) by ring, exp_neg,
    ← log_rpow hφ, exp_log (by positivity)]
  have h2 : goldenRatio ^ (2 : ℝ) = goldenRatio + 1 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, rpow_natCast, goldenRatio_sq]
  rw [h2]
  have hsq := goldenRatio_sq
  generalize goldenRatio = φ at hφ hsq ⊢
  field_simp
  nlinarith [hsq]

example : ∃! θ, 0 < θ ∧ scoreMGF q₀ f₀ θ = 1 :=
  existsUnique_scoreMGF_eq_one f₀ hq₀ (fun _ => by norm_num [q₀]) (by rw [mean_f₀]; norm_num)
    ⟨true, by norm_num [f₀]⟩

theorem log_goldenRatio_nonneg : 0 ≤ log goldenRatio := log_nonneg one_lt_goldenRatio.le

theorem log_goldenRatio_pos : 0 < log goldenRatio := log_pos one_lt_goldenRatio

-- the unique positive Cramér root of `+1` / `-2` is `log φ`
example : ∃! θ, 0 < θ ∧ scoreMGF q₀ f₀ θ = 1 := by
  have hu := existsUnique_scoreMGF_eq_one f₀ hq₀ (fun _ => by norm_num [q₀])
    (by rw [mean_f₀]; norm_num) ⟨true, by norm_num [f₀]⟩
  exact ⟨log goldenRatio, ⟨log_goldenRatio_pos, scoreMGF_log_goldenRatio⟩,
    fun θ hθ => hu.unique hθ ⟨log_goldenRatio_pos, scoreMGF_log_goldenRatio⟩⟩

example (θ : ℝ) (h0 : 0 < θ) (h : scoreMGF q₀ f₀ θ = 1) : θ = log goldenRatio :=
  (existsUnique_scoreMGF_eq_one f₀ hq₀ (fun _ => by norm_num [q₀]) (by rw [mean_f₀]; norm_num)
    ⟨true, by norm_num [f₀]⟩).unique ⟨h0, h⟩ ⟨log_goldenRatio_pos, scoreMGF_log_goldenRatio⟩

-- the exponential tail of the walk maximum, uniformly in the horizon
example (n : ℕ) (t : ℝ) :
    scoreProb q₀ f₀ n (fun l => t ≤ walkMax l) ≤ exp (-log goldenRatio * t) :=
  scoreProb_le_walkMax_le f₀ hq₀ log_goldenRatio_nonneg scoreMGF_log_goldenRatio n t

-- the reflected walk has the same tail
example (n : ℕ) (t : ℝ) :
    scoreProb q₀ f₀ n (fun l => t ≤ lindley l) ≤ exp (-log goldenRatio * t) :=
  (scoreProb_le_lindley f₀ n t).trans_le
    (scoreProb_le_walkMax_le f₀ hq₀ log_goldenRatio_nonneg scoreMGF_log_goldenRatio n t)

-- the maximal segment score: `P(M₁₀₀ ≥ 20) ≤ 100 φ^{-20}`
example : scoreProb q₀ f₀ 100 (fun l => 20 ≤ maxSegScore l) ≤
    (100 : ℕ) * exp (-log goldenRatio * 20) :=
  scoreProb_le_maxSegScore_le f₀ hq₀ log_goldenRatio_nonneg scoreMGF_log_goldenRatio 100
    (by norm_num)

-- the tilted ladder-height law is defective
open Classical in
example (n : ℕ) : ∑ k ∈ Finset.range (n + 1), scoreExpect q₀ f₀ k
    (fun u => if IsFirstLadder u then exp (log goldenRatio * u.sum) else 0) ≤ 1 :=
  sum_scoreExpect_firstLadder_exp_le_one f₀ hq₀.1 scoreMGF_log_goldenRatio n

-- a one-step probability, by the first-step decomposition: `P(walkMax [X₀] ≥ 1) = 1/2`
example : scoreProb q₀ f₀ 1 (fun l => 1 ≤ walkMax l) = 1 / 2 := by
  rw [scoreProb_succ]
  simp [scoreProb, scoreExpect_zero, walkMax, q₀, f₀]
  norm_num

-- the renewal equation at horizon `2`
open Classical in
example : scoreProb q₀ f₀ 2 (fun l => 1 ≤ walkMax l) = ∑ k ∈ Finset.range (2 + 1),
    scoreExpect q₀ f₀ k (fun u =>
      if IsFirstLadder u then scoreProb q₀ f₀ (2 - k) (fun v => 1 - u.sum ≤ walkMax v) else 0) :=
  scoreProb_le_walkMax_eq_sum f₀ one_pos 2

-- regeneration at the first ladder epoch: (height on `{τ₊ = 1}`) × (walk maximum afterwards)
open Classical in
example : scoreExpect q₀ f₀ 3 (fun l =>
      (if IsFirstLadder (l.take 1) then (l.take 1).sum else 0) * walkMax (l.drop 1)) =
    scoreExpect q₀ f₀ 1 (fun u => if IsFirstLadder u then u.sum else 0) *
      scoreExpect q₀ f₀ (3 - 1) walkMax :=
  scoreExpect_firstLadder_regeneration f₀ (by norm_num) (fun u => u.sum) walkMax

-- independent blocks: first score positive, and the remaining walk reaches `1`
example : scoreProb q₀ f₀ 3 (fun l => (0 < (l.take 1).sum) ∧ 1 ≤ walkMax (l.drop 1)) =
    scoreProb q₀ f₀ 1 (fun u => 0 < u.sum) * scoreProb q₀ f₀ (3 - 1) (fun v => 1 ≤ walkMax v) :=
  scoreProb_take_and_drop f₀ (by norm_num) (fun u => 0 < u.sum) (fun v => 1 ≤ walkMax v)

-- the first two ladder segments are iid: `P(τ₁ = 1, H₁ = 1, τ₂ - τ₁ = 3, H₂ = 1)` factorizes
example : scoreProb q₀ f₀ 4 (fun l => (IsFirstLadder (l.take 1) ∧ (l.take 1).sum = 1) ∧
      (IsFirstLadder ((l.drop 1).take 3) ∧ ((l.drop 1).take 3).sum = 1)) =
    scoreProb q₀ f₀ 1 (fun u => IsFirstLadder u ∧ u.sum = 1) *
      scoreProb q₀ f₀ 3 (fun u => IsFirstLadder u ∧ u.sum = 1) :=
  scoreProb_two_ladders f₀ hq₀ (show 1 + 3 ≤ 4 by norm_num) (fun u => u.sum = 1)
    (fun u => u.sum = 1)

-- `P(X > 0) > 0`: the maximal segment score grows without bound (even though `E[X] < 0`)
example (t : ℝ) : Filter.Tendsto (fun n => scoreProb q₀ f₀ n (fun l => t ≤ maxSegScore l))
    Filter.atTop (nhds 1) :=
  tendsto_scoreProb_le_maxSegScore f₀ hq₀ (b₀ := true) (by norm_num [q₀]) (by norm_num [f₀]) t

/-! ## Boundary laws -/

/-- Score `+2` / `-1`: positive drift `E[X] = 1/2`. -/
def f₁ : Bool → ℝ := fun b => if b then 2 else -1

example (t : ℝ) : Filter.Tendsto (fun n => scoreProb q₀ f₁ n (fun l => t ≤ walkMax l))
    Filter.atTop (nhds 1) :=
  tendsto_scoreProb_le_walkMax_of_mean_pos f₁ hq₀ (by norm_num [q₀, f₁]) t

example (t : ℝ) : Filter.Tendsto (fun n => scoreProb q₀ f₁ n (fun l => t ≤ maxSegScore l))
    Filter.atTop (nhds 1) :=
  tendsto_scoreProb_le_maxSegScore_of_mean_nonneg f₁ hq₀ (by norm_num [q₀, f₁])
    ⟨true, by norm_num [q₀], by norm_num [f₁]⟩ t

/-- Score `0` / `-1`: no positive score. -/
def f₂ : Bool → ℝ := fun b => if b then 0 else -1

example (n : ℕ) : scoreProb q₀ f₂ n (fun l => 0 < maxSegScore l) = 0 :=
  scoreProb_maxSegScore_pos_eq_zero f₂ hq₀.1 (fun b _ => by cases b <;> norm_num [f₂]) n

end Cslib.Bioinformatics.Alignment.ScoreSignificance.SingleSequence
