/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.BayesianStackelbergCommitmentDefs
-- `Fin.sum_univ_one` evaluates the sums over one leader action and one follower type.
import Mathlib.Algebra.BigOperators.Fin
-- `linarith` closes the real-valued utility inequalities.
import Mathlib.Tactic.Linarith

namespace MetaMathlibExt.Complexity.NPComplete.BayesianStackelbergCommitment

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

/-- One leader action, two follower actions, one follower type, and threshold `(k - 0) / d`.
The follower strictly prefers action `1`, where the leader gets `4`. -/
private abbrev game (k d : ℕ) : BayesianStackelbergCommitmentInstance :=
  (1, 2, [1], [[(0, 0), (4, 0)]], [[[(0, 0), (1, 0)]]], ((k, 0), d))

/-- The follower's unique best response is action `1`, worth `4` to the leader. -/
private theorem value (k d : ℕ) (p : Fin (game k d).1 → ℝ) (hp1 : ∑ s, p s = 1)
    (t : Fin (game k d).2.2.1.length → Fin (game k d).2.1)
    (hbr : ∀ θ t', ∑ s, p s * followerUtility (game k d) θ s t' ≤
      ∑ s, p s * followerUtility (game k d) θ s (t θ)) :
    ∑ θ, prior (game k d) θ * ∑ s, p s * leaderUtility (game k d) s (t θ) = 4 := by
  dsimp only [game, List.length_singleton] at p hp1 t hbr ⊢
  simp only [Fin.sum_univ_one] at hp1 ⊢
  have h := hbr 0 1
  simp only [Fin.sum_univ_one] at h
  rcases (by omega : (t 0 : ℕ) = 0 ∨ (t 0 : ℕ) = 1) with h0 | h0
  · obtain h0 : t 0 = 0 := Fin.ext h0
    rw [h0] at h
    simp [followerUtility, intVal, hp1] at h
    linarith
  · obtain h0 : t 0 = 1 := Fin.ext h0
    rw [h0]
    simp [prior, leaderUtility, intVal, hp1]

/-- Committing to the only leader action, with the follower's best response `1`. -/
private theorem witness (k d : ℕ) (hk : threshold (game k d) ≤ 4) :
    BayesianStackelbergCommitmentFeasible (game k d) := by
  refine ⟨fun _ => 1, fun _ => zero_le_one, by simp, fun _ => 1, ?_, ?_⟩
  · dsimp only [game, List.length_singleton]
    intro θ t'
    simp only [Fin.sum_univ_one]
    rcases (by omega : (t' : ℕ) = 0 ∨ (t' : ℕ) = 1) with h0 | h0
    · obtain rfl : t' = 0 := Fin.ext h0
      simp [followerUtility, intVal]
    · obtain rfl : t' = 1 := Fin.ext h0
      simp
  · dsimp only [game, List.length_singleton] at hk ⊢
    simp only [Fin.sum_univ_one]
    simpa [prior, leaderUtility, intVal] using hk

private theorem threshold_eq (k : ℕ) : threshold (game k 1) = k := by simp [threshold, intVal]

/-- The decision problem accepts threshold `3`. -/
example : bayesianStackelbergCommitmentDec (bitEncode (game 3 1)) = true := by
  have hw : WellFormed (game 3 1) := by unfold WellFormed; decide
  have hf := witness 3 1 (by rw [threshold_eq]; norm_num)
  simp [bayesianStackelbergCommitmentDec, bitDecode_bitEncode, hw, hf]

/-- The decision problem rejects the well-formed threshold `5`: every best response of the
follower leaves the leader `4`. -/
example : WellFormed (game 5 1) ∧
    bayesianStackelbergCommitmentDec (bitEncode (game 5 1)) = false := by
  have hf : ¬ BayesianStackelbergCommitmentFeasible (game 5 1) := by
    rintro ⟨p, -, hp1, t, hbr, hk⟩
    rw [value 5 1 p hp1 t hbr, threshold_eq] at hk
    norm_num at hk
  exact ⟨by unfold WellFormed; decide,
    by simp [bayesianStackelbergCommitmentDec, bitDecode_bitEncode, hf]⟩

/-- A zero denominator in the threshold is malformed, although the threshold `7 / 0` then
evaluates to `0`, which the leader exceeds. -/
example : BayesianStackelbergCommitmentFeasible (game 7 0) ∧
    bayesianStackelbergCommitmentDec (bitEncode (game 7 0)) = false := by
  have hw : ¬ WellFormed (game 7 0) := by unfold WellFormed; decide
  exact ⟨witness 7 0 (by simp [threshold]),
    by simp [bayesianStackelbergCommitmentDec, bitDecode_bitEncode, hw]⟩

/-- A lone continuation bit is a truncated instance encoding. -/
example : bayesianStackelbergCommitmentDec [true] = false := by
  have h : bitDecode (α := BayesianStackelbergCommitmentInstance) [true] = none := rfl
  simp [bayesianStackelbergCommitmentDec, h]

end MetaMathlibExt.Complexity.NPComplete.BayesianStackelbergCommitment
