/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public meta import MathlibExt.GameTheory.SocialChoice.ApprovalCommittee
import MathlibExt.GameTheory.SocialChoice.ApprovalCommittee

open MathlibExt.GameTheory.SocialChoice.ApprovalCommittee

/-- Two voters approve only candidate `0`, two approve only candidate `1`. -/
private def twoBlocs : Fin 4 → Finset (Fin 3) := ![{0}, {0}, {1}, {1}]

-- The committee `{0, 1}` represents both blocs, so it provides JR for `k = 2`.
example : checkJR twoBlocs 2 {0, 1} = true := by decide

-- The committee `{0, 2}` leaves the second bloc (2 of 4 voters, at least `n / k`)
-- unrepresented, so it does not provide JR.
example : checkJR twoBlocs 2 {0, 2} = false := by decide

-- `checkJR` agrees with `ProvidesJR` on these committees.
example : ProvidesJR twoBlocs 2 {0, 1} := by
  rw [← checkJR_eq_true_iff]
  decide

example : ¬ ProvidesJR twoBlocs 2 {0, 2} := by
  rw [← checkJR_eq_true_iff]
  decide

-- The deterministic GreedyAV committee provides JR, as Theorem 1 requires.
example : ProvidesJR twoBlocs 2 (greedyAV twoBlocs 2) :=
  (isGreedyAVRun_greedyAV twoBlocs (by simp)).providesJR

-- The AV score of `{0, 1}` counts all four voters once.
example : avScore twoBlocs {0, 1} = 4 := by decide

-- Against `W = {0, 2}`, candidate `1` has two uncovered approvers.
example : uncoveredSupport twoBlocs {0, 2} 1 = 2 := by decide

-- Tie-breaking is toward the least candidate: `0` and `1` tie at two
-- uncovered approvers each, and the pick is `0`.
example : greedyAVPick twoBlocs ∅ = some 0 := by native_decide

-- Picking from a full committee gives `none`.
example : greedyAVPick twoBlocs {0, 1, 2} = none := by native_decide

-- SAV: ballots `{0, 1}` and `∅`, committee `{0}`: `1/2 + 0 = 1/2`
-- (the empty ballot contributes `0`).
example : savScore (![{0, 1}, ∅] : Fin 2 → Finset (Fin 3)) {0} = 1 / 2 := by
  native_decide

-- PAV: one ballot `{0, 1}`, committee `{0, 1}`: `H(2) = 1 + 1/2 = 3/2`.
example : pavScore (![{0, 1}] : Fin 1 → Finset (Fin 3)) {0, 1} = 3 / 2 := by
  native_decide

-- MAV with no voters is `0`.
example : mavScore (Fin.elim0 : Fin 0 → Finset (Fin 3)) {0} = 0 := by decide

-- Deterministic GreedyAV on `twoBlocs` seats `0` first.
example : greedyAV twoBlocs 1 = {0} := by native_decide
