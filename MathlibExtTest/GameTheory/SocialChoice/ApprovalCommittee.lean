/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

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
