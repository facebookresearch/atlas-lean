/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Distributed.TokenRingConvergence

/-! # Tests for bounded convergence of Dijkstra's token ring -/

namespace Cslib.Distributed.TokenRing.Tests

-- Every one-machine configuration is legal already, without taking a step.
example (x : ZMod 1 → ZMod 2) : PiecewiseLegal x := by
  refine ⟨0, le_rfl, fun i => ?_⟩
  have hzero : ∀ j : ZMod 1, j = 0 := by decide
  rw [hzero i]
  simp

private def threeStart : ZMod 3 → ZMod 4 := fun i => if i = 1 then 1 else 0
private def threeEnd : ZMod 3 → ZMod 4 := fun _ => 0

-- States (0, 1, 0) have three privileges. The central daemon can choose machine 1,
-- whose copy produces the constant, legal configuration (0, 0, 0).
example : ¬ Legit threeStart := by
  have h0 : privileged threeStart 0 := by unfold privileged threeStart; decide
  have h1 : privileged threeStart 1 := by unfold privileged threeStart; decide
  rintro ⟨p, _, hp⟩
  have h01 : (0 : ZMod 3) ≠ 1 := by decide
  exact h01 ((hp _ h0).trans (hp _ h1).symm)

private theorem threeFirstStep : Step threeStart threeEnd := by
  refine ⟨1, ?_, ?_⟩
  · unfold privileged threeStart
    decide
  · unfold moveVal threeStart threeEnd
    decide

example : PiecewiseLegal threeEnd := by
  exact ⟨2, le_rfl, fun i => by simp [threeEnd, Nat.le_of_lt_succ (ZMod.val_lt i)]⟩

-- Exercise the theorem on a real 18-step prefix starting from the illegitimate state.
private noncomputable def threeRun : ℕ → ZMod 3 → ZMod 4
  | 0 => threeStart
  | 1 => threeEnd
  | t + 2 =>
    let x := threeRun (t + 1)
    let i := Classical.choose (exists_privileged x)
    Function.update x i (moveVal x i)

private theorem threeRun_step (t : ℕ) : Step (threeRun t) (threeRun (t + 1)) := by
  cases t with
  | zero => exact threeFirstStep
  | succ t => exact ⟨_, Classical.choose_spec (exists_privileged (threeRun (t + 1))), rfl⟩

example : ∃ t ≤ 18, PiecewiseLegal (threeRun t) :=
  exists_piecewiseLegal_of_steps (n := 2) threeRun fun t _ => threeRun_step t

example : Legit (threeRun 18) :=
  legit_at_quadratic_bound (n := 2) threeRun fun t _ => threeRun_step t

-- A single privilege does not force consecutive colors: the colors (0, 1) modulo 3
-- have just one privilege, but the second color is neither 0 nor 0 - 1.
private def twoNonconsecutive : ZMod 2 → ZMod 3 := fun i => if i = 0 then 0 else 1

example : Legit twoNonconsecutive ∧ ¬ PiecewiseLegal twoNonconsecutive := by
  constructor
  · exact ⟨1, by unfold privileged twoNonconsecutive; decide,
        by unfold privileged twoNonconsecutive; decide⟩
  · intro h
    have hlast := (piecewiseLegal_iff.mp h).2
    have hbad : ¬ (twoNonconsecutive (-1) = twoNonconsecutive 0 ∨
        twoNonconsecutive (-1) = twoNonconsecutive 0 - 1) := by
      unfold twoNonconsecutive
      decide
    exact hbad hlast

end Cslib.Distributed.TokenRing.Tests
