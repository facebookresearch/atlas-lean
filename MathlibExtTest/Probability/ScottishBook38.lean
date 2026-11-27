/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.ScottishBook38
import Mathlib.Tactic.FinCases

open MathlibExt.Probability.ScottishBook38Wanted

-- There is one empty assignment, and every pair of its vertices is reachable.
example (k : ℕ) : KOutConnectedProb k 0 = 1 := by
  simp [KOutConnectedProb, KOutConnected, Set.ncard_univ]

-- A single vertex cannot choose itself as its one friend.
example : KOutConnectedProb 1 1 = 0 := by
  have hempty : {c : Fin 1 → Finset (Fin 1) | ∀ i, (c i).card = 1 ∧ i ∉ c i} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro c hc
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp (hc 0).1
    exact (hc 0).2 (by simp [hx, Subsingleton.elim x 0])
  rw [KOutConnectedProb, hempty, Set.ncard_empty, Nat.cast_zero, div_zero]

-- Both endpoints chose the middle vertex. The second edge is traversed backwards.
example : KOutReachable 3 (fun i => if i = 1 then ∅ else {1}) 0 2 := by
  refine ⟨2, id, rfl, rfl, fun i => ?_⟩
  fin_cases i <;> decide
