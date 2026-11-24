/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Robotics.Hybrid.RankedResponse

open Robotics.Hybrid

-- Rank `0` at the request step forces a goal immediately.
example {goal : ℕ → Prop} {i : ℕ}
    (hdrop : ∀ k, i ≤ k →
      (∀ j, i ≤ j → j ≤ k → ¬ goal j) → (fun _ => 0) (k + 1) < (fun _ => 0) k) :
    ∃ j, i ≤ j ∧ j ≤ i + 0 ∧ goal j :=
  exists_goal_of_rank_drops (ρ := fun _ => 0) hdrop

-- Concrete dropping ranks `2, 1, 0` with the only goal at
-- `i + 2`: the goal is attained at the bound.
example {i : ℕ} :
    ∃ j, i ≤ j ∧ j ≤ i + (i + 2 - i) ∧ j = i + 2 :=
  exists_goal_of_rank_drops (goal := fun j => j = i + 2)
    (ρ := fun k => i + 2 - k) (i := i) (by
      intro k hik hnone
      have hki : k < i + 2 := by
        by_contra hcon
        push Not at hcon
        exact hnone (i + 2) (by omega) hcon rfl
      omega)

-- A constant rank with no goal at `i` cannot satisfy the
-- strict-drop hypothesis.
example {goal : ℕ → Prop} {i : ℕ} (hgoal : ¬ goal i) :
    ¬ ∀ k, i ≤ k →
      (∀ j, i ≤ j → j ≤ k → ¬ goal j) → (fun _ => 1) (k + 1) < (fun _ => 1) k := by
  intro hdrop
  have := hdrop i le_rfl (fun j hij hjk => by
    have heq : j = i := le_antisymm hjk hij
    rw [heq]
    exact hgoal)
  simp at this

#print axioms exists_goal_of_rank_drops
