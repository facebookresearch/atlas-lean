/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Interval.Finset.Basic

/-!
# Bounded response from a dropping rank

If a pending request's natural-valued rank strictly drops
at every step where no goal has occurred yet, then a goal
occurs within the initial rank bound.
-/

@[expose] public section

namespace Robotics.Hybrid

private theorem aux_rank_bound {goal : ℕ → Prop} {ρ : ℕ → ℕ} :
    ∀ (n i : ℕ), ρ i ≤ n →
      (∀ k, i ≤ k →
        (∀ j, i ≤ j → j ≤ k → ¬ goal j) → ρ (k + 1) < ρ k) →
      ∃ j, i ≤ j ∧ j ≤ i + ρ i ∧ goal j := by
  intro n
  induction n with
  | zero =>
      intro i hle hdrop
      by_cases hi : goal i
      · exact ⟨i, le_rfl, by omega, hi⟩
      · have hlt : ρ (i + 1) < ρ i := hdrop i le_rfl (fun j hij hjk => by
          have heq : j = i := le_antisymm hjk hij
          rw [heq]
          exact hi)
        have hcontra : False := by omega
        exact False.elim hcontra
  | succ n ih =>
      intro i hle hdrop
      by_cases hi : goal i
      · exact ⟨i, le_rfl, by omega, hi⟩
      · have hlt : ρ (i + 1) < ρ i := hdrop i le_rfl (fun j hij hjk => by
          have heq : j = i := le_antisymm hjk hij
          rw [heq]
          exact hi)
        have hle' : ρ (i + 1) ≤ n := by omega
        have hdrop' : ∀ k, i + 1 ≤ k →
            (∀ j, i + 1 ≤ j → j ≤ k → ¬ goal j) → ρ (k + 1) < ρ k := by
          intro k hk hnone
          apply hdrop k (by omega)
          intro j hij hjk
          by_cases heq : j = i
          · rw [heq]
            exact hi
          · exact hnone j (by omega) hjk
        obtain ⟨j, hij, hjub, hgj⟩ := ih (i + 1) hle' hdrop'
        exact ⟨j, by omega, by omega, hgj⟩

/-- Bounded response from a dropping rank. On an infinite
run with a pending request at step `i`, let `ρ k` be the
pending-request rank at step `k`. If the rank strictly
drops at every step where no goal has occurred yet, then
a goal occurs at some step `j` with
`i ≤ j ≤ i + ρ i`. -/
theorem exists_goal_of_rank_drops {goal : ℕ → Prop}
    {ρ : ℕ → ℕ} {i : ℕ}
    (hdrop : ∀ k, i ≤ k →
      (∀ j, i ≤ j → j ≤ k → ¬ goal j) → ρ (k + 1) < ρ k) :
    ∃ j, i ≤ j ∧ j ≤ i + ρ i ∧ goal j := by
  exact aux_rank_bound (ρ i) i le_rfl hdrop

end Robotics.Hybrid
