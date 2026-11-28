/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Planning.DeterministicSearch
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Basic.ENNReal.Real
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.NormNum.Basic

/-! Semantic tests for deterministic search problems and their solution costs. -/

set_option autoImplicit false

open scoped ENNReal NNReal

namespace Cslib.Planning.DeterministicSearch

private def payments : Problem (Option Bool) where
  initial := some false
  Action
    | none => Empty
    | some _ => Unit
  step s a := match s with
    | none => nomatch a
    | some false => some true
    | some true => none
  goal s := s = none
  goalDecidable _ := inferInstance
  stepCost s a := match s with
    | none => nomatch a
    | some false => 2
    | some true => 3

-- There is no legal one-step constructor at the goal: its applicable action type is empty.
example : IsEmpty (payments.Action none) := inferInstanceAs (IsEmpty Empty)

private def payLast : payments.Solution (some true) :=
  ⟨.cons () (.nil none), rfl⟩

private def payBoth : payments.Solution payments.initial :=
  ⟨.cons () payLast.1, rfl⟩

example : payBoth.1.states = [some false, some true, none] := rfl

example : payLast.1.cost = 3 := by
  change 3 + 0 = (3 : ℝ≥0)
  exact add_zero _

example : payBoth.1.cost = 5 := by
  change 2 + (3 + 0) = (5 : ℝ≥0)
  norm_num

example : (Problem.Plan.nil (P := payments) none).states = [none] := rfl

example : payments.optimalCost none = 0 := Problem.optimalCost_eq_zero_of_goal rfl

private def deadEnd : Problem Unit where
  initial := ()
  Action _ := Empty
  step _ a := nomatch a
  goal _ := False
  goalDecidable _ := inferInstance
  stepCost _ a := nomatch a

example : deadEnd.optimalCost deadEnd.initial = ⊤ :=
  Problem.optimalCost_eq_top_iff.mpr ⟨fun p => p.2⟩

-- At each natural number one can advance for free or exit for a positive cost tending to zero.
private noncomputable def approach : Problem (Option ℕ) where
  initial := some 0
  Action
    | none => Empty
    | some _ => Bool
  step s a := match s with
    | none => nomatch a
    | some n => if a then none else some (n + 1)
  goal s := s = none
  goalDecidable _ := inferInstance
  stepCost s a := match s with
    | none => nomatch a
    | some n => if a then 1 / ((n : ℝ≥0) + 1) else 0

example : approach.FinitelyBranching ∧ Infinite (Option ℕ) := by
  refine ⟨?_, inferInstance⟩
  intro s
  cases s with
  | none => exact Finite.of_injective (Empty.elim : Empty → Unit) (by intro x; cases x)
  | some _ => exact inferInstanceAs (Finite Bool)

private noncomputable def exitAfter (n k : ℕ) : approach.Solution (some n) :=
  match k with
  | 0 => ⟨.cons true (.nil none), rfl⟩
  | k + 1 =>
    let tail := exitAfter (n + 1) k
    ⟨.cons false tail.1, tail.2⟩

private theorem exitAfter_cost (n k : ℕ) :
    (exitAfter n k).1.cost = 1 / (((n + k : ℕ) : ℝ≥0) + 1) := by
  induction k generalizing n with
  | zero =>
    change 1 / ((n : ℝ≥0) + 1) + 0 = 1 / (((n + 0 : ℕ) : ℝ≥0) + 1)
    simp
  | succ k ih =>
    change 0 + (exitAfter (n + 1) k).1.cost = 1 / (((n + (k + 1) : ℕ) : ℝ≥0) + 1)
    rw [zero_add, ih, Nat.add_right_comm n 1 k, Nat.add_assoc]

private theorem approach_cost_pos {s : Option ℕ} (p : approach.Plan s)
    (hn : s ≠ none) (hg : approach.goal p.endState) : 0 < p.cost := by
  induction p with
  | nil _ => exact (hn hg).elim
  | @cons s a tail ih =>
    cases s with
    | none => exact (hn rfl).elim
    | some n =>
      cases a with
      | false =>
        change 0 < 0 + tail.cost
        rw [zero_add]
        exact ih (by change some (n + 1) ≠ none; simp) hg
      | true =>
        change 0 < 1 / ((n : ℝ≥0) + 1) + tail.cost
        exact lt_of_lt_of_le (one_div_pos.mpr (by positivity)) (le_add_of_nonneg_right bot_le)

private theorem approach_optimalCost_zero : approach.optimalCost (some 0) = 0 := by
  by_contra h
  let r := approach.optimalCost (some 0)
  have hr : r ≠ ⊤ := by
    intro ht
    exact ((Problem.optimalCost_eq_top_iff.mp ht).false (exitAfter 0 0))
  have hpos : 0 < r.toNNReal := ENNReal.toNNReal_pos h hr
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
  have hupper := Problem.optimalCost_le (exitAfter 0 k)
  rw [exitAfter_cost, Nat.zero_add] at hupper
  change r ≤ _ at hupper
  rw [← ENNReal.coe_toNNReal hr] at hupper
  exact (not_lt_of_ge (ENNReal.coe_le_coe.mp hupper)) hk

-- Nonempty solution family, finite infimum, and no solution of that cost.
example : approach.optimalCost approach.initial = 0 ∧
    Nonempty (approach.Solution approach.initial) ∧
    ∀ p : approach.Solution approach.initial, approach.optimalCost approach.initial < p.1.cost := by
  refine ⟨approach_optimalCost_zero, ⟨exitAfter 0 0⟩, fun p => ?_⟩
  rw [show approach.optimalCost approach.initial = 0 from approach_optimalCost_zero]
  exact ENNReal.coe_pos.mpr (approach_cost_pos p.1 (by change some 0 ≠ none; simp) p.2)

end Cslib.Planning.DeterministicSearch
