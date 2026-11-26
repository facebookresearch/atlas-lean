/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Planning.NavigationFunction
import Mathlib.Basic.ENNReal.Inv
import Mathlib.Tactic.NormNum

/-! # Tests for first arrival under a feasible navigation function -/

open Cslib.Planning.Navigation
open scoped NNReal ENNReal

namespace NavigationFunctionTest.Branch

inductive State | hub | left | right | dead deriving DecidableEq
open State

instance : Fintype State := ⟨{hub, left, right, dead}, by intro s; cases s <;> simp⟩

abbrev Action : State → Type
  | hub => Fin 4
  | _ => Unit

def step : (s : State) → Action s → State
  | hub, a => if a < 2 then left else if a = 2 then right else dead
  | left, _ => dead
  | right, _ => dead
  | dead, _ => dead

def goals : Set State := {s | s = left ∨ s = right}

noncomputable abbrev d := distance step goals

def policy (a : Fin 4) : (s : State) → Action s
  | hub => a
  | left | right | dead => ()

private theorem dead_dist : d dead = ⊤ := by
  apply distance_eq_top.mpr
  rintro ⟨n, h⟩
  induction n with
  | zero => rcases hitsIn_zero.mp h with h | h <;> cases h
  | succ n ih => obtain ⟨_, h⟩ := hitsIn_succ.mp h; exact ih h

private theorem goal_dist {s : State} (hs : s ∈ goals) : d s = 0 :=
  distance_feasible.zero_of_goal _ hs

private theorem good {a : Fin 4} (ha : step hub a ∈ goals) : Greedy step d (policy a) := by
  intro s b
  cases s with
  | hub =>
    change d (step hub a) ≤ d (step hub b)
    rw [goal_dist ha]
    exact zero_le
  | left | right | dead => exact le_rfl

-- Duplicate actions, a tie between distinct successors, and a strictly worse legal choice.
example : step hub 0 = step hub 1 ∧ step hub 0 ≠ step hub 2 ∧
    Greedy step d (policy 0) ∧ Greedy step d (policy 1) ∧ Greedy step d (policy 2) ∧
    ¬ Greedy step d (policy 3) := by
  refine ⟨rfl, by decide, good (Or.inl rfl), good (Or.inl rfl), good (Or.inr rfl), ?_⟩
  intro hg
  have h : d dead ≤ d left := hg hub 0
  rw [dead_dist, goal_dist (Or.inl rfl : left ∈ goals)] at h
  exact not_le_of_gt (WithTop.coe_lt_top (0 : ℕ)) h

-- First arrival for the two-goal distance: it costs one action from the hub, but no
-- actions from the left goal, even though the very next state has infinite distance.
example : d hub = 1 ∧ DescendingFirstHit goals d (run step (policy 2) hub) 1 ∧
    DescendingFirstHit goals d (run step (policy 2) left) 0 ∧
    d (run step (policy 2) left 1) = ⊤ := by
  have walk : HitsIn step goals hub 1 := hitsIn_succ.mpr ⟨0, hitsIn_zero.mpr (Or.inl rfl)⟩
  have hr : GoalReachable step goals hub := ⟨1, walk⟩
  obtain ⟨k, hk, attained, least⟩ := distance_spec hr
  have hk1 : k ≤ 1 := least walk
  have hk0 : k ≠ 0 := by
    rintro rfl
    rcases hitsIn_zero.mp attained with h | h <;> cases h
  have he : k = 1 := by omega
  have hd : d hub = 1 := by simpa [he] using hk
  obtain ⟨n, hn, hit⟩ := firstHit_at_distance (good (Or.inr rfl : step hub 2 ∈ goals)) hr
  have hn1 : n = 1 := by exact_mod_cast hn.symm.trans hd
  exact ⟨hd, hn1 ▸ hit, ⟨Or.inl rfl, by simp, by simp⟩, dead_dist⟩

end NavigationFunctionTest.Branch

namespace NavigationFunctionTest.HalfSteps

inductive Phase | start | middle | finish deriving DecidableEq
open Phase

instance : Fintype Phase := ⟨{start, middle, finish}, by intro s; cases s <;> simp⟩

def step : Phase → Unit → Phase
  | start, _ => middle
  | middle, _ => finish
  | finish, _ => start

def goal : Set Phase := {finish}

noncomputable def value (s : Phase) : ℝ≥0∞ :=
  ((match s with | start => 1 | middle => 1 / 2 | finish => 0 : ℝ≥0) : ℝ≥0∞)

private theorem reachable (s : Phase) : GoalReachable step goal s := by
  have h₀ : HitsIn step goal finish 0 := hitsIn_zero.mpr rfl
  have h₁ : HitsIn step goal middle 1 := hitsIn_succ.mpr ⟨(), h₀⟩
  cases s with
  | start => exact ⟨2, hitsIn_succ.mpr ⟨(), h₁⟩⟩
  | middle => exact ⟨1, h₁⟩
  | finish => exact ⟨0, h₀⟩

private theorem feasible : Feasible step goal value where
  zero_of_goal _ hx := by obtain rfl : _ = finish := hx; rfl
  top_iff s := by simp [value, reachable]
  descends s _ hn := by
    use ()
    cases s with
    | start | middle => norm_num [value, step]
    | finish => exact (hn rfl).elim

-- Initial real value 1 does not bound the hitting time: 1, 1/2, 0 takes exactly
-- |X| - 1 = 2 steps. The example exercises the general arrival bound at ℝ≥0∞.
example : let s := run step (fun _ => ()) start
    value (s 0) = 1 ∧ value (s 1) = 1 / 2 ∧ (∀ k ≤ 1, s k ∉ goal) ∧
    DescendingFirstHit goal value s (Fintype.card Phase - 1) := by
  dsimp only
  have before (k : ℕ) (hk : k ≤ 1) : run step (fun _ => ()) start k ∉ goal := by
    change run step (fun _ => ()) start k ≠ finish
    have h : k = 0 ∨ k = 1 := by omega
    rcases h with rfl | rfl <;> decide
  have card : Fintype.card Phase = 3 := by decide
  obtain ⟨n, hn, hit⟩ := firstHit_le_card_sub_one feasible
    (show Greedy step value (fun _ => ()) from fun _ _ => le_rfl) (reachable start)
  have hge : ¬ n ≤ 1 := fun h => before n h hit.hit
  have he : n = Fintype.card Phase - 1 := by omega
  exact ⟨rfl, by change ((1 / 2 : ℝ≥0) : ℝ≥0∞) = 1 / 2; norm_num, before, he ▸ hit⟩

end NavigationFunctionTest.HalfSteps
