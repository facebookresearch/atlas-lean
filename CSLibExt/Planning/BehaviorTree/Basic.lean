/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Disjoint
public import Mathlib.Logic.Function.Iterate

/-!
# Behavior trees as switched difference equations

A tree specifies a deterministic update and a return status on the *same current state*.
Each composition is again a tree: the switching decision is made anew on each tick.
In particular, handing off to a second child does not first apply the first child's update.
The source takes `X = Fin n → ℝ`; none of the switching laws needs vector-space structure.
A common positive step indexes the trees. Positivity is a forward-time convention, not an
assumption on the update or its convergence. Only sampled states and times are defined.

## Reference

Michele Colledanchise and Petter Ögren, *Behavior Trees in Robotics and AI: An Introduction*
(2018), [arXiv:1709.00084v6](https://arxiv.org/abs/1709.00084), 25 October 2022,
§5.1, Definitions 5.1–5.3 and Assumption 5.1, pp. 63–65, equations (5.1)–(5.18).
-/

@[expose] public section

namespace Cslib.Planning.BehaviorTree

/-- A positive physical time increment shared by all children of a composition. -/
abbrev TimeStep := {t : ℝ // 0 < t}

/-- Physical time of sample `k` from initial time `t₀`, at constant step `δ`. -/
noncomputable def sampleTime (δ : TimeStep) (t₀ : ℝ) (k : ℕ) : ℝ := t₀ + k * δ.val

@[simp] theorem sampleTime_zero (δ : TimeStep) (t₀ : ℝ) : sampleTime δ t₀ 0 = t₀ := by
  simp [sampleTime]

theorem sampleTime_succ (δ : TimeStep) (t₀ : ℝ) (k : ℕ) :
    sampleTime δ t₀ (k + 1) = sampleTime δ t₀ k + δ.val := by
  simp [sampleTime, add_mul, add_assoc]

theorem sampleTime_lt_succ (δ : TimeStep) (t₀ : ℝ) (k : ℕ) :
    sampleTime δ t₀ k < sampleTime δ t₀ (k + 1) := by
  rw [sampleTime_succ]
  exact lt_add_of_pos_right _ δ.property

/-- The three possible observations of a behavior tree. -/
inductive Status where
  | running | success | failure
  deriving DecidableEq, Repr

/-- A tree on a shared clock has a deterministic update and a current-state return map.
For the real state space of Definition 5.1 take `X = Fin n → ℝ`. -/
@[ext] structure Tree (X : Type*) (δ : TimeStep) where
  /-- The next sampled state. -/
  next : X → X
  /-- The return value at the current state, before `next` is applied. -/
  status : X → Status

/-- The state-space specialization of Definition 5.1: an update and return map on `ℝⁿ`. -/
abbrev RealTree (n : ℕ) (δ : TimeStep) := Tree (Fin n → ℝ) δ

namespace Tree

variable {X : Type*} {δ : TimeStep}

/-- Execution from `x` after `k` ticks is the `k`-fold iterate of the tree's update. -/
def stateAt (T : Tree X δ) (x : X) (k : ℕ) : X := T.next^[k] x

@[simp] theorem stateAt_zero (T : Tree X δ) (x : X) : T.stateAt x 0 = x := rfl

theorem stateAt_succ (T : Tree X δ) (x : X) (k : ℕ) :
    T.stateAt x (k + 1) = T.next (T.stateAt x k) := Function.iterate_succ_apply' ..

/-- The states returning `s` are the preimage of its singleton under the return map. -/
def region (T : Tree X δ) (s : Status) : Set X := T.status ⁻¹' {s}

@[simp] theorem mem_region (T : Tree X δ) (s : Status) (x : X) :
    x ∈ T.region s ↔ T.status x = s := Iff.rfl

theorem region_disjoint (T : Tree X δ) {s t : Status} (h : s ≠ t) :
    Disjoint (T.region s) (T.region t) :=
  Set.disjoint_left.mpr fun _ hs ht => h (hs.symm.trans ht)

theorem region_cover (T : Tree X δ) :
    T.region .running ∪ T.region .success ∪ T.region .failure = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  cases h : T.status x <;> simp [Set.mem_union, h]

/-- Hand off both the update and the status to `b` exactly where `a` returns `s`.
Both maps of the selected child are evaluated at the original `x`. -/
def switchOn (s : Status) (a b : Tree X δ) : Tree X δ where
  next x := if a.status x = s then b.next x else a.next x
  status x := if a.status x = s then b.status x else a.status x

/-- Reactive sequence: a successful first child hands off to the second. -/
def sequence (a b : Tree X δ) : Tree X δ := switchOn .success a b

/-- Reactive fallback: a failed first child hands off to the second. -/
def fallback (a b : Tree X δ) : Tree X δ := switchOn .failure a b

/-- On the handoff region the second child's regions apply; elsewhere the first child's do. -/
theorem switchOn_region (s t : Status) (a b : Tree X δ) :
    (switchOn s a b).region t = (a.region s ∩ b.region t) ∪ (a.region t \ a.region s) := by
  ext x
  by_cases h : a.status x = s <;> simp [switchOn, h]

@[simp] theorem sequence_success_region (a b : Tree X δ) :
    (sequence a b).region .success = a.region .success ∩ b.region .success := by
  simp [sequence, switchOn_region]

@[simp] theorem fallback_failure_region (a b : Tree X δ) :
    (fallback a b).region .failure = a.region .failure ∩ b.region .failure := by
  simp [fallback, switchOn_region]

/-- Rebracketing switches with the same handoff status preserves both maps. -/
theorem switchOn_assoc (s : Status) (a b c : Tree X δ) :
    switchOn s (switchOn s a b) c = switchOn s a (switchOn s b c) := by
  apply Tree.ext <;> funext x <;> by_cases h : a.status x = s <;> simp [switchOn, h]

theorem sequence_assoc (a b c : Tree X δ) :
    sequence (sequence a b) c = sequence a (sequence b c) := switchOn_assoc ..

theorem fallback_assoc (a b c : Tree X δ) :
    fallback (fallback a b) c = fallback a (fallback b c) := switchOn_assoc ..

end Tree

end Cslib.Planning.BehaviorTree
