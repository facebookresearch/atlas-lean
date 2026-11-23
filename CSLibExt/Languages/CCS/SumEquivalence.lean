/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `9db2af32bec4c1fe1731f17c030e9410961257ed`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

/-
# Equivalence laws for finite CCS sums
-/
module

public import CSLibExt.Languages.CCS.ExpansionStatic
public import Mathlib.Data.List.Dedup

/-!
# Equivalence laws for finite CCS sums

A finite sum represents a set of initial transitions: order and repeated
branches do not affect its behaviour.  This module establishes that extensional
principle directly and derives permutation, append, and duplicate-elimination
laws used by duplicate-free head normalization.
-/

@[expose] public section

namespace Cslib.CCS.StaticProcess

open Cslib.LTS

variable {Name : Type*} [DecidableEq Name]

/-- Finite sums with the same members are strongly bisimilar. -/
theorem sum_bisimilar_of_mem_iff {left right : List (Summand Name)}
    (members : ∀ branch, branch ∈ left ↔ branch ∈ right) :
    lts.HomBisimilarity (sum left) (sum right) := by
  let equation : StaticProcess Name → StaticProcess Name → Prop := fun source target ↦
    source = sum left ∧ target = sum right
  refine ⟨EquationClosure equation, Or.inr ⟨rfl, rfl⟩,
    equationClosure_isBisimulation ?_ ?_⟩
  · rintro source target action next ⟨rfl, rfl⟩ hstep
    rw [sum_step_iff] at hstep
    exact ⟨next, sum_step_iff.mpr (members _ |>.mp hstep), Or.inl rfl⟩
  · rintro source target action next ⟨rfl, rfl⟩ hstep
    rw [sum_step_iff] at hstep
    exact ⟨next, sum_step_iff.mpr (members _ |>.mpr hstep), Or.inl rfl⟩

/-- A list permutation does not change the represented finite sum. -/
theorem sum_bisimilar_of_perm {left right : List (Summand Name)}
    (permutation : left.Perm right) :
    lts.HomBisimilarity (sum left) (sum right) :=
  sum_bisimilar_of_mem_iff (fun _branch ↦ permutation.mem_iff)

/-- Reversing the presentation order of a finite sum is behaviourally inert. -/
theorem sum_reverse_bisimilar (summands : List (Summand Name)) :
    lts.HomBisimilarity (sum summands.reverse) (sum summands) := by
  apply sum_bisimilar_of_mem_iff
  simp

/-- Swapping two blocks of summands does not change the represented process. -/
theorem sum_append_comm_bisimilar (left right : List (Summand Name)) :
    lts.HomBisimilarity (sum (left ++ right)) (sum (right ++ left)) := by
  apply sum_bisimilar_of_mem_iff
  intro branch
  simp only [List.mem_append, or_comm]

omit [DecidableEq Name] in
/-- Reassociating three blocks of summands leaves the finite sum unchanged. -/
theorem sum_append_assoc (first second third : List (Summand Name)) :
    sum ((first ++ second) ++ third) = sum (first ++ (second ++ third)) := by
  rw [List.append_assoc]

/-- Inserting a branch that is already present does not change a finite sum. -/
theorem sum_cons_of_mem_bisimilar {branch : Summand Name}
    {summands : List (Summand Name)} (member : branch ∈ summands) :
    lts.HomBisimilarity (sum (branch :: summands)) (sum summands) := by
  apply sum_bisimilar_of_mem_iff
  intro candidate
  simp only [List.mem_cons]
  constructor
  · rintro (rfl | h)
    · exact member
    · exact h
  · exact Or.inr

/-- Removing duplicate summands preserves strong behaviour. -/
theorem sum_dedup_bisimilar (summands : List (Summand Name)) :
    lts.HomBisimilarity (sum summands.dedup) (sum summands) := by
  apply sum_bisimilar_of_mem_iff
  intro branch
  simp

/-- Filtering a finite sum twice by the same predicate is behaviourally
idempotent (and in fact produces the same list). -/
theorem sum_filter_filter_bisimilar (predicate : Summand Name → Bool)
    (summands : List (Summand Name)) :
    lts.HomBisimilarity
      (sum ((summands.filter predicate).filter predicate))
      (sum (summands.filter predicate)) := by
  apply sum_bisimilar_of_mem_iff
  intro branch
  simp

omit [DecidableEq Name] in
/-- Mapping the identity over summands leaves the finite sum unchanged. -/
theorem sum_map_id (summands : List (Summand Name)) :
    sum (summands.map id) = sum summands := by
  simp

/-- The empty list is the unique finite sum without transitions, up to strong
bisimilarity. -/
theorem sum_bisimilar_nil_of_forall_not_mem {summands : List (Summand Name)}
    (empty : ∀ branch, branch ∉ summands) :
    lts.HomBisimilarity (sum summands) (.nil : StaticProcess Name) := by
  apply sum_bisimilar_of_mem_iff (right := [])
  intro branch
  simp [empty branch]

/-- A finite sum enables an action exactly when one of its summands carries
that action. -/
theorem sum_enabled_iff {summands : List (Summand Name)} {action : Label Name} :
    lts.HasOutLabel (sum summands) action ↔
      ∃ continuation, (action, continuation) ∈ summands := by
  constructor
  · rintro ⟨continuation, hstep⟩
    exact ⟨continuation, sum_step_iff.mp hstep⟩
  · rintro ⟨continuation, hmember⟩
    exact ⟨continuation, sum_step_iff.mpr hmember⟩

/-- Extensional equality of the enabled branch set is sufficient for equality
of ready sets. -/
theorem sum_readySet_eq_of_mem_iff {left right : List (Summand Name)}
    (members : ∀ branch, branch ∈ left ↔ branch ∈ right) :
    lts.outgoingLabels (sum left) = lts.outgoingLabels (sum right) :=
  HomBisimilarity.outgoingLabels_eq (sum_bisimilar_of_mem_iff members)

end Cslib.CCS.StaticProcess
