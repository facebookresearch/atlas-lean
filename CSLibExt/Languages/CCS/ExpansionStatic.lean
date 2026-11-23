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
# Static operators on finite CCS sums
-/
module

public import CSLibExt.Languages.CCS.Expansion

/-!
# Static operators on finite CCS sums

Restriction deletes blocked head summands and recursively restricts every
surviving continuation. Relabelling transforms every head action and
continuation. This module proves these two syntactic transformations sound up
to strong bisimilarity and packages useful finite-sum equations.

The laws are the head-normal-form presentation of Milner,
*Communication and Concurrency*, Chapters 2--3.
-/

@[expose] public section

namespace Cslib.CCS.StaticProcess

open Cslib.LTS

variable {Name : Type*} [DecidableEq Name]

/-- Restrict each allowed summand and discard each blocked summand. -/
def restrictSummands (blocked : List Name) :
    List (Summand Name) → List (Summand Name)
  | [] => []
  | (action, continuation) :: rest =>
      if Allowed blocked action then
        (action, .restriction blocked continuation) :: restrictSummands blocked rest
      else
        restrictSummands blocked rest

theorem mem_restrictSummands_iff {blocked : List Name} {summands : List (Summand Name)}
    {action : Label Name} {next : StaticProcess Name} :
    (action, next) ∈ restrictSummands blocked summands ↔
      ∃ continuation, (action, continuation) ∈ summands ∧ Allowed blocked action ∧
        next = .restriction blocked continuation := by
  induction summands with
  | nil => simp [restrictSummands]
  | cons head rest ih =>
      rcases head with ⟨headAction, headNext⟩
      by_cases allowed : Allowed blocked headAction
      · simp only [restrictSummands, allowed, ite_eq_left, List.mem_cons, ih]
        grind
      · simp only [restrictSummands, allowed]
        grind

theorem restrictSummands_append (blocked : List Name)
    (left right : List (Summand Name)) :
    restrictSummands blocked (left ++ right) =
      restrictSummands blocked left ++ restrictSummands blocked right := by
  induction left with
  | nil => rfl
  | cons head rest ih =>
      rcases head with ⟨action, continuation⟩
      simp only [List.cons_append, restrictSummands]
      split <;> simp [ih]

theorem restrictSummands_length_le (blocked : List Name)
    (summands : List (Summand Name)) :
    (restrictSummands blocked summands).length ≤ summands.length := by
  induction summands with
  | nil => simp [restrictSummands]
  | cons head rest ih =>
      rcases head with ⟨action, continuation⟩
      simp only [restrictSummands]
      split <;> simp_all; omega

/-- Every branch surviving restriction has an allowed action; in particular,
silent actions always survive. -/
theorem allowed_of_mem_restrictSummands {blocked : List Name}
    {summands : List (Summand Name)} {branch : Summand Name}
    (member : branch ∈ restrictSummands blocked summands) :
    Allowed blocked branch.1 := by
  obtain ⟨continuation, _, allowed, equality⟩ :=
    mem_restrictSummands_iff.mp member
  simpa [equality]

/-- Restriction of a finite sum is the sum of precisely its allowed branches. -/
theorem restriction_sum_bisimilar (blocked : List Name)
    (summands : List (Summand Name)) :
    lts.HomBisimilarity (.restriction blocked (sum summands))
      (sum (restrictSummands blocked summands)) := by
  let equation : StaticProcess Name → StaticProcess Name → Prop := fun source target =>
    source = .restriction blocked (sum summands) ∧
      target = sum (restrictSummands blocked summands)
  refine ⟨EquationClosure equation, Or.inr ⟨rfl, rfl⟩,
    equationClosure_isBisimulation ?_ ?_⟩
  · rintro source target action next ⟨rfl, rfl⟩ hstep
    rw [restriction_step_iff] at hstep
    obtain ⟨continuation, hsum, allowed, rfl⟩ := hstep
    rw [sum_step_iff] at hsum
    exact ⟨_, sum_step_iff.mpr (mem_restrictSummands_iff.mpr
      ⟨continuation, hsum, allowed, rfl⟩), Or.inl rfl⟩
  · rintro source target action next ⟨rfl, rfl⟩ hstep
    rw [sum_step_iff, mem_restrictSummands_iff] at hstep
    obtain ⟨continuation, hsum, allowed, rfl⟩ := hstep
    exact ⟨_, .restrict (sum_step_iff.mpr hsum) allowed, Or.inl rfl⟩

/-- Relabel every head action and recursively relabel every continuation. -/
def relabelSummands (rename : Relabelling Name) :
    List (Summand Name) → List (Summand Name) :=
  List.map fun branch =>
    (relabelAction rename branch.1, .relabelling rename branch.2)

theorem mem_relabelSummands_iff {rename : Relabelling Name}
    {summands : List (Summand Name)} {action : Label Name} {next : StaticProcess Name} :
    (action, next) ∈ relabelSummands rename summands ↔
      ∃ sourceAction continuation,
        (sourceAction, continuation) ∈ summands ∧
        action = relabelAction rename sourceAction ∧
        next = .relabelling rename continuation := by
  constructor
  · intro h
    simp only [relabelSummands, List.mem_map] at h
    obtain ⟨⟨sourceAction, continuation⟩, hmember, hpair⟩ := h
    simp only [Prod.mk.injEq] at hpair
    exact ⟨sourceAction, continuation, hmember, hpair.1.symm, hpair.2.symm⟩
  · rintro ⟨sourceAction, continuation, hmember, rfl, rfl⟩
    simp only [relabelSummands, List.mem_map]
    exact ⟨(sourceAction, continuation), hmember, rfl⟩

theorem relabelSummands_append (rename : Relabelling Name)
    (left right : List (Summand Name)) :
    relabelSummands rename (left ++ right) =
      relabelSummands rename left ++ relabelSummands rename right := by
  simp [relabelSummands]

@[simp] theorem relabelSummands_length (rename : Relabelling Name)
    (summands : List (Summand Name)) :
    (relabelSummands rename summands).length = summands.length := by
  simp [relabelSummands]

theorem relabelSummands_nil_iff (rename : Relabelling Name)
    (summands : List (Summand Name)) :
    relabelSummands rename summands = [] ↔ summands = [] := by
  simp [relabelSummands]

/-- Relabelling of a finite sum is the sum of its relabelled branches. -/
theorem relabelling_sum_bisimilar (rename : Relabelling Name)
    (summands : List (Summand Name)) :
    lts.HomBisimilarity (.relabelling rename (sum summands))
      (sum (relabelSummands rename summands)) := by
  let equation : StaticProcess Name → StaticProcess Name → Prop := fun source target =>
    source = .relabelling rename (sum summands) ∧
      target = sum (relabelSummands rename summands)
  refine ⟨EquationClosure equation, Or.inr ⟨rfl, rfl⟩,
    equationClosure_isBisimulation ?_ ?_⟩
  · rintro source target action next ⟨rfl, rfl⟩ hstep
    rw [relabelling_step_iff] at hstep
    obtain ⟨sourceAction, continuation, hsum, rfl, rfl⟩ := hstep
    rw [sum_step_iff] at hsum
    exact ⟨_, sum_step_iff.mpr (mem_relabelSummands_iff.mpr
      ⟨sourceAction, continuation, hsum, rfl, rfl⟩), Or.inl rfl⟩
  · rintro source target action next ⟨rfl, rfl⟩ hstep
    rw [sum_step_iff, mem_relabelSummands_iff] at hstep
    obtain ⟨sourceAction, continuation, hsum, rfl, rfl⟩ := hstep
    exact ⟨_, .relabel (sum_step_iff.mpr hsum), Or.inl rfl⟩

/-- Concatenating summand lists represents binary nondeterministic choice. -/
theorem sum_append_bisimilar_choice (left right : List (Summand Name)) :
    lts.HomBisimilarity (sum (left ++ right)) (.choice (sum left) (sum right)) := by
  let equation : StaticProcess Name → StaticProcess Name → Prop := fun source target =>
    source = sum (left ++ right) ∧ target = .choice (sum left) (sum right)
  refine ⟨EquationClosure equation, Or.inr ⟨rfl, rfl⟩,
    equationClosure_isBisimulation ?_ ?_⟩
  · rintro source target action next ⟨rfl, rfl⟩ hstep
    rw [sum_step_iff, List.mem_append] at hstep
    rcases hstep with hleft | hright
    · exact ⟨_, .choiceLeft (sum_step_iff.mpr hleft), Or.inl rfl⟩
    · exact ⟨_, .choiceRight (sum_step_iff.mpr hright), Or.inl rfl⟩
  · rintro source target action next ⟨rfl, rfl⟩ hstep
    rw [choice_step_iff] at hstep
    rcases hstep with hleft | hright
    · rw [sum_step_iff] at hleft
      exact ⟨_, sum_step_iff.mpr (List.mem_append.mpr (Or.inl hleft)), Or.inl rfl⟩
    · rw [sum_step_iff] at hright
      exact ⟨_, sum_step_iff.mpr (List.mem_append.mpr (Or.inr hright)), Or.inl rfl⟩

/-- A singleton sum represents one prefixed process. -/
theorem sum_singleton_bisimilar_prefix (action : Label Name)
    (continuation : StaticProcess Name) :
    lts.HomBisimilarity (sum [(action, continuation)]) (.prefix action continuation) := by
  let equation : StaticProcess Name → StaticProcess Name → Prop := fun source target =>
    source = sum [(action, continuation)] ∧ target = .prefix action continuation
  refine ⟨EquationClosure equation, Or.inr ⟨rfl, rfl⟩,
    equationClosure_isBisimulation ?_ ?_⟩
  · rintro source target label next ⟨rfl, rfl⟩ hstep
    rw [sum_step_iff] at hstep
    simp only [List.mem_singleton, Prod.mk.injEq] at hstep
    obtain ⟨rfl, rfl⟩ := hstep
    exact ⟨_, .prefix _ _, Or.inl rfl⟩
  · rintro source target label next ⟨rfl, rfl⟩ hstep
    rw [prefix_step_iff] at hstep
    obtain ⟨rfl, rfl⟩ := hstep
    exact ⟨_, sum_step_iff.mpr (by simp), Or.inl rfl⟩

end Cslib.CCS.StaticProcess
