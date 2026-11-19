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
# Finite CCS expansion law
-/
module

public import CSLibExt.Languages.CCS.StrongCongruence

/-!
# Finite CCS expansion law

This module represents finite head-normal forms as lists of action-prefixed
summands.  It then constructs the standard expansion of a parallel composition:
every left move, every right move, and every synchronizing pair becomes one
summand.  The main theorem proves that this finite expansion is strongly
bisimilar to the original parallel composition.

The presentation follows Robin Milner, *Communication and Concurrency*,
Prentice Hall, 1989, Chapter 3 (ISBN 978-0-13-115007-2).
-/

@[expose] public section

namespace Cslib.CCS.StaticProcess

open Cslib.LTS

variable {Name : Type*} [DecidableEq Name]

/-- One action-prefixed branch of a finite head-normal form. -/
abbrev Summand (Name : Type*) := Label Name × StaticProcess Name

/-- Interpret a list of summands as a right-associated finite choice. -/
def sum : List (Summand Name) → StaticProcess Name
  | [] => .nil
  | (action, continuation) :: rest =>
      .choice (.prefix action continuation) (sum rest)

omit [DecidableEq Name] in
@[simp] theorem sum_nil : sum ([] : List (Summand Name)) = .nil := rfl

omit [DecidableEq Name] in
@[simp] theorem sum_cons (head : Summand Name) (tail : List (Summand Name)) :
    sum (head :: tail) = .choice (.prefix head.1 head.2) (sum tail) := by
  cases head
  rfl

/-- The transitions of a finite sum are exactly its listed summands. -/
theorem sum_step_iff {summands : List (Summand Name)} {action : Label Name}
    {next : StaticProcess Name} :
    Step (sum summands) action next ↔ (action, next) ∈ summands := by
  induction summands with
  | nil => simp [sum, nil_no_step]
  | cons head tail ih =>
      rcases head with ⟨headAction, headNext⟩
      rw [sum_cons, choice_step_iff, prefix_step_iff, ih]
      simp only [Prod.mk.injEq, List.mem_cons]

/-- Left-component moves appearing in the expansion of a parallel sum. -/
def leftMoves (left : List (Summand Name)) (right : StaticProcess Name) :
    List (Summand Name) :=
  left.map fun branch => (branch.1, .parallel branch.2 right)

/-- Right-component moves appearing in the expansion of a parallel sum. -/
def rightMoves (left : StaticProcess Name) (right : List (Summand Name)) :
    List (Summand Name) :=
  right.map fun branch => (branch.1, .parallel left branch.2)

/-- Synchronization summands contributed by one fixed left branch. -/
def synchronizationsWith (left : Summand Name) (right : List (Summand Name)) :
    List (Summand Name) :=
  right.filterMap fun branch =>
    match Label.synchronize left.1 branch.1 with
    | some _ => some (.tau, .parallel left.2 branch.2)
    | none => none

/-- All synchronization summands in the expansion of two finite sums. -/
def synchronizationMoves (left right : List (Summand Name)) :
    List (Summand Name) :=
  left.flatMap fun branch => synchronizationsWith branch right

/-- The summands in the syntactic expansion of two finite sums. -/
def expansionSummands (left right : List (Summand Name)) : List (Summand Name) :=
  leftMoves left (sum right) ++ rightMoves (sum left) right ++
    synchronizationMoves left right

/-- The syntactic expansion of the parallel composition of two finite sums. -/
def expansion (left right : List (Summand Name)) : StaticProcess Name :=
  sum (expansionSummands left right)

omit [DecidableEq Name] in
theorem mem_leftMoves_iff {left : List (Summand Name)} {right : StaticProcess Name}
    {action : Label Name} {next : StaticProcess Name} :
    (action, next) ∈ leftMoves left right ↔
      ∃ continuation, (action, continuation) ∈ left ∧
        next = .parallel continuation right := by
  constructor
  · intro h
    simp only [leftMoves, List.mem_map] at h
    obtain ⟨⟨branchAction, continuation⟩, hmember, hpair⟩ := h
    simp only [Prod.mk.injEq] at hpair
    exact ⟨continuation, hpair.1 ▸ hmember, hpair.2.symm⟩
  · rintro ⟨continuation, hmember, rfl⟩
    simp only [leftMoves, List.mem_map]
    exact ⟨(action, continuation), hmember, rfl⟩

omit [DecidableEq Name] in
theorem mem_rightMoves_iff {left : StaticProcess Name} {right : List (Summand Name)}
    {action : Label Name} {next : StaticProcess Name} :
    (action, next) ∈ rightMoves left right ↔
      ∃ continuation, (action, continuation) ∈ right ∧
        next = .parallel left continuation := by
  constructor
  · intro h
    simp only [rightMoves, List.mem_map] at h
    obtain ⟨⟨branchAction, continuation⟩, hmember, hpair⟩ := h
    simp only [Prod.mk.injEq] at hpair
    exact ⟨continuation, hpair.1 ▸ hmember, hpair.2.symm⟩
  · rintro ⟨continuation, hmember, rfl⟩
    simp only [rightMoves, List.mem_map]
    exact ⟨(action, continuation), hmember, rfl⟩

theorem mem_synchronizationsWith_iff {left : Summand Name}
    {right : List (Summand Name)} {action : Label Name} {next : StaticProcess Name} :
    (action, next) ∈ synchronizationsWith left right ↔
      action = .tau ∧ ∃ rightAction rightNext,
        (rightAction, rightNext) ∈ right ∧
        left.1.Complementary rightAction ∧ next = .parallel left.2 rightNext := by
  constructor
  · intro h
    simp only [synchronizationsWith, List.mem_filterMap] at h
    obtain ⟨branch, hbranch, hmatch⟩ := h
    rcases branch with ⟨rightAction, rightNext⟩
    cases hs : Label.synchronize left.1 rightAction with
    | none => simp [hs] at hmatch
    | some result =>
      simp only [hs, Option.some.injEq, Prod.mk.injEq] at hmatch
      have complementary := (Label.synchronize_eq_some_iff.mp hs).2
      exact ⟨hmatch.1.symm, rightAction, rightNext, hbranch, complementary, hmatch.2.symm⟩
  · rintro ⟨rfl, rightAction, rightNext, hmember, complementary, rfl⟩
    simp only [synchronizationsWith, List.mem_filterMap]
    refine ⟨(rightAction, rightNext), hmember, ?_⟩
    have hs : Label.synchronize left.1 rightAction = some .tau :=
      Label.synchronize_eq_some_iff.mpr ⟨rfl, complementary⟩
    simp [hs]

theorem mem_synchronizationMoves_iff {left right : List (Summand Name)}
    {action : Label Name} {next : StaticProcess Name} :
    (action, next) ∈ synchronizationMoves left right ↔
      action = .tau ∧ ∃ leftAction leftNext rightAction rightNext,
        (leftAction, leftNext) ∈ left ∧ (rightAction, rightNext) ∈ right ∧
        leftAction.Complementary rightAction ∧ next = .parallel leftNext rightNext := by
  constructor
  · intro h
    simp only [synchronizationMoves, List.mem_flatMap] at h
    obtain ⟨branch, hbranch, hsync⟩ := h
    obtain ⟨rfl, rightAction, rightNext, hright, complementary, rfl⟩ :=
      mem_synchronizationsWith_iff.mp hsync
    exact ⟨rfl, branch.1, branch.2, rightAction, rightNext, hbranch, hright,
      complementary, rfl⟩
  · rintro ⟨rfl, leftAction, leftNext, rightAction, rightNext, hleft, hright,
      complementary, rfl⟩
    simp only [synchronizationMoves, List.mem_flatMap]
    exact ⟨(leftAction, leftNext), hleft, mem_synchronizationsWith_iff.mpr
      ⟨rfl, rightAction, rightNext, hright, complementary, rfl⟩⟩

/-- A transition of the syntactic expansion is exactly a left move, a right
move, or a complementary pair synchronized to `tau`. -/
theorem expansion_step_iff {left right : List (Summand Name)}
    {action : Label Name} {next : StaticProcess Name} :
    Step (expansion left right) action next ↔
      (∃ continuation, (action, continuation) ∈ left ∧
        next = .parallel continuation (sum right)) ∨
      (∃ continuation, (action, continuation) ∈ right ∧
        next = .parallel (sum left) continuation) ∨
      (action = .tau ∧ ∃ leftAction leftNext rightAction rightNext,
        (leftAction, leftNext) ∈ left ∧ (rightAction, rightNext) ∈ right ∧
        leftAction.Complementary rightAction ∧ next = .parallel leftNext rightNext) := by
  rw [expansion, expansionSummands, sum_step_iff]
  simp only [List.mem_append, mem_leftMoves_iff, mem_rightMoves_iff,
    mem_synchronizationMoves_iff]
  constructor
  · rintro ((hleft | hright) | hsync)
    · exact Or.inl hleft
    · exact Or.inr (Or.inl hright)
    · exact Or.inr (Or.inr hsync)
  · rintro (hleft | hright | hsync)
    · exact Or.inl (Or.inl hleft)
    · exact Or.inl (Or.inr hright)
    · exact Or.inr hsync

/-- Milner's finite expansion law: parallel composition of two finite sums is
strongly bisimilar to the sum of their interleavings and communications. -/
theorem parallel_sum_bisimilar_expansion (left right : List (Summand Name)) :
    lts.HomBisimilarity (.parallel (sum left) (sum right)) (expansion left right) := by
  let equation : StaticProcess Name → StaticProcess Name → Prop := fun source target =>
    source = .parallel (sum left) (sum right) ∧ target = expansion left right
  refine ⟨EquationClosure equation, Or.inr ⟨rfl, rfl⟩,
    equationClosure_isBisimulation ?_ ?_⟩
  · rintro source target action next ⟨rfl, rfl⟩ hstep
    cases hstep with
    | parallelLeft step =>
        rw [sum_step_iff] at step
        refine ⟨_, expansion_step_iff.mpr (Or.inl ⟨_, step, rfl⟩), Or.inl rfl⟩
    | parallelRight step =>
        rw [sum_step_iff] at step
        refine ⟨_, expansion_step_iff.mpr (Or.inr (Or.inl ⟨_, step, rfl⟩)), Or.inl rfl⟩
    | communicate leftStep rightStep complementary =>
        rw [sum_step_iff] at leftStep rightStep
        refine ⟨_, expansion_step_iff.mpr (Or.inr (Or.inr ⟨rfl, _, _, _, _,
          leftStep, rightStep, complementary, rfl⟩)), Or.inl rfl⟩
  · rintro source target action next ⟨rfl, rfl⟩ hstep
    rw [expansion_step_iff] at hstep
    rcases hstep with ⟨continuation, hmember, rfl⟩ |
        ⟨continuation, hmember, rfl⟩ |
        ⟨rfl, leftAction, leftNext, rightAction, rightNext, hleft, hright,
          complementary, rfl⟩
    · exact ⟨_, .parallelLeft (sum_step_iff.mpr hmember), Or.inl rfl⟩
    · exact ⟨_, .parallelRight (sum_step_iff.mpr hmember), Or.inl rfl⟩
    · exact ⟨_, .communicate (sum_step_iff.mpr hleft) (sum_step_iff.mpr hright)
        complementary, Or.inl rfl⟩

end Cslib.CCS.StaticProcess
