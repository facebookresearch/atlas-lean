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
# Weak algebraic laws for extended finite CCS
-/
module

public import CSLibExt.Languages.CCS.WeakStaticParallel

/-!
# Weak algebraic laws for extended finite CCS

The strong static equations already proved for restriction, relabelling, and
choice remain valid at both observational-congruence and weak-bisimilarity
levels. This module exposes those consequences explicitly, so clients of the
weak semantics do not need to move through the strong theory by hand.

The two layers are deliberately kept distinct. The rooted results are safe in
all congruence contexts developed for extended CCS; the ordinary weak results
are convenient coarser corollaries.

The equations follow Robin Milner, *Communication and Concurrency*, Prentice
Hall, 1989, Chapters 2--3 and 5 (ISBN 978-0-13-115007-2).
-/

@[expose] public section

namespace Cslib.CCS.StaticProcess

open Cslib.LTS

variable {Name : Type*} [DecidableEq Name]

/-! ## Restriction laws -/

/-- Restriction of termination is observationally congruent to termination. -/
theorem restriction_nil_observationCongruent (blocked : List Name) :
    ObservationCongruent (.restriction blocked .nil) .nil :=
  observationCongruent_of_bisimilar (restriction_nil blocked)

/-- Restriction commutes with an allowed prefix up to observational
congruence. -/
theorem restriction_prefix_of_allowed_observationCongruent
    (blocked : List Name) (action : Label Name) (process : StaticProcess Name)
    (allowed : Allowed blocked action) :
    ObservationCongruent (.restriction blocked (.prefix action process))
      (.prefix action (.restriction blocked process)) :=
  observationCongruent_of_bisimilar
    (restriction_prefix_of_allowed blocked action process allowed)

/-- Restriction suppresses a blocked prefix up to observational congruence. -/
theorem restriction_prefix_of_blocked_observationCongruent
    (blocked : List Name) (action : Label Name) (process : StaticProcess Name)
    (notAllowed : ¬Allowed blocked action) :
    ObservationCongruent (.restriction blocked (.prefix action process)) .nil :=
  observationCongruent_of_bisimilar
    (restriction_prefix_of_blocked blocked action process notAllowed)

/-- Restriction distributes over choice up to observational congruence. -/
theorem restriction_choice_observationCongruent
    (blocked : List Name) (left right : StaticProcess Name) :
    ObservationCongruent (.restriction blocked (.choice left right))
      (.choice (.restriction blocked left) (.restriction blocked right)) :=
  observationCongruent_of_bisimilar (restriction_choice blocked left right)

/-- Empty restriction is observationally congruent to the original process. -/
theorem restriction_empty_observationCongruent (process : StaticProcess Name) :
    ObservationCongruent (.restriction [] process) process :=
  observationCongruent_of_bisimilar (restriction_empty process)

/-- Extensionally equal blocked-name lists induce observationally congruent
restrictions. -/
theorem restriction_congr_list_observationCongruent
    {first second : List Name} (process : StaticProcess Name)
    (hmem : ∀ name, name ∈ first ↔ name ∈ second) :
    ObservationCongruent (.restriction first process) (.restriction second process) :=
  observationCongruent_of_bisimilar (restriction_congr_list hmem process)

/-! ## Relabelling laws -/

/-- Relabelling termination is observationally congruent to termination. -/
theorem relabelling_nil_observationCongruent (rename : Relabelling Name) :
    ObservationCongruent (.relabelling rename .nil) .nil :=
  observationCongruent_of_bisimilar (relabelling_nil rename)

/-- Relabelling commutes with prefix up to observational congruence. -/
theorem relabelling_prefix_observationCongruent
    (rename : Relabelling Name) (action : Label Name) (process : StaticProcess Name) :
    ObservationCongruent (.relabelling rename (.prefix action process))
      (.prefix (relabelAction rename action) (.relabelling rename process)) :=
  observationCongruent_of_bisimilar (relabelling_prefix rename action process)

/-- Relabelling distributes over choice up to observational congruence. -/
theorem relabelling_choice_observationCongruent
    (rename : Relabelling Name) (left right : StaticProcess Name) :
    ObservationCongruent (.relabelling rename (.choice left right))
      (.choice (.relabelling rename left) (.relabelling rename right)) :=
  observationCongruent_of_bisimilar (relabelling_choice rename left right)

/-- Empty relabelling is observationally congruent to the original process. -/
theorem relabelling_empty_observationCongruent (process : StaticProcess Name) :
    ObservationCongruent (.relabelling ⟨[]⟩ process) process :=
  observationCongruent_of_bisimilar (relabelling_empty process)

/-! ## Choice laws -/

/-- Choice is commutative up to observational congruence. -/
theorem choice_comm_observationCongruent (left right : StaticProcess Name) :
    ObservationCongruent (.choice left right) (.choice right left) :=
  observationCongruent_of_bisimilar (choice_comm left right)

/-- Termination is a left unit for choice up to observational congruence. -/
theorem choice_nil_left_observationCongruent (process : StaticProcess Name) :
    ObservationCongruent (.choice .nil process) process :=
  observationCongruent_of_bisimilar (choice_nil_left process)

/-- Choice is idempotent up to observational congruence. -/
theorem choice_self_observationCongruent (process : StaticProcess Name) :
    ObservationCongruent (.choice process process) process :=
  observationCongruent_of_bisimilar (choice_self process)

/-! ## Ordinary weak corollaries -/

/-- Restriction of termination is weakly bisimilar to termination. -/
theorem restriction_nil_weaklyBisimilar (blocked : List Name) :
    WeaklyBisimilar (.restriction blocked .nil) .nil :=
  (restriction_nil_observationCongruent blocked).to_homWeakBisimilarity

/-- Restriction commutes with an allowed prefix up to weak bisimilarity. -/
theorem restriction_prefix_of_allowed_weaklyBisimilar
    (blocked : List Name) (action : Label Name) (process : StaticProcess Name)
    (allowed : Allowed blocked action) :
    WeaklyBisimilar (.restriction blocked (.prefix action process))
      (.prefix action (.restriction blocked process)) :=
  (restriction_prefix_of_allowed_observationCongruent
    blocked action process allowed).to_homWeakBisimilarity

/-- Restriction suppresses a blocked prefix up to weak bisimilarity. -/
theorem restriction_prefix_of_blocked_weaklyBisimilar
    (blocked : List Name) (action : Label Name) (process : StaticProcess Name)
    (notAllowed : ¬Allowed blocked action) :
    WeaklyBisimilar (.restriction blocked (.prefix action process)) .nil :=
  (restriction_prefix_of_blocked_observationCongruent
    blocked action process notAllowed).to_homWeakBisimilarity

/-- Restriction distributes over choice up to weak bisimilarity. -/
theorem restriction_choice_weaklyBisimilar
    (blocked : List Name) (left right : StaticProcess Name) :
    WeaklyBisimilar (.restriction blocked (.choice left right))
      (.choice (.restriction blocked left) (.restriction blocked right)) :=
  (restriction_choice_observationCongruent blocked left right).to_homWeakBisimilarity

/-- Empty restriction is weakly bisimilar to the original process. -/
theorem restriction_empty_weaklyBisimilar (process : StaticProcess Name) :
    WeaklyBisimilar (.restriction [] process) process :=
  (restriction_empty_observationCongruent process).to_homWeakBisimilarity

/-- Extensionally equal blocked-name lists induce weakly bisimilar
restrictions. -/
theorem restriction_congr_list_weaklyBisimilar
    {first second : List Name} (process : StaticProcess Name)
    (hmem : ∀ name, name ∈ first ↔ name ∈ second) :
    WeaklyBisimilar (.restriction first process) (.restriction second process) :=
  (restriction_congr_list_observationCongruent process hmem).to_homWeakBisimilarity

/-- Relabelling termination is weakly bisimilar to termination. -/
theorem relabelling_nil_weaklyBisimilar (rename : Relabelling Name) :
    WeaklyBisimilar (.relabelling rename .nil) .nil :=
  (relabelling_nil_observationCongruent rename).to_homWeakBisimilarity

/-- Relabelling commutes with prefix up to weak bisimilarity. -/
theorem relabelling_prefix_weaklyBisimilar
    (rename : Relabelling Name) (action : Label Name) (process : StaticProcess Name) :
    WeaklyBisimilar (.relabelling rename (.prefix action process))
      (.prefix (relabelAction rename action) (.relabelling rename process)) :=
  (relabelling_prefix_observationCongruent rename action process).to_homWeakBisimilarity

/-- Relabelling distributes over choice up to weak bisimilarity. -/
theorem relabelling_choice_weaklyBisimilar
    (rename : Relabelling Name) (left right : StaticProcess Name) :
    WeaklyBisimilar (.relabelling rename (.choice left right))
      (.choice (.relabelling rename left) (.relabelling rename right)) :=
  (relabelling_choice_observationCongruent rename left right).to_homWeakBisimilarity

/-- Empty relabelling is weakly bisimilar to the original process. -/
theorem relabelling_empty_weaklyBisimilar (process : StaticProcess Name) :
    WeaklyBisimilar (.relabelling ⟨[]⟩ process) process :=
  (relabelling_empty_observationCongruent process).to_homWeakBisimilarity

/-- Choice is commutative up to weak bisimilarity. -/
theorem choice_comm_weaklyBisimilar (left right : StaticProcess Name) :
    WeaklyBisimilar (.choice left right) (.choice right left) :=
  (choice_comm_observationCongruent left right).to_homWeakBisimilarity

/-- Termination is a left unit for choice up to weak bisimilarity. -/
theorem choice_nil_left_weaklyBisimilar (process : StaticProcess Name) :
    WeaklyBisimilar (.choice .nil process) process :=
  (choice_nil_left_observationCongruent process).to_homWeakBisimilarity

/-- Choice is idempotent up to weak bisimilarity. -/
theorem choice_self_weaklyBisimilar (process : StaticProcess Name) :
    WeaklyBisimilar (.choice process process) process :=
  (choice_self_observationCongruent process).to_homWeakBisimilarity

end Cslib.CCS.StaticProcess
