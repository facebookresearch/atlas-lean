/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.OperationalSemantics
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Relation

/-!
Allocation-site heap language, internal interface for later Andersen pointer-analysis work.
Folded site addresses with total store and heap functions updated by `Function.update`.
Excluded: Andersen constraint generation, least solution, solver, soundness,
Steensgaard, field sensitivity, concrete fresh-address semantics with separate
site tagging, conditionals, loops, free, arithmetic, Boolean guards, and any
separation-logic or Hoare coupling. No Andersen soundness claim is made here.
-/

@[expose] public section
set_option autoImplicit false
namespace Cslib.Languages.PointerAnalysis.HeapLang
open Cslib.Languages.OperationalSemantics

/-- Allocation site identifier, folded onto natural numbers. -/
abbrev Site := Nat

/-- Heap address, folded onto natural numbers for the site model. -/
abbrev Addr := Nat

/-- Total store mapping each identifier to an address. -/
abbrev Store := Nat -> Addr

/-- Total heap mapping each address to its stored address. -/
abbrev Heap := Nat -> Addr

/-- Heap language statements: skip, sequencing, and heap operations. -/
inductive Stmt where
  | skip
  | seq (first second : Stmt)
  | new (dst : Nat) (site : Site)
  | copy (dst src : Nat)
  | load (dst src : Nat)
  | store (dst src : Nat)
deriving DecidableEq, Repr

/-- Machine configuration: statement with total store and heap. -/
abbrev Config := Stmt × Store × Heap

/-- Small-step relation for the allocation-site heap language. -/
inductive Step : Config -> Config -> Prop where
  | new {dst : Nat} {site : Site} {store : Store} {heap : Heap} :
      Step (.new dst site, store, heap)
        (.skip, Function.update store dst site, Function.update heap site 0)
  | copy {dst src : Nat} {store : Store} {heap : Heap} :
      Step (.copy dst src, store, heap)
        (.skip, Function.update store dst (store src), heap)
  | load {dst src : Nat} {store : Store} {heap : Heap} :
      Step (.load dst src, store, heap)
        (.skip, Function.update store dst (heap (store src)), heap)
  | store {dst src : Nat} {store : Store} {heap : Heap} :
      Step (.store dst src, store, heap)
        (.skip, store, Function.update heap (store dst) (store src))
  | seqSkip {next : Stmt} {store : Store} {heap : Heap} :
      Step (.seq .skip next, store, heap) (next, store, heap)
  | seqStep {first first' second : Stmt} {store store' : Store}
      {heap heap' : Heap} :
      Step (first, store, heap) (first', store', heap') ->
      Step (.seq first second, store, heap) (.seq first' second, store', heap')

/-- Multi-step closure of `Step` via reflexive-transitive closure. -/
abbrev Steps : Config -> Config -> Prop := Relation.ReflTransGen Step

/-- Skip configurations never take a small step. -/
theorem Step.skip_not_step {store : Store} {heap : Heap} {c' : Config} :
    ¬ Step (.skip, store, heap) c' := by
  intro h
  cases h

/-- Steps from `new` reach exactly the allocation successor. -/
theorem Step.new_iff {dst : Nat} {site : Site} {store : Store} {heap : Heap}
    {c' : Config} :
    Step (.new dst site, store, heap) c' ↔
      c' = (.skip, Function.update store dst site,
        Function.update heap site 0) := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    subst h
    exact Step.new

/-- Steps from `copy` reach exactly the copy successor. -/
theorem Step.copy_iff {dst src : Nat} {store : Store} {heap : Heap}
    {c' : Config} :
    Step (.copy dst src, store, heap) c' ↔
      c' = (.skip, Function.update store dst (store src), heap) := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    subst h
    exact Step.copy

/-- Steps from `load` reach exactly the load successor. -/
theorem Step.load_iff {dst src : Nat} {store : Store} {heap : Heap}
    {c' : Config} :
    Step (.load dst src, store, heap) c' ↔
      c' = (.skip, Function.update store dst (heap (store src)), heap) := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    subst h
    exact Step.load

/-- Steps from `store` reach exactly the store successor. -/
theorem Step.store_iff {dst src : Nat} {store : Store} {heap : Heap}
    {c' : Config} :
    Step (.store dst src, store, heap) c' ↔
      c' = (.skip, store, Function.update heap (store dst) (store src)) := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    subst h
    exact Step.store

/-- Steps from `seq` split into skip and congruence cases. -/
theorem Step.seq_iff {first second : Stmt} {store : Store} {heap : Heap}
    {c' : Config} :
    Step (.seq first second, store, heap) c' ↔
      (first = .skip ∧ c' = (second, store, heap)) ∨
        ∃ (first' : Stmt) (store' : Store) (heap' : Heap),
          Step (first, store, heap) (first', store', heap') ∧
            c' = (.seq first' second, store', heap') := by
  constructor
  · intro h
    cases h
    case seqSkip => exact Or.inl ⟨rfl, rfl⟩
    case seqStep hsub => exact Or.inr ⟨_, _, _, hsub, rfl⟩
  · intro h
    cases h
    case inl hleft =>
      obtain ⟨hfirst, hsucc⟩ := hleft
      subst hfirst
      subst hsucc
      exact Step.seqSkip
    case inr hright =>
      obtain ⟨first', store', heap', hstep, hsucc⟩ := hright
      subst hsucc
      exact Step.seqStep hstep

/-- The heap language as an operational semantics with unit labels: its steps are `Step`, and a
configuration is final when its statement is `skip`. -/
def opsem : OpSem Config Unit where
  lts := { Tr := fun x _ y => Step x y }
  Final := fun c => c.1 = .skip
  final_terminal := by
    intro c hfinal _ c' hstep
    obtain ⟨stmt, store, heap⟩ := c
    simp at hfinal
    subst hfinal
    cases hstep

/-- Single steps of `opsem` coincide with `Step`. -/
theorem opsem_step_iff {x y : Config} :
    OpSem.Step opsem x y ↔ Step x y := by
  constructor
  · intro h
    obtain ⟨_, hstep⟩ := h
    exact hstep
  · intro hstep
    exact ⟨(), hstep⟩

/-- Multi-steps of `opsem` coincide with `Steps`. -/
theorem opsem_steps_iff {x y : Config} :
    OpSem.Steps opsem x y ↔ Steps x y := by
  rw [(OpSem.steps_iff_reflTransGen opsem)]
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih =>
      exact Relation.ReflTransGen.tail ih ((opsem_step_iff).mp hstep)
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih =>
      exact Relation.ReflTransGen.tail ih ((opsem_step_iff).mpr hstep)

/-- The small-step relation is deterministic. -/
theorem Step.deterministic {x y z : Config} :
    Step x y -> Step x z -> y = z := by
  intro h1 h2
  induction h1 generalizing z with
  | new => cases h2; rfl
  | copy => cases h2; rfl
  | load => cases h2; rfl
  | store => cases h2; rfl
  | seqSkip =>
    cases h2 with
    | seqSkip => rfl
    | seqStep hsub => exact absurd hsub Step.skip_not_step
  | seqStep hsub ih =>
    cases h2 with
    | seqSkip => exact absurd hsub Step.skip_not_step
    | seqStep hsub2 =>
      have heq := ih hsub2
      simp_all

/-- The operational semantics `opsem` is deterministic. -/
theorem opsem_deterministic : OpSem.Deterministic opsem := by
  intro x y z h1 h2
  exact Step.deterministic (opsem_step_iff.mp h1) (opsem_step_iff.mp h2)

end Cslib.Languages.PointerAnalysis.HeapLang
