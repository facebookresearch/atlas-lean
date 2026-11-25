/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.PointerAnalysis.HeapLang

/-!
Heap language statement-stage tests: aliasing and nonaliasing runs.
-/

@[expose] public section
set_option autoImplicit false
namespace Cslib.Languages.PointerAnalysis.HeapLangTests
open Cslib.Languages.OperationalSemantics Cslib.Languages.PointerAnalysis.HeapLang

/-- Aliasing program using vars x y w z and sites 10 20. -/
def aliasProg : Stmt :=
  .seq (.new 0 10)
    (.seq (.copy 1 0)
      (.seq (.new 2 20) (.seq (.store 0 2) (.load 3 1))))

/-- Nonaliasing program using vars x y w z and sites 10 20. -/
def nonAliasProg : Stmt :=
  .seq (.new 0 10) (.seq (.new 2 20) (.seq (.store 0 2) (.load 3 1)))

/-- Aliasing run reaches store 20 at z and heap 20 at site 10. -/
theorem aliasing_example_runs :
    ∃ (store : Store) (heap : Heap),
      Steps (aliasProg, fun _ => 0, fun _ => 0) (.skip, store, heap) ∧
        store 3 = 20 ∧ heap 10 = 20 := by
  refine ⟨Function.update ?s3 3 ?v, Function.update ?h2 ?a ?b,
    ?hsteps, ?hstore, ?hheap⟩
  case hsteps =>
    apply Relation.ReflTransGen.head (Step.seqStep Step.new)
    apply Relation.ReflTransGen.head Step.seqSkip
    apply Relation.ReflTransGen.head (Step.seqStep Step.copy)
    apply Relation.ReflTransGen.head Step.seqSkip
    apply Relation.ReflTransGen.head (Step.seqStep Step.new)
    apply Relation.ReflTransGen.head Step.seqSkip
    apply Relation.ReflTransGen.head (Step.seqStep Step.store)
    apply Relation.ReflTransGen.head Step.seqSkip
    apply Relation.ReflTransGen.head Step.load
    exact Relation.ReflTransGen.refl
  case hstore => simp
  case hheap => simp

/-- Nonaliasing run keeps z at 0 while heap 10 holds 20. -/
theorem nonalias_counterexample :
    ∃ (store : Store) (heap : Heap),
      Steps (nonAliasProg, fun _ => 0, fun _ => 0) (.skip, store, heap) ∧
        store 3 = 0 ∧ heap 10 = 20 := by
  refine ⟨Function.update ?s2 3 ?v, Function.update ?h2 ?a ?b,
    ?hsteps, ?hstore, ?hheap⟩
  case hsteps =>
    apply Relation.ReflTransGen.head (Step.seqStep Step.new)
    apply Relation.ReflTransGen.head Step.seqSkip
    apply Relation.ReflTransGen.head (Step.seqStep Step.new)
    apply Relation.ReflTransGen.head Step.seqSkip
    apply Relation.ReflTransGen.head (Step.seqStep Step.store)
    apply Relation.ReflTransGen.head Step.seqSkip
    apply Relation.ReflTransGen.head Step.load
    exact Relation.ReflTransGen.refl
  case hstore => simp
  case hheap => simp

/-- Skip is final and takes no steps from the empty state. -/
theorem skip_final_terminal :
    opsem.Final (.skip, fun _ => 0, fun _ => 0) ∧
      ¬ ∃ c' : Config, Step (.skip, fun _ => 0, fun _ => 0) c' := by
  constructor
  · simp [opsem]
  · intro h
    obtain ⟨c', hstep⟩ := h
    exact Step.skip_not_step hstep

/-- Adapter aliasing run reaches store 20 at z. -/
theorem opsem_aliasing_example_runs :
    ∃ (store : Store) (heap : Heap),
      OpSem.Steps opsem (aliasProg, fun _ => 0, fun _ => 0)
        (.skip, store, heap) ∧ store 3 = 20 := by
  refine ⟨Function.update ?s3 3 ?v, Function.update ?h2 ?a ?b,
    ?hsteps, ?hstore⟩
  case hsteps =>
    apply (opsem_steps_iff).mpr
    apply Relation.ReflTransGen.head (Step.seqStep Step.new)
    apply Relation.ReflTransGen.head Step.seqSkip
    apply Relation.ReflTransGen.head (Step.seqStep Step.copy)
    apply Relation.ReflTransGen.head Step.seqSkip
    apply Relation.ReflTransGen.head (Step.seqStep Step.new)
    apply Relation.ReflTransGen.head Step.seqSkip
    apply Relation.ReflTransGen.head (Step.seqStep Step.store)
    apply Relation.ReflTransGen.head Step.seqSkip
    apply Relation.ReflTransGen.head Step.load
    exact Relation.ReflTransGen.refl
  case hstore => simp

end Cslib.Languages.PointerAnalysis.HeapLangTests
