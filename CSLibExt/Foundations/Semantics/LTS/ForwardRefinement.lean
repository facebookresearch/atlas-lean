/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Foundations.Semantics.LTS.OmegaExecution
public import Mathlib.Data.Set.Basic

/-!
# Data refinement by forward simulation

A mapping defined only on invariant concrete states preserves initial states and transitions
with the same operation, argument, and result. It transfers finite traces and maps finite and
infinite executions pointwise without inserting or deleting steps.

This is the label-preserving safety specialization of Abadi and Lamport, *The existence of
refinement mappings*, Theoretical Computer Science 82(2), 1991, §1.2 and Proposition 1.
It does not compare termination or divergence of operations.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.LTS

variable {C A Label : Type*}

/-- The traces of an LTS from any state in its initial set. For a data type, the common label
records the operation, argument, and result. -/
def tracesFrom {State : Type*} (lts : LTS State Label) (initial : Set State) : Set (List Label) :=
  { labels | ∃ s ∈ initial, labels ∈ lts.traces s }

/-- A forward refinement map is defined on invariant concrete states. Every concrete initial
state satisfies the invariant and maps to an abstract initial state. Each concrete step from an
invariant state stays in the invariant and maps to an abstract step with the same label. -/
structure ForwardRefinement (concrete : LTS C Label) (abstract : LTS A Label)
    (concreteInit : Set C) (abstractInit : Set A) (invariant : Set C) where
  mapState : {s // s ∈ invariant} → A
  initial_mem : ∀ s, s ∈ concreteInit → s ∈ invariant
  initial_map : ∀ s (hs : s ∈ concreteInit), mapState ⟨s, initial_mem s hs⟩ ∈ abstractInit
  step_mem : ∀ {s t label}, s ∈ invariant → concrete.Tr s label t → t ∈ invariant
  step_map : ∀ {s t label} (hs : s ∈ invariant) (h : concrete.Tr s label t),
    abstract.Tr (mapState ⟨s, hs⟩) label (mapState ⟨t, step_mem hs h⟩)

namespace ForwardRefinement

variable {concrete : LTS C Label} {abstract : LTS A Label}
  {concreteInit : Set C} {abstractInit : Set A} {invariant : Set C}
  (f : ForwardRefinement concrete abstract concreteInit abstractInit invariant)

/-- Every state of a finite execution from an invariant state stays in the invariant. Applying
the refinement map to each state gives an abstract execution with the original labels. -/
theorem map_execution {s t : C} {labels : List Label} {ss : List C}
    (h : concrete.Execution s labels t ss) (hs : s ∈ invariant) :
    ∃ (hss : ∀ x ∈ ss, x ∈ invariant) (ht : t ∈ invariant),
      abstract.Execution (f.mapState ⟨s, hs⟩) labels (f.mapState ⟨t, ht⟩)
        (ss.pmap (fun x hx => f.mapState ⟨x, hx⟩) hss) := by
  induction h with
  | refl s =>
      refine ⟨?_, hs, .refl _⟩
      intro x hx
      obtain rfl := List.mem_singleton.mp hx
      exact hs
  | @stepL r s t label labels ss hstep htail ih =>
      obtain ⟨hss, ht, hmap⟩ := ih (f.step_mem hs hstep)
      have hcons : ∀ x ∈ r :: ss, x ∈ invariant := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hs
        · exact hss x hx
      exact ⟨hcons, ht, .stepL (f.step_map hs hstep) hmap⟩

include f in
/-- **Finite trace inclusion by forward refinement.** Every operation trace from a concrete
initial state is also an operation trace from an abstract initial state. This includes the empty
trace and applies to nondeterministic transition systems. -/
theorem tracesFrom_subset :
    concrete.tracesFrom concreteInit ⊆ abstract.tracesFrom abstractInit := by
  rintro labels ⟨s, hs, t, h⟩
  obtain ⟨ss, hex⟩ := mTr_iff_execution.mp h
  obtain ⟨_, ht, hmap⟩ := f.map_execution hex (f.initial_mem s hs)
  exact ⟨f.mapState ⟨s, f.initial_mem s hs⟩, f.initial_map s hs, f.mapState ⟨t, ht⟩, hmap.to_mTr⟩

/-- The pointwise image of an infinite concrete execution from an initial state starts in the
abstract initial set and is an abstract execution with the same label at every position. -/
theorem map_initial_omegaExecution {ss : ωSequence C} {labels : ωSequence Label}
    (h : concrete.OmegaExecution ss labels) (hinit : ss 0 ∈ concreteInit) :
    ∃ hss : ∀ i, ss i ∈ invariant,
      f.mapState ⟨ss 0, hss 0⟩ ∈ abstractInit ∧
        abstract.OmegaExecution (⟨fun i => f.mapState ⟨ss i, hss i⟩⟩ : ωSequence A) labels := by
  have hss (i : ℕ) : ss i ∈ invariant := by
    induction i with
    | zero => exact f.initial_mem _ hinit
    | succ i ih => exact f.step_mem ih (h i)
  exact ⟨hss, f.initial_map _ hinit, fun i => f.step_map (hss i) (h i)⟩

end ForwardRefinement

end Cslib.LTS
