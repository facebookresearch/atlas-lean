/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.ConcreteBondProgram

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.ConcreteBondProgram`

* `program_realizes_selectorSpec` on `Fin 2`: the concrete program realizes its own selector
  specification (a concrete inhabitant of `CompleteBondwiseSelectorSpec`);
* `program_complete_word_eq_nil_or_singleton`: complete events select words of length at most one;
* `program_not_realizes_of_two_segment_fiber` and
  `intendedOneStepRealization_isEmpty_of_noncanonical_chosen` (the refutations) applied.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.ConcreteBondProgram

open _root_.StatMech.Sharpness _root_.StatMech.Sharpness.BackboneConcreteBondProgram
open _root_.StatMech.Sharpness.BackboneConcreteSelector

/-- Classical decidability of adjacency, matching the library's section-local instance. -/
noncomputable local instance instDecAdjTest {W : Type*} (H : SimpleGraph W) :
    DecidableRel H.Adj :=
  Classical.decRel _

-- The program realizes its selector specification on two vertices.
example : ProgramRealizes (program (V := Fin 2)) selectorSpec.toPartialSelector :=
  program_realizes_selectorSpec

-- Complete events select the empty word or a single segment.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (d : shb_ExplorationDomain V)
    (m : d.graph.edgeFinset → ℕ) (word : List (shb_ExplorationSegment V))
    (h : program.CompleteEvent d word m) : word = [] ∨ ∃ s, word = [s] :=
  program_complete_word_eq_nil_or_singleton d m word h

-- A selector with a nonempty fiber on a two-letter word is not realized.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (S : shb_PartialCurrentDynamicSelector) (d : shb_ExplorationDomain V)
    (m : d.graph.edgeFinset → ℕ) (s t : shb_ExplorationSegment V)
    (h : S.Fiber d [s, t] m) : ¬ ProgramRealizes program S :=
  program_not_realizes_of_two_segment_fiber S d m s t [] h

-- The intended one-step selector is not realized once a non-canonical segment is chosen.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (d : shb_ExplorationDomain V)
    (m : d.graph.edgeFinset → ℕ) (s : shb_ExplorationSegment V)
    (hsrc : sources d.graph (ofEdgeFun d.graph m) ≠ ∅) (hs : shb_oneStepChosenSegment d m = some s)
    (hnc : ∀ e : d.graph.edgeFinset, canonicalEdgeSegment d.graph e ≠ s) :
    IsEmpty (IntendedOneStepRealization (V := V)) :=
  intendedOneStepRealization_isEmpty_of_noncanonical_chosen d m s hsrc hs hnc

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.ConcreteBondProgram
