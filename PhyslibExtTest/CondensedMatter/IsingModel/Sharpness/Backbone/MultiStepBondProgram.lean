/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.MultiStepBondProgram

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.MultiStepBondProgram`

* `selectorRealization` and `program_realizes_selectorSpec` on `Fin 3`: the two-step program
  realizes its selector specification (concrete inhabitants);
* `program_complete_word_eq_nil_or_pair`: complete events select the empty word or a pair;
* `intendedOneStepRealization_isEmpty_of_designated_pair` (refutation) and
  `selectorSpec_fiber_designated_twoUnitFlux` applied to a designated pair.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.MultiStepBondProgram

open _root_.StatMech.Sharpness _root_.StatMech.Sharpness.BackboneMultiStepBondProgram

/-- Classical decidability of adjacency, matching the library's section-local instance. -/
noncomputable local instance instDecAdjTest {W : Type*} (H : SimpleGraph W) :
    DecidableRel H.Adj :=
  Classical.decRel _

-- The two-step program realizes its specification on three vertices.
example : BackboneConcreteBondProgram.SelectorRealization (program (V := Fin 3))
    selectorSpec.toPartialSelector :=
  selectorRealization

-- The same, in the `ProgramRealizes` form.
example : BackboneConcreteBondProgram.ProgramRealizes (program (V := Fin 3))
    selectorSpec.toPartialSelector :=
  program_realizes_selectorSpec

-- Complete events select the empty word or a pair of segments.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (d : shb_ExplorationDomain V)
    (m : d.graph.edgeFinset → ℕ) (word : List (shb_ExplorationSegment V))
    (h : program.CompleteEvent d word m) : word = [] ∨ ∃ s t, word = [s, t] :=
  program_complete_word_eq_nil_or_pair d m word h

-- A designated pair with active canonical segments rules out realizing the one-step selector.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (d : shb_ExplorationDomain V)
    (e f : d.graph.edgeFinset) (hp : IsDesignatedPair d e f)
    (he : BackboneConcreteBondProgram.canonicalEdgeSegment d.graph e ∈ d.active)
    (hf : BackboneConcreteBondProgram.canonicalEdgeSegment d.graph f ∈ d.active) :
    IsEmpty (BackboneConcreteBondProgram.SelectorRealization (program (V := V))
        shb_oneStepPartialSelector) ∧
      selectorSpec.toPartialSelector.Fiber d
        [BackboneConcreteBondProgram.canonicalEdgeSegment d.graph e,
          BackboneConcreteBondProgram.canonicalEdgeSegment d.graph f]
        (twoUnitFlux d.graph e f) :=
  ⟨intendedOneStepRealization_isEmpty_of_designated_pair d e f hp he hf,
    selectorSpec_fiber_designated_twoUnitFlux d e f hp he hf⟩

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.MultiStepBondProgram
