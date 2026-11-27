/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.TwoEdgeBondToggle

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.TwoEdgeBondToggle`

* `program_complete_canonical_singleton_unitFlux`: a unit flux on an active edge completes the
  one-letter word;
* `twoUnit_pair_toggle` applied under its geometric hypotheses (toggling `secondCopy`).
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.TwoEdgeBondToggle

open _root_.StatMech.Sharpness _root_.StatMech.Sharpness.BackboneTwoEdgeBondToggle

/-- Classical decidability of adjacency, matching the library's section-local instance. -/
noncomputable local instance instDecAdjTest {W : Type*} (H : SimpleGraph W) :
    DecidableRel H.Adj :=
  Classical.decRel _

-- A unit flux on an active edge completes the one-letter word.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (d : shb_ExplorationDomain V)
    (e : d.graph.edgeFinset)
    (he : BackboneConcreteBondProgram.canonicalEdgeSegment d.graph e ∈ d.active) :
    BackboneTwoEdgeBondProgram.program.CompleteEvent d
      [BackboneConcreteBondProgram.canonicalEdgeSegment d.graph e]
      (BackboneConcreteBondProgram.unitFlux d.graph e) :=
  program_complete_canonical_singleton_unitFlux d e he

-- The pair toggle on the two-unit flux.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (d : shb_ExplorationDomain V)
    (e f : d.graph.edgeFinset) (hne : e ≠ f) :=
  twoUnit_pair_toggle d e f hne

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.TwoEdgeBondToggle
