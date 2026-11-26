/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.TwoEdgeExhaustiveProgram

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.TwoEdgeExhaustiveProgram`

* `Cycle.not_selectorSpec_fiber_oddTrianglePair` (refutation): the path-plus-odd-triangle current
  is not selected;
* `twoUnit_pair_toggle` applied under its geometric hypotheses;
* `selectorSpec` is a complete specification of `program` on `Fin 3`.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.TwoEdgeExhaustiveProgram

open _root_.StatMech.Sharpness _root_.StatMech.Sharpness.BackboneTwoEdgeExhaustiveProgram
open _root_.StatMech.Sharpness.BackboneTwoEdgeExhaustiveProgram.Cycle

/-- Classical decidability of adjacency, matching the library's section-local instance. -/
noncomputable local instance instDecAdjTest {W : Type*} (H : SimpleGraph W) :
    DecidableRel H.Adj :=
  Classical.decRel _

-- The odd-triangle current is not in the two-segment fiber.
example := Cycle.not_selectorSpec_fiber_oddTrianglePair

-- The pair toggle on two-unit fluxes.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (d : shb_ExplorationDomain V)
    (e f : d.graph.edgeFinset) (hne : e ≠ f) :=
  twoUnit_pair_toggle d e f hne

-- The specification on three vertices.
noncomputable example :
    BackboneConcreteSelector.CompleteBondwiseSelectorSpec (program (V := Fin 3)) :=
  selectorSpec

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.TwoEdgeExhaustiveProgram
