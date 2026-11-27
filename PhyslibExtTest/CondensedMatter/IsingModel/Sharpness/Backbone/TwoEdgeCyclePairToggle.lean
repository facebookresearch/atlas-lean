/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.TwoEdgeCyclePairToggle

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.TwoEdgeCyclePairToggle`

* `complete_pair_bits_eq_twoUnit`: complete two-edge runs on the cycle domain have the parity
  pattern of the two-unit flux;
* `exhaustive_cycle_pair_toggle_exists` applied under `hfirst`, `hpath` (conditional).
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.TwoEdgeCyclePairToggle

open _root_.StatMech.Sharpness _root_.StatMech.Sharpness.BackboneTwoEdgeCyclePairToggle

/-- Classical decidability of adjacency, matching the library's section-local instance. -/
noncomputable local instance instDecAdjTest {W : Type*} (H : SimpleGraph W) :
    DecidableRel H.Adj :=
  Classical.decRel _

-- Complete runs have the two-unit parity pattern.
example := complete_pair_bits_eq_twoUnit

-- A toggling set of copies exists, conditional on `hfirst` and `hpath`.
example := exhaustive_cycle_pair_toggle_exists

-- The parity statement specialised to a given complete flux.
example (p : BackboneTwoEdgeCycleObstruction.domain.graph.edgeFinset → ℕ)
    (hp : BackboneTwoEdgeExhaustiveProgram.program.CompleteEvent
      BackboneTwoEdgeCycleObstruction.domain
      [BackboneConcreteBondProgram.canonicalEdgeSegment
          BackboneTwoEdgeCycleObstruction.domain.graph BackboneTwoEdgeCycleObstruction.headEdge,
        BackboneConcreteBondProgram.canonicalEdgeSegment
          BackboneTwoEdgeCycleObstruction.domain.graph BackboneTwoEdgeCycleObstruction.suffixEdge]
      p) :=
  complete_pair_bits_eq_twoUnit p hp

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.TwoEdgeCyclePairToggle
