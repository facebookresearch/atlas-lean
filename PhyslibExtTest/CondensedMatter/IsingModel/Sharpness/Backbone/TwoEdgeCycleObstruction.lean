/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.TwoEdgeCycleObstruction

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.TwoEdgeCycleObstruction`

* `not_canonicalComponentwiseToggleExists` at `β = J = 1` (refutation on the explicit
  path-plus-triangle domain);
* `no_residualVacuum_suffix_covariance` for the empty set of copies and for every set.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.TwoEdgeCycleObstruction

open _root_.StatMech.Sharpness _root_.StatMech.Sharpness.BackboneTwoEdgeCycleObstruction

/-- Classical decidability of adjacency, matching the library's section-local instance. -/
noncomputable local instance instDecAdjTest {W : Type*} (H : SimpleGraph W) :
    DecidableRel H.Adj :=
  Classical.decRel _

-- No canonical componentwise toggle at `β = J = 1`.
example : ¬ BackboneTwoEdgeBondProgram.selectorSpec.CanonicalComponentwiseToggleExists 1
    (fun _ => 1) domain (BackboneConcreteBondProgram.canonicalEdgeSegment domain.graph headEdge)
    [BackboneConcreteBondProgram.canonicalEdgeSegment domain.graph suffixEdge] head_active :=
  not_canonicalComponentwiseToggleExists 1 _ one_pos fun _ => one_pos

-- Toggling no copies is not a covariance of the residual runs.
example := no_residualVacuum_suffix_covariance ∅

-- Nor is toggling any set of copies.
example := @no_residualVacuum_suffix_covariance

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.TwoEdgeCycleObstruction
