/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
-- Co-import regression: the two file-local adjacency instances must not collide.
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.ActualSelectorObstruction
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.ActualSelectorSwitching

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.ActualSelectorSwitching`

* on one vertex (`Fin 1`) every current is sourceless;
* `shb_activeSegmentFiberMass_eq_segmentNum` (unconditional).

The vacuous selector API (`shb_CurrentDynamicSelector`, its switching law, and the actual
fiber mass identities) was removed; its tests were removed with it.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.ActualSelectorSwitching

open _root_.StatMech _root_.StatMech.Sharpness

/-- Classical decidability of adjacency, matching the library's section-local instance. -/
noncomputable local instance instDecAdjTest {W : Type*} (H : SimpleGraph W) :
    DecidableRel H.Adj :=
  Classical.decRel _


/-- On one vertex every current has no sources. -/
theorem sources_fin1 (G : SimpleGraph (Fin 1)) [DecidableRel G.Adj] (n : Current (Fin 1)) :
    sources G n = ∅ := by
  have hG : G.edgeFinset = ∅ := by
    ext e
    induction e using Sym2.ind with
    | _ a b => simp [Subsingleton.elim a b]
  simp [sources, incidentFlux, hG]

-- The active segment fiber mass is the segment numerator.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (β : ℝ) (J : Sym2 V → ℝ)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V) (hs : s ∈ d.active) :
    (∑' m : d.graph.edgeFinset → ℕ,
      if shb_ActiveSegmentFiber d s hs m then shb_explorationCoordinateWeight β J d m else 0) =
      shb_segmentNum β J d s :=
  shb_activeSegmentFiberMass_eq_segmentNum β J d s hs

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.ActualSelectorSwitching
