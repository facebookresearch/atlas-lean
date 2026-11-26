/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.P2CoordinateToggleObstruction

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.P2CoordinateToggleObstruction`

* `vacuumCoordinateToggleData_isEmpty` (refutation): no coordinate toggle data for the vacuum
  selector when the segment numerator is nonzero;
* `coordinateToggleData_isEmpty_of_left_zero_right_ne`: none when the left side of the active
  identity vanishes and the right side does not;
* both phrased as `¬ Nonempty`.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.P2CoordinateToggleObstruction

open _root_.StatMech.Sharpness _root_.StatMech.Sharpness.BackboneP2CoordinateToggleObstruction

/-- Classical decidability of adjacency, matching the library's section-local instance. -/
noncomputable local instance instDecAdjTest {W : Type*} (H : SimpleGraph W) :
    DecidableRel H.Adj :=
  Classical.decRel _

-- No toggle data for the vacuum selector.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (β : ℝ) (J : Sym2 V → ℝ)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V) (hs : s ∈ d.active)
    (hnum : shb_segmentNum β J d s ≠ 0) :
    ¬ Nonempty (CoordinateToggleData shb_vacuumPartialSelector β J d s [] hs) :=
  not_nonempty_iff.mpr (vacuumCoordinateToggleData_isEmpty β J d s hs hnum)

-- No toggle data when the left side vanishes and the right side does not.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (S : shb_PartialCurrentDynamicSelector) (β : ℝ) (J : Sym2 V → ℝ) (d : shb_ExplorationDomain V)
    (s : shb_ExplorationSegment V) (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (h0 : S.actualMass β J d (s :: ss) = 0)
    (hne : shb_segmentNum β J d s *
      S.actualMass β J (shb_BackboneExplorationDomain.advance d s) ss ≠ 0) :
    ¬ Nonempty (CoordinateToggleData S β J d s ss hs) :=
  not_nonempty_iff.mpr
    (coordinateToggleData_isEmpty_of_left_zero_right_ne S β J d s ss hs h0 hne)

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.P2CoordinateToggleObstruction
