/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.P2CoordinateReindex

/-!
# Obstruction to coordinate toggle data

The coordinate toggle data of `P2CoordinateReindex` imply the active cut resummation identity, so
they cannot exist when its left side vanishes and its right side does not. For the vacuum partial
selector this happens at every active segment with nonzero numerator.

## i. Overview

`CoordinateToggleData` bundles the contributing-path selector, its source condition and the
transport equivalence used by `actualMass_active_of_coordinateToggle`. Since these data yield the
identity `fiber(s :: ss) × Z(residual) = N(s) × fiber(ss)`, the type is empty whenever the left
side is zero and the right side nonzero (`coordinateToggleData_isEmpty_of_left_zero_right_ne`).
The vacuum selector `shb_vacuumPartialSelector` selects only the empty word, so its fiber of a
nonempty word is empty, while its fiber of the empty word has mass `Z`; hence
`vacuumCoordinateToggleData_isEmpty`.

All results are proved unconditionally (the emptiness results under their stated numeric
hypotheses).

## ii. Key results

- `CoordinateToggleData` : the data of a coordinate toggle
- `coordinateToggleData_isEmpty_of_left_zero_right_ne` : no data when the identity fails
- `vacuumCoordinateToggleData_isEmpty` : no data for the vacuum selector at a segment with nonzero
  numerator

## iii. Table of contents

- A. Coordinate toggle data
- B. Emptiness for the vacuum selector

## iv. References

None beyond those in the imported modules.

-/

@[expose] public section

open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false

namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

/-- Classical decidability of adjacency, used throughout this file. -/
noncomputable local instance coordinateToggleObstructionDecidableAdj
    (G : SimpleGraph V) : DecidableRel G.Adj := Classical.decRel _

namespace BackboneP2CoordinateToggleObstruction

open BackboneLabeledSwitching
open BackbonePartialP2Reindex
open BackboneP2CoordinateReindex
open FluxEdgeCopy

/-! ## A. Coordinate toggle data -/

/-- The data of a coordinate toggle at an active segment: a contributing-path selector, its source
condition, and the transport equivalence between the two pair fibers. -/
structure CoordinateToggleData
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active) where
  path : ContributingPathSelector d.graph beta J
    (S.sourceClass d (s :: ss)) (stepToggleSource S d s ss)
    (S.Fiber d (s :: ss)) (liftedResidualVacuum d s)
    (shb_ActiveSegmentFiber d s hs) (liftedResidualFiber S d s ss)
  path_sources : ∀ m hm,
    RandomCurrent.sources (endsM d.graph m) (path m hm) =
      stepToggleSource S d s ss
  transport : ∀ m hm T,
    (S.Fiber d (s :: ss) (profileFlux d.graph m T) ∧
        liftedResidualVacuum d s
          (profileFlux d.graph m (univ \ T))) <->
      (shb_ActiveSegmentFiber d s hs
          (profileFlux d.graph m (T ∆ path m hm)) ∧
        liftedResidualFiber S d s ss
          (profileFlux d.graph m (univ \ (T ∆ path m hm))))

/-- Coordinate toggle data give the active cut resummation identity. -/
lemma actualMass_active_of_data
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (R : CoordinateToggleData S beta J d s ss hs) :
    S.actualMass beta J d (s :: ss) *
        currentSum (shb_BackboneExplorationDomain.advance d s).graph
          beta J ∅ =
      shb_segmentNum beta J d s *
        S.actualMass beta J
          (shb_BackboneExplorationDomain.advance d s) ss := by
  exact actualMass_active_of_coordinateToggle S beta J d s ss hs
    R.path R.path_sources R.transport

/-- There are no coordinate toggle data when the left side of the active identity vanishes and
the right side does not. -/
lemma coordinateToggleData_isEmpty_of_left_zero_right_ne
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (hleft : S.actualMass beta J d (s :: ss) = 0)
    (hright : shb_segmentNum beta J d s *
        S.actualMass beta J
          (shb_BackboneExplorationDomain.advance d s) ss ≠ 0) :
    IsEmpty (CoordinateToggleData S beta J d s ss hs) := by
  constructor
  intro R
  have h := actualMass_active_of_data S beta J d s ss hs R
  rw [hleft, zero_mul] at h
  exact hright h.symm

/-! ## B. Emptiness for the vacuum selector -/

/-- The vacuum selector has zero actual mass on nonempty words. -/
lemma vacuumActualMass_cons_eq_zero
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) :
    shb_vacuumPartialSelector.actualMass beta J d (s :: ss) = 0 := by
  unfold shb_PartialCurrentDynamicSelector.actualMass
  rw [show (fun m : d.graph.edgeFinset -> Nat =>
      if shb_vacuumPartialSelector.Fiber d (s :: ss) m then
        weight d.graph beta J (ofEdgeFun d.graph m) else 0) =
      (fun _ => 0) by
    funext m
    rw [ite_eq_right]
    unfold shb_PartialCurrentDynamicSelector.Fiber
    by_cases hsrc : sources d.graph (ofEdgeFun d.graph m) = ∅ <;>
      simp [shb_vacuumPartialSelector, hsrc]]
  exact tsum_zero

/-- There are no coordinate toggle data for the vacuum selector at an active segment with nonzero
numerator. -/
lemma vacuumCoordinateToggleData_isEmpty
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (hs : s ∈ d.active) (hsegment : shb_segmentNum beta J d s ≠ 0) :
    IsEmpty
      (CoordinateToggleData shb_vacuumPartialSelector beta J d s [] hs) := by
  apply coordinateToggleData_isEmpty_of_left_zero_right_ne
    shb_vacuumPartialSelector beta J d s [] hs
    (vacuumActualMass_cons_eq_zero beta J d s [])
  rw [shb_PartialCurrentDynamicSelector.actualMass_nil]
  exact mul_ne_zero hsegment
    (ne_of_gt (StatMech.Ising.acr_currentSum_empty_pos
      (shb_BackboneExplorationDomain.advance d s).graph beta J))

end BackboneP2CoordinateToggleObstruction

end

end StatMech.Sharpness
