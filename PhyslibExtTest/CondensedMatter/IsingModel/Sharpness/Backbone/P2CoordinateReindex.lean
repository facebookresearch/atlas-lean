/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.P2CoordinateReindex

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.P2CoordinateReindex`

* `tsum_liftedVacuum_eq_currentSum` and `tsum_liftedPredicate_eq` for `H = G` (lifting along
  `le_rfl`);
* `partialActualMass_mul_residualCurrentSum_eq_pairTsum` and
  `segmentNum_mul_partialActualMass_eq_pairTsum` (unconditional pair-sum forms);
* `actualMass_active_of_coordinateToggle` applied under its path hypotheses.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.P2CoordinateReindex

open _root_.StatMech.Sharpness _root_.StatMech.Sharpness.BackboneP2CoordinateReindex

/-- Classical decidability of adjacency, matching the library's section-local instance. -/
noncomputable local instance instDecAdjTest {W : Type*} (H : SimpleGraph W) :
    DecidableRel H.Adj :=
  Classical.decRel _

-- Lifting the vacuum predicate along `G ≤ G` recovers the partition function.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] (G : SimpleGraph V) (β : ℝ)
    (J : Sym2 V → ℝ) :=
  tsum_liftedVacuum_eq_currentSum (V := V) (le_refl G) β J

-- Lifted predicate sums agree.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V] {H G : SimpleGraph V}
    (hHG : H ≤ G) (β : ℝ) (J : Sym2 V → ℝ) (P : (H.edgeFinset → ℕ) → Prop) [DecidablePred P] :=
  tsum_liftedPredicate_eq (V := V) hHG β J P

-- The two sides of the active identity as pair sums.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (S : shb_PartialCurrentDynamicSelector (V := V)) (β : ℝ) (J : Sym2 V → ℝ)
    (d : shb_ExplorationDomain V)
    (s : shb_ExplorationSegment V) (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active) :=
  And.intro (partialActualMass_mul_residualCurrentSum_eq_pairTsum S β J d s ss)
    (segmentNum_mul_partialActualMass_eq_pairTsum S β J d s ss hs)

-- The active identity from a coordinate toggle.
example {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (S : shb_PartialCurrentDynamicSelector (V := V)) (β : ℝ) (J : Sym2 V → ℝ)
    (d : shb_ExplorationDomain V)
    (s : shb_ExplorationSegment V) (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active) :=
  actualMass_active_of_coordinateToggle S β J d s ss hs

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.Backbone.P2CoordinateReindex
