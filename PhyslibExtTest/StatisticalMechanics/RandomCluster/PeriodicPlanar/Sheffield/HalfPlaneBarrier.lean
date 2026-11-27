/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.HalfPlaneBarrier

/-!
# Tests for `Sheffield.HalfPlaneBarrier`

Module under test: `Sheffield.HalfPlaneBarrier` in
`PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar`.

* `ContinuousHalfPlaneBarrier.joined_boundary_arms_intersect_transverse_path` on the explicit
  strip `0 < x < 1`, `0 < y < 1`, for arbitrary paths meeting its hypotheses.
* `PeriodicPlanarDualPair.no_open_dual_transverse_walk_of_joined_primal_arms` elaborates
  (check-only; its hypotheses need a concrete dual pair).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
namespace HalfPlaneBarrier

open _root_.StatMech _root_.StatMech.FK.PeriodicPlanar

variable {V W : Type*} [DecidableEq V] [DecidableEq W] [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

-- The continuum barrier on the unit strip.
example {lo hi j gl gr : Fin 2 → ℝ} (lower : Path lo j) (upper : Path hi j)
    (gamma : Path gl gr) (hgl : gl 0 < 0) (hgr : 1 < gr 0) (hlo : lo 1 < 0) (hhi : 1 < hi 1)
    (hlowerX : ∀ t : unitInterval, 0 < lower t 0 ∧ lower t 0 < 1)
    (hupperX : ∀ t : unitInterval, 0 < upper t 0 ∧ upper t 0 < 1)
    (hgammaY : ∀ t : unitInterval, 0 < gamma t 1 ∧ gamma t 1 < 1) :
    (Set.range gamma ∩ (Set.range lower ∪ Set.range upper)).Nonempty :=
  ContinuousHalfPlaneBarrier.joined_boundary_arms_intersect_transverse_path zero_lt_one
    zero_lt_one lower upper gamma hgl hgr hlo hhi hlowerX hupperX hgammaY

open PeriodicPlanarDualPair in
example := @no_open_dual_transverse_walk_of_joined_primal_arms

end HalfPlaneBarrier
end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
