/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.HalfPlaneTopologyClosure

/-!
# Tests for `Sheffield.HalfPlaneTopologyClosure`

Module under test: `Sheffield.HalfPlaneTopologyClosure` in
`PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar`.

* `PeriodicPlanarDualPair.threeCrossingCageEvent_disjoint_boundaryBandHasInfiniteCluster` for an
  arbitrary dual pair with arc bound `1` and the explicit cage `r = 0`, `A = 1`, `R = 20`,
  `C = 0`, `Tbottom = 20`, `c = 21`, `d = 22`, `Ttop = 23`, `D0 = 40` (all margins satisfied).
* `PeriodicPlanarDualPair.threeCrossingCageEvent` is an event at those parameters.
* `PeriodicPlanarDualPair.finiteJoinedBoundaryArmEvent_disjoint_boundaryBand_of_subset_cage`
  elaborates (check-only).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
namespace HalfPlaneTopologyClosure

open _root_.StatMech _root_.StatMech.FK.PeriodicPlanar

variable {V W : Type*} [DecidableEq V] [DecidableEq W] [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

-- The cage event at explicit parameters.
example (D : PeriodicPlanarDualPair P Pdual) : Set (ConfigSpace (Sym2 V)) :=
  PeriodicPlanarDualPair.threeCrossingCageEvent D 1 0 20 0 40 1 20 23

-- The cage excludes a dual infinite cluster in the boundary band `[21, 22]`.
example (D : PeriodicPlanarDualPair P Pdual)
    (hBp : ∀ {u v : V} (huv : P.graph.Adj u v) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc huv t - D.primalEmbedding.vertex u) i| ≤ 1)
    (hBd : ∀ {u v : W} (huv : Pdual.graph.Adj u v) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc huv t - D.dualEmbedding.vertex u) i| ≤ 1) :=
  PeriodicPlanarDualPair.threeCrossingCageEvent_disjoint_boundaryBandHasInfiniteCluster D
    (r := 0) (R := 20) (C := 0) (D0 := 40) (A := 1) (Tbottom := 20) (Ttop := 23) (c := 21)
    (d := 22) one_pos hBp hBd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

open PeriodicPlanarDualPair in
example := @finiteJoinedBoundaryArmEvent_disjoint_boundaryBand_of_subset_cage

end HalfPlaneTopologyClosure
end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
