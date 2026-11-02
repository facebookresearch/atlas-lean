/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.KingSaturatedOrbitJordan
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.KingSaturatedOrbitJordan`

* `joc_kingSaturated_orbit_uniqueBoundedRegion` and `joc_cycle_uniqueBoundedRegion` on the orbit
  loop of the unit cell: exactly one bounded region (discrete Jordan curve theorem).
* `joc_domino_kingSaturated`.
* `joc_Ltromino_kingSaturated`: the L-tromino is king-saturated.
-/

@[expose] public section

open StatMech StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.KingSaturatedOrbitJordan

theorem hp : 3 ≤ dartOrbitPeriod unitCell ucBase := by rw [unitCell_orbitPeriod_eq_four]; norm_num

example : Nat.card (jcb_BoundedRegion (joc_cycleSubgraph (mpl_orbitLoop unitCell ucBase)
    (joc_kingSaturated_orbitLoop_isCycle unitCell ucBase hp joc_unitCell_kingSaturated))) = 1 :=
  joc_kingSaturated_orbit_uniqueBoundedRegion unitCell ucBase hp joc_unitCell_kingSaturated

example : Nat.card (jcb_BoundedRegion (joc_cycleSubgraph (mpl_orbitLoop unitCell ucBase)
    (joc_kingSaturated_orbitLoop_isCycle unitCell ucBase hp joc_unitCell_kingSaturated))) = 1 :=
  joc_cycle_uniqueBoundedRegion _ _

example : npm_KingSaturated domino := joc_domino_kingSaturated

example : npm_KingSaturated joc_Ltromino := joc_Ltromino_kingSaturated

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.KingSaturatedOrbitJordan
