/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.StarHullWinding

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.StarHullWinding`

* The named predicate `shw_MinVertStepLeft` holds for the unit cell.
* `shw_windingWitness_of_minLeft` is instantiated at the unit cell, with the cycle hypothesis
  proved from `shw_unitCell_faceInj` and the period `4`.
* `shw_starHull_mpl_isCycle` for boundary orbits of the star hull of the unit cell.
-/

@[expose] public section

open StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.StarHullWinding

example : shw_MinVertStepLeft unitCell ucBase := shw_unitCell_minVertStepLeft

/-- The face loop of the unit cell is a cycle. -/
theorem unitCell_loop_isCycle : (mpl_orbitLoop unitCell ucBase).IsCycle :=
  mpl_orbitLoop_isCycle unitCell ucBase (by rw [unitCell_orbitPeriod_eq_four]; norm_num)
    shw_unitCell_faceInj

example : wei_WindingWitness unitCell ucBase :=
  shw_windingWitness_of_minLeft unitCell ucBase unitCell_loop_isCycle shw_unitCell_minVertStepLeft

example (a : {e : Dart // IsBoundaryDart (ndt_StarHull unitCell) e})
    (hp : 3 ≤ dartOrbitPeriod (ndt_StarHull unitCell) a) :
    (mpl_orbitLoop (ndt_StarHull unitCell) a).IsCycle :=
  shw_starHull_mpl_isCycle unitCell a hp

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.StarHullWinding
