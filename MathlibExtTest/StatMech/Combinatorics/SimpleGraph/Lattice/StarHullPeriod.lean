/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.StarHullPeriod

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.StarHullPeriod`

* `shp_period_ge_three` at the unit cell and the domino, and the concrete instances.
* The face loop of every boundary orbit of a box is a cycle (`shp_box_orbit_isCycle`, at `n = 1`).
-/

@[expose] public section

open StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.StarHullPeriod

example : 3 ≤ dartOrbitPeriod unitCell ucBase :=
  shp_period_ge_three unitCell unitCell_finite ucBase

example : 3 ≤ dartOrbitPeriod domino dmBase := shp_domino_period_ge_three

example (a : {e : Dart // IsBoundaryDart (box 2 1) e}) :
    ((dartOrbitFaceWalk (box 2 1) a.1 a.2 (dartOrbitPeriod (box 2 1) a)).copy rfl
      (by rw [orbit_iterate_period_eq (box 2 1) a])).IsCycle :=
  shp_box_orbit_isCycle 1 a

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.StarHullPeriod
