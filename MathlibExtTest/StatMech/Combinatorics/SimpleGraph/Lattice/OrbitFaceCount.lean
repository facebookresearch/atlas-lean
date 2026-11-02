/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitFaceCount
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitFaceCount`

* `gbe_singleton_totalTurn_eq_four` for the site `(2, -1)`.
* `gbe_starHull_orbitFaces_card_eq_period` for every orbit of the star hull of the unit cell.
-/

@[expose] public section

open StatMech StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.OrbitFaceCount

example (a : {e : Dart // IsBoundaryDart ({![2, -1]} : Set (Site 2)) e}) :
    totalTurnZ ({![2, -1]} : Set (Site 2)) a.1 (dartOrbitPeriod ({![2, -1]} : Set (Site 2)) a)
      = 4 ∨ totalTurnZ ({![2, -1]} : Set (Site 2)) a.1
        (dartOrbitPeriod ({![2, -1]} : Set (Site 2)) a) = -4 :=
  gbe_singleton_totalTurn_eq_four _ a

example (a : {e : Dart // IsBoundaryDart (ndt_StarHull unitCell) e}) :
    (usc_orbitFaces (ndt_StarHull unitCell) a).card = dartOrbitPeriod (ndt_StarHull unitCell) a :=
  gbe_starHull_orbitFaces_card_eq_period unitCell a

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.OrbitFaceCount
