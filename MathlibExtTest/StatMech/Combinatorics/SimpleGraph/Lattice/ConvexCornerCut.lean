/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.ConvexCornerCut

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.ConvexCornerCut`

* `cutWitness` is king-saturated, and the counterexample
  `sht_kingSat_singleCycle_convex_corner_can_disconnect` is restated.
* The star hull of the unit cell is nonempty.
-/

@[expose] public section

open StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.ConvexCornerCut

example : npm_KingSaturated cutWitness := sht_cutWitness_kingSaturated

example : ∃ (K : Set (Site 2)) (c : Site 2),
    K.Finite ∧ K.Nonempty ∧ npm_KingSaturated K ∧ IsExtremeCell K c ∧
      turnZ K (leftDart c) = -1 ∧ ¬ CellConnected (K \ {c}) :=
  sht_kingSat_singleCycle_convex_corner_can_disconnect

example : (ndt_StarHull unitCell).Nonempty :=
  sht_starHull_nonempty unitCell (Set.singleton_nonempty _)

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.ConvexCornerCut
