/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.OriginCorridors

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.OriginCorridors`

* `bc59_evenLines_hasDisjointCorridors`: the even-lines configuration has three disjoint
  corridors at the origin (instance), so `bc59_corridors_give_trifurcation` gives a classical
  trifurcation after forcing.
* `bc59_arms_distinct`: the three arms `(1, 0)`, `(-1, 0)`, `(0, 1)` are distinct.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.OriginCorridors

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls

-- The even-lines configuration has disjoint corridors.
example : bc59_DisjointCorridors bc57_evenLines :=
  bc59_evenLines_hasDisjointCorridors

-- Forcing the corridors gives a classical trifurcation at the origin.
example : ∃ G : Finset (Sym2 (Site 2)),
    bc47_IsClassicalTrifurcation (forceOpenFinset G bc57_evenLines) 0 :=
  bc59_corridors_give_trifurcation _ bc59_evenLines_hasDisjointCorridors

-- The three arms are distinct.
example : bc59_a1 ≠ bc59_a2 ∧ bc59_a1 ≠ bc59_a3 ∧ bc59_a2 ≠ bc59_a3 :=
  bc59_arms_distinct

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.OriginCorridors
