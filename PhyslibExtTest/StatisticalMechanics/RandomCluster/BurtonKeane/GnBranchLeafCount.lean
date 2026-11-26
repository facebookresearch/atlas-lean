/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GnBranchLeafCount

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GnBranchLeafCount`

* The last conjunct of `bc80_status`: the origin is a coarse trifurcation of `bc60_upperLines`
  for `L = 3` (instance).
* `bc80_branch_le_leaf` and `bc80_GnTrifCount_le_boundary` as conditional statements on a fibre
  spanning forest without isolated vertices.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GnBranchLeafCount

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls

-- The origin is a coarse trifurcation of the upper-lines configuration.
example : bc61_IsCoarseTrifurcation bc60_upperLines 3 (0 : Site 2) :=
  bc80_status.2.2.2 le_rfl

open Classical in
-- Branch vertices are at most leaves.
example (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) (c : Fin 2 → Fin (2 * L + 1))
    (S : Set (Site 2)) [Fintype (↑S : Type)] [Nonempty (↑S : Type)]
    (hmin : ∀ v : (↑S : Type), 1 ≤ (bc75_spanForest ω L R c S).degree v) :
    (bc80_branchFinset ω L R c S).card ≤ (bc80_leafFinset ω L R c S).card :=
  bc80_branch_le_leaf ω L R c S hmin

open Classical in
-- With leaves injected into the boundary, the fibre count is at most the boundary size.
example (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) (c : Fin 2 → Fin (2 * L + 1))
    (S : Set (Site 2)) [Fintype (↑S : Type)] [Nonempty (↑S : Type)]
    (hmin : ∀ v : (↑S : Type), 1 ≤ (bc75_spanForest ω L R c S).degree v)
    (hleaf : bc80_LeafBoundaryInj ω L R c S) :
    bc80_GnTrifCount ω L R c S ≤ boxSV_boundaryCard 2 R :=
  bc80_GnTrifCount_le_boundary ω L R c S hmin hleaf

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GnBranchLeafCount
