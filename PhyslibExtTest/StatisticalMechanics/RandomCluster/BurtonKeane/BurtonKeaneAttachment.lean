/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BurtonKeaneAttachment

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BurtonKeaneAttachment`

* `bka_three_independent_axis_neighbours` for the three axes of `ℤ³`;
* `bka_corridor_refl` with the empty corridor;
* `bka_residue_iff_corridorConfinement` and `bka_disjointRouting_of_mergeFree` in conditional
  form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.BurtonKeaneAttachment

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation
open _root_.StatMech.Percolation.DisjointPaths

-- The three unit vectors of `ℤ³` are distinct neighbours of the origin.
example := bka_three_independent_axis_neighbours (d := 3) (j₁ := 0) (j₂ := 1) (j₃ := 2)
  (by decide) (by decide) (by decide)

-- A site reaches itself through the empty corridor.
example : Relation.ReflTransGen (CorridorStep (∅ : Finset (Sym2 (Site 2)))) 0 0 :=
  bka_corridor_refl ∅ 0

-- The distinct-clusters residue is corridor confinement.
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (h : bka_CorridorConfinement ω) :
    bcc_distinct_clusters_residue ω :=
  (bka_residue_iff_corridorConfinement ω).mpr h

-- Merge freedom gives disjoint corridor routing.
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (h : bka_MergeFree ω) :
    DisjointCorridorRouting ω :=
  bka_disjointRouting_of_mergeFree ω h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.BurtonKeaneAttachment
