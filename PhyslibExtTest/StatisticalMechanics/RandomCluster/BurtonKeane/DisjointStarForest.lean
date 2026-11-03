/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.DisjointStarForest

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.DisjointStarForest`

In the plane:
* `bfc_status`: the star forest over `Bool` is acyclic, and `bc112_SeparatedArmGraph` holds for the
  all-closed configuration at `L = 3`;
* `bfc_disjointStar_leaves_interior` at `R = 2`;
* `bfc_acyclic_of_walkInjHom` with the identity homomorphism of the explicit star `bc64_starG`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.DisjointStarForest

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls MeasureTheory
open scoped NNReal

/-- The all-closed configuration of the planar lattice. -/
def closed2 : ConfigSpace (Sym2 (Site 2)) := fun _ => false

-- The star forest is acyclic, and the separated arm graph exists at `L = 3`.
example : (bc64_starForest Bool).IsAcyclic ∧ bc112_SeparatedArmGraph closed2 3 5 :=
  ⟨(bfc_status (d := 2) (by norm_num)).1 Bool,
    (bfc_status (d := 2) (by norm_num)).2.1 closed2 3 5 le_rfl⟩

-- The disjoint-star leaf next to the origin is interior to the radius-2 box.
example : bc112_leaf (d := 2) (by norm_num) (0 : Site 2) 1 ∉ vertexBoundary 2 2 :=
  bfc_disjointStar_leaves_interior (by norm_num) le_rfl

-- Acyclicity transfers along the identity homomorphism.
example : bc64_starG.IsAcyclic :=
  bfc_acyclic_of_walkInjHom (SimpleGraph.Hom.id) bc64_starG_isTree.isAcyclic
    fun _ _ => Function.injective_id.injOn

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.DisjointStarForest
