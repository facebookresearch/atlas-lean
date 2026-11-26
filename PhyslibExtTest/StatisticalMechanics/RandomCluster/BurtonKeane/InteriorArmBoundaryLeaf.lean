/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.InteriorArmBoundaryLeaf

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.InteriorArmBoundaryLeaf`

* `blf_leaf_of_interiorDeg2` on the complete graph on `Fin 3` (every degree is two), with the
  empty boundary predicate: it has no leaf (instance).
* The fourth conjunct of `blf_status`: the explicit tree `bof2_advT ⊆ bof2_advG` has a leaf of
  `bof2_advT` that is interior in `bof2_advG`.
* `blf_bc69_of_acyclicArmUnion` as a conditional statement.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.InteriorArmBoundaryLeaf

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls

-- The triangle has no leaf, since interior degree two forces leaves onto an empty boundary.
example : ∀ v : Fin 3, (⊤ : SimpleGraph (Fin 3)).degree v = 1 → False :=
  blf_leaf_of_interiorDeg2 (B := fun _ => False) fun v _ => by simp

-- The interior-leaf witness.
example : bof2_advT ≤ bof2_advG ∧ bof2_advT.IsAcyclic ∧ bof2_advG.degree 2 = 2 ∧
    bof2_advT.degree 2 = 1 :=
  ⟨blf_status.2.2.2.1, blf_status.2.2.2.2.1, blf_status.2.2.2.2.2.1, blf_status.2.2.2.2.2.2.1⟩

-- An acyclic arm union gives the global contracted forest.
example (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) (h : blf_AcyclicArmUnion ω L R) :
    bc69_Gn_globalForest ω L R :=
  blf_bc69_of_acyclicArmUnion ω L R h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.InteriorArmBoundaryLeaf
