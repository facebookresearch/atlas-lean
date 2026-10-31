/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GnSpanningTreeRay

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GnSpanningTreeRay`

* The first conjunct of `bsg_status`: the contracted graph `bgn_Gn` of the upper-lines
  configuration is a subgraph of `ℤ²` (instance).
* `bsg_GnTreeRay_reaches_boundary` as a conditional statement.
* The fifth conjunct: arm-subforest data bound the coarse count (conditional form).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GnSpanningTreeRay

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls

-- The contracted graph is a subgraph of the lattice.
example : bgn_Gn bc60_upperLines 3 ≤ hypercubicLattice 2 :=
  bsg_status.1 _ 3

-- A tree ray in an infinite component reaches the boundary.
example (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (T : SimpleGraph (Site 2)) [T.LocallyFinite]
    (hT : T ≤ bgn_Gn ω L) {w : Site 2} (hw : w ∈ box 2 2)
    (hinf : (ray34_AvoidCluster T ∅ w).Infinite) :
    ∃ r : ℕ → Site 2, r 0 = w ∧ Function.Injective r ∧
      (∀ k, T.Adj (r k) (r (k + 1))) ∧ (∃ k, r k ∈ vertexBoundary 2 2) :=
  bsg_GnTreeRay_reaches_boundary ω L T hT (by norm_num) hw hinf

-- Arm-subforest data bound the coarse count.
example (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) (h : bau_ArmSubforestData ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R :=
  bsg_status.2.2.2.2.1 ω L R h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GnSpanningTreeRay
