/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.AcyclicArmSubforest
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TreeCutVertex

/-!
# The arm subforest datum gives the count

The arm subforest datum bounds the coarse count by the boundary, and its separation field follows
from the spanning tree.

## i. Overview

The arm subforest datum `bau_ArmSubforestData` gives
`bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R`. In a connected graph `H` with spanning tree `T`,
three neighbours of `x` separated in `H` without `x` are separated in `T` without `x`, so the
separation field of the datum follows from the others.

## ii. Key results

- `bca_datum_implies_count` : the coarse count from the datum.
- `bca_fieldD_free` : the separation field follows from the spanning tree.

## iii. Table of contents

- A. The datum and the count

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
-/

@[expose] public section

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

/-! ## A. The datum and the count -/

lemma bca_datum_implies_count (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ)
    (h : bau_ArmSubforestData ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R :=
  bc69_count_via_leafBound ω L R (bau_bc69_of_subforestData ω L R h)

lemma bca_fieldD_free {V : Type*} [Fintype V] {H T : SimpleGraph V} [DecidableRel T.Adj]
    (hTH : T ≤ H) (hTconn : T.Connected) {x a₁ a₂ a₃ : V}
    (hne₁ : a₁ ≠ x) (hne₂ : a₂ ≠ x) (hne₃ : a₃ ≠ x)
    (hsep₁₂ : ¬ (bkg_deleteVertex H x).Reachable a₁ a₂)
    (hsep₁₃ : ¬ (bkg_deleteVertex H x).Reachable a₁ a₃)
    (hsep₂₃ : ¬ (bkg_deleteVertex H x).Reachable a₂ a₃) :
    3 ≤ T.degree x :=
  bcv_trif_degree_ge_three hTH hTconn hne₁ hne₂ hne₃ hsep₁₂ hsep₁₃ hsep₂₃

lemma bca_status :
    (∀ (p : ℝ≥0) (hp1 : p ≤ 1), 0 < p →
      (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R) →
      bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ),
      bau_ArmSubforestData ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R) ∧
    (∀ {V : Type} {H : SimpleGraph V}, H.Connected → ∃ T : SimpleGraph V, T ≤ H ∧ T.IsTree) ∧
    (∀ {V : Type} {T G : SimpleGraph V}, T.IsTree → G ≤ T → G.IsAcyclic) ∧
    (bau_star.IsTree ∧ bau_star.IsAcyclic ∧ bau_star.degree 0 = 3) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p hp1 hp0 hdata; exact StatMech.Walls.bau_bk_of_subforestData p hp1 hp0 hdata
  · intro ω L R h; exact bca_datum_implies_count ω L R h
  · intro V H hH; exact SimpleGraph.Connected.exists_isTree_le hH
  · intro V T G hT hle; exact StatMech.Walls.bau_isAcyclic_of_le_tree hT hle
  · exact ⟨StatMech.Walls.bau_star_witness.1, StatMech.Walls.bau_star_witness.2.1,
      StatMech.Walls.bau_star_witness.2.2.1⟩

end StatMech.Walls
