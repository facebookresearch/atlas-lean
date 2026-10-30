/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.FineArmTreeLeaf
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.FieldFreeDatum
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SpanningTreeLeafCount

/-!
# Branch vertices of a forest

In a finite forest of minimum degree one, the vertices of degree at least three are at most the
leaves, and so at most any set of sites the leaves inject into.

## i. Overview

`bfk_forestCount` bounds the number of vertices of degree at least three in a finite acyclic graph
of minimum degree one by the size of any index set into which the leaves inject. A star checks it.

## ii. Key results

- `bfk_forestCount` : the branch count of a finite forest.

## iii. Table of contents

- A. The branch count

## iv. References

- D. König, *Theorie der endlichen und unendlichen Graphen*, Leipzig (1936).
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

variable {d : ℕ}

/-! ## A. The branch count -/

lemma bfk_forestCount {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hacyc : G.IsAcyclic) (hmin : ∀ v, 1 ≤ G.degree v)
    {ι : Type*} [Fintype ι] (f : ι → V) (hf : Function.Injective f)
    (hdeg3 : ∀ i, 3 ≤ G.degree (f i))
    (B : Finset V) (hleaf : ∀ v, G.degree v = 1 → v ∈ B) :
    Fintype.card ι ≤ B.card := by
  classical
  have hbranch : Finset.univ.image f ⊆ Finset.univ.filter (fun v => 3 ≤ G.degree v) := by
    intro v hv
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hv
    obtain ⟨i, rfl⟩ := hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hdeg3 i
  calc Fintype.card ι = (Finset.univ.image f).card := by
          rw [Finset.card_image_of_injective _ hf, Finset.card_univ]
    _ ≤ (Finset.univ.filter (fun v => 3 ≤ G.degree v)).card := Finset.card_le_card hbranch
    _ ≤ (Finset.univ.filter (fun v => G.degree v = 1)).card :=
        StatMech.Walls.bc65_connected_leaf_count G hacyc hmin
    _ ≤ B.card := by
          apply Finset.card_le_card
          intro v hv
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
          exact hleaf v hv

lemma bfk_star_count_witness :
    Fintype.card (Fin 1) ≤ ({1, 2, 3} : Finset (Fin 4)).card := by
  refine bfk_forestCount bau_star bau_star_witness.1.isAcyclic ?_
    (fun _ => (0 : Fin 4)) ?_ ?_ {1, 2, 3} ?_
  · decide
  · intro a b _; exact Subsingleton.elim a b
  · intro i; exact (by decide : (3 : ℕ) ≤ bau_star.degree 0)
  · decide

lemma bfk_forestCount_status :
    (∀ {V : Type} [Fintype V] [Nonempty V] {G : SimpleGraph V} [_i : DecidableRel G.Adj],
      G.IsAcyclic → (∀ v, 1 ≤ G.degree v) →
      (Finset.univ.filter (fun v => 3 ≤ G.degree v)).card
        ≤ (Finset.univ.filter (fun v => G.degree v = 1)).card) ∧
    (∀ {V : Type} [Fintype V] [Nonempty V] {G : SimpleGraph V} [_i : DecidableRel G.Adj],
      G.IsAcyclic → (∀ v, 1 ≤ G.degree v) →
      ∀ {ι : Type} [Fintype ι] (f : ι → V), Function.Injective f → (∀ i, 3 ≤ G.degree (f i)) →
      ∀ (B : Finset V), (∀ v, G.degree v = 1 → v ∈ B) → Fintype.card ι ≤ B.card) ∧
    (∀ {V : Type} {T : SimpleGraph V}, T.IsTree → ∀ {ι : Type} (Gs : ι → SimpleGraph V),
      (∀ i, Gs i ≤ T) → (⨆ i, Gs i).IsAcyclic) ∧
    (Fintype.card (Fin 1) ≤ ({1, 2, 3} : Finset (Fin 4)).card) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (R : ℕ),
      bau_ArmSubforestData ω 0 R → bc61_coarseTcount ω 0 R ≤ boxSV_boundaryCard 2 R) ∧
    (∀ (p : ℝ≥0) (hp1 : p ≤ 1), 0 < p →
      (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R) →
      bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro V _ _ G _ hacyc hmin; exact StatMech.Walls.bc65_connected_leaf_count G hacyc hmin
  · intro V _ _ G _ hacyc hmin ι _ f hf hdeg3 B hleaf
    exact bfk_forestCount G hacyc hmin f hf hdeg3 B hleaf
  · intro V T hT ι Gs hle; exact StatMech.Walls.bfl_armUnion_acyclic hT Gs hle
  · exact bfk_star_count_witness
  · intro ω R h; exact StatMech.Walls.bfl_fineCount_of_armSubforest ω R h
  · intro p hp1 hp0 hdata; exact StatMech.Walls.bau_bk_of_subforestData p hp1 hp0 hdata

end StatMech.Walls
