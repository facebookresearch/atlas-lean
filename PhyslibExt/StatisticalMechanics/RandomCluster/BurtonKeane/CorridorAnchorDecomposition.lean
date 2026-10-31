/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Set.Finite.Lattice
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForcedCorridorRouting

/-!
# Anchor decomposition of forced connections

A connection after forcing a finite edge set either exists already or passes through an endpoint of
a forced edge, so forced clusters are covered by finitely many original clusters.

## i. Overview

`anchorSites G` is the set of endpoints of edges of `G`; it is finite. A connection in
`forceOpenFinset G ω` is either a connection in `ω` or reaches an anchor, so the forced cluster of
`x` is covered by the clusters of `x` and of the anchors. `bc3_corridorUnion` is the union of three
axis corridors; pairwise separation of their mouths is a statement about the forced union. The
origin and the corridor cells are anchors.

## ii. Key results

- `StatMech.Percolation.anchor_decomp` (in `BurtonKeaneMerge`) : the anchor decomposition of forced
  connections.
- `bc3_cluster_covered_by_anchors` : forced clusters are covered by finitely many clusters.

## iii. Table of contents

- A. Anchors
- B. Three corridors

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths

namespace StatMech

namespace Walls

variable {d : ℕ}

/-! ## A. Anchors -/

@[simp] lemma bc3_mem_anchorSites {G : Finset (Sym2 (Site d))} {a : Site d} :
    a ∈ Percolation.anchorSites G ↔ ∃ e ∈ G, a ∈ e := Iff.rfl

lemma bc3_cluster_covered_by_anchors (G : Finset (Sym2 (Site d)))
    (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    cluster d (forceOpenFinset G ω) x ⊆
      ⋃ a ∈ insert x (Percolation.anchorSites G), cluster d ω a := by
  intro z hz
  rw [mem_cluster] at hz
  rcases Percolation.anchor_decomp G ω x z hz with hconn | ⟨a, ha, haz⟩
  · exact Set.mem_biUnion (Set.mem_insert x _) (by rw [mem_cluster]; exact hconn)
  · exact Set.mem_biUnion (Set.mem_insert_of_mem x ha) (by rw [mem_cluster]; exact haz)

lemma bc3_anchor_cover_index_finite (G : Finset (Sym2 (Site d))) (x : Site d) :
    (insert x (Percolation.anchorSites G)).Finite := (Percolation.anchorSites_finite G).insert x

/-! ## B. Three corridors -/

/-- The union of the three axis corridors along `j₁`, `j₂`, `j₃` with lengths `L₁ + 1`, `L₂ + 1`,
`L₃ + 1`. -/
noncomputable def bc3_corridorUnion (j₁ j₂ j₃ : Fin d) (L₁ L₂ L₃ : ℕ) :
    Finset (Sym2 (Site d)) :=
  hrHD_corridorEdges j₁ (L₁ + 1) ∪ hrHD_corridorEdges j₂ (L₂ + 1) ∪
    hrHD_corridorEdges j₃ (L₃ + 1)

lemma bc3_corridorUnion_eq_pairwiseSeparated_wiring (ω : ConfigSpace (Sym2 (Site d)))
    (j₁ j₂ j₃ : Fin d) (L₁ L₂ L₃ : ℕ) :
    bc2_PairwiseSeparated ω j₁ j₂ j₃ L₁ L₂ L₃ ↔
      (¬ Connected d (removeSite 0 (forceOpenFinset (bc3_corridorUnion j₁ j₂ j₃ L₁ L₂ L₃) ω))
          (hrHD_rayPt j₁ 1) (hrHD_rayPt j₂ 1) ∧
       ¬ Connected d (removeSite 0 (forceOpenFinset (bc3_corridorUnion j₁ j₂ j₃ L₁ L₂ L₃) ω))
          (hrHD_rayPt j₁ 1) (hrHD_rayPt j₃ 1) ∧
       ¬ Connected d (removeSite 0 (forceOpenFinset (bc3_corridorUnion j₁ j₂ j₃ L₁ L₂ L₃) ω))
          (hrHD_rayPt j₂ 1) (hrHD_rayPt j₃ 1)) := Iff.rfl

lemma bc3_anchor_decomp_corridor (j₁ j₂ j₃ : Fin d) (L₁ L₂ L₃ : ℕ)
    (ω : ConfigSpace (Sym2 (Site d))) (x z : Site d)
    (h : Connected d (forceOpenFinset (bc3_corridorUnion j₁ j₂ j₃ L₁ L₂ L₃) ω) x z) :
    Connected d ω x z ∨
      ∃ a ∈ Percolation.anchorSites (bc3_corridorUnion j₁ j₂ j₃ L₁ L₂ L₃), Connected d ω a z :=
  Percolation.anchor_decomp _ ω x z h

lemma bc3_origin_mem_anchorSites_corridor (j : Fin d) (L : ℕ) :
    (0 : Site d) ∈ Percolation.anchorSites (hrHD_corridorEdges j (L + 1)) := by
  refine ⟨s(hrHD_rayPt j (0 : ℤ), hrHD_rayPt j ((0 : ℤ) + 1)),
    hrHD_mem_corridorEdges (Nat.succ_pos L), ?_⟩
  have h0 : hrHD_rayPt j (0 : ℤ) = (0 : Site d) := by simp [hrHD_rayPt]
  rw [← h0]; exact Sym2.mem_mk_left _ _

lemma bc3_rayPt_mem_anchorSites_corridor (j : Fin d) (L t : ℕ) (ht : t < L) :
    hrHD_rayPt j ((t : ℤ) + 1) ∈ Percolation.anchorSites (hrHD_corridorEdges j L) :=
  ⟨_, hrHD_mem_corridorEdges ht, Sym2.mem_mk_right _ _⟩

lemma bc3_anchorSites_corridorUnion_nonempty (j₁ j₂ j₃ : Fin d) (L₁ L₂ L₃ : ℕ) :
    (Percolation.anchorSites (bc3_corridorUnion j₁ j₂ j₃ L₁ L₂ L₃)).Nonempty := by
  refine ⟨0, ?_⟩
  obtain ⟨e, he, h0e⟩ := bc3_origin_mem_anchorSites_corridor j₁ L₁
  exact ⟨e, by
    rw [bc3_corridorUnion]
    exact (Finset.subset_union_left.trans Finset.subset_union_left) he, h0e⟩

end Walls

end StatMech
