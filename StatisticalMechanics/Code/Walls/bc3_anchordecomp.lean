/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/















































































import Mathlib
import Code.Walls.bc2_core

open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths

namespace StatMech

namespace Walls

variable {d : ℕ}







def bc3_anchorSites (G : Finset (Sym2 (Site d))) : Set (Site d) :=
  {a | ∃ e ∈ G, a ∈ e}

@[simp] lemma bc3_mem_anchorSites {G : Finset (Sym2 (Site d))} {a : Site d} :
    a ∈ bc3_anchorSites G ↔ ∃ e ∈ G, a ∈ e := Iff.rfl



theorem bc3_anchorSites_finite (G : Finset (Sym2 (Site d))) : (bc3_anchorSites G).Finite := by
  have hsub : bc3_anchorSites G ⊆ ⋃ e ∈ G, {a | a ∈ e} := by
    intro a ha; obtain ⟨e, he, hae⟩ := ha; exact Set.mem_biUnion he hae
  refine Set.Finite.subset (Set.Finite.biUnion G.finite_toSet ?_) hsub
  intro e _
  induction e with
  | h p q =>
    refine Set.Finite.subset ((Set.finite_singleton q).insert p) ?_
    intro a ha
    simp only [Set.mem_setOf_eq, Sym2.mem_iff] at ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; exact ha
















theorem bc3_anchor_decomp (G : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d)))
    (x z : Site d) (h : Connected d (forceOpenFinset G ω) x z) :
    Connected d ω x z ∨ ∃ a ∈ bc3_anchorSites G, Connected d ω a z := by
  unfold Connected at h
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact Or.inl connected_rfl
  | @tail b c hxb hbc ih =>
    rcases adj_forceOpenFinset_cases G ω hbc with hadj | hF
    · 
      rcases ih with hxb' | ⟨a, ha, hab⟩
      · exact Or.inl (hxb'.trans (SimpleGraph.Adj.reachable (G := openSubgraph d ω) hadj))
      · exact Or.inr ⟨a, ha, hab.trans (SimpleGraph.Adj.reachable (G := openSubgraph d ω) hadj)⟩
    · 
      exact Or.inr ⟨c, ⟨s(b, c), hF, Sym2.mem_mk_right b c⟩, connected_rfl⟩












theorem bc3_cluster_covered_by_anchors (G : Finset (Sym2 (Site d)))
    (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    cluster d (forceOpenFinset G ω) x ⊆
      ⋃ a ∈ insert x (bc3_anchorSites G), cluster d ω a := by
  intro z hz
  rw [mem_cluster] at hz
  rcases bc3_anchor_decomp G ω x z hz with hconn | ⟨a, ha, haz⟩
  · exact Set.mem_biUnion (Set.mem_insert x _) (by rw [mem_cluster]; exact hconn)
  · exact Set.mem_biUnion (Set.mem_insert_of_mem x ha) (by rw [mem_cluster]; exact haz)



theorem bc3_anchor_cover_index_finite (G : Finset (Sym2 (Site d))) (x : Site d) :
    (insert x (bc3_anchorSites G)).Finite := (bc3_anchorSites_finite G).insert x









noncomputable def bc3_corridorUnion (j₁ j₂ j₃ : Fin d) (L₁ L₂ L₃ : ℕ) :
    Finset (Sym2 (Site d)) :=
  hrHD_corridorEdges j₁ (L₁ + 1) ∪ hrHD_corridorEdges j₂ (L₂ + 1) ∪
    hrHD_corridorEdges j₃ (L₃ + 1)




theorem bc3_corridorUnion_eq_pairwiseSeparated_wiring (ω : ConfigSpace (Sym2 (Site d)))
    (j₁ j₂ j₃ : Fin d) (L₁ L₂ L₃ : ℕ) :
    bc2_PairwiseSeparated ω j₁ j₂ j₃ L₁ L₂ L₃ ↔
      (¬ Connected d (removeSite 0 (forceOpenFinset (bc3_corridorUnion j₁ j₂ j₃ L₁ L₂ L₃) ω))
          (hrHD_rayPt j₁ 1) (hrHD_rayPt j₂ 1) ∧
       ¬ Connected d (removeSite 0 (forceOpenFinset (bc3_corridorUnion j₁ j₂ j₃ L₁ L₂ L₃) ω))
          (hrHD_rayPt j₁ 1) (hrHD_rayPt j₃ 1) ∧
       ¬ Connected d (removeSite 0 (forceOpenFinset (bc3_corridorUnion j₁ j₂ j₃ L₁ L₂ L₃) ω))
          (hrHD_rayPt j₂ 1) (hrHD_rayPt j₃ 1)) := Iff.rfl





theorem bc3_anchor_decomp_corridor (j₁ j₂ j₃ : Fin d) (L₁ L₂ L₃ : ℕ)
    (ω : ConfigSpace (Sym2 (Site d))) (x z : Site d)
    (h : Connected d (forceOpenFinset (bc3_corridorUnion j₁ j₂ j₃ L₁ L₂ L₃) ω) x z) :
    Connected d ω x z ∨
      ∃ a ∈ bc3_anchorSites (bc3_corridorUnion j₁ j₂ j₃ L₁ L₂ L₃), Connected d ω a z :=
  bc3_anchor_decomp _ ω x z h










theorem bc3_origin_mem_anchorSites_corridor (j : Fin d) (L : ℕ) :
    (0 : Site d) ∈ bc3_anchorSites (hrHD_corridorEdges j (L + 1)) := by
  refine ⟨s(hrHD_rayPt j (0 : ℤ), hrHD_rayPt j ((0 : ℤ) + 1)),
    hrHD_mem_corridorEdges (Nat.succ_pos L), ?_⟩
  have h0 : hrHD_rayPt j (0 : ℤ) = (0 : Site d) := by simp [hrHD_rayPt]
  rw [← h0]; exact Sym2.mem_mk_left _ _



theorem bc3_rayPt_mem_anchorSites_corridor (j : Fin d) (L t : ℕ) (ht : t < L) :
    hrHD_rayPt j ((t : ℤ) + 1) ∈ bc3_anchorSites (hrHD_corridorEdges j L) :=
  ⟨_, hrHD_mem_corridorEdges ht, Sym2.mem_mk_right _ _⟩




theorem bc3_anchorSites_corridorUnion_nonempty (j₁ j₂ j₃ : Fin d) (L₁ L₂ L₃ : ℕ) :
    (bc3_anchorSites (bc3_corridorUnion j₁ j₂ j₃ L₁ L₂ L₃)).Nonempty := by
  refine ⟨0, ?_⟩
  obtain ⟨e, he, h0e⟩ := bc3_origin_mem_anchorSites_corridor j₁ L₁
  exact ⟨e, by
    rw [bc3_corridorUnion]
    exact (Finset.subset_union_left.trans Finset.subset_union_left) he, h0e⟩

end Walls

end StatMech
