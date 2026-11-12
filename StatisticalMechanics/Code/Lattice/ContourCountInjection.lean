/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














































import Mathlib
import Code.Lattice.ClusterBoundaryRecovery
import Code.Lattice.ClusterContourBijection

open Finset Set SimpleGraph

namespace StatMech

namespace Lattice

open StatMech.Ising (latticeOn IsConnectedCluster origin crosses crosses_mk crossEdges
  contourLen connClusterFamily pcc_mem_connClusterFamily clusterFamily_subset_box
  bondFinsetTouch adj_of_mem_bondFinsetTouch bondPairsTouch boxFinset mem_boxFinset)

attribute [local instance] Classical.propDecidable

variable {d : ℕ}





theorem crosses_iff_edgeStraddles (K : Set (Site d)) (e : Sym2 (Site d)) :
    crosses K e ↔ edgeStraddles K e := by
  induction e with
  | h x y => rw [crosses_mk, edgeStraddles_mk]




theorem mem_crossEdges_iff_mem_boundaryEdgeSet (K : Set (Site d)) (B : Finset (Sym2 (Site d)))
    (hB : ∀ e ∈ B, e ∈ (hypercubicLattice d).edgeSet) (e : Sym2 (Site d)) :
    e ∈ crossEdges K B ↔ (e ∈ B ∧ e ∈ boundaryEdgeSet K) := by
  unfold StatMech.Ising.crossEdges
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨heB, hcr⟩
    refine ⟨heB, ⟨hB e heB, ?_⟩⟩
    exact (crosses_iff_edgeStraddles K e).mp hcr
  · rintro ⟨heB, _, hstr⟩
    exact ⟨heB, (crosses_iff_edgeStraddles K e).mpr hstr⟩









theorem mk_mem_bondFinsetTouch {n : ℕ} {x y : Site d}
    (hadj : (hypercubicLattice d).Adj x y) (htouch : x ∈ box d n ∨ y ∈ box d n) :
    s(x, y) ∈ bondFinsetTouch d n := by
  rw [StatMech.Ising.bondFinsetTouch, Finset.mem_image]
  refine ⟨(x, y), ?_, rfl⟩
  rw [StatMech.Ising.bondPairsTouch, Finset.mem_filter, Finset.mem_product]
  refine ⟨⟨?_, ?_⟩, hadj, htouch⟩
  · rw [mem_boxFinset]
    rcases htouch with h | h
    · exact box_subset_succ d n h
    · exact ccb_adj_mem_box_succ hadj.symm h
  · rw [mem_boxFinset]
    rcases htouch with h | h
    · exact ccb_adj_mem_box_succ hadj h
    · exact box_subset_succ d n h




theorem boundaryEdgeSet_subset_bondFinsetTouch {K : Set (Site d)} {n : ℕ}
    (hKbox : K ⊆ box d n) {e : Sym2 (Site d)} (he : e ∈ boundaryEdgeSet K) :
    e ∈ bondFinsetTouch d n := by
  obtain ⟨hedge, hstr⟩ := he
  induction e with
  | h x y =>
    rw [SimpleGraph.mem_edgeSet] at hedge
    rw [edgeStraddles_mk] at hstr
    
    refine mk_mem_bondFinsetTouch hedge ?_
    by_cases hx : x ∈ K
    · exact Or.inl (hKbox hx)
    · have hy : y ∈ K := by
        by_contra hyK; exact hx (hstr.mpr hyK)
      exact Or.inr (hKbox hy)





theorem bondFinsetTouch_subset_edgeSet (n : ℕ) :
    ∀ e ∈ bondFinsetTouch d n, e ∈ (hypercubicLattice d).edgeSet := by
  intro e he
  induction e with
  | h x y =>
    rw [SimpleGraph.mem_edgeSet]
    exact adj_of_mem_bondFinsetTouch (n := n) he






theorem coe_crossEdges_eq_boundaryEdgeSet {K : Set (Site d)} {n : ℕ} (hKbox : K ⊆ box d n) :
    (↑(crossEdges K (bondFinsetTouch d n)) : Set (Sym2 (Site d))) = boundaryEdgeSet K := by
  ext e
  rw [Finset.mem_coe,
    mem_crossEdges_iff_mem_boundaryEdgeSet K (bondFinsetTouch d n)
      (bondFinsetTouch_subset_edgeSet n) e]
  constructor
  · rintro ⟨_, hmem⟩; exact hmem
  · intro hmem
    exact ⟨boundaryEdgeSet_subset_bondFinsetTouch hKbox hmem, hmem⟩



theorem boundaryEdgeSet_eq_of_crossEdges_eq {K₁ K₂ : Set (Site d)} {n : ℕ}
    (h1 : K₁ ⊆ box d n) (h2 : K₂ ⊆ box d n)
    (h : crossEdges K₁ (bondFinsetTouch d n) = crossEdges K₂ (bondFinsetTouch d n)) :
    boundaryEdgeSet K₁ = boundaryEdgeSet K₂ := by
  rw [← coe_crossEdges_eq_boundaryEdgeSet h1, ← coe_crossEdges_eq_boundaryEdgeSet h2, h]












theorem connBoxCluster_crossEdges_injOn {n : ℕ} :
    Set.InjOn (fun K : Finset (Site d) => crossEdges (↑K : Set (Site d)) (bondFinsetTouch d n))
      (connClusterFamily (d := d) n : Set (Finset (Site d))) := by
  intro K₁ hK₁ K₂ hK₂ h
  rw [Finset.mem_coe, pcc_mem_connClusterFamily] at hK₁ hK₂
  have hbox1 : (↑K₁ : Set (Site d)) ⊆ box d n := clusterFamily_subset_box hK₁.1
  have hbox2 : (↑K₂ : Set (Site d)) ⊆ box d n := clusterFamily_subset_box hK₂.1
  have hbe : boundaryEdgeSet (↑K₁ : Set (Site d)) = boundaryEdgeSet (↑K₂ : Set (Site d)) :=
    boundaryEdgeSet_eq_of_crossEdges_eq hbox1 hbox2 h
  exact connCluster_eq_of_boundaryEdgeSet_eq hK₁.2 hK₂.2 hbe











theorem crossEdges_subset_bondFinsetTouch (K : Set (Site d)) (n : ℕ) :
    crossEdges K (bondFinsetTouch d n) ⊆ bondFinsetTouch d n :=
  Finset.filter_subset _ _






theorem connClusterFamily_card_le_powerset (n : ℕ) :
    (connClusterFamily (d := d) n).card ≤ (bondFinsetTouch d n).powerset.card := by
  classical
  refine Finset.card_le_card_of_injOn
    (fun K : Finset (Site d) => crossEdges (↑K : Set (Site d)) (bondFinsetTouch d n)) ?_ ?_
  · intro K _hK
    rw [Finset.mem_coe, Finset.mem_powerset]
    exact crossEdges_subset_bondFinsetTouch (↑K : Set (Site d)) n
  · exact connBoxCluster_crossEdges_injOn








theorem connFamily_fixedLen_card_le_subsets (n ℓ : ℕ) :
    ((connClusterFamily (d := d) n).filter
        (fun K : Finset (Site d) => contourLen (↑K) (bondFinsetTouch d n) = ℓ)).card
      ≤ ((bondFinsetTouch d n).powerset.filter (fun E => E.card = ℓ)).card := by
  classical
  refine Finset.card_le_card_of_injOn
    (fun K : Finset (Site d) => crossEdges (↑K : Set (Site d)) (bondFinsetTouch d n)) ?_ ?_
  · intro K hK
    rw [Finset.mem_coe, Finset.mem_filter] at hK
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨crossEdges_subset_bondFinsetTouch (↑K : Set (Site d)) n, ?_⟩
    
    have := hK.2
    rwa [StatMech.Ising.contourLen] at this
  · 
    refine (connBoxCluster_crossEdges_injOn (n := n)).mono ?_
    intro K hK
    rw [Finset.mem_coe, Finset.mem_filter] at hK
    exact Finset.mem_coe.mpr hK.1


















noncomputable def realisedContours (d n ℓ : ℕ) : Finset (Finset (Sym2 (Site d))) :=
  ((connClusterFamily (d := d) n).filter
      (fun K : Finset (Site d) => contourLen (↑K) (bondFinsetTouch d n) = ℓ)).image
    (fun K : Finset (Site d) => crossEdges (↑K : Set (Site d)) (bondFinsetTouch d n))












def ContourSubsetCountBound (d n ℓ : ℕ) : Prop :=
  (realisedContours d n ℓ).card ≤ ℓ * (2 * d) ^ ℓ





theorem connFamily_fixedLen_card_eq_realised (n ℓ : ℕ) :
    ((connClusterFamily (d := d) n).filter
        (fun K : Finset (Site d) => contourLen (↑K) (bondFinsetTouch d n) = ℓ)).card
      = (realisedContours d n ℓ).card := by
  classical
  unfold realisedContours
  rw [Finset.card_image_of_injOn]
  
  refine (connBoxCluster_crossEdges_injOn (n := n)).mono ?_
  intro K hK
  rw [Finset.mem_coe, Finset.mem_filter] at hK
  exact Finset.mem_coe.mpr hK.1











theorem connFamily_fixedLen_card_le_peierls (n ℓ : ℕ) (h : ContourSubsetCountBound d n ℓ) :
    ((connClusterFamily (d := d) n).filter
        (fun K : Finset (Site d) => contourLen (↑K) (bondFinsetTouch d n) = ℓ)).card
      ≤ ℓ * (2 * d) ^ ℓ := by
  rw [connFamily_fixedLen_card_eq_realised]
  exact h








theorem singleton_origin_isConnectedCluster :
    IsConnectedCluster ({origin d} : Finset (Site d)) := by
  refine ⟨Finset.mem_singleton_self _, ?_⟩
  intro x hx
  rw [Finset.mem_singleton] at hx
  subst hx
  exact SimpleGraph.Reachable.refl _

end Lattice

end StatMech
