/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










































































import Mathlib
import Code.Lattice.ContourCountInjection
import Code.Lattice.PlanarTopology

open Finset Set SimpleGraph

namespace StatMech

namespace Lattice

open StatMech.Ising (crosses crosses_mk crossEdges contourLen connClusterFamily bondFinsetTouch
  ConnectedContourCount origin IsConnectedCluster pcc_mem_connClusterFamily
  clusterFamily_subset_box clusterFamily mem_boxFinset origin_mem_box)

attribute [local instance] Classical.propDecidable








section Engine

variable {V : Type*} (G : SimpleGraph V) [DecidableEq V] [SimpleGraph.LocallyFinite G]



noncomputable def walkEdgeSets (B : Finset V) (ℓ : ℕ) : Finset (Finset (Sym2 V)) :=
  (B.sigma (fun v => G.finsetWalkLength ℓ v v)).image (fun p => p.2.edges.toFinset)





theorem card_walkEdgeSets_le {D : ℕ} (hD : ∀ v, G.degree v ≤ D) (B : Finset V) (ℓ : ℕ) :
    (walkEdgeSets G B ℓ).card ≤ B.card * D ^ ℓ :=
  le_trans Finset.card_image_le (card_circuits_based_in_le G hD B ℓ)

end Engine

variable {d : ℕ}




theorem card_walkEdgeSets_le_pow (B : Finset (Site d)) (ℓ : ℕ) :
    (walkEdgeSets (hypercubicLattice d) B ℓ).card ≤ B.card * (2 * d) ^ ℓ :=
  card_walkEdgeSets_le (hypercubicLattice d) (degree_le d) B ℓ


















def ContourWalkRealisation (d n ℓ : ℕ) : Prop :=
  ∃ anchors : Finset (Site d), anchors.card ≤ ℓ ∧
    realisedContours d n ℓ ⊆ walkEdgeSets (hypercubicLattice d) anchors ℓ




theorem realisedContours_card_le_of_walkRealisation {n ℓ : ℕ}
    (h : ContourWalkRealisation d n ℓ) :
    (realisedContours d n ℓ).card ≤ ℓ * (2 * d) ^ ℓ := by
  obtain ⟨anchors, hcard, hsub⟩ := h
  calc (realisedContours d n ℓ).card
      ≤ (walkEdgeSets (hypercubicLattice d) anchors ℓ).card := Finset.card_le_card hsub
    _ ≤ anchors.card * (2 * d) ^ ℓ := card_walkEdgeSets_le_pow anchors ℓ
    _ ≤ ℓ * (2 * d) ^ ℓ := Nat.mul_le_mul_right _ hcard



theorem contourSubsetCountBound_of_walkRealisation {n ℓ : ℕ}
    (h : ContourWalkRealisation d n ℓ) : ContourSubsetCountBound d n ℓ :=
  realisedContours_card_le_of_walkRealisation h






theorem connectedContourCount_of_walkRealisation {n : ℕ}
    (h : ∀ ℓ, ContourWalkRealisation d n ℓ) :
    ConnectedContourCount d n := by
  intro ℓ
  have hnat : ((connClusterFamily (d := d) n).filter
      (fun K : Finset (Site d) => contourLen (↑K) (bondFinsetTouch d n) = ℓ)).card
      ≤ ℓ * (2 * d) ^ ℓ :=
    connFamily_fixedLen_card_le_peierls n ℓ (contourSubsetCountBound_of_walkRealisation (h ℓ))
  calc (((connClusterFamily (d := d) n).filter
          (fun (K : Finset (Site d)) =>
            contourLen (↑K) (bondFinsetTouch d n) = ℓ)).card : ℝ)
      ≤ ((ℓ * (2 * d) ^ ℓ : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ := by push_cast; ring












theorem contourLen_pos_of_nonempty (hd : 1 ≤ d) {n : ℕ} {K : Finset (Site d)}
    (hKbox : (↑K : Set (Site d)) ⊆ box d n) (hne : K.Nonempty) :
    0 < contourLen (↑K : Set (Site d)) (bondFinsetTouch d n) := by
  classical
  set c : Fin d := ⟨0, hd⟩ with hc
  
  obtain ⟨v, hvK, hvmax⟩ := Finset.exists_max_image K (fun x => x c) hne
  
  set w : Site d := fun i => if i = c then v i + 1 else v i with hw
  have hadj : (hypercubicLattice d).Adj v w := by
    rw [hypercubicLattice_adj, Finset.sum_eq_single c]
    · simp [hw]
    · intro i _ hic; simp [hw, hic]
    · intro h; exact absurd (Finset.mem_univ c) h
  have hwc : w c = v c + 1 := by simp [hw]
  
  have hwnotin : w ∉ (↑K : Set (Site d)) := by
    intro hwin
    have := hvmax w (by exact_mod_cast hwin)
    rw [hwc] at this; omega
  
  have hsmem : s(v, w) ∈ bondFinsetTouch d n :=
    mk_mem_bondFinsetTouch hadj (Or.inl (hKbox (by exact_mod_cast hvK)))
  have hcross : crosses (↑K : Set (Site d)) s(v, w) := by
    rw [crosses_mk]; exact ⟨fun _ => hwnotin, fun _ => by exact_mod_cast hvK⟩
  have hmem : s(v, w) ∈ crossEdges (↑K : Set (Site d)) (bondFinsetTouch d n) := by
    unfold StatMech.Ising.crossEdges; rw [Finset.mem_filter]; exact ⟨hsmem, hcross⟩
  rw [StatMech.Ising.contourLen]
  exact Finset.card_pos.mpr ⟨_, hmem⟩




theorem realisedContours_zero_eq_empty (hd : 1 ≤ d) (n : ℕ) :
    realisedContours d n 0 = ∅ := by
  classical
  unfold realisedContours
  rw [Finset.image_eq_empty, Finset.filter_eq_empty_iff]
  intro K hK hlen
  
  rw [pcc_mem_connClusterFamily] at hK
  have hbox : (↑K : Set (Site d)) ⊆ box d n := clusterFamily_subset_box hK.1
  have hne : K.Nonempty := ⟨origin d, hK.2.1⟩
  have hpos := contourLen_pos_of_nonempty hd hbox hne
  omega



theorem contourWalkRealisation_zero (hd : 1 ≤ d) (n : ℕ) :
    ContourWalkRealisation d n 0 := by
  refine ⟨∅, by simp, ?_⟩
  rw [realisedContours_zero_eq_empty hd n]
  exact Finset.empty_subset _



theorem connectedContourCount_zero (hd : 1 ≤ d) (n : ℕ) :
    (((connClusterFamily (d := d) n).filter
        (fun (K : Finset (Site d)) => contourLen (↑K) (bondFinsetTouch d n) = 0)).card : ℝ)
      ≤ (0 : ℝ) * (2 * d : ℝ) ^ 0 := by
  have h0 := realisedContours_card_le_of_walkRealisation (contourWalkRealisation_zero hd n)
  rw [← connFamily_fixedLen_card_eq_realised] at h0
  calc (((connClusterFamily (d := d) n).filter
          (fun (K : Finset (Site d)) =>
            contourLen (↑K) (bondFinsetTouch d n) = 0)).card : ℝ)
      ≤ ((0 * (2 * d) ^ 0 : ℕ) : ℝ) := by exact_mod_cast h0
    _ = (0 : ℝ) * (2 * d : ℝ) ^ 0 := by push_cast; ring










theorem contourWalkRealisation_of_empty {n ℓ : ℕ} (hempty : realisedContours d n ℓ = ∅) :
    ContourWalkRealisation d n ℓ := by
  refine ⟨∅, by simp, ?_⟩
  rw [hempty]; exact Finset.empty_subset _







theorem singleton_origin_mem_realisedContours (n : ℕ) :
    crossEdges (↑({origin d} : Finset (Site d)) : Set (Site d)) (bondFinsetTouch d n)
      ∈ realisedContours d n
          (contourLen (↑({origin d} : Finset (Site d)) : Set (Site d)) (bondFinsetTouch d n)) := by
  classical
  unfold realisedContours
  rw [Finset.mem_image]
  refine ⟨{origin d}, ?_, rfl⟩
  rw [Finset.mem_filter]
  refine ⟨?_, rfl⟩
  
  rw [pcc_mem_connClusterFamily]
  refine ⟨?_, singleton_origin_isConnectedCluster⟩
  rw [clusterFamily, Finset.mem_powerset]
  intro x hx
  rw [Finset.mem_singleton] at hx; subst hx
  rw [mem_boxFinset]; exact origin_mem_box n

end Lattice

end StatMech
