/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















































import Mathlib
import Code.Lattice.JordanEnclosure
import Code.Lattice.PeierlsSingleCircuit
import Code.Lattice.PeierlsBoundaryConnected
import Code.Walls.pc2boundaryconn
import Code.Walls.fbcconnected

open Finset Set SimpleGraph

namespace StatMech

namespace Walls

open StatMech.Lattice
open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable








theorem ats_mem_insert_of_ne {K : Finset (Site 2)} {c x : Site 2} (hx : x ≠ c) :
    x ∈ (↑(insert c K) : Set (Site 2)) ↔ x ∈ (↑K : Set (Site 2)) := by
  simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe]
  constructor
  · rintro (rfl | h); · exact absurd rfl hx
    · exact h
  · exact fun h => Or.inr h



theorem ats_bdEdge_insert_of_notMem {K : Finset (Site 2)} {c x y : Site 2}
    (hx : x ≠ c) (hy : y ≠ c) :
    bdEdge (↑(insert c K) : Set (Site 2)) s(x, y) ↔ bdEdge (↑K : Set (Site 2)) s(x, y) := by
  rw [bdEdge_mk, bdEdge_mk, ats_mem_insert_of_ne hx, ats_mem_insert_of_ne hy]










theorem ats_adj_insert_of_shared_avoid {K : Finset (Site 2)} {c f g u v : Site 2}
    (hshared : sharedPrimalEdge f g = s(u, v)) (hu : u ≠ c) (hv : v ≠ c) :
    (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Adj f g ↔
      (faceBoundaryGraph (↑K : Set (Site 2))).Adj f g := by
  rw [faceBoundaryGraph_adj, faceBoundaryGraph_adj, hshared,
    ats_bdEdge_insert_of_notMem hu hv]








def ats_faceHasCorner (c f : Site 2) : Prop :=
  c = ![f 0, f 1] ∨ c = ![f 0 + 1, f 1] ∨ c = ![f 0 + 1, f 1 + 1] ∨ c = ![f 0, f 1 + 1]




theorem ats_sharedPrimalEdge_corners_of_f {f g : Site 2}
    (hadj : (hypercubicLattice 2).Adj f g) :
    ∃ u v : Site 2, sharedPrimalEdge f g = s(u, v) ∧
      (u = ![f 0, f 1] ∨ u = ![f 0 + 1, f 1] ∨ u = ![f 0 + 1, f 1 + 1] ∨ u = ![f 0, f 1 + 1]) ∧
      (v = ![f 0, f 1] ∨ v = ![f 0 + 1, f 1] ∨ v = ![f 0 + 1, f 1 + 1] ∨ v = ![f 0, f 1 + 1]) := by
  classical
  have hfeq : f = ![f 0, f 1] := by funext i; fin_cases i <;> rfl
  have hgeq : g = ![g 0, g 1] := by funext i; fin_cases i <;> rfl
  
  have hd := hadj
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hd
  
  by_cases h0 : f 0 = g 0
  · 
    have h1 : (f 1 - g 1).natAbs = 1 := by
      have : (f 0 - g 0).natAbs = 0 := by omega
      omega
    rcases Int.natAbs_eq_iff.mp h1 with he | he <;> simp only [Nat.cast_one] at he
    · 
      have hg : g = ![f 0, f 1 - 1] := by
        rw [hgeq]; rw [site2_eq]; exact ⟨h0.symm, by omega⟩
      subst hg
      have h := sharedPrimalEdge_bottom (f 0) (f 1)
      rw [show (![f 0, f 1] : Site 2) = f from hfeq.symm] at h
      refine ⟨_, _, h, ?_, ?_⟩
      · unfold faceCorner00; left; rfl
      · unfold faceCorner10; right; left; rfl
    · 
      have hg : g = ![f 0, f 1 + 1] := by
        rw [hgeq]; rw [site2_eq]; exact ⟨h0.symm, by omega⟩
      subst hg
      have h := sharedPrimalEdge_top (f 0) (f 1)
      rw [show (![f 0, f 1] : Site 2) = f from hfeq.symm] at h
      refine ⟨_, _, h, ?_, ?_⟩
      · unfold faceCorner01; right; right; right; rfl
      · unfold faceCorner11; right; right; left; rfl
  · 
    have hf1 : f 1 = g 1 := by
      have hb : (f 0 - g 0).natAbs ≥ 1 := by
        rcases Int.natAbs_eq (f 0 - g 0) with hh | hh <;> omega
      by_contra hne
      have : (f 1 - g 1).natAbs ≥ 1 := by
        rcases Int.natAbs_eq (f 1 - g 1) with hh | hh <;> omega
      omega
    have h0abs : (f 0 - g 0).natAbs = 1 := by
      have : (f 1 - g 1).natAbs = 0 := by omega
      omega
    rcases Int.natAbs_eq_iff.mp h0abs with he | he <;> simp only [Nat.cast_one] at he
    · 
      have hg : g = ![f 0 - 1, f 1] := by
        rw [hgeq]; rw [site2_eq]; exact ⟨by omega, hf1.symm⟩
      subst hg
      have h := sharedPrimalEdge_left (f 0) (f 1)
      rw [show (![f 0, f 1] : Site 2) = f from hfeq.symm] at h
      refine ⟨_, _, h, ?_, ?_⟩
      · unfold faceCorner00; left; rfl
      · unfold faceCorner01; right; right; right; rfl
    · 
      have hg : g = ![f 0 + 1, f 1] := by
        rw [hgeq]; rw [site2_eq]; exact ⟨by omega, hf1.symm⟩
      subst hg
      have h := sharedPrimalEdge_right (f 0) (f 1)
      rw [show (![f 0, f 1] : Site 2) = f from hfeq.symm] at h
      refine ⟨_, _, h, ?_, ?_⟩
      · unfold faceCorner10; right; left; rfl
      · unfold faceCorner11; right; right; left; rfl





theorem ats_adj_insert_iff_of_notCorner {K : Finset (Site 2)} {c f g : Site 2}
    (hadj : (hypercubicLattice 2).Adj f g) (hc : ¬ ats_faceHasCorner c f) :
    (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Adj f g ↔
      (faceBoundaryGraph (↑K : Set (Site 2))).Adj f g := by
  obtain ⟨u, v, hshared, hu, hv⟩ := ats_sharedPrimalEdge_corners_of_f hadj
  unfold ats_faceHasCorner at hc
  push Not at hc
  apply ats_adj_insert_of_shared_avoid hshared
  · rcases hu with rfl | rfl | rfl | rfl
    · exact fun h => hc.1 h.symm
    · exact fun h => hc.2.1 h.symm
    · exact fun h => hc.2.2.1 h.symm
    · exact fun h => hc.2.2.2 h.symm
  · rcases hv with rfl | rfl | rfl | rfl
    · exact fun h => hc.1 h.symm
    · exact fun h => hc.2.1 h.symm
    · exact fun h => hc.2.2.1 h.symm
    · exact fun h => hc.2.2.2 h.symm












theorem ats_walk_transfer_of_avoid {K : Finset (Site 2)} {c a b : Site 2}
    (p : (faceBoundaryGraph (↑K : Set (Site 2))).Walk a b)
    (havoid : ∀ w ∈ p.support, ¬ ats_faceHasCorner c w) :
    ∃ q : (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Walk a b,
      q.support = p.support := by
  induction p with
  | nil => exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | @cons x y z hxy q ih =>
    have hx : ¬ ats_faceHasCorner c x := havoid x (by
      rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_self)
    have htail : ∀ w ∈ q.support, ¬ ats_faceHasCorner c w := by
      intro w hw
      exact havoid w (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hw)
    obtain ⟨q', hq'⟩ := ih htail
    have hxy' : (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Adj x y :=
      (ats_adj_insert_iff_of_notCorner hxy.1 hx).mpr hxy
    refine ⟨SimpleGraph.Walk.cons hxy' q', ?_⟩
    rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_cons, hq']




theorem ats_walk_transfer_of_avoid' {K : Finset (Site 2)} {c a b : Site 2}
    (p : (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Walk a b)
    (havoid : ∀ w ∈ p.support, ¬ ats_faceHasCorner c w) :
    ∃ q : (faceBoundaryGraph (↑K : Set (Site 2))).Walk a b,
      q.support = p.support := by
  induction p with
  | nil => exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | @cons x y z hxy q ih =>
    have hx : ¬ ats_faceHasCorner c x := havoid x (by
      rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_self)
    have htail : ∀ w ∈ q.support, ¬ ats_faceHasCorner c w := by
      intro w hw
      exact havoid w (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hw)
    obtain ⟨q', hq'⟩ := ih htail
    have hxy' : (faceBoundaryGraph (↑K : Set (Site 2))).Adj x y :=
      (ats_adj_insert_iff_of_notCorner hxy.1 hx).mp hxy
    refine ⟨SimpleGraph.Walk.cons hxy' q', ?_⟩
    rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_cons, hq']




theorem ats_reachable_insert_of_avoidWalk {K : Finset (Site 2)} {c a b : Site 2}
    (p : (faceBoundaryGraph (↑K : Set (Site 2))).Walk a b)
    (havoid : ∀ w ∈ p.support, ¬ ats_faceHasCorner c w) :
    (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Reachable a b :=
  let ⟨q, _⟩ := ats_walk_transfer_of_avoid p havoid
  ⟨q⟩











theorem ats_mem_support_insert_iff_of_notCorner {K : Finset (Site 2)} {c f : Site 2}
    (hc : ¬ ats_faceHasCorner c f) :
    f ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support ↔
      f ∈ (faceBoundaryGraph (↑K : Set (Site 2))).support := by
  rw [SimpleGraph.mem_support, SimpleGraph.mem_support]
  constructor
  · rintro ⟨g, hg⟩; exact ⟨g, (ats_adj_insert_iff_of_notCorner hg.1 hc).mp hg⟩
  · rintro ⟨g, hg⟩; exact ⟨g, (ats_adj_insert_iff_of_notCorner hg.1 hc).mpr hg⟩



















def ats_AttachPatch : Prop :=
  ∀ (K : Finset (Site 2)) (c : Site 2), c ∉ K →
    IsConnectedCluster K → pc2_HoleFree (↑K : Set (Site 2)) →
    fbc_BoundaryReachable (↑K : Set (Site 2)) →
    IsConnectedCluster (insert c K) → pc2_HoleFree (↑(insert c K) : Set (Site 2)) →
    ∀ f g : Site 2,
      f ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support →
      g ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support →
      (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Reachable f g




theorem ats_attachStep_of_patch (h : ats_AttachPatch) : fbc_AttachStep := by
  intro K c hc hconn hhf hreach hconn' hhf' f g hf hg
  exact h K c hc hconn hhf hreach hconn' hhf' f g hf hg


















theorem ats_faceHasCorner_iff_mem_cornerFaces (c f : Site 2) :
    ats_faceHasCorner c f ↔ f ∈ cornerFaces c := by
  have hfeq : f = ![f 0, f 1] := by funext i; fin_cases i <;> rfl
  have hceq : c = ![c 0, c 1] := by funext i; fin_cases i <;> rfl
  unfold ats_faceHasCorner cornerFaces
  simp only [Finset.mem_insert, Finset.mem_singleton]
  conv_lhs => rw [hceq]
  
  conv_rhs => rw [hfeq]
  rw [site2_eq, site2_eq, site2_eq, site2_eq, site2_eq, site2_eq, site2_eq, site2_eq]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega






theorem ats_boundaryReachable_insert_of_anchor {K : Finset (Site 2)} {c : Site 2}
    {a₀ : Site 2}
    (hA : ∀ f : Site 2, ¬ ats_faceHasCorner c f →
        f ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support →
        ∃ p : (faceBoundaryGraph (↑K : Set (Site 2))).Walk f a₀,
          ∀ w ∈ p.support, ¬ ats_faceHasCorner c w)
    (hB : ∀ f : Site 2, ats_faceHasCorner c f →
        f ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support →
        (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Reachable f a₀) :
    fbc_BoundaryReachable (↑(insert c K) : Set (Site 2)) := by
  
  have hreach_a0 : ∀ f : Site 2,
      f ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support →
      (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Reachable f a₀ := by
    intro f hf
    by_cases hcorner : ats_faceHasCorner c f
    · exact hB f hcorner hf
    · obtain ⟨p, hp⟩ := hA f hcorner hf
      exact ats_reachable_insert_of_avoidWalk p hp
  intro f g hf hg
  exact (hreach_a0 f hf).trans (hreach_a0 g hg).symm
















noncomputable def ats_domino : Finset (Site 2) :=
  {![(0:ℤ), 0], ![(1:ℤ), 0]}


theorem ats_insert_domino_eq_tromino :
    insert (![(0:ℤ), 1] : Site 2) ats_domino = pc2_tromino := by
  unfold ats_domino pc2_tromino
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto


theorem ats_domino_isConnectedCluster : IsConnectedCluster ats_domino := by
  refine ⟨by unfold ats_domino; rw [origin_eq_zerozero]; simp, ?_⟩
  intro x hx
  have hm : (![x 0, x 1] : Site 2) ∈ (↑ats_domino : Set (Site 2)) := by
    rw [show (![x 0, x 1] : Site 2) = x from by funext i; fin_cases i <;> rfl, Finset.mem_coe]
    exact hx
  unfold ats_domino at hm
  rw [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hm
  rw [origin_eq_zerozero, show x = ![x 0, x 1] from by funext i; fin_cases i <;> rfl]
  have m00 : (![(0:ℤ), 0] : Site 2) ∈ (↑ats_domino : Set (Site 2)) := by
    unfold ats_domino; simp
  have m10 : (![(1:ℤ), 0] : Site 2) ∈ (↑ats_domino : Set (Site 2)) := by
    unfold ats_domino; simp
  rcases hm with h | h
  · rw [h]
  · rw [h]
    refine SimpleGraph.Adj.reachable ⟨?_, m00, m10⟩
    have := latAdj_right 0 0; rwa [show (0:ℤ) + 1 = 1 from by ring] at this


theorem ats_c_notMem_domino : (![(0:ℤ), 1] : Site 2) ∉ ats_domino := by
  unfold ats_domino
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rw [site2_eq, site2_eq]; omega




theorem ats_support_tromino_subset :
    (faceBoundaryGraph (↑pc2_tromino : Set (Site 2))).support ⊆ (pc2_tromFrame : Set (Site 2)) := by
  intro f hf
  have h := support_faceBoundaryGraph_subset (↑pc2_tromino : Set (Site 2)) hf
  rw [Set.mem_iUnion] at h
  obtain ⟨c, hc⟩ := h
  rw [Set.mem_iUnion] at hc
  obtain ⟨hcK, hfc⟩ := hc
  
  rw [Finset.mem_coe] at hcK
  have hcc : c = ![c 0, c 1] := by funext i; fin_cases i <;> rfl
  rw [hcc, ← Finset.mem_coe, pc2_mem_tromino] at hcK
  
  rw [Finset.mem_coe] at hfc
  unfold cornerFaces at hfc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hfc
  
  rw [Finset.mem_coe]
  unfold pc2_tromFrame
  simp only [Finset.mem_insert, Finset.mem_singleton]
  have hff : f = ![f 0, f 1] := by funext i; fin_cases i <;> rfl
  
  rcases hcK with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    (rcases hfc with hfe | hfe | hfe | hfe <;>
      (rw [hfe];
       rw [site2_eq, site2_eq, site2_eq, site2_eq, site2_eq, site2_eq, site2_eq, site2_eq];
       omega))






theorem ats_tromino_boundaryReachable :
    fbc_BoundaryReachable (↑pc2_tromino : Set (Site 2)) :=
  fbc_boundaryReachable_of_faceBoundaryConnected ats_support_tromino_subset
    pc2_tromino_faceBoundaryConnected







theorem ats_attachStep_witness_tromino :
    (![(0:ℤ), 1] : Site 2) ∉ ats_domino ∧
      IsConnectedCluster ats_domino ∧
      insert (![(0:ℤ), 1] : Site 2) ats_domino = pc2_tromino ∧
      IsConnectedCluster pc2_tromino ∧
      fbc_BoundaryReachable (↑pc2_tromino : Set (Site 2)) :=
  ⟨ats_c_notMem_domino, ats_domino_isConnectedCluster, ats_insert_domino_eq_tromino,
    pc2_tromino_isConnectedCluster, ats_tromino_boundaryReachable⟩

















































end Walls

end StatMech
