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
import Code.Walls.atsattachsurgery
import Code.Walls.arrreroute

open Finset Set SimpleGraph

namespace StatMech

namespace Walls

open StatMech.Lattice
open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable








def cyc_BoundaryCycle (K : Set (Site 2)) : Prop :=
  fbc_BoundaryReachable K ∧
    ∀ f : Site 2, f ∈ (faceBoundaryGraph K).support → (faceBoundaryGraph K).degree f = 2


theorem cyc_connected {K : Set (Site 2)} (h : cyc_BoundaryCycle K) : fbc_BoundaryReachable K :=
  h.1


theorem cyc_degreeTwo {K : Set (Site 2)} (h : cyc_BoundaryCycle K)
    {f : Site 2} (hf : f ∈ (faceBoundaryGraph K).support) :
    (faceBoundaryGraph K).degree f = 2 :=
  h.2 f hf




theorem cyc_boundaryCycle_imp_reachable {K : Set (Site 2)} (h : cyc_BoundaryCycle K) :
    fbc_BoundaryReachable K :=
  h.1











theorem cyc_degree_pos_of_support {K : Set (Site 2)} {f : Site 2}
    (hf : f ∈ (faceBoundaryGraph K).support) :
    0 < (faceBoundaryGraph K).degree f := by
  classical
  obtain ⟨g, hg⟩ := hf
  rw [SimpleGraph.degree, Finset.card_pos]
  exact ⟨g, by rw [SimpleGraph.mem_neighborFinset]; exact hg⟩



theorem cyc_degree_ge_two_of_support {K : Set (Site 2)} {f : Site 2}
    (hf : f ∈ (faceBoundaryGraph K).support) :
    2 ≤ (faceBoundaryGraph K).degree f := by
  have heven := degree_faceBoundaryGraph_even K f
  have hpos := cyc_degree_pos_of_support hf
  rcases heven with ⟨k, hk⟩
  omega




theorem cyc_degree_two_iff_le_two {K : Set (Site 2)} {f : Site 2}
    (hf : f ∈ (faceBoundaryGraph K).support) :
    (faceBoundaryGraph K).degree f = 2 ↔ (faceBoundaryGraph K).degree f ≤ 2 := by
  have hge := cyc_degree_ge_two_of_support hf
  omega












def cyc_NoPinch (K : Set (Site 2)) : Prop :=
  ∀ f : Site 2, f ∈ (faceBoundaryGraph K).support → (faceBoundaryGraph K).degree f ≤ 2



theorem cyc_boundaryCycle_of_noPinch {K : Set (Site 2)}
    (hreach : fbc_BoundaryReachable K) (hnp : cyc_NoPinch K) :
    cyc_BoundaryCycle K := by
  refine ⟨hreach, fun f hf => ?_⟩
  rw [cyc_degree_two_iff_le_two hf]
  exact hnp f hf









theorem cyc_singleton_face00_degree_two :
    (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).degree ![(0:ℤ), 0] = 2 := by
  rw [show (![(0:ℤ), 0] : Site 2) = ![(0:ℤ), (0:ℤ)] from rfl, degree_faceBoundaryGraph]
  unfold faceBoundaryDegree bdInd faceCorner00 faceCorner10 faceCorner11 faceCorner01
  simp only [mem_singletonOrigin]
  norm_num












noncomputable def cyc_pinch : Finset (Site 2) := {![(0:ℤ), 0], ![(1:ℤ), 1]}




theorem cyc_pinch_face_degree_four :
    (faceBoundaryGraph (↑cyc_pinch : Set (Site 2))).degree ![(0:ℤ), 0] = 4 := by
  rw [show (![(0:ℤ), 0] : Site 2) = ![(0:ℤ), (0:ℤ)] from rfl, degree_faceBoundaryGraph]
  unfold faceBoundaryDegree bdInd faceCorner00 faceCorner10 faceCorner11 faceCorner01 cyc_pinch
  have h00 : (![(0:ℤ), 0] : Site 2) ∈ (↑({![(0:ℤ), 0], ![(1:ℤ), 1]} : Finset (Site 2))
      : Set (Site 2)) := by simp
  have h11 : (![(1:ℤ), 1] : Site 2) ∈ (↑({![(0:ℤ), 0], ![(1:ℤ), 1]} : Finset (Site 2))
      : Set (Site 2)) := by simp
  have h10 : (![(1:ℤ), 0] : Site 2) ∉ (↑({![(0:ℤ), 0], ![(1:ℤ), 1]} : Finset (Site 2))
      : Set (Site 2)) := by
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [site2_eq, site2_eq]; omega
  have h01 : (![(0:ℤ), 1] : Site 2) ∉ (↑({![(0:ℤ), 0], ![(1:ℤ), 1]} : Finset (Site 2))
      : Set (Site 2)) := by
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [site2_eq, site2_eq]; omega
  simp only [show ((0:ℤ) + 1) = 1 from by ring]
  rw [if_pos (by tauto), if_pos (by tauto), if_pos (by tauto), if_pos (by tauto)]



theorem cyc_pinch_not_boundaryCycle :
    ¬ cyc_BoundaryCycle (↑cyc_pinch : Set (Site 2)) := by
  intro h
  
  have hd4 := cyc_pinch_face_degree_four
  have hsupp : (![(0:ℤ), 0] : Site 2) ∈ (faceBoundaryGraph (↑cyc_pinch : Set (Site 2))).support := by
    have hpos : 0 < (faceBoundaryGraph (↑cyc_pinch : Set (Site 2))).degree ![(0:ℤ), 0] := by
      rw [hd4]; norm_num
    obtain ⟨g, hg⟩ := SimpleGraph.degree_pos_iff_nonempty.mp hpos
    exact ⟨g, hg⟩
  have hd2 := cyc_degreeTwo h hsupp
  rw [hd4] at hd2
  norm_num at hd2

















theorem cyc_mem_support_iff_neighbor_nonempty {K : Set (Site 2)} {f : Site 2} :
    f ∈ (faceBoundaryGraph K).support ↔ ((faceBoundaryGraph K).neighborSet f).Nonempty := by
  constructor
  · rintro ⟨g, hg⟩; exact ⟨g, hg⟩
  · rintro ⟨g, hg⟩; exact ⟨g, hg⟩



theorem cyc_neighborSet_ncard_of_degree_two {K : Set (Site 2)} {f : Site 2}
    (h : (faceBoundaryGraph K).degree f = 2) :
    ((faceBoundaryGraph K).neighborSet f).ncard = 2 := by
  classical
  have hbridge : ((faceBoundaryGraph K).neighborSet f).ncard
      = (faceBoundaryGraph K).degree f := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card,
      SimpleGraph.card_neighborSet_eq_degree]
  rw [hbridge, h]




theorem cyc_isCycles_of_boundaryCycle {K : Set (Site 2)} (h : cyc_BoundaryCycle K) :
    (faceBoundaryGraph K).IsCycles := by
  intro v hv
  have hsupp : v ∈ (faceBoundaryGraph K).support :=
    cyc_mem_support_iff_neighbor_nonempty.mpr hv
  exact cyc_neighborSet_ncard_of_degree_two (cyc_degreeTwo h hsupp)


theorem cyc_degree_two_of_isCycles {K : Set (Site 2)} (h : (faceBoundaryGraph K).IsCycles)
    {f : Site 2} (hf : f ∈ (faceBoundaryGraph K).support) :
    (faceBoundaryGraph K).degree f = 2 := by
  classical
  have hne := cyc_mem_support_iff_neighbor_nonempty.mp hf
  have hnc : ((faceBoundaryGraph K).neighborSet f).ncard = 2 := h hne
  have hbridge : ((faceBoundaryGraph K).neighborSet f).ncard
      = (faceBoundaryGraph K).degree f := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card,
      SimpleGraph.card_neighborSet_eq_degree]
  rw [← hbridge, hnc]


theorem cyc_boundaryCycle_of_isCycles {K : Set (Site 2)}
    (hreach : fbc_BoundaryReachable K) (hcyc : (faceBoundaryGraph K).IsCycles) :
    cyc_BoundaryCycle K :=
  ⟨hreach, fun _f hf => cyc_degree_two_of_isCycles hcyc hf⟩




















theorem cyc_reachable_deleteEdge {K : Finset (Site 2)} {v w : Site 2}
    (hadj : (faceBoundaryGraph (↑K : Set (Site 2))).Adj v w) :
    ((faceBoundaryGraph (↑K : Set (Site 2))).deleteEdges {s(v, w)}).Reachable v w := by
  classical
  set G := faceBoundaryGraph (↑K : Set (Site 2)) with hG
  
  obtain ⟨T, hsupp⟩ :=
    exists_finset_support_faceBoundaryGraph (↑K : Set (Site 2)) (K : Set (Site 2)).toFinite
  rw [← hG] at hsupp
  set H := G.induce (T : Set (Site 2)) with hH
  haveI : Fintype (T : Set (Site 2)) := FinsetCoe.fintype T
  haveI : DecidableRel H.Adj := Classical.decRel _
  have hvT : v ∈ (T : Set (Site 2)) := hsupp hadj.mem_support_left
  have hwT : w ∈ (T : Set (Site 2)) := hsupp hadj.mem_support_right
  
  have hdegH : ∀ x : (T : Set (Site 2)), H.degree x = G.degree (x : Site 2) := by
    intro x
    rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
    refine Fintype.card_congr ?_
    refine ⟨fun y => ⟨(y.1 : Site 2), y.2⟩,
      fun y => ⟨⟨y.1, hsupp y.2.symm.mem_support_left⟩, y.2⟩, ?_, ?_⟩
    · intro y; ext; rfl
    · intro y; ext; rfl
  have hHeven : ∀ x : (T : Set (Site 2)), Even (H.degree x) := by
    intro x; rw [hdegH x]; exact degree_faceBoundaryGraph_even _ _
  have hadjH : H.Adj ⟨v, hvT⟩ ⟨w, hwT⟩ := hadj
  
  have hrH := EvenDegree.reachable_deleteEdges_of_even H hHeven hadjH
  
  obtain ⟨p⟩ := hrH
  let emb : H ↪g G := SimpleGraph.Embedding.induce (T : Set (Site 2))
  
  let φ : (H.deleteEdges {s((⟨v, hvT⟩ : (T : Set (Site 2))), ⟨w, hwT⟩)})
      →g (G.deleteEdges {s(v, w)}) := by
    refine ⟨fun x => (x : Site 2), ?_⟩
    intro a b hab
    rw [SimpleGraph.deleteEdges_adj] at hab ⊢
    refine ⟨emb.toHom.map_adj hab.1, ?_⟩
    intro hmem
    apply hab.2
    rw [Set.mem_singleton_iff] at hmem ⊢
    rw [Sym2.eq_iff] at hmem ⊢
    rcases hmem with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · left; exact ⟨Subtype.ext ha, Subtype.ext hb⟩
    · right; exact ⟨Subtype.ext ha, Subtype.ext hb⟩
  exact ⟨p.map φ⟩




















def cyc_AttachPreservesCycle : Prop :=
  ∀ (K : Finset (Site 2)) (c : Site 2), c ∉ K →
    IsConnectedCluster K → pc2_HoleFree (↑K : Set (Site 2)) →
    cyc_BoundaryCycle (↑K : Set (Site 2)) →
    IsConnectedCluster (insert c K) → pc2_HoleFree (↑(insert c K) : Set (Site 2)) →
    cyc_BoundaryCycle (↑(insert c K) : Set (Site 2))





theorem cyc_attachReachable_of_preserves (hpres : cyc_AttachPreservesCycle)
    (K : Finset (Site 2)) (c : Site 2) (hc : c ∉ K)
    (hconn : IsConnectedCluster K) (hhf : pc2_HoleFree (↑K : Set (Site 2)))
    (hcyc : cyc_BoundaryCycle (↑K : Set (Site 2)))
    (hconn' : IsConnectedCluster (insert c K))
    (hhf' : pc2_HoleFree (↑(insert c K) : Set (Site 2))) :
    fbc_BoundaryReachable (↑(insert c K) : Set (Site 2)) :=
  cyc_boundaryCycle_imp_reachable
    (hpres K c hc hconn hhf hcyc hconn' hhf')












theorem cyc_boundaryCycle_singleton :
    cyc_BoundaryCycle (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) := by
  refine ⟨fbc_boundaryReachable_singleton, fun f hf => ?_⟩
  
  have hf4 := support_singletonOrigin_subset hf
  rw [Finset.mem_coe] at hf4
  
  have hfeq : f = ![f 0, f 1] := by funext i; fin_cases i <;> rfl
  rw [hfeq, degree_faceBoundaryGraph]
  
  rcases singletonBoundarySupport_cases hf4 with rfl | rfl | rfl | rfl <;>
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    unfold faceBoundaryDegree bdInd faceCorner00 faceCorner10 faceCorner11 faceCorner01
    simp only [mem_singletonOrigin]
    norm_num




theorem cyc_boundaryCycle_of_inputs (hpres : cyc_AttachPreservesCycle) (hrem : fbc_HasRemovableCell)
    (K : Finset (Site 2)) (hconn : IsConnectedCluster K) (hhf : pc2_HoleFree (↑K : Set (Site 2))) :
    cyc_BoundaryCycle (↑K : Set (Site 2)) := by
  induction hn : K.card using Nat.strong_induction_on generalizing K with
  | _ n ih =>
    subst hn
    have hne : K.Nonempty := ⟨origin 2, hconn.1⟩
    have hpos : 1 ≤ K.card := Finset.card_pos.mpr hne
    rcases Nat.lt_or_ge K.card 2 with h1 | h2
    · have hc1 : K.card = 1 := by omega
      rw [fbc_card_one_eq_singleton hconn hc1]
      exact cyc_boundaryCycle_singleton
    · obtain ⟨c, hcK, _hcorigin, hconn', hhf'⟩ := hrem K h2 hconn hhf
      have hcard' : (K.erase c).card < K.card := by
        rw [Finset.card_erase_of_mem hcK]; omega
      have hcyc' : cyc_BoundaryCycle (↑(K.erase c) : Set (Site 2)) :=
        ih (K.erase c).card hcard' (K.erase c) hconn' hhf' rfl
      have hins : insert c (K.erase c) = K := Finset.insert_erase hcK
      have hcnotin : c ∉ K.erase c := Finset.notMem_erase c K
      have := hpres (K.erase c) c hcnotin hconn' hhf' hcyc'
        (by rw [hins]; exact hconn) (by rw [hins]; exact hhf)
      rwa [hins] at this







theorem cyc_boundaryConnResidue_of_inputs
    (hpres : cyc_AttachPreservesCycle) (hrem : fbc_HasRemovableCell) :
    fbc_BoundaryConnResidue :=
  fun K hconn hhf => cyc_boundaryCycle_imp_reachable
    (cyc_boundaryCycle_of_inputs hpres hrem K hconn hhf)





















theorem cyc_attachPreservesCycle_of_reachable_noPinch
    (hI : ∀ (K : Finset (Site 2)) (c : Site 2), c ∉ K →
        IsConnectedCluster K → pc2_HoleFree (↑K : Set (Site 2)) →
        cyc_BoundaryCycle (↑K : Set (Site 2)) →
        IsConnectedCluster (insert c K) → pc2_HoleFree (↑(insert c K) : Set (Site 2)) →
        fbc_BoundaryReachable (↑(insert c K) : Set (Site 2)))
    (hII : ∀ (K : Finset (Site 2)) (c : Site 2), c ∉ K →
        IsConnectedCluster K → pc2_HoleFree (↑K : Set (Site 2)) →
        cyc_BoundaryCycle (↑K : Set (Site 2)) →
        IsConnectedCluster (insert c K) → pc2_HoleFree (↑(insert c K) : Set (Site 2)) →
        cyc_NoPinch (↑(insert c K) : Set (Site 2))) :
    cyc_AttachPreservesCycle := by
  intro K c hc hconn hhf hcyc hconn' hhf'
  exact cyc_boundaryCycle_of_noPinch
    (hI K c hc hconn hhf hcyc hconn' hhf')
    (hII K c hc hconn hhf hcyc hconn' hhf')








theorem cyc_reachable_of_arr {K : Finset (Site 2)} {c a₀ : Site 2}
    (hR : arr_ReRoute K c a₀) (hH : arr_Hook K c) :
    fbc_BoundaryReachable (↑(insert c K) : Set (Site 2)) :=
  arr_boundaryReachable_of_reroute_hook hR hH








theorem cyc_reachable_of_arcReachable {K : Finset (Site 2)} {c a₀ : Site 2}
    (ha₀ : a₀ ∈ arr_offPatchSet c)
    (harc : ∀ (f : Site 2) (hfc : f ∈ arr_offPatchSet c),
        f ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support →
        ((faceBoundaryGraph (↑K : Set (Site 2))).induce (arr_offPatchSet c)).Reachable
          ⟨f, hfc⟩ ⟨a₀, ha₀⟩)
    (hH : arr_Hook K c) :
    fbc_BoundaryReachable (↑(insert c K) : Set (Site 2)) :=
  arr_boundaryReachable_of_reroute_hook (arr_reRoute_of_induceReachable ha₀ harc) hH





















end Walls

end StatMech
