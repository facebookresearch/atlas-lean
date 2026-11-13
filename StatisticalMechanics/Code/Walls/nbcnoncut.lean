/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























































import Mathlib
import Code.Lattice.JordanEnclosure
import Code.Lattice.EarExistence
import Code.Lattice.EarContraction
import Code.Walls.fbcconnected
import Code.Walls.atcattachstep
import Code.Walls.jc_leafremoval
import Code.Walls.pc2boundaryconn

open Finset Set SimpleGraph

namespace StatMech

namespace Walls

open StatMech.Lattice
open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable










def nbc_inclHom (K : Set (Site 2)) :
    ((hypercubicLattice 2).induce K) →g (latticeOn K) where
  toFun := Subtype.val
  map_rel' := by
    intro a b hab
    rw [SimpleGraph.induce_adj] at hab
    exact ⟨hab, a.2, b.2⟩


theorem nbc_induce_adj_of_latticeOn {K : Set (Site 2)} {x y : Site 2}
    (hx : x ∈ K) (hy : y ∈ K) (h : (latticeOn K).Adj x y) :
    ((hypercubicLattice 2).induce K).Adj ⟨x, hx⟩ ⟨y, hy⟩ := by
  rw [SimpleGraph.induce_adj]; exact h.1


theorem nbc_induce_reachable_of_latticeOn {K : Set (Site 2)} :
    ∀ {x y : Site 2} (hx : x ∈ K) (hy : y ∈ K),
      (latticeOn K).Walk x y → ((hypercubicLattice 2).induce K).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  intro x y hx hy w
  induction w with
  | nil => exact Reachable.refl _
  | @cons a b c hab q ih =>
    
    have hb : b ∈ K := hab.2.2
    have hstep : ((hypercubicLattice 2).induce K).Adj ⟨a, hx⟩ ⟨b, hb⟩ :=
      nbc_induce_adj_of_latticeOn hx hb hab
    exact hstep.reachable.trans (ih hb hy)



theorem nbc_cellConnected_of_isConnectedCluster {K : Finset (Site 2)}
    (h : IsConnectedCluster K) : CellConnected (↑K : Set (Site 2)) := by
  obtain ⟨ho, hreach⟩ := h
  have hoK : origin 2 ∈ (↑K : Set (Site 2)) := by exact_mod_cast ho
  rw [CellConnected, SimpleGraph.connected_iff]
  refine ⟨?_, ⟨⟨origin 2, hoK⟩⟩⟩
  intro u v
  obtain ⟨u, hu⟩ := u
  obtain ⟨v, hv⟩ := v
  have hru : ((hypercubicLattice 2).induce (↑K : Set (Site 2))).Reachable
      ⟨origin 2, hoK⟩ ⟨u, hu⟩ := by
    obtain ⟨w⟩ := hreach u (by exact_mod_cast hu)
    exact nbc_induce_reachable_of_latticeOn hoK hu w
  have hrv : ((hypercubicLattice 2).induce (↑K : Set (Site 2))).Reachable
      ⟨origin 2, hoK⟩ ⟨v, hv⟩ := by
    obtain ⟨w⟩ := hreach v (by exact_mod_cast hv)
    exact nbc_induce_reachable_of_latticeOn hoK hv w
  exact hru.symm.trans hrv




theorem nbc_isConnectedCluster_of_cellConnected {J : Finset (Site 2)}
    (hoJ : origin 2 ∈ J) (h : CellConnected (↑J : Set (Site 2))) : IsConnectedCluster J := by
  refine ⟨hoJ, ?_⟩
  intro x hx
  have hoJ' : origin 2 ∈ (↑J : Set (Site 2)) := by exact_mod_cast hoJ
  have hxJ' : x ∈ (↑J : Set (Site 2)) := by exact_mod_cast hx
  rw [CellConnected] at h
  have hr := h.preconnected ⟨origin 2, hoJ'⟩ ⟨x, hxJ'⟩
  obtain ⟨p⟩ := hr
  
  exact ⟨p.map (nbc_inclHom (↑J : Set (Site 2)))⟩













theorem nbc_tree_two_leaves {V : Type*} [Fintype V] (T : SimpleGraph V) [DecidableRel T.Adj]
    (hT : T.IsTree) (hn : 2 ≤ Fintype.card V) :
    ∃ a b : V, a ≠ b ∧ T.degree a = 1 ∧ T.degree b = 1 := by
  classical
  have hNontriv : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hn
  
  have hpos : ∀ v : V, 1 ≤ T.degree v := by
    intro v
    have := hT.connected.preconnected.minDegree_pos_of_nontrivial (G := T)
    exact le_trans this (T.minDegree_le_degree v)
  
  have hsum : ∑ v : V, T.degree v = 2 * #T.edgeFinset := T.sum_degrees_eq_twice_card_edges
  have hedge : #T.edgeFinset + 1 = Fintype.card V := hT.card_edgeFinset
  
  by_contra hcon
  push Not at hcon
  
  
  have hleaf_sub : ∀ a b : V, T.degree a = 1 → T.degree b = 1 → a = b := by
    intro a b ha hb
    by_contra hab
    exact hcon a b hab ha hb
  
  
  obtain ⟨v0, hv0⟩ := hT.exists_vert_degree_one_of_nontrivial
  have hlower : 2 * Fintype.card V - 1 ≤ ∑ v : V, T.degree v := by
    have hbound : ∀ v : V, (if v = v0 then 1 else 2) ≤ T.degree v := by
      intro v
      by_cases hvv : v = v0
      · subst hvv; simp [hv0]
      · simp only [if_neg hvv]
        
        rcases Nat.lt_or_ge (T.degree v) 2 with hlt | hge
        · have h1 : T.degree v = 1 := by have := hpos v; omega
          exact absurd (hleaf_sub v v0 h1 hv0) hvv
        · exact hge
    have hconst : (∑ v : V, (if v = v0 then (1:ℕ) else 2)) + 1 = 2 * Fintype.card V := by
      have hstep : (∑ v : V, (if v = v0 then (1:ℕ) else 2)) + 1
          = ∑ v : V, ((if v = v0 then (1:ℕ) else 2) + (if v = v0 then 1 else 0)) := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ v0]
        simp only [Finset.mem_univ, if_true]
      rw [hstep]
      have : ∀ v : V, (if v = v0 then (1:ℕ) else 2) + (if v = v0 then 1 else 0) = 2 := by
        intro v; by_cases hvv : v = v0 <;> simp [hvv]
      rw [Finset.sum_congr rfl (fun v _ => this v), Finset.sum_const, Finset.card_univ,
        smul_eq_mul, mul_comm]
    have hsumif : ∑ v : V, (if v = v0 then (1:ℕ) else 2) ≤ ∑ v : V, T.degree v :=
      Finset.sum_le_sum (fun v _ => hbound v)
    omega
  omega










theorem nbc_induce_mono_left {V : Type*} {T G : SimpleGraph V} (s : Set V) (hle : T ≤ G) :
    T.induce s ≤ G.induce s := by
  intro a b hab
  rw [SimpleGraph.induce_adj] at hab ⊢
  exact hle hab



theorem nbc_cellConnected_diff_of_treeCut {K : Finset (Site 2)}
    {T : SimpleGraph (↑(↑K : Set (Site 2)))}
    (hle : T ≤ (hypercubicLattice 2).induce (↑K : Set (Site 2)))
    {v : ↑(↑K : Set (Site 2))} (h1 : (T.induce ({v}ᶜ : Set _)).Connected) :
    CellConnected ((↑K : Set (Site 2)) \ {v.1}) := by
  classical
  
  have h2 : (((hypercubicLattice 2).induce (↑K : Set (Site 2))).induce
      ({(⟨v.1, v.2⟩ : ↑(↑K : Set (Site 2)))}ᶜ : Set _)).Connected :=
    h1.mono (nbc_induce_mono_left _ hle)
  exact cellConnected_diff_of_iso (↑K : Set (Site 2)) v.1 v.2 h2



theorem nbc_two_noncut {K : Finset (Site 2)} (hcard : 2 ≤ K.card)
    (hconn : CellConnected (↑K : Set (Site 2))) :
    ∃ a ∈ K, ∃ b ∈ K, a ≠ b ∧ CellConnected ((↑K : Set (Site 2)) \ {a}) ∧
      CellConnected ((↑K : Set (Site 2)) \ {b}) := by
  classical
  set G := (hypercubicLattice 2).induce (↑K : Set (Site 2)) with hG
  
  have hfin : Fintype (↑(↑K : Set (Site 2))) := FinsetCoe.fintype K
  have hcardV : Fintype.card (↑(↑K : Set (Site 2))) = K.card := by
    simp [Fintype.card_coe]
  
  obtain ⟨T, hle, hT⟩ := hconn.exists_isTree_le
  haveI : DecidableRel T.Adj := Classical.decRel _
  obtain ⟨a, b, hab, hda, hdb⟩ := nbc_tree_two_leaves T hT (by rw [hcardV]; exact hcard)
  have hca : (T.induce ({a}ᶜ : Set _)).Connected :=
    hT.connected.induce_compl_singleton_of_degree_eq_one hda
  have hcb : (T.induce ({b}ᶜ : Set _)).Connected :=
    hT.connected.induce_compl_singleton_of_degree_eq_one hdb
  refine ⟨a.1, a.2, b.1, b.2, ?_, ?_, ?_⟩
  · intro h; exact hab (Subtype.ext h)
  · exact nbc_cellConnected_diff_of_treeCut hle hca
  · exact nbc_cellConnected_diff_of_treeCut hle hcb



theorem nbc_exists_noncut_ne_origin {K : Finset (Site 2)} (hcard : 2 ≤ K.card)
    (hconn : CellConnected (↑K : Set (Site 2))) :
    ∃ c ∈ K, c ≠ origin 2 ∧ CellConnected ((↑K : Set (Site 2)) \ {c}) := by
  obtain ⟨a, haK, b, hbK, hab, hda, hdb⟩ := nbc_two_noncut hcard hconn
  by_cases ha : a = origin 2
  · refine ⟨b, hbK, ?_, hdb⟩
    intro hb; exact hab (ha.trans hb.symm)
  · exact ⟨a, haK, ha, hda⟩








theorem nbc_coe_erase (K : Finset (Site 2)) (c : Site 2) :
    (↑(K.erase c) : Set (Site 2)) = (↑K : Set (Site 2)) \ {c} := by
  ext x
  simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff]



theorem nbc_isConnectedCluster_erase {K : Finset (Site 2)} {c : Site 2}
    (ho : origin 2 ∈ K) (hcorigin : c ≠ origin 2)
    (h : CellConnected ((↑K : Set (Site 2)) \ {c})) : IsConnectedCluster (K.erase c) := by
  have hoerase : origin 2 ∈ K.erase c := Finset.mem_erase.mpr ⟨fun h => hcorigin h.symm, ho⟩
  apply nbc_isConnectedCluster_of_cellConnected hoerase
  rw [CellConnected, nbc_coe_erase]
  rw [CellConnected] at h; exact h

















def nbc_BoundaryNonCutExists : Prop :=
  ∀ (K : Finset (Site 2)), 2 ≤ K.card → IsConnectedCluster K →
    ∃ c ∈ K, c ≠ origin 2 ∧ (∃ n ∉ K, (hypercubicLattice 2).Adj c n) ∧
      CellConnected ((↑K : Set (Site 2)) \ {c})




theorem nbc_atc_of_boundaryNonCut (h : nbc_BoundaryNonCutExists) : atc_HasRemovableConnCell := by
  intro K hcard hconn
  obtain ⟨c, hcK, hcorigin, hbdry, hcell⟩ := h K hcard hconn
  exact ⟨c, hcK, hcorigin, hbdry, nbc_isConnectedCluster_erase hconn.1 hcorigin hcell⟩





theorem nbc_fbc_hasRemovableCell_of_boundaryNonCut (h : nbc_BoundaryNonCutExists) :
    fbc_HasRemovableCell :=
  atc_hasRemovableCell_of_conn (nbc_atc_of_boundaryNonCut h)










theorem nbc_pendant_boundary {K : Finset (Site 2)} {c : Site 2}
    (hpend : jc_IsPendantCell (↑K : Set (Site 2)) c) :
    ∃ n ∉ K, (hypercubicLattice 2).Adj c n := by
  classical
  obtain ⟨hc, u, ⟨huK, hadj⟩, huniq⟩ := hpend
  
  set n1 := c + ![1, 0] with hn1
  set n2 := c + ![-1, 0] with hn2
  set n3 := c + ![0, 1] with hn3
  set n4 := c + ![0, -1] with hn4
  have hadj1 : (hypercubicLattice 2).Adj c n1 := by
    rw [hn1, hypercubicLattice_adj, Fin.sum_univ_two]; simp [Pi.add_apply]
  have hadj2 : (hypercubicLattice 2).Adj c n2 := by
    rw [hn2, hypercubicLattice_adj, Fin.sum_univ_two]; simp [Pi.add_apply]
  have hadj3 : (hypercubicLattice 2).Adj c n3 := by
    rw [hn3, hypercubicLattice_adj, Fin.sum_univ_two]; simp [Pi.add_apply]
  
  have hne12 : n1 ≠ n2 := by
    rw [hn1, hn2]; intro h; have := congrFun h 0; simp [Pi.add_apply] at this
  have hne13 : n1 ≠ n3 := by
    rw [hn1, hn3]; intro h; have := congrFun h 0; simp [Pi.add_apply] at this
  have hne23 : n2 ≠ n3 := by
    rw [hn2, hn3]; intro h; have := congrFun h 0; simp [Pi.add_apply] at this
  
  by_contra hcon
  push Not at hcon
  
  have h1 : n1 ∈ K := by by_contra h; exact hcon n1 h hadj1
  have h2 : n2 ∈ K := by by_contra h; exact hcon n2 h hadj2
  have h3 : n3 ∈ K := by by_contra h; exact hcon n3 h hadj3
  
  have e1 : n1 = u := huniq n1 ⟨by exact_mod_cast h1, hadj1⟩
  have e2 : n2 = u := huniq n2 ⟨by exact_mod_cast h2, hadj2⟩
  have e3 : n3 = u := huniq n3 ⟨by exact_mod_cast h3, hadj3⟩
  exact hne12 (e1.trans e2.symm)



theorem nbc_boundaryNonCut_of_pendant {K : Finset (Site 2)}
    (hconn : IsConnectedCluster K) {c : Site 2} (hcorigin : c ≠ origin 2)
    (hpend : jc_IsPendantCell (↑K : Set (Site 2)) c) :
    ∃ c ∈ K, c ≠ origin 2 ∧ (∃ n ∉ K, (hypercubicLattice 2).Adj c n) ∧
      CellConnected ((↑K : Set (Site 2)) \ {c}) := by
  refine ⟨c, by exact_mod_cast hpend.1, hcorigin, nbc_pendant_boundary hpend, ?_⟩
  exact jc_cellConnected_diff_of_pendant (↑K : Set (Site 2)) c
    (nbc_cellConnected_of_isConnectedCluster hconn) hpend











theorem nbc_tromino_pendant_10 : jc_IsPendantCell (↑pc2_tromino : Set (Site 2)) ![1, 0] := by
  classical
  refine ⟨?_, ![0, 0], ⟨?_, ?_⟩, ?_⟩
  · rw [pc2_mem_tromino]; tauto
  · rw [pc2_mem_tromino]; tauto
  · rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  · rintro w ⟨hwK, hadj⟩
    unfold pc2_tromino at hwK
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
      Set.mem_singleton_iff] at hwK
    rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
    
    rcases hwK with h | h | h <;> subst h <;> revert hadj <;> decide






theorem nbc_tromino_nonvacuous :
    ∃ c ∈ pc2_tromino, c ≠ origin 2 ∧
      (∃ n ∉ pc2_tromino, (hypercubicLattice 2).Adj c n) ∧
      CellConnected ((↑pc2_tromino : Set (Site 2)) \ {c}) := by
  have hne : (![1, 0] : Site 2) ≠ origin 2 := by
    rw [origin_eq_zerozero]; intro h; have := congrFun h 0; simp at this
  exact nbc_boundaryNonCut_of_pendant pc2_tromino_isConnectedCluster hne nbc_tromino_pendant_10
