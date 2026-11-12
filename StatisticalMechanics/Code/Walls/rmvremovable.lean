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
import Code.Walls.nbcnoncut
import Code.Walls.earremovable

open Finset Set SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice
open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable














theorem rmv_reroute_reachable {V : Type*} (G : SimpleGraph V) (c w : V) (hwc : w ≠ c)
    (hhub : ∀ z, G.Adj c z → z ≠ w → G.Adj w z) :
    ∀ (n : ℕ) {x : V} (hx : x ≠ c) (p : G.Walk x w), p.length = n →
      (G.induce ({c}ᶜ : Set V)).Reachable ⟨x, hx⟩ ⟨w, hwc⟩ := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro x hx p hlen
    cases p with
    | nil => exact Reachable.refl _
    | @cons _ b _ hab q =>
      
      by_cases hbc : b = c
      · 
        have hxc_adj : G.Adj x c := hbc ▸ hab
        by_cases hxw : x = w
        · 
          have : (⟨x, hx⟩ : ↑({c}ᶜ : Set V)) = ⟨w, hwc⟩ := Subtype.ext hxw
          rw [this]
        · have hwx : G.Adj w x := hhub x hxc_adj.symm hxw
          have hstep : (G.induce ({c}ᶜ : Set V)).Adj ⟨x, hx⟩ ⟨w, hwc⟩ := by
            rw [SimpleGraph.induce_adj]; exact hwx.symm
          exact hstep.reachable
      · 
        have hstep : (G.induce ({c}ᶜ : Set V)).Adj ⟨x, hx⟩ ⟨b, hbc⟩ := by
          rw [SimpleGraph.induce_adj]; exact hab
        have hqlen : q.length < n := by
          simp only [SimpleGraph.Walk.length_cons] at hlen; omega
        exact hstep.reachable.trans (IH q.length hqlen hbc q rfl)












theorem rmv_noncut_of_common_neighbour {K : Set (Site 2)} (hconn : CellConnected K)
    {c w : Site 2} (hc : c ∈ K) (hw : w ∈ K) (hwc : w ≠ c)
    (hhub : ∀ z ∈ K, (hypercubicLattice 2).Adj c z → z ≠ w → (hypercubicLattice 2).Adj w z) :
    CellConnected (K \ {c}) := by
  classical
  set G := (hypercubicLattice 2).induce K with hG
  
  set cv : ↥K := ⟨c, hc⟩ with hcv
  set wv : ↥K := ⟨w, hw⟩ with hwv
  have hwvcv : wv ≠ cv := by
    intro h; exact hwc (congrArg Subtype.val h)
  
  have hhubG : ∀ zv : ↥K, G.Adj cv zv → zv ≠ wv → G.Adj wv zv := by
    intro zv hadj hne
    rw [hG, SimpleGraph.induce_adj] at hadj ⊢
    refine hhub zv.1 zv.2 hadj ?_
    intro h; exact hne (Subtype.ext h)
  
  apply cellConnected_diff_of_iso K c hc
  
  have hwvmem : wv ∈ ({cv}ᶜ : Set ↥K) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact hwvcv
  haveI : Nonempty ↥({cv}ᶜ : Set ↥K) := ⟨⟨wv, hwvmem⟩⟩
  refine SimpleGraph.Connected.mk ?_
  
  · have reach : ∀ t : ↥({cv}ᶜ : Set ↥K),
        (G.induce ({cv}ᶜ : Set ↥K)).Reachable ⟨wv, hwvmem⟩ t := by
      intro t
      obtain ⟨tv, htv⟩ := t
      have htvc : tv ≠ cv := by
        intro h; rw [Set.mem_compl_iff, Set.mem_singleton_iff] at htv; exact htv h
      
      obtain ⟨p⟩ := hconn.preconnected tv wv
      
      have hr := rmv_reroute_reachable G cv wv hwvcv hhubG p.length htvc p rfl
      
      have e1 : (⟨wv, hwvmem⟩ : ↥({cv}ᶜ : Set ↥K)) = ⟨wv, hwvcv⟩ := rfl
      have e2 : (⟨tv, htv⟩ : ↥({cv}ᶜ : Set ↥K)) = ⟨tv, htvc⟩ := rfl
      rw [e1, e2]; exact hr.symm
    intro u v
    exact (reach u).symm.trans (reach v)












theorem rmv_adj_diag_leftCell (c : Site 2) :
    (hypercubicLattice 2).Adj (c + ![-1, -1]) (ear_leftCell c) := by
  rw [ear_leftCell, hypercubicLattice_adj, Fin.sum_univ_two]
  simp only [Pi.add_apply]
  norm_num


theorem rmv_adj_diag_downCell (c : Site 2) :
    (hypercubicLattice 2).Adj (c + ![-1, -1]) (ear_downCell c) := by
  rw [ear_downCell, hypercubicLattice_adj, Fin.sum_univ_two]
  simp only [Pi.add_apply]
  norm_num


theorem rmv_diag_ne (c : Site 2) : c + ![-1, -1] ≠ c := by
  intro h; have := congrFun h 0; simp [Pi.add_apply] at this




theorem rmv_extreme_diag_noncut {K : Set (Site 2)} (hconn : CellConnected K) {c : Site 2}
    (hc : ear_IsGlobalExtreme K c) (hdiag : c + ![-1, -1] ∈ K) :
    CellConnected (K \ {c}) := by
  refine rmv_noncut_of_common_neighbour hconn hc.mem hdiag (rmv_diag_ne c) ?_
  intro z hzK hadj _
  
  rcases ear_globalExtreme_neighbor_leftCell_or_downCell K c z hc hzK hadj with h | h
  · rw [h]; exact rmv_adj_diag_leftCell c
  · rw [h]; exact rmv_adj_diag_downCell c




theorem rmv_extreme_diag_removable {K : Finset (Site 2)}
    (hconn : IsConnectedCluster K) {c : Site 2}
    (hc : ear_IsGlobalExtreme (↑K : Set (Site 2)) c) (hcorigin : c ≠ origin 2)
    (hdiag : c + ![-1, -1] ∈ (↑K : Set (Site 2))) :
    ∃ d ∈ K, d ≠ origin 2 ∧ (∃ n ∉ K, (hypercubicLattice 2).Adj d n) ∧
      CellConnected ((↑K : Set (Site 2)) \ {d}) := by
  refine ⟨c, by exact_mod_cast hc.mem, hcorigin,
    ear_globalExtreme_boundary (↑K : Set (Site 2)) c hc, ?_⟩
  exact rmv_extreme_diag_noncut (nbc_cellConnected_of_isConnectedCluster hconn) hc hdiag














theorem rmv_extreme_dichotomy {K : Finset (Site 2)} (hcard : 2 ≤ K.card)
    (hconn : IsConnectedCluster K) {c : Site 2}
    (hc : ear_IsGlobalExtreme (↑K : Set (Site 2)) c) (hcorigin : c ≠ origin 2) :
    (∃ d ∈ K, d ≠ origin 2 ∧ (∃ n ∉ K, (hypercubicLattice 2).Adj d n) ∧
        CellConnected ((↑K : Set (Site 2)) \ {d}))
      ∨ (ear_leftCell c ∈ (↑K : Set (Site 2)) ∧ ear_downCell c ∈ (↑K : Set (Site 2)) ∧
          c + ![-1, -1] ∉ (↑K : Set (Site 2))) := by
  classical
  
  rcases ear_globalExtreme_dichotomy hcard hconn hc hcorigin with hrem | ⟨hp, hq⟩
  · exact Or.inl hrem
  · 
    by_cases hdiag : c + ![-1, -1] ∈ (↑K : Set (Site 2))
    · exact Or.inl (rmv_extreme_diag_removable hconn hc hcorigin hdiag)
    · exact Or.inr ⟨hp, hq, hdiag⟩








noncomputable def rmv_block : Set (Site 2) := {![0, 0], ![1, 0], ![0, 1], ![1, 1]}

theorem rmv_mem_block (v : Site 2) :
    v ∈ rmv_block ↔ v = ![0, 0] ∨ v = ![1, 0] ∨ v = ![0, 1] ∨ v = ![1, 1] := by
  unfold rmv_block; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]


theorem rmv_block_globalExtreme : ear_IsGlobalExtreme rmv_block ![1, 1] := by
  refine ⟨by rw [rmv_mem_block]; tauto, ?_⟩
  intro v hv
  rw [rmv_mem_block] at hv
  unfold ear_gKey
  rcases hv with h | h | h | h <;> subst h <;> rw [Prod.Lex.toLex_le_toLex] <;> simp


theorem rmv_block_diag_mem : (![1, 1] : Site 2) + ![-1, -1] ∈ rmv_block := by
  rw [rmv_mem_block]
  left; funext i; fin_cases i <;> simp [Pi.add_apply]


theorem rmv_block_cellConnected : CellConnected rmv_block := by
  classical
  rw [CellConnected, SimpleGraph.connected_iff]
  refine ⟨?_, ⟨⟨![0, 0], by rw [rmv_mem_block]; tauto⟩⟩⟩
  intro u v
  
  have h00 : (![0, 0] : Site 2) ∈ rmv_block := by rw [rmv_mem_block]; tauto
  have anchor : ∀ t : ↥rmv_block,
      ((hypercubicLattice 2).induce rmv_block).Reachable ⟨![0, 0], h00⟩ t := by
    rintro ⟨t, ht⟩
    rw [rmv_mem_block] at ht
    rcases ht with h | h | h | h <;> subst h
    · exact Reachable.refl _
    · refine SimpleGraph.Adj.reachable ?_
      rw [SimpleGraph.induce_adj, hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
    · refine SimpleGraph.Adj.reachable ?_
      rw [SimpleGraph.induce_adj, hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
    · 
      have h1 : ((hypercubicLattice 2).induce rmv_block).Adj
          ⟨![0, 0], by rw [rmv_mem_block]; tauto⟩ ⟨![1, 0], by rw [rmv_mem_block]; tauto⟩ := by
        rw [SimpleGraph.induce_adj, hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
      have h2 : ((hypercubicLattice 2).induce rmv_block).Adj
          ⟨![1, 0], by rw [rmv_mem_block]; tauto⟩ ⟨![1, 1], by rw [rmv_mem_block]; tauto⟩ := by
        rw [SimpleGraph.induce_adj, hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
      exact h1.reachable.trans h2.reachable
  exact (anchor u).symm.trans (anchor v)






theorem rmv_block_removable : CellConnected (rmv_block \ {![1, 1]}) :=
  rmv_extreme_diag_noncut rmv_block_cellConnected rmv_block_globalExtreme rmv_block_diag_mem





theorem rmv_tromino_nonvacuous :
    ∃ c ∈ pc2_tromino, c ≠ origin 2 ∧
      (∃ n ∉ pc2_tromino, (hypercubicLattice 2).Adj c n) ∧
      CellConnected ((↑pc2_tromino : Set (Site 2)) \ {c}) :=
  ear_tromino_nonvacuous







theorem rmv_vtromino_reflex_residue :
    (![0, 0] : Site 2) + ![-1, -1] ∉ ear_vtromino ∧
      ¬ CellConnected (ear_vtromino \ {![0, 0]}) := by
  refine ⟨?_, ear_vtromino_extreme_cut⟩
  rw [ear_mem_vtromino]
  push Not
  refine ⟨?_, ?_, ?_⟩ <;> intro h
  · have := congrFun h 0; norm_num [Pi.add_apply] at this
  · have := congrFun h 1; norm_num [Pi.add_apply] at this
  · have := congrFun h 0; norm_num [Pi.add_apply] at this

















def rmv_ReflexCornerResidue : Prop :=
  ∀ (K : Finset (Site 2)), 2 ≤ K.card → IsConnectedCluster K →
    ∀ c, ear_IsGlobalExtreme (↑K : Set (Site 2)) c → c ≠ origin 2 →
      ear_leftCell c ∈ (↑K : Set (Site 2)) → ear_downCell c ∈ (↑K : Set (Site 2)) →
      c + ![-1, -1] ∉ (↑K : Set (Site 2)) →
      ∃ d ∈ K, d ≠ origin 2 ∧ (∃ n ∉ K, (hypercubicLattice 2).Adj d n) ∧
        CellConnected ((↑K : Set (Site 2)) \ {d})







def rmv_AntiReflexCornerResidue : Prop :=
  ∀ (K : Finset (Site 2)), 2 ≤ K.card → IsConnectedCluster K →
    ∀ b, ear_IsAntiExtreme (↑K : Set (Site 2)) b → b ≠ origin 2 →
      ear_rightCell b ∈ (↑K : Set (Site 2)) → ear_upCell b ∈ (↑K : Set (Site 2)) →
      b + ![1, 1] ∉ (↑K : Set (Site 2)) →
      ∃ d ∈ K, d ≠ origin 2 ∧ (∃ n ∉ K, (hypercubicLattice 2).Adj d n) ∧
        CellConnected ((↑K : Set (Site 2)) \ {d})




theorem rmv_removable_of_extreme_ne_origin (hres : rmv_ReflexCornerResidue)
    {K : Finset (Site 2)} (hcard : 2 ≤ K.card) (hconn : IsConnectedCluster K) {c : Site 2}
    (hc : ear_IsGlobalExtreme (↑K : Set (Site 2)) c) (hcorigin : c ≠ origin 2) :
    ∃ d ∈ K, d ≠ origin 2 ∧ (∃ n ∉ K, (hypercubicLattice 2).Adj d n) ∧
      CellConnected ((↑K : Set (Site 2)) \ {d}) := by
  rcases rmv_extreme_dichotomy hcard hconn hc hcorigin with hrem | ⟨hp, hq, hdiag⟩
  · exact hrem
  · exact hres K hcard hconn c hc hcorigin hp hq hdiag













theorem rmv_nbc_of_reflexResidue (hres : rmv_ReflexCornerResidue)
    (hresAnti : rmv_AntiReflexCornerResidue) : nbc_BoundaryNonCutExists := by
  classical
  intro K hcard hconn
  
  obtain ⟨c, hc⟩ := ear_exists_globalExtreme (↑K : Set (Site 2)) K.finite_toSet
    (by rw [Finset.coe_nonempty]; exact ⟨origin 2, hconn.1⟩)
  by_cases hco : c = origin 2
  · 
    obtain ⟨b, hb⟩ := ear_exists_antiExtreme (↑K : Set (Site 2)) K.finite_toSet
      (by rw [Finset.coe_nonempty]; exact ⟨origin 2, hconn.1⟩)
    have hbc : b ≠ c := (ear_extremes_distinct hcard hc hb).symm
    have hborigin : b ≠ origin 2 := by rw [hco] at hbc; exact hbc
    
    rcases ear_antiExtreme_dichotomy hcard hconn hb hborigin with hrem | ⟨hr, hu⟩
    · exact hrem
    · 
      by_cases hdiag : b + ![1, 1] ∈ (↑K : Set (Site 2))
      · 
        refine ⟨b, by exact_mod_cast hb.mem, hborigin,
          ear_antiExtreme_boundary (↑K : Set (Site 2)) b hb, ?_⟩
        refine rmv_noncut_of_common_neighbour
          (nbc_cellConnected_of_isConnectedCluster hconn) hb.mem hdiag ?_ ?_
        · intro h; have := congrFun h 0; simp [Pi.add_apply] at this
        · intro z hzK hadj _
          rcases ear_antiExtreme_neighbor_rightCell_or_upCell (↑K : Set (Site 2)) b z hb hzK hadj
            with h | h
          · rw [h, ear_rightCell]
            rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp only [Pi.add_apply]; norm_num
          · rw [h, ear_upCell]
            rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp only [Pi.add_apply]; norm_num
      · 
        exact hresAnti K hcard hconn b hb hborigin hr hu hdiag
  · 
    exact rmv_removable_of_extreme_ne_origin hres hcard hconn hc hco









theorem rmv_atc_of_reflexResidue (hres : rmv_ReflexCornerResidue)
    (hresAnti : rmv_AntiReflexCornerResidue) : atc_HasRemovableConnCell :=
  nbc_atc_of_boundaryNonCut (rmv_nbc_of_reflexResidue hres hresAnti)




theorem rmv_fbc_hasRemovableCell_of_reflexResidue (hres : rmv_ReflexCornerResidue)
    (hresAnti : rmv_AntiReflexCornerResidue) : fbc_HasRemovableCell :=
  nbc_fbc_hasRemovableCell_of_boundaryNonCut (rmv_nbc_of_reflexResidue hres hresAnti)

end Walls

end StatMech
