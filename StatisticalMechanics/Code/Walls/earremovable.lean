/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





























































import Mathlib
import Code.Lattice.EarExistence
import Code.Lattice.EarContraction
import Code.Walls.nbcnoncut
import Code.Walls.jc_leafremoval
import Code.Walls.atcattachstep

open Finset Set SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice
open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable











noncomputable def ear_gKey (v : Site 2) : ℤ ×ₗ ℤ := toLex (v 1, v 0)



structure ear_IsGlobalExtreme (K : Set (Site 2)) (c : Site 2) : Prop where
  
  mem : c ∈ K
  
  maximal : ∀ v ∈ K, ear_gKey v ≤ ear_gKey c



theorem ear_exists_globalExtreme (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty) :
    ∃ c, ear_IsGlobalExtreme K c := by
  have hfne : hK.toFinset.Nonempty := by rwa [Set.Finite.toFinset_nonempty]
  obtain ⟨c, hc, hmax⟩ := Finset.exists_max_image hK.toFinset ear_gKey hfne
  refine ⟨c, ⟨by rwa [Set.Finite.mem_toFinset] at hc, ?_⟩⟩
  intro v hv
  exact hmax v (by rwa [Set.Finite.mem_toFinset])


theorem ear_globalExtreme_not_mem_of_higher (K : Set (Site 2)) (c v : Site 2)
    (hc : ear_IsGlobalExtreme K c) (hy : c 1 < v 1) : v ∉ K := by
  intro hv
  have h := hc.maximal v hv
  unfold ear_gKey at h
  rw [Prod.Lex.toLex_le_toLex] at h
  rcases h with h | ⟨h1, h2⟩ <;> omega


theorem ear_globalExtreme_not_mem_of_right (K : Set (Site 2)) (c v : Site 2)
    (hc : ear_IsGlobalExtreme K c) (hy : v 1 = c 1) (hx : c 0 < v 0) : v ∉ K := by
  intro hv
  have h := hc.maximal v hv
  unfold ear_gKey at h
  rw [Prod.Lex.toLex_le_toLex] at h
  rcases h with h | ⟨h1, h2⟩ <;> omega


theorem ear_globalExtreme_up_nmem (K : Set (Site 2)) (c : Site 2)
    (hc : ear_IsGlobalExtreme K c) : c + ![0, 1] ∉ K := by
  apply ear_globalExtreme_not_mem_of_higher K c _ hc; simp [Pi.add_apply]


theorem ear_globalExtreme_right_nmem (K : Set (Site 2)) (c : Site 2)
    (hc : ear_IsGlobalExtreme K c) : c + ![1, 0] ∉ K := by
  apply ear_globalExtreme_not_mem_of_right K c _ hc <;> simp [Pi.add_apply]



theorem ear_globalExtreme_boundary (K : Set (Site 2)) (c : Site 2)
    (hc : ear_IsGlobalExtreme K c) : ∃ n ∉ K, (hypercubicLattice 2).Adj c n := by
  refine ⟨c + ![0, 1], ear_globalExtreme_up_nmem K c hc, ?_⟩
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  simp [Pi.add_apply]




theorem ear_globalExtreme_neighbor_left_or_down (K : Set (Site 2)) (c v : Site 2)
    (hc : ear_IsGlobalExtreme K c) (hv : v ∈ K) (hadj : (hypercubicLattice 2).Adj v c) :
    v = c + ![-1, 0] ∨ v = c + ![0, -1] := by
  rcases adj_neighbor_cases v c hadj with h | h | h | h
  · exact absurd (h ▸ hv) (ear_globalExtreme_right_nmem K c hc)
  · exact Or.inl h
  · exact absurd (h ▸ hv) (ear_globalExtreme_up_nmem K c hc)
  · exact Or.inr h







noncomputable def ear_leftCell (c : Site 2) : Site 2 := c + ![-1, 0]


noncomputable def ear_downCell (c : Site 2) : Site 2 := c + ![0, -1]

theorem ear_adj_leftCell (c : Site 2) : (hypercubicLattice 2).Adj c (ear_leftCell c) := by
  rw [ear_leftCell, hypercubicLattice_adj, Fin.sum_univ_two]; simp [Pi.add_apply]

theorem ear_adj_downCell (c : Site 2) : (hypercubicLattice 2).Adj c (ear_downCell c) := by
  rw [ear_downCell, hypercubicLattice_adj, Fin.sum_univ_two]; simp [Pi.add_apply]

theorem ear_leftCell_ne_downCell (c : Site 2) : ear_leftCell c ≠ ear_downCell c := by
  rw [ear_leftCell, ear_downCell]; intro h
  have := congrFun h 0; simp [Pi.add_apply] at this


theorem ear_globalExtreme_neighbor_leftCell_or_downCell (K : Set (Site 2)) (c v : Site 2)
    (hc : ear_IsGlobalExtreme K c) (hv : v ∈ K) (hadj : (hypercubicLattice 2).Adj c v) :
    v = ear_leftCell c ∨ v = ear_downCell c := by
  have h := ear_globalExtreme_neighbor_left_or_down K c v hc hv hadj.symm
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr h












theorem ear_exists_neighbor_of_conn {K : Finset (Site 2)} (hcard : 2 ≤ K.card)
    (hconn : IsConnectedCluster K) {c : Site 2} (hc : c ∈ K) :
    ∃ v ∈ K, (hypercubicLattice 2).Adj c v := by
  classical
  by_contra hcon
  push Not at hcon
  
  have hcell : CellConnected (↑K : Set (Site 2)) := nbc_cellConnected_of_isConnectedCluster hconn
  obtain ⟨d, hdK, hdc⟩ : ∃ d ∈ K, d ≠ c := by
    by_contra h
    push Not at h
    
    have hsub : K ⊆ {c} := by
      intro x hx; rw [Finset.mem_singleton]; exact h x hx
    have := Finset.card_le_card hsub
    simp at this; omega
  have hcK : c ∈ (↑K : Set (Site 2)) := by exact_mod_cast hc
  have hdK' : d ∈ (↑K : Set (Site 2)) := by exact_mod_cast hdK
  
  have hr := hcell.preconnected ⟨c, hcK⟩ ⟨d, hdK'⟩
  obtain ⟨w⟩ := hr
  
  cases w with
  | nil => exact hdc rfl
  | @cons _ b _ hab _ =>
    have hab' : (hypercubicLattice 2).Adj c b.1 := by
      simpa only [SimpleGraph.comap_adj, Function.Embedding.coe_subtype] using hab
    exact hcon b.1 (by exact_mod_cast b.2) hab'




theorem ear_globalExtreme_pendant_of_down_nmem {K : Finset (Site 2)} (hcard : 2 ≤ K.card)
    (hconn : IsConnectedCluster K) {c : Site 2} (hc : ear_IsGlobalExtreme (↑K : Set (Site 2)) c)
    (hdown : ear_downCell c ∉ (↑K : Set (Site 2))) :
    jc_IsPendantCell (↑K : Set (Site 2)) c := by
  classical
  obtain ⟨v, hvK, hadj⟩ := ear_exists_neighbor_of_conn hcard hconn (by exact_mod_cast hc.mem)
  have hvK' : v ∈ (↑K : Set (Site 2)) := by exact_mod_cast hvK
  refine ⟨hc.mem, ear_leftCell c, ⟨?_, ear_adj_leftCell c⟩, ?_⟩
  · 
    rcases ear_globalExtreme_neighbor_leftCell_or_downCell (↑K : Set (Site 2)) c v hc hvK' hadj with
      h | h
    · rw [← h]; exact hvK'
    · exact absurd (h ▸ hvK') hdown
  · rintro w ⟨hwK, hwadj⟩
    rcases ear_globalExtreme_neighbor_leftCell_or_downCell (↑K : Set (Site 2)) c w hc hwK hwadj with
      h | h
    · exact h
    · exact absurd (h ▸ hwK) hdown


theorem ear_globalExtreme_pendant_of_left_nmem {K : Finset (Site 2)} (hcard : 2 ≤ K.card)
    (hconn : IsConnectedCluster K) {c : Site 2} (hc : ear_IsGlobalExtreme (↑K : Set (Site 2)) c)
    (hleft : ear_leftCell c ∉ (↑K : Set (Site 2))) :
    jc_IsPendantCell (↑K : Set (Site 2)) c := by
  classical
  obtain ⟨v, hvK, hadj⟩ := ear_exists_neighbor_of_conn hcard hconn (by exact_mod_cast hc.mem)
  have hvK' : v ∈ (↑K : Set (Site 2)) := by exact_mod_cast hvK
  refine ⟨hc.mem, ear_downCell c, ⟨?_, ear_adj_downCell c⟩, ?_⟩
  · rcases ear_globalExtreme_neighbor_leftCell_or_downCell (↑K : Set (Site 2)) c v hc hvK' hadj with
      h | h
    · exact absurd (h ▸ hvK') hleft
    · rw [← h]; exact hvK'
  · rintro w ⟨hwK, hwadj⟩
    rcases ear_globalExtreme_neighbor_leftCell_or_downCell (↑K : Set (Site 2)) c w hc hwK hwadj with
      h | h
    · exact absurd (h ▸ hwK) hleft
    · exact h
























theorem ear_removable_of_pendant_ne_origin {K : Finset (Site 2)}
    (hconn : IsConnectedCluster K) {c : Site 2} (hc : ear_IsGlobalExtreme (↑K : Set (Site 2)) c)
    (hcorigin : c ≠ origin 2) (hpend : jc_IsPendantCell (↑K : Set (Site 2)) c) :
    ∃ d ∈ K, d ≠ origin 2 ∧ (∃ n ∉ K, (hypercubicLattice 2).Adj d n) ∧
      CellConnected ((↑K : Set (Site 2)) \ {d}) := by
  refine ⟨c, by exact_mod_cast hc.mem, hcorigin,
    ear_globalExtreme_boundary (↑K : Set (Site 2)) c hc, ?_⟩
  exact jc_cellConnected_diff_of_pendant (↑K : Set (Site 2)) c
    (nbc_cellConnected_of_isConnectedCluster hconn) hpend











noncomputable def ear_vtromino : Set (Site 2) := {![0, 0], ![-1, 0], ![0, -1]}

theorem ear_mem_vtromino (v : Site 2) :
    v ∈ ear_vtromino ↔ v = ![0, 0] ∨ v = ![-1, 0] ∨ v = ![0, -1] := by
  unfold ear_vtromino; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]

theorem ear_vt_v00 : (![0, 0] : Site 2) ∈ ear_vtromino := by rw [ear_mem_vtromino]; tauto
theorem ear_vt_vm10 : (![-1, 0] : Site 2) ∈ ear_vtromino := by rw [ear_mem_vtromino]; tauto
theorem ear_vt_v0m1 : (![0, -1] : Site 2) ∈ ear_vtromino := by rw [ear_mem_vtromino]; tauto


theorem ear_vtromino_globalExtreme : ear_IsGlobalExtreme ear_vtromino ![0, 0] := by
  refine ⟨ear_vt_v00, ?_⟩
  intro v hv
  rw [ear_mem_vtromino] at hv
  unfold ear_gKey
  rcases hv with h | h | h <;> subst h <;> rw [Prod.Lex.toLex_le_toLex] <;> simp



theorem ear_vtromino_two_neighbours :
    ear_leftCell (![0, 0] : Site 2) ∈ ear_vtromino ∧
      ear_downCell (![0, 0] : Site 2) ∈ ear_vtromino := by
  constructor
  · rw [ear_mem_vtromino, ear_leftCell]; right; left; funext i; fin_cases i <;> simp
  · rw [ear_mem_vtromino, ear_downCell]; right; right; funext i; fin_cases i <;> simp

theorem ear_vtd_vm10 : (![-1, 0] : Site 2) ∈ ear_vtromino \ {![0, 0]} := by
  refine ⟨ear_vt_vm10, ?_⟩
  simp only [Set.mem_singleton_iff]; intro h; have := congrFun h 0; simp at this

theorem ear_vtd_v0m1 : (![0, -1] : Site 2) ∈ ear_vtromino \ {![0, 0]} := by
  refine ⟨ear_vt_v0m1, ?_⟩
  simp only [Set.mem_singleton_iff]; intro h; have := congrFun h 1; simp at this



theorem ear_vtromino_arm_isolated :
    ((hypercubicLattice 2).induce (ear_vtromino \ {![0, 0]})).neighborSet ⟨![-1, 0], ear_vtd_vm10⟩
      = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro ⟨w, hw⟩ hadj
  rw [SimpleGraph.mem_neighborSet, SimpleGraph.induce_adj, hypercubicLattice_adj,
    Fin.sum_univ_two] at hadj
  obtain ⟨hwK, hwne⟩ := hw
  rw [Set.mem_singleton_iff] at hwne
  rw [ear_mem_vtromino] at hwK
  rcases hwK with h | h | h <;> subst h
  · exact hwne rfl
  · simp at hadj
  · simp at hadj

theorem ear_vtromino_arm_ne :
    (⟨![-1, 0], ear_vtd_vm10⟩ : ↑(ear_vtromino \ {![0, 0]})) ≠ ⟨![0, -1], ear_vtd_v0m1⟩ := by
  intro h
  have := congrFun (congrArg Subtype.val h) 0
  norm_num at this








theorem ear_vtromino_extreme_cut : ¬ CellConnected (ear_vtromino \ {![0, 0]}) := by
  intro h
  have hreach := h.preconnected ⟨![-1, 0], ear_vtd_vm10⟩ ⟨![0, -1], ear_vtd_v0m1⟩
  exact not_reachable_of_neighborSet_left_eq_empty ear_vtromino_arm_ne
    ear_vtromino_arm_isolated hreach













structure ear_IsAntiExtreme (K : Set (Site 2)) (b : Site 2) : Prop where
  
  mem : b ∈ K
  
  minimal : ∀ v ∈ K, ear_gKey b ≤ ear_gKey v


theorem ear_exists_antiExtreme (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty) :
    ∃ b, ear_IsAntiExtreme K b := by
  have hfne : hK.toFinset.Nonempty := by rwa [Set.Finite.toFinset_nonempty]
  obtain ⟨b, hb, hmin⟩ := Finset.exists_min_image hK.toFinset ear_gKey hfne
  refine ⟨b, ⟨by rwa [Set.Finite.mem_toFinset] at hb, ?_⟩⟩
  intro v hv
  exact hmin v (by rwa [Set.Finite.mem_toFinset])


theorem ear_antiExtreme_not_mem_of_lower (K : Set (Site 2)) (b v : Site 2)
    (hb : ear_IsAntiExtreme K b) (hy : v 1 < b 1) : v ∉ K := by
  intro hv
  have h := hb.minimal v hv
  unfold ear_gKey at h
  rw [Prod.Lex.toLex_le_toLex] at h
  rcases h with h | ⟨h1, h2⟩ <;> omega


theorem ear_antiExtreme_not_mem_of_left (K : Set (Site 2)) (b v : Site 2)
    (hb : ear_IsAntiExtreme K b) (hy : v 1 = b 1) (hx : v 0 < b 0) : v ∉ K := by
  intro hv
  have h := hb.minimal v hv
  unfold ear_gKey at h
  rw [Prod.Lex.toLex_le_toLex] at h
  rcases h with h | ⟨h1, h2⟩ <;> omega


theorem ear_antiExtreme_down_nmem (K : Set (Site 2)) (b : Site 2)
    (hb : ear_IsAntiExtreme K b) : b + ![0, -1] ∉ K := by
  apply ear_antiExtreme_not_mem_of_lower K b _ hb; simp [Pi.add_apply]


theorem ear_antiExtreme_left_nmem (K : Set (Site 2)) (b : Site 2)
    (hb : ear_IsAntiExtreme K b) : b + ![-1, 0] ∉ K := by
  apply ear_antiExtreme_not_mem_of_left K b _ hb <;> simp [Pi.add_apply]



theorem ear_antiExtreme_boundary (K : Set (Site 2)) (b : Site 2)
    (hb : ear_IsAntiExtreme K b) : ∃ n ∉ K, (hypercubicLattice 2).Adj b n := by
  refine ⟨b + ![0, -1], ear_antiExtreme_down_nmem K b hb, ?_⟩
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [Pi.add_apply]


noncomputable def ear_rightCell (b : Site 2) : Site 2 := b + ![1, 0]


noncomputable def ear_upCell (b : Site 2) : Site 2 := b + ![0, 1]

theorem ear_adj_rightCell (b : Site 2) : (hypercubicLattice 2).Adj b (ear_rightCell b) := by
  rw [ear_rightCell, hypercubicLattice_adj, Fin.sum_univ_two]; simp [Pi.add_apply]

theorem ear_adj_upCell (b : Site 2) : (hypercubicLattice 2).Adj b (ear_upCell b) := by
  rw [ear_upCell, hypercubicLattice_adj, Fin.sum_univ_two]; simp [Pi.add_apply]


theorem ear_antiExtreme_neighbor_rightCell_or_upCell (K : Set (Site 2)) (b v : Site 2)
    (hb : ear_IsAntiExtreme K b) (hv : v ∈ K) (hadj : (hypercubicLattice 2).Adj b v) :
    v = ear_rightCell b ∨ v = ear_upCell b := by
  rcases adj_neighbor_cases v b hadj.symm with h | h | h | h
  · exact Or.inl h
  · exact absurd (h ▸ hv) (ear_antiExtreme_left_nmem K b hb)
  · exact Or.inr h
  · exact absurd (h ▸ hv) (ear_antiExtreme_down_nmem K b hb)


theorem ear_antiExtreme_pendant_of_up_nmem {K : Finset (Site 2)} (hcard : 2 ≤ K.card)
    (hconn : IsConnectedCluster K) {b : Site 2} (hb : ear_IsAntiExtreme (↑K : Set (Site 2)) b)
    (hup : ear_upCell b ∉ (↑K : Set (Site 2))) :
    jc_IsPendantCell (↑K : Set (Site 2)) b := by
  classical
  obtain ⟨v, hvK, hadj⟩ := ear_exists_neighbor_of_conn hcard hconn (by exact_mod_cast hb.mem)
  have hvK' : v ∈ (↑K : Set (Site 2)) := by exact_mod_cast hvK
  refine ⟨hb.mem, ear_rightCell b, ⟨?_, ear_adj_rightCell b⟩, ?_⟩
  · rcases ear_antiExtreme_neighbor_rightCell_or_upCell (↑K : Set (Site 2)) b v hb hvK' hadj with
      h | h
    · rw [← h]; exact hvK'
    · exact absurd (h ▸ hvK') hup
  · rintro w ⟨hwK, hwadj⟩
    rcases ear_antiExtreme_neighbor_rightCell_or_upCell (↑K : Set (Site 2)) b w hb hwK hwadj with
      h | h
    · exact h
    · exact absurd (h ▸ hwK) hup


theorem ear_antiExtreme_pendant_of_right_nmem {K : Finset (Site 2)} (hcard : 2 ≤ K.card)
    (hconn : IsConnectedCluster K) {b : Site 2} (hb : ear_IsAntiExtreme (↑K : Set (Site 2)) b)
    (hright : ear_rightCell b ∉ (↑K : Set (Site 2))) :
    jc_IsPendantCell (↑K : Set (Site 2)) b := by
  classical
  obtain ⟨v, hvK, hadj⟩ := ear_exists_neighbor_of_conn hcard hconn (by exact_mod_cast hb.mem)
  have hvK' : v ∈ (↑K : Set (Site 2)) := by exact_mod_cast hvK
  refine ⟨hb.mem, ear_upCell b, ⟨?_, ear_adj_upCell b⟩, ?_⟩
  · rcases ear_antiExtreme_neighbor_rightCell_or_upCell (↑K : Set (Site 2)) b v hb hvK' hadj with
      h | h
    · exact absurd (h ▸ hvK') hright
    · rw [← h]; exact hvK'
  · rintro w ⟨hwK, hwadj⟩
    rcases ear_antiExtreme_neighbor_rightCell_or_upCell (↑K : Set (Site 2)) b w hb hwK hwadj with
      h | h
    · exact absurd (h ▸ hwK) hright
    · exact h










theorem ear_gKey_injective : Function.Injective ear_gKey := by
  intro a b h
  unfold ear_gKey at h
  
  have h' : (a 1, a 0) = (b 1, b 0) := h
  rw [Prod.mk.injEq] at h'
  obtain ⟨h1, h0⟩ := h'
  funext i; fin_cases i <;> assumption




theorem ear_extremes_distinct {K : Finset (Site 2)} (hcard : 2 ≤ K.card) {c b : Site 2}
    (hc : ear_IsGlobalExtreme (↑K : Set (Site 2)) c)
    (hb : ear_IsAntiExtreme (↑K : Set (Site 2)) b) :
    c ≠ b := by
  classical
  intro hcb
  subst hcb
  
  have hall : ∀ v ∈ (↑K : Set (Site 2)), v = c := by
    intro v hv
    have h1 := hc.maximal v hv
    have h2 := hb.minimal v hv
    exact ear_gKey_injective (le_antisymm h1 h2)
  
  have hsub : K ⊆ {c} := by
    intro x hx
    rw [Finset.mem_singleton]
    exact hall x (by exact_mod_cast hx)
  have := Finset.card_le_card hsub
  simp at this; omega



theorem ear_removable_of_antiPendant_ne_origin {K : Finset (Site 2)}
    (hconn : IsConnectedCluster K) {b : Site 2} (hb : ear_IsAntiExtreme (↑K : Set (Site 2)) b)
    (hborigin : b ≠ origin 2) (hpend : jc_IsPendantCell (↑K : Set (Site 2)) b) :
    ∃ d ∈ K, d ≠ origin 2 ∧ (∃ n ∉ K, (hypercubicLattice 2).Adj d n) ∧
      CellConnected ((↑K : Set (Site 2)) \ {d}) := by
  refine ⟨b, by exact_mod_cast hb.mem, hborigin,
    ear_antiExtreme_boundary (↑K : Set (Site 2)) b hb, ?_⟩
  exact jc_cellConnected_diff_of_pendant (↑K : Set (Site 2)) b
    (nbc_cellConnected_of_isConnectedCluster hconn) hpend





theorem ear_globalExtreme_dichotomy {K : Finset (Site 2)} (hcard : 2 ≤ K.card)
    (hconn : IsConnectedCluster K) {c : Site 2} (hc : ear_IsGlobalExtreme (↑K : Set (Site 2)) c)
    (hcorigin : c ≠ origin 2) :
    (∃ d ∈ K, d ≠ origin 2 ∧ (∃ n ∉ K, (hypercubicLattice 2).Adj d n) ∧
        CellConnected ((↑K : Set (Site 2)) \ {d}))
      ∨ (ear_leftCell c ∈ (↑K : Set (Site 2)) ∧ ear_downCell c ∈ (↑K : Set (Site 2))) := by
  classical
  by_cases hp : ear_leftCell c ∈ (↑K : Set (Site 2))
  · by_cases hq : ear_downCell c ∈ (↑K : Set (Site 2))
    · exact Or.inr ⟨hp, hq⟩
    · exact Or.inl (ear_removable_of_pendant_ne_origin hconn hc hcorigin
        (ear_globalExtreme_pendant_of_down_nmem hcard hconn hc hq))
  · exact Or.inl (ear_removable_of_pendant_ne_origin hconn hc hcorigin
      (ear_globalExtreme_pendant_of_left_nmem hcard hconn hc hp))



theorem ear_antiExtreme_dichotomy {K : Finset (Site 2)} (hcard : 2 ≤ K.card)
    (hconn : IsConnectedCluster K) {b : Site 2} (hb : ear_IsAntiExtreme (↑K : Set (Site 2)) b)
    (hborigin : b ≠ origin 2) :
    (∃ d ∈ K, d ≠ origin 2 ∧ (∃ n ∉ K, (hypercubicLattice 2).Adj d n) ∧
        CellConnected ((↑K : Set (Site 2)) \ {d}))
      ∨ (ear_rightCell b ∈ (↑K : Set (Site 2)) ∧ ear_upCell b ∈ (↑K : Set (Site 2))) := by
  classical
  by_cases hr : ear_rightCell b ∈ (↑K : Set (Site 2))
  · by_cases hu : ear_upCell b ∈ (↑K : Set (Site 2))
    · exact Or.inr ⟨hr, hu⟩
    · exact Or.inl (ear_removable_of_antiPendant_ne_origin hconn hb hborigin
        (ear_antiExtreme_pendant_of_up_nmem hcard hconn hb hu))
  · exact Or.inl (ear_removable_of_antiPendant_ne_origin hconn hb hborigin
      (ear_antiExtreme_pendant_of_right_nmem hcard hconn hb hr))








theorem ear_boundaryNonCut_of_pendantExtreme {K : Finset (Site 2)} (_hcard : 2 ≤ K.card)
    (hconn : IsConnectedCluster K)
    (hpend : (∃ c, ear_IsGlobalExtreme (↑K : Set (Site 2)) c ∧ c ≠ origin 2 ∧
                jc_IsPendantCell (↑K : Set (Site 2)) c)
           ∨ (∃ b, ear_IsAntiExtreme (↑K : Set (Site 2)) b ∧ b ≠ origin 2 ∧
                jc_IsPendantCell (↑K : Set (Site 2)) b)) :
    ∃ d ∈ K, d ≠ origin 2 ∧ (∃ n ∉ K, (hypercubicLattice 2).Adj d n) ∧
      CellConnected ((↑K : Set (Site 2)) \ {d}) := by
  rcases hpend with ⟨c, hc, hco, hp⟩ | ⟨b, hb, hbo, hp⟩
  · exact ear_removable_of_pendant_ne_origin hconn hc hco hp
  · exact ear_removable_of_antiPendant_ne_origin hconn hb hbo hp













theorem ear_cutWitness_globalExtreme : ear_IsGlobalExtreme cutWitness ![2, 1] := by
  refine ⟨cw_v21, ?_⟩
  intro v hv
  rw [mem_cutWitness] at hv
  unfold ear_gKey
  rcases hv with h | h | h | h <;> subst h <;> rw [Prod.Lex.toLex_le_toLex] <;> simp



theorem ear_cutWitness_globalExtreme_pendant : jc_IsPendantCell cutWitness ![2, 1] := by
  classical
  refine ⟨cw_v21, ![1, 1], ⟨cw_v11, ?_⟩, ?_⟩
  · rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  · rintro w ⟨hwK, hadj⟩
    rw [mem_cutWitness] at hwK
    rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
    rcases hwK with h | h | h | h <;> subst h <;> revert hadj <;> decide






theorem ear_cutWitness_removable : CellConnected (cutWitness \ {![2, 1]}) :=
  jc_cellConnected_diff_of_pendant cutWitness ![2, 1] cutWitness_cellConnected
    ear_cutWitness_globalExtreme_pendant










theorem ear_tromino_globalExtreme : ear_IsGlobalExtreme (↑pc2_tromino : Set (Site 2)) ![0, 1] := by
  refine ⟨by rw [pc2_mem_tromino]; tauto, ?_⟩
  intro v hv
  obtain ⟨p, q, rfl⟩ : ∃ p q, v = ![p, q] := ⟨v 0, v 1, by funext i; fin_cases i <;> rfl⟩
  rw [pc2_mem_tromino] at hv
  unfold ear_gKey
  rcases hv with ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩ <;> subst hp <;> subst hq <;>
    rw [Prod.Lex.toLex_le_toLex] <;> simp


theorem ear_tromino_antiExtreme : ear_IsAntiExtreme (↑pc2_tromino : Set (Site 2)) ![0, 0] := by
  refine ⟨by rw [pc2_mem_tromino]; tauto, ?_⟩
  intro v hv
  obtain ⟨p, q, rfl⟩ : ∃ p q, v = ![p, q] := ⟨v 0, v 1, by funext i; fin_cases i <;> rfl⟩
  rw [pc2_mem_tromino] at hv
  unfold ear_gKey
  rcases hv with ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩ <;> subst hp <;> subst hq <;>
    rw [Prod.Lex.toLex_le_toLex] <;> simp






theorem ear_tromino_nonvacuous :
    ∃ c ∈ pc2_tromino, c ≠ origin 2 ∧
      (∃ n ∉ pc2_tromino, (hypercubicLattice 2).Adj c n) ∧
      CellConnected ((↑pc2_tromino : Set (Site 2)) \ {c}) := by
  classical
  have hne : (![0, 1] : Site 2) ≠ origin 2 := by
    rw [origin_eq_zerozero]; intro h; have := congrFun h 1; simp at this
  
  have hpend : jc_IsPendantCell (↑pc2_tromino : Set (Site 2)) ![0, 1] := by
    refine ⟨by rw [pc2_mem_tromino]; tauto, ![0, 0], ⟨by rw [pc2_mem_tromino]; tauto, ?_⟩, ?_⟩
    · rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
    · rintro w ⟨hwK, hadj⟩
      obtain ⟨p, q, rfl⟩ : ∃ p q, w = ![p, q] := ⟨w 0, w 1, by funext i; fin_cases i <;> rfl⟩
      rw [pc2_mem_tromino] at hwK
      rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
      rcases hwK with ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩ <;> subst hp <;> subst hq <;>
        revert hadj <;> decide
  refine ⟨![0, 1], by rw [← Finset.mem_coe, pc2_mem_tromino]; tauto, hne,
    ?_, ?_⟩
  · obtain ⟨n, hn, hadj⟩ := ear_globalExtreme_boundary (↑pc2_tromino : Set (Site 2)) ![0, 1]
      ear_tromino_globalExtreme
    exact ⟨n, fun hc => hn (Finset.mem_coe.mpr hc), hadj⟩
  exact jc_cellConnected_diff_of_pendant (↑pc2_tromino : Set (Site 2)) ![0, 1]
    (nbc_cellConnected_of_isConnectedCluster pc2_tromino_isConnectedCluster) hpend

end Walls

end StatMech
