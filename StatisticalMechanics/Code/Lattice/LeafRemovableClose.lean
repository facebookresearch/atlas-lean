/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.StraightWalk
import Code.Lattice.FiniteComplementConnected
import Code.Lattice.FloodFillConnected
import Code.Lattice.ArcNoSeparation
import Code.Lattice.ArcExteriorClose
import Code.Lattice.UniqueInfiniteComponent

open Set SimpleGraph

namespace StatMech

namespace Lattice









theorem lrc_farLeft_offS {S : Set (Site 2)} {b : ℤ} (hb : ∀ q ∈ S, b ≤ q 0)
    {z : Site 2} (hz : z 0 ≤ b - 1) : z ∉ S := by
  intro hzS
  have := hb z hzS
  omega





theorem lrc_reachesFarLeft_offS {S : Set (Site 2)} (hS : arcns_OffSupportConnected S)
    {b : ℤ} (hb : ∀ q ∈ S, b ≤ q 0) {x : Site 2} (hx : x ∉ S) :
    ∃ p : (hypercubicLattice 2).Walk x ![b - 1, x 1], (∀ w ∈ p.support, w ∉ S) := by
  have hc : (![b - 1, x 1] : Site 2) ∉ S :=
    lrc_farLeft_offS hb (z := ![b - 1, x 1]) (by simp)
  exact arcns_walk_of_connected hS hx hc























def lrc_ringS : Set (Site 2) :=
  {![1, 1], ![1, -1], ![0, 1], ![0, -1], ![-1, 1], ![-1, 0], ![-1, -1]}


def lrc_uPrime : Site 2 := ![1, 0]



theorem lrc_cell_ne {a b c d : ℤ} (h : a ≠ c ∨ b ≠ d) : (![a, b] : Site 2) ≠ ![c, d] := by
  intro he
  rcases h with h | h
  · exact h (by have := congrFun he 0; simpa using this)
  · exact h (by have := congrFun he 1; simpa using this)


theorem lrc_uPrime_not_mem : lrc_uPrime ∉ lrc_ringS := by
  simp only [lrc_uPrime, lrc_ringS, Set.mem_insert_iff, Set.mem_singleton_iff]
  push_neg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply lrc_cell_ne <;> omega




theorem lrc_origin_neighbours_in_barrier :
    (![1, 0] : Site 2) ∈ insert lrc_uPrime lrc_ringS ∧
    (![-1, 0] : Site 2) ∈ insert lrc_uPrime lrc_ringS ∧
    (![0, 1] : Site 2) ∈ insert lrc_uPrime lrc_ringS ∧
    (![0, -1] : Site 2) ∈ insert lrc_uPrime lrc_ringS := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · simp only [lrc_uPrime, lrc_ringS, Set.mem_insert_iff, Set.mem_singleton_iff]; tauto


theorem lrc_origin_off_barrier : (![0, 0] : Site 2) ∉ insert lrc_uPrime lrc_ringS := by
  simp only [lrc_uPrime, lrc_ringS, Set.mem_insert_iff, Set.mem_singleton_iff]
  push_neg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply lrc_cell_ne <;> omega


theorem lrc_east_off_barrier : (![2, 0] : Site 2) ∉ insert lrc_uPrime lrc_ringS := by
  simp only [lrc_uPrime, lrc_ringS, Set.mem_insert_iff, Set.mem_singleton_iff]
  push_neg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply lrc_cell_ne <;> omega



theorem lrc_adj_origin_cases {z : Site 2} (h : (hypercubicLattice 2).Adj ![0, 0] z) :
    z = ![1, 0] ∨ z = ![-1, 0] ∨ z = ![0, 1] ∨ z = ![0, -1] := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
  
  have hez : z = ![z 0, z 1] := by ext i; fin_cases i <;> simp
  have : (z 0 = 1 ∧ z 1 = 0) ∨ (z 0 = -1 ∧ z 1 = 0) ∨
      (z 0 = 0 ∧ z 1 = 1) ∨ (z 0 = 0 ∧ z 1 = -1) := by omega
  rcases this with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;>
    [ (left); (right; left); (right; right; left); (right; right; right) ] <;>
    · rw [hez, a, b]



theorem lrc_origin_isolated {z : Site 2} :
    ¬ (ffc_offSupportLattice (insert lrc_uPrime lrc_ringS)).Adj ![0, 0] z := by
  rw [ffc_offSupportLattice_adj]
  rintro ⟨hadj, _, hz⟩
  obtain ⟨h1, h2, h3, h4⟩ := lrc_origin_neighbours_in_barrier
  rcases lrc_adj_origin_cases hadj with rfl | rfl | rfl | rfl
  · exact hz h1
  · exact hz h2
  · exact hz h3
  · exact hz h4



theorem lrc_eq_of_walk_from_isolated {V : Type*} {G : SimpleGraph V} {a b : V}
    (w : G.Walk a b) (hiso : ∀ z, ¬ G.Adj a z) : a = b := by
  cases w with
  | nil => rfl
  | cons hadj _ => exact absurd hadj (hiso _)




theorem lrc_origin_not_reachable_east :
    ¬ (ffc_offSupportLattice (insert lrc_uPrime lrc_ringS)).Reachable ![0, 0] ![2, 0] := by
  rintro ⟨w⟩
  have hne : (![0, 0] : Site 2) ≠ ![2, 0] := lrc_cell_ne (by left; omega)
  exact hne (lrc_eq_of_walk_from_isolated w (fun z => lrc_origin_isolated))



theorem lrc_insert_not_connected :
    ¬ arcns_OffSupportConnected (insert lrc_uPrime lrc_ringS) := by
  intro hconn
  exact lrc_origin_not_reachable_east
    (hconn ![0, 0] ![2, 0] lrc_origin_off_barrier lrc_east_off_barrier)
















theorem lrc_ringS_subset_box : lrc_ringS ⊆ box 2 1 := by
  intro z hz
  simp only [lrc_ringS, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rw [mem_box]
  intro i
  fin_cases i <;>
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide



theorem lrc_box_off_ring_cases {z : Site 2} (hbox : z ∈ box 2 1) (hoff : z ∉ lrc_ringS) :
    z = ![0, 0] ∨ z = ![1, 0] := by
  rw [mem_box] at hbox
  have h0 := hbox 0
  have h1 := hbox 1
  
  have hc0 : z 0 = -1 ∨ z 0 = 0 ∨ z 0 = 1 := by omega
  have hc1 : z 1 = -1 ∨ z 1 = 0 ∨ z 1 = 1 := by omega
  have hez : z = ![z 0, z 1] := by ext i; fin_cases i <;> simp
  simp only [lrc_ringS, Set.mem_insert_iff, Set.mem_singleton_iff] at hoff
  push_neg at hoff
  obtain ⟨n11, n1m1, n01, n0m1, nm11, nm10, nm1m1⟩ := hoff
  
  have mk : ∀ a b : ℤ, z 0 = a → z 1 = b → z = ![a, b] := by
    intro a b ha hb; rw [hez, ha, hb]
  rcases hc0 with e0 | e0 | e0 <;> rcases hc1 with e1 | e1 | e1 <;>
    first
      | (left; exact mk _ _ e0 e1)
      | (right; exact mk _ _ e0 e1)
      | (exfalso; first
          | (exact n11 (mk _ _ e0 e1)) | (exact n1m1 (mk _ _ e0 e1))
          | (exact n01 (mk _ _ e0 e1)) | (exact n0m1 (mk _ _ e0 e1))
          | (exact nm11 (mk _ _ e0 e1)) | (exact nm10 (mk _ _ e0 e1))
          | (exact nm1m1 (mk _ _ e0 e1)))




theorem lrc_row0_clear {c t : ℤ} (hc : 0 ≤ c) (ht : t ∈ Set.uIcc c (1 + 1 : ℤ)) :
    (![t, 0] : Site 2) ∉ lrc_ringS := by
  rw [Set.mem_uIcc] at ht
  have htge : 0 ≤ t := by omega
  simp only [lrc_ringS, Set.mem_insert_iff, Set.mem_singleton_iff]
  push_neg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply lrc_cell_ne <;> omega




theorem lrc_origin_reachesExterior :
    ∃ (e : Site 2) (p : (hypercubicLattice 2).Walk ![0, 0] e),
      (∀ w ∈ p.support, w ∉ lrc_ringS) ∧ e ∈ exterior 2 1 := by
  refine arcxc_reachesExterior_of_rowClear (z := ![0, 0]) ?_
  intro t ht hmem
  simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero] at ht
  exact lrc_row0_clear (by norm_num) ht hmem


theorem lrc_gap_reachesExterior :
    ∃ (e : Site 2) (p : (hypercubicLattice 2).Walk ![1, 0] e),
      (∀ w ∈ p.support, w ∉ lrc_ringS) ∧ e ∈ exterior 2 1 := by
  refine arcxc_reachesExterior_of_rowClear (z := ![1, 0]) ?_
  intro t ht hmem
  simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero] at ht
  exact lrc_row0_clear (by norm_num) ht hmem




theorem lrc_ring_reachesExterior : arcxc_ReachesExterior lrc_ringS 1 := by
  refine ⟨lrc_ringS_subset_box, ?_⟩
  intro x hx
  by_cases hbox : x ∈ box 2 1
  · rcases lrc_box_off_ring_cases hbox hx with rfl | rfl
    · exact lrc_origin_reachesExterior
    · exact lrc_gap_reachesExterior
  · 
    have hxext : x ∈ exterior 2 1 := by
      rw [exterior_eq_compl_box]; exact hbox
    exact ⟨x, SimpleGraph.Walk.nil, by
      intro w hw; rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw; exact hw ▸ hx,
      hxext⟩




theorem lrc_ring_connected : arcns_OffSupportConnected lrc_ringS :=
  arcxc_connected_of_reachesExterior lrc_ring_reachesExterior















theorem lrc_leafRemovable_false :
    ¬ arcns_LeafRemovable lrc_ringS lrc_uPrime := by
  intro hres
  exact lrc_insert_not_connected (hres lrc_ring_connected)



















theorem lrc_leafRemovable_of_reachesFarLeft {S : Set (Site 2)} {u' : Site 2}
    (h : arcns_ReachesFarLeft (insert u' S)) : arcns_LeafRemovable S u' :=
  fun _ => arcns_connected_of_reachesFarLeft h






theorem lrc_leafRemovable_of_reachesExterior {S : Set (Site 2)} {u' : Site 2} {R : ℕ}
    (h : arcxc_ReachesExterior (insert u' S) R) : arcns_LeafRemovable S u' :=
  fun _ => arcxc_connected_of_reachesExterior h








theorem lrc_reduction_nonvacuous :
    arcns_LeafRemovable (∅ : Set (Site 2)) ![0, 0] := by
  have hu : (![0, 0] : Site 2) ∈ box 2 0 := by rw [mem_box]; intro i; fin_cases i <;> decide
  have hreach : arcxc_ReachesExterior (insert (![0, 0] : Site 2) (∅ : Set (Site 2))) 0 := by
    have hins : insert (![0, 0] : Site 2) (∅ : Set (Site 2)) = ({![0, 0]} : Set (Site 2)) := by
      simp
    rw [hins]
    exact arcxc_singlePoint_reachesExterior ![0, 0] hu
  exact lrc_leafRemovable_of_reachesExterior hreach






























end Lattice

end StatMech
