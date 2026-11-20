/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































import Mathlib
import Code.Lattice.Clusters

open Set SimpleGraph Finset
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Walls

variable {d : ℕ}








theorem bc4_adj_origin_sum (n : Site d) (h : (hypercubicLattice d).Adj 0 n) :
    ∑ j, (n j).natAbs = 1 := by
  rw [hypercubicLattice_adj] at h
  simpa [Int.natAbs_neg] using h



theorem bc4_witness_coord (n : Site d) (h : ∑ j, (n j).natAbs = 1) :
    ∃ i, (n i = 1 ∨ n i = -1) ∧ ∀ j, j ≠ i → n j = 0 := by
  
  obtain ⟨i, _, hzero⟩ : ∃ i ∈ Finset.univ, (n i).natAbs ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_and, ne_eq, not_not, Finset.mem_univ,
      forall_true_left] at hcon
    have : ∑ j, (n j).natAbs = 0 := Finset.sum_eq_zero (fun j _ => hcon j)
    omega
  
  have hni1 : (n i).natAbs = 1 := by
    have hle : (n i).natAbs ≤ ∑ j, (n j).natAbs :=
      Finset.single_le_sum (f := fun j => (n j).natAbs)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [h] at hle; omega
  refine ⟨i, ?_, ?_⟩
  · rcases Int.natAbs_eq_iff.mp hni1 with h1 | h1
    · left; simpa using h1
    · right; simpa using h1
  · 
    intro j hj
    by_contra hnj
    have hjpos : (n j).natAbs ≥ 1 := by
      have := Int.natAbs_eq_zero.not.mpr hnj; omega
    have hsub : ({i, j} : Finset (Fin d)) ⊆ Finset.univ := fun k _ => Finset.mem_univ k
    have hpair : ∑ k ∈ ({i, j} : Finset (Fin d)), (n k).natAbs
        = (n i).natAbs + (n j).natAbs := Finset.sum_pair (Ne.symm hj)
    have hbig : ∑ k ∈ ({i, j} : Finset (Fin d)), (n k).natAbs ≤ ∑ k, (n k).natAbs :=
      Finset.sum_le_sum_of_subset hsub
    rw [hpair, h] at hbig; omega






theorem bc4_openNbr_adj (ω : ConfigSpace (Sym2 (Site d))) {n : Site d}
    (hn : (openSubgraph d ω).Adj 0 n) : (hypercubicLattice d).Adj 0 n := hn.1



theorem bc4_openNbr_mem_box_one (ω : ConfigSpace (Sym2 (Site d))) {n : Site d}
    (hn : (openSubgraph d ω).Adj 0 n) : n ∈ box d 1 := by
  rw [mem_box]
  intro i
  have hadj : (hypercubicLattice d).Adj 0 n := bc4_openNbr_adj ω hn
  rw [hypercubicLattice_adj] at hadj
  
  have hle : ((0 : Site d) i - n i).natAbs ≤ ∑ j, ((0 : Site d) j - n j).natAbs :=
    Finset.single_le_sum (f := fun j => ((0 : Site d) j - n j).natAbs)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  rw [hadj] at hle
  simpa using hle


theorem bc4_origin_openNeighbours_subset_box (ω : ConfigSpace (Sym2 (Site d))) :
    {n : Site d | (openSubgraph d ω).Adj 0 n} ⊆ box d 1 :=
  fun _ hn => bc4_openNbr_mem_box_one ω hn





theorem bc4_origin_openNeighbours_finite (ω : ConfigSpace (Sym2 (Site d))) :
    {n : Site d | (openSubgraph d ω).Adj 0 n}.Finite :=
  (box_finite d 1).subset (bc4_origin_openNeighbours_subset_box ω)











noncomputable def bc4_nbrKey [NeZero d] (n : Site d) : Fin d × Bool := by
  classical
  by_cases h : ∑ j, (n j).natAbs = 1
  · exact ((bc4_witness_coord n h).choose,
      decide (n ((bc4_witness_coord n h).choose) = 1))
  · exact (⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩, false)


theorem bc4_nbrKey_eq [NeZero d] (n : Site d) (h : ∑ j, (n j).natAbs = 1) :
    bc4_nbrKey n
      = ((bc4_witness_coord n h).choose,
         decide (n ((bc4_witness_coord n h).choose) = 1)) := by
  simp only [bc4_nbrKey]; rw [dif_pos h]


theorem bc4_nbrKey_witness [NeZero d] (n : Site d) (h : ∑ j, (n j).natAbs = 1) :
    (n (bc4_nbrKey n).1 = 1 ∨ n (bc4_nbrKey n).1 = -1)
      ∧ (∀ j, j ≠ (bc4_nbrKey n).1 → n j = 0)
      ∧ (bc4_nbrKey n).2 = decide (n (bc4_nbrKey n).1 = 1) := by
  rw [bc4_nbrKey_eq n h]
  exact ⟨(bc4_witness_coord n h).choose_spec.1,
    (bc4_witness_coord n h).choose_spec.2, rfl⟩



theorem bc4_nbr_eq_of_key {n m : Site d} {i : Fin d}
    (hn1 : n i = 1 ∨ n i = -1) (hnz : ∀ j, j ≠ i → n j = 0)
    (hm1 : m i = 1 ∨ m i = -1) (hmz : ∀ j, j ≠ i → m j = 0)
    (hsign : decide (n i = 1) = decide (m i = 1)) : n = m := by
  
  have hsig : (n i = 1) ↔ (m i = 1) := by
    constructor <;> intro h <;> simp_all
  funext j
  by_cases hj : j = i
  · subst hj
    rcases hn1 with h | h <;> rcases hm1 with h' | h' <;> simp_all
  · rw [hnz j hj, hmz j hj]


theorem bc4_nbrKey_injOn [NeZero d] :
    Set.InjOn bc4_nbrKey {n : Site d | (hypercubicLattice d).Adj 0 n} := by
  intro n hn m hm hkey
  have hns : ∑ j, (n j).natAbs = 1 := bc4_adj_origin_sum n hn
  have hms : ∑ j, (m j).natAbs = 1 := bc4_adj_origin_sum m hm
  obtain ⟨hn1, hnz, hnsgn⟩ := bc4_nbrKey_witness n hns
  obtain ⟨hm1, hmz, hmsgn⟩ := bc4_nbrKey_witness m hms
  
  have hi : (bc4_nbrKey n).1 = (bc4_nbrKey m).1 := by rw [hkey]
  
  rw [hi] at hn1 hnz hnsgn
  set j := (bc4_nbrKey m).1 with hjdef
  have hsgn : decide (n j = 1) = decide (m j = 1) := by
    rw [← hnsgn, ← hmsgn, hkey]
  exact bc4_nbr_eq_of_key hn1 hnz hm1 hmz hsgn



theorem bc4_origin_latticeNeighbours_ncard_le_pos [NeZero d] :
    {n : Site d | (hypercubicLattice d).Adj 0 n}.ncard ≤ 2 * d := by
  classical
  have hinj := bc4_nbrKey_injOn (d := d)
  
  rw [← hinj.ncard_image]
  have hsub : bc4_nbrKey '' {n : Site d | (hypercubicLattice d).Adj 0 n}
      ⊆ (Set.univ : Set (Fin d × Bool)) := Set.subset_univ _
  calc (bc4_nbrKey '' {n : Site d | (hypercubicLattice d).Adj 0 n}).ncard
      ≤ (Set.univ : Set (Fin d × Bool)).ncard :=
        Set.ncard_le_ncard hsub Set.finite_univ
    _ = Fintype.card (Fin d × Bool) := by
        rw [Set.ncard_univ]; simp [Nat.card_eq_fintype_card]
    _ = 2 * d := by simp [Fintype.card_prod, mul_comm]




theorem bc4_origin_latticeNeighbours_ncard_le :
    {n : Site d | (hypercubicLattice d).Adj 0 n}.ncard ≤ 2 * d := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    
    have : {n : Site 0 | (hypercubicLattice 0).Adj 0 n} = ∅ := by
      ext n
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hadj
      have := bc4_adj_origin_sum n hadj
      simp at this
    rw [this]; simp
  · haveI : NeZero d := ⟨hd.ne'⟩
    exact bc4_origin_latticeNeighbours_ncard_le_pos



theorem bc4_origin_openNeighbours_ncard_le (ω : ConfigSpace (Sym2 (Site d))) :
    {n : Site d | (openSubgraph d ω).Adj 0 n}.ncard ≤ 2 * d := by
  refine le_trans (Set.ncard_le_ncard ?_ ?_) bc4_origin_latticeNeighbours_ncard_le
  · intro n hn; exact bc4_openNbr_adj ω hn
  · 
    apply (box_finite d 1).subset
    intro n hn
    rw [mem_box]
    intro i
    have hadj : (hypercubicLattice d).Adj 0 n := hn
    rw [hypercubicLattice_adj] at hadj
    have hle : ((0 : Site d) i - n i).natAbs ≤ ∑ j, ((0 : Site d) j - n j).natAbs :=
      Finset.single_le_sum (f := fun j => ((0 : Site d) j - n j).natAbs)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [hadj] at hle
    simpa using hle

end Walls

end StatMech
