/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































import Mathlib
import Code.Percolation.HrouteHighDim

open Set
open StatMech.Lattice StatMech.Percolation

namespace StatMech

namespace Walls

variable {d : ℕ}









lemma bc7_adj_exists_unique_diff {x y : Site d} (hadj : (hypercubicLattice d).Adj x y) :
    ∃ k : Fin d, (x k - y k).natAbs = 1 ∧ ∀ i, i ≠ k → x i = y i := by
  rw [hypercubicLattice_adj] at hadj
  
  have hk : ∃ k, (x k - y k).natAbs = 1 := by
    by_contra h
    push Not at h
    have hzero : ∀ i ∈ (Finset.univ : Finset (Fin d)), (x i - y i).natAbs = 0 := by
      intro i _
      have hle : (x i - y i).natAbs ≤ ∑ j, (x j - y j).natAbs :=
        Finset.single_le_sum (f := fun j => (x j - y j).natAbs) (by intros; positivity)
          (Finset.mem_univ i)
      have := h i
      omega
    rw [Finset.sum_eq_zero hzero] at hadj
    exact absurd hadj (by norm_num)
  obtain ⟨k, hk⟩ := hk
  refine ⟨k, hk, ?_⟩
  
  intro i hik
  have hsplit : (x k - y k).natAbs + ∑ j ∈ Finset.univ.erase k, (x j - y j).natAbs = 1 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)] at hadj
    omega
  have hi0 : (x i - y i).natAbs = 0 := by
    have hle := Finset.single_le_sum (f := fun j => (x j - y j).natAbs)
      (s := Finset.univ.erase k) (by intros; positivity)
      (Finset.mem_erase.mpr ⟨hik, Finset.mem_univ i⟩)
    simp only at hle
    omega
  have : x i - y i = 0 := Int.natAbs_eq_zero.mp hi0
  omega












lemma bc7_rayPt_offBox_neighbor {a : Fin d} {N s : ℕ} (hs1 : 1 ≤ s) (hsN : s ≤ N)
    {v : Site d} (hadj : (hypercubicLattice d).Adj (hrHD_rayPt a (s : ℤ)) v)
    (hvbox : v ∉ box d N) :
    s = N ∧ v = hrHD_rayPt a ((s : ℤ) + 1) := by
  obtain ⟨k, hk1, hkrest⟩ := bc7_adj_exists_unique_diff hadj
  set u : Site d := hrHD_rayPt a (s : ℤ) with hu
  by_cases hka : k = a
  · 
    subst hka
    
    have hvi : ∀ i, i ≠ k → v i = 0 := by
      intro i hi; rw [← hkrest i hi, hu, hrHD_rayPt_of_ne k (s : ℤ) hi]
    have huk : u k = (s : ℤ) := by rw [hu, hrHD_rayPt_self]
    rw [huk] at hk1
    
    have hcase : v k = (s : ℤ) + 1 ∨ v k = (s : ℤ) - 1 := by omega
    rcases hcase with hvk | hvk
    · 
      have hveq : v = hrHD_rayPt k ((s : ℤ) + 1) := by
        funext i
        by_cases hi : i = k
        · subst hi; rw [hvk, hrHD_rayPt_self]
        · rw [hvi i hi, hrHD_rayPt_of_ne k ((s : ℤ) + 1) hi]
      refine ⟨?_, hveq⟩
      rw [mem_box, not_forall] at hvbox
      obtain ⟨j, hj⟩ := hvbox
      by_cases hjk : j = k
      · subst hjk
        rw [hvk] at hj
        have hnat : ((s : ℤ) + 1).natAbs = s + 1 := by omega
        rw [hnat] at hj; omega
      · rw [hvi j hjk] at hj; simp at hj
    · 
      exfalso
      apply hvbox; rw [mem_box]
      intro i
      by_cases hi : i = k
      · subst hi; rw [hvk]
        rcases Nat.eq_zero_or_pos s with h0 | hpos
        · omega
        · have : ((s : ℤ) - 1).natAbs = s - 1 := by omega
          omega
      · rw [hvi i hi]; simp
  · 
    exfalso
    apply hvbox; rw [mem_box]
    intro i
    by_cases hia : i = a
    · 
      have hik : i ≠ k := by rw [hia]; exact fun h => hka h.symm
      rw [← hkrest i hik, hu, hia, hrHD_rayPt_self]
      simpa using hsN
    · by_cases hik : i = k
      · 
        subst hik
        have hui : u i = 0 := by rw [hu, hrHD_rayPt_of_ne a (s : ℤ) hia]
        rw [hui] at hk1
        have h1 : (v i).natAbs = 1 := by simpa using hk1
        omega
      · 
        rw [← hkrest i hik, hu, hrHD_rayPt_of_ne a (s : ℤ) hia]; simp





lemma bc7_offBox_neighbor_eq_succ_rayPt {a : Fin d} {N s : ℕ} (hs1 : 1 ≤ s) (hsN : s ≤ N)
    {v : Site d} (hadj : (hypercubicLattice d).Adj (hrHD_rayPt a (s : ℤ)) v)
    (hvbox : v ∉ box d N) :
    v = hrHD_rayPt a ((s : ℤ) + 1) :=
  (bc7_rayPt_offBox_neighbor hs1 hsN hadj hvbox).2



lemma bc7_offBox_neighbor_forces_farEnd {a : Fin d} {N s : ℕ} (hs1 : 1 ≤ s) (hsN : s ≤ N)
    {v : Site d} (hadj : (hypercubicLattice d).Adj (hrHD_rayPt a (s : ℤ)) v)
    (hvbox : v ∉ box d N) :
    s = N :=
  (bc7_rayPt_offBox_neighbor hs1 hsN hadj hvbox).1

end Walls

end StatMech
