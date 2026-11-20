/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.CrossingParity
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.JordanInteriorLib
import Code.Lattice.MatchedConnectivityInterior
import Code.Lattice.KingStepConnectClose
import Code.Lattice.KingNoSeparationClose
import Code.Lattice.EscapeThickPointClose
import Code.Lattice.EscapeWallThickClose
import Code.Lattice.GlobalThickPointClose
import Code.Lattice.CrossArcThickClose
import Code.Lattice.KingSegmentDownClose
import Code.Lattice.RowLinkedClose
import Code.Lattice.SegmentDownClose

open Set SimpleGraph Function

namespace StatMech

namespace Lattice









noncomputable def wpc_fig8 : (hypercubicLattice 2).Walk ![(2:ℤ),(2:ℤ)] ![(2:ℤ),(2:ℤ)] :=
  let a1 : (hypercubicLattice 2).Walk ![(2:ℤ),2] ![0,2] :=
    ((jec_hsegRight 2 0 2).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  let a2 : (hypercubicLattice 2).Walk ![(0:ℤ),2] ![0,0] :=
    ((jec_vsegUp 0 0 2).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  let a3 : (hypercubicLattice 2).Walk ![(0:ℤ),0] ![2,0] :=
    (jec_hsegRight 0 0 2).copy rfl (by ext i; fin_cases i <;> simp)
  let a4 : (hypercubicLattice 2).Walk ![(2:ℤ),0] ![2,2] :=
    (jec_vsegUp 2 0 2).copy rfl (by ext i; fin_cases i <;> simp)
  let b1 : (hypercubicLattice 2).Walk ![(2:ℤ),2] ![4,2] :=
    (jec_hsegRight 2 2 2).copy rfl (by ext i; fin_cases i <;> simp)
  let b2 : (hypercubicLattice 2).Walk ![(4:ℤ),2] ![4,4] :=
    (jec_vsegUp 4 2 2).copy rfl (by ext i; fin_cases i <;> simp)
  let b3 : (hypercubicLattice 2).Walk ![(4:ℤ),4] ![2,4] :=
    ((jec_hsegRight 4 2 2).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  let b4 : (hypercubicLattice 2).Walk ![(2:ℤ),4] ![2,2] :=
    ((jec_vsegUp 2 2 2).copy rfl (by ext i; fin_cases i <;> simp)).reverse
  (a1.append (a2.append (a3.append a4))).append (b1.append (b2.append (b3.append b4)))





theorem wpc_fig8_raycount (z : Site 2) :
    jec_rayCount z wpc_fig8 =
      (if 0 ≤ z 0 - 1 ∧ 0 ≤ z 1 - 1 ∧ z 1 - 1 ≤ 0 + (2:ℤ) - 1 then 1 else 0)
      + (if 2 ≤ z 0 - 1 ∧ 0 ≤ z 1 - 1 ∧ z 1 - 1 ≤ 0 + (2:ℤ) - 1 then 1 else 0)
      + (if 4 ≤ z 0 - 1 ∧ 2 ≤ z 1 - 1 ∧ z 1 - 1 ≤ 2 + (2:ℤ) - 1 then 1 else 0)
      + (if 2 ≤ z 0 - 1 ∧ 2 ≤ z 1 - 1 ∧ z 1 - 1 ≤ 2 + (2:ℤ) - 1 then 1 else 0) := by
  unfold wpc_fig8
  simp only [jec_rayCount_append, jec_rayCount_copy, jec_rayCount_reverse,
    jec_rayCount_vsegUp, jec_rayCount_hsegRight]
  push_cast; ring_nf







theorem wpc_fig8_support_locus (p : Site 2) (hp : p ∈ wpc_fig8.support) :
      (p 1 = 2 ∧ 0 ≤ p 0 ∧ p 0 ≤ 2) ∨ (p 0 = 0 ∧ 0 ≤ p 1 ∧ p 1 ≤ 2) ∨
      (p 1 = 0 ∧ 0 ≤ p 0 ∧ p 0 ≤ 2) ∨ (p 0 = 2 ∧ 0 ≤ p 1 ∧ p 1 ≤ 2) ∨
      (p 1 = 2 ∧ 2 ≤ p 0 ∧ p 0 ≤ 4) ∨ (p 0 = 4 ∧ 2 ≤ p 1 ∧ p 1 ≤ 4) ∨
      (p 1 = 4 ∧ 2 ≤ p 0 ∧ p 0 ≤ 4) ∨ (p 0 = 2 ∧ 2 ≤ p 1 ∧ p 1 ≤ 4) := by
  unfold wpc_fig8 at hp
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse] at hp
  rcases hp with (h|h|h|h)|h|h|h|h
  · obtain ⟨a, b, c⟩ := jec_hsegRight_support 2 0 2 h; push_cast at *; omega
  · obtain ⟨a, b, c⟩ := jec_vsegUp_support 0 0 2 h; push_cast at *; omega
  · obtain ⟨a, b, c⟩ := jec_hsegRight_support 0 0 2 h; push_cast at *; omega
  · obtain ⟨a, b, c⟩ := jec_vsegUp_support 2 0 2 h; push_cast at *; omega
  · obtain ⟨a, b, c⟩ := jec_hsegRight_support 2 2 2 h; push_cast at *; omega
  · obtain ⟨a, b, c⟩ := jec_vsegUp_support 4 2 2 h; push_cast at *; omega
  · obtain ⟨a, b, c⟩ := jec_hsegRight_support 4 2 2 h; push_cast at *; omega
  · obtain ⟨a, b, c⟩ := jec_vsegUp_support 2 2 2 h; push_cast at *; omega


theorem wpc_fig8_off_11 : (![1, 1] : Site 2) ∉ wpc_fig8.support := by
  intro h; have := wpc_fig8_support_locus _ h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this; omega


theorem wpc_fig8_off_33 : (![3, 3] : Site 2) ∉ wpc_fig8.support := by
  intro h; have := wpc_fig8_support_locus _ h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this; omega


theorem wpc_fig8_interior_11 : (![1, 1] : Site 2) ∈ jec_leftRegion wpc_fig8 := by
  rw [jec_mem_leftRegion, wpc_fig8_raycount]; decide


theorem wpc_fig8_interior_33 : (![3, 3] : Site 2) ∈ jec_leftRegion wpc_fig8 := by
  rw [jec_mem_leftRegion, wpc_fig8_raycount]; decide


theorem wpc_fig8_mem_interior_11 : (![1, 1] : Site 2) ∈ jil_offSupportInterior wpc_fig8 :=
  (jil_mem_offSupportInterior wpc_fig8 _).mpr ⟨wpc_fig8_off_11, wpc_fig8_interior_11⟩


theorem wpc_fig8_mem_interior_33 : (![3, 3] : Site 2) ∈ jil_offSupportInterior wpc_fig8 :=
  (jil_mem_offSupportInterior wpc_fig8 _).mpr ⟨wpc_fig8_off_33, wpc_fig8_interior_33⟩



set_option maxHeartbeats 1000000 in


theorem wpc_support_cells (p : Site 2) (hp : p ∈ wpc_fig8.support) :
    p = (![0,0]:Site 2) ∨ p = (![1,0]:Site 2) ∨ p = (![2,0]:Site 2) ∨ p = (![0,1]:Site 2) ∨
    p = (![2,1]:Site 2) ∨ p = (![0,2]:Site 2) ∨ p = (![1,2]:Site 2) ∨ p = (![2,2]:Site 2) ∨
    p = (![3,2]:Site 2) ∨ p = (![4,2]:Site 2) ∨ p = (![2,3]:Site 2) ∨ p = (![4,3]:Site 2) ∨
    p = (![2,4]:Site 2) ∨ p = (![3,4]:Site 2) ∨ p = (![4,4]:Site 2) := by
  have hl := wpc_fig8_support_locus p hp
  have toCell : ∀ a b : ℤ, p 0 = a → p 1 = b → p = (![a, b] : Site 2) := by
    intro a b h0 h1; ext i; fin_cases i <;> simp [h0, h1]
  have hpair : (p 0 = 0 ∧ p 1 = 0) ∨ (p 0 = 1 ∧ p 1 = 0) ∨ (p 0 = 2 ∧ p 1 = 0) ∨
      (p 0 = 0 ∧ p 1 = 1) ∨ (p 0 = 2 ∧ p 1 = 1) ∨ (p 0 = 0 ∧ p 1 = 2) ∨
      (p 0 = 1 ∧ p 1 = 2) ∨ (p 0 = 2 ∧ p 1 = 2) ∨ (p 0 = 3 ∧ p 1 = 2) ∨
      (p 0 = 4 ∧ p 1 = 2) ∨ (p 0 = 2 ∧ p 1 = 3) ∨ (p 0 = 4 ∧ p 1 = 3) ∨
      (p 0 = 2 ∧ p 1 = 4) ∨ (p 0 = 3 ∧ p 1 = 4) ∨ (p 0 = 4 ∧ p 1 = 4) := by
    rcases hl with h|h|h|h|h|h|h|h <;> omega
  rcases hpair with ⟨h0,h1⟩|⟨h0,h1⟩|⟨h0,h1⟩|⟨h0,h1⟩|⟨h0,h1⟩|⟨h0,h1⟩|⟨h0,h1⟩|⟨h0,h1⟩|⟨h0,h1⟩|⟨h0,h1⟩|⟨h0,h1⟩|⟨h0,h1⟩|⟨h0,h1⟩|⟨h0,h1⟩|⟨h0,h1⟩ <;>
    [ exact Or.inl (toCell _ _ h0 h1);
      exact Or.inr (Or.inl (toCell _ _ h0 h1));
      exact Or.inr (Or.inr (Or.inl (toCell _ _ h0 h1)));
      exact Or.inr (Or.inr (Or.inr (Or.inl (toCell _ _ h0 h1))));
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (toCell _ _ h0 h1)))));
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (toCell _ _ h0 h1))))));
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (toCell _ _ h0 h1)))))));
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (toCell _ _ h0 h1))))))));
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (toCell _ _ h0 h1)))))))));
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (toCell _ _ h0 h1))))))))));
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (toCell _ _ h0 h1)))))))))));
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (toCell _ _ h0 h1))))))))))));
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (toCell _ _ h0 h1)))))))))))));
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (toCell _ _ h0 h1))))))))))))));
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (toCell _ _ h0 h1))))))))))))) ) ]







set_option maxHeartbeats 1000000 in


theorem wpc_edges_mem : ∀ e : Sym2 (Site 2),
    (e = s((![0,2]:Site 2),(![1,2]:Site 2)) ∨ e = s((![1,2]:Site 2),(![2,2]:Site 2)) ∨
     e = s((![0,0]:Site 2),(![0,1]:Site 2)) ∨ e = s((![0,1]:Site 2),(![0,2]:Site 2)) ∨
     e = s((![0,0]:Site 2),(![1,0]:Site 2)) ∨ e = s((![1,0]:Site 2),(![2,0]:Site 2)) ∨
     e = s((![2,0]:Site 2),(![2,1]:Site 2)) ∨ e = s((![2,1]:Site 2),(![2,2]:Site 2)) ∨
     e = s((![2,2]:Site 2),(![3,2]:Site 2)) ∨ e = s((![3,2]:Site 2),(![4,2]:Site 2)) ∨
     e = s((![4,2]:Site 2),(![4,3]:Site 2)) ∨ e = s((![4,3]:Site 2),(![4,4]:Site 2)) ∨
     e = s((![2,4]:Site 2),(![3,4]:Site 2)) ∨ e = s((![3,4]:Site 2),(![4,4]:Site 2)) ∨
     e = s((![2,2]:Site 2),(![2,3]:Site 2)) ∨ e = s((![2,3]:Site 2),(![2,4]:Site 2))) →
    e ∈ wpc_fig8.edges := by
  rintro e (h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h) <;> subst h <;> unfold wpc_fig8 <;>
    simp only [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_copy,
      SimpleGraph.Walk.edges_reverse, List.mem_append, List.mem_reverse]
  · left; left
    have := ksd_hsegRight_edge_mem' 2 0 2 0 (by norm_num) (by norm_num); simpa using this
  · left; left
    have := ksd_hsegRight_edge_mem' 2 0 2 1 (by norm_num) (by norm_num); simpa using this
  · left; right; left
    have := ksd_vsegUp_edge_mem' 0 0 2 0 (by norm_num) (by norm_num); simpa using this
  · left; right; left
    have := ksd_vsegUp_edge_mem' 0 0 2 1 (by norm_num) (by norm_num); simpa using this
  · left; right; right; left
    have := ksd_hsegRight_edge_mem' 0 0 2 0 (by norm_num) (by norm_num); simpa using this
  · left; right; right; left
    have := ksd_hsegRight_edge_mem' 0 0 2 1 (by norm_num) (by norm_num); simpa using this
  · left; right; right; right
    have := ksd_vsegUp_edge_mem' 2 0 2 0 (by norm_num) (by norm_num); simpa using this
  · left; right; right; right
    have := ksd_vsegUp_edge_mem' 2 0 2 1 (by norm_num) (by norm_num); simpa using this
  · right; left
    have := ksd_hsegRight_edge_mem' 2 2 2 2 (by norm_num) (by norm_num); simpa using this
  · right; left
    have := ksd_hsegRight_edge_mem' 2 2 2 3 (by norm_num) (by norm_num); simpa using this
  · right; right; left
    have := ksd_vsegUp_edge_mem' 4 2 2 2 (by norm_num) (by norm_num); simpa using this
  · right; right; left
    have := ksd_vsegUp_edge_mem' 4 2 2 3 (by norm_num) (by norm_num); simpa using this
  · right; right; right; left
    have := ksd_hsegRight_edge_mem' 4 2 2 2 (by norm_num) (by norm_num); simpa using this
  · right; right; right; left
    have := ksd_hsegRight_edge_mem' 4 2 2 3 (by norm_num) (by norm_num); simpa using this
  · right; right; right; right
    have := ksd_vsegUp_edge_mem' 2 2 2 2 (by norm_num) (by norm_num); simpa using this
  · right; right; right; right
    have := ksd_vsegUp_edge_mem' 2 2 2 3 (by norm_num) (by norm_num); simpa using this

set_option maxHeartbeats 4000000 in






theorem wpc_fig8_fourThin : mci_FourThin wpc_fig8 := by
  intro u v hu hv hadj
  have hu15 := wpc_support_cells u hu
  have hv15 := wpc_support_cells v hv
  apply wpc_edges_mem
  rcases hu15 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    rcases hv15 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      first
        | (exfalso; revert hadj; rw [hypercubicLattice_adj, Fin.sum_univ_two]; decide)
        | (revert hadj; decide)









theorem wpc_on_Arow0 (c : ℤ) (h1 : 0 ≤ c) (h2 : c ≤ 2) :
    (![c, 0] : Site 2) ∈ wpc_fig8.support := by
  unfold wpc_fig8
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse]
  left; right; right; left; exact sdc_hsegRight_mem' 0 0 2 c h1 h2


theorem wpc_on_Arow2 (c : ℤ) (h1 : 0 ≤ c) (h2 : c ≤ 2) :
    (![c, 2] : Site 2) ∈ wpc_fig8.support := by
  unfold wpc_fig8
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse]
  left; left; exact sdc_hsegRight_mem' 2 0 2 c h1 h2


theorem wpc_on_Acol0 (r : ℤ) (h1 : 0 ≤ r) (h2 : r ≤ 2) :
    (![0, r] : Site 2) ∈ wpc_fig8.support := by
  unfold wpc_fig8
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse]
  left; right; left; exact sdc_vsegUp_mem' 0 0 2 r h1 h2


theorem wpc_on_Acol2 (r : ℤ) (h1 : 0 ≤ r) (h2 : r ≤ 2) :
    (![2, r] : Site 2) ∈ wpc_fig8.support := by
  unfold wpc_fig8
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse]
  left; right; right; right; exact sdc_vsegUp_mem' 2 0 2 r h1 h2




theorem wpc_fig8_singleton_saturated :
    ksc_KingSaturated wpc_fig8 {(![1, 1] : Site 2)} := by
  rintro u v hu hvI hadj
  rw [Set.mem_singleton_iff] at hu ⊢
  subst hu
  exfalso
  obtain ⟨h0, h1, hne⟩ := hadj
  have hvoff := (jil_mem_offSupportInterior wpc_fig8 v |>.mp hvI).1
  apply hvoff
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  have hb0 : v 0 = 0 ∨ v 0 = 1 ∨ v 0 = 2 := by omega
  have hb1 : v 1 = 0 ∨ v 1 = 1 ∨ v 1 = 2 := by omega
  have hveq : v = ![v 0, v 1] := by ext i; fin_cases i <;> simp
  rw [hveq]
  rcases hb0 with e0|e0|e0 <;> rcases hb1 with e1|e1|e1 <;> rw [e0, e1]
  · exact wpc_on_Arow0 0 (by norm_num) (by norm_num)
  · exact wpc_on_Acol0 1 (by norm_num) (by norm_num)
  · exact wpc_on_Acol0 2 (by norm_num) (by norm_num)
  · exact wpc_on_Arow0 1 (by norm_num) (by norm_num)
  · exact absurd rfl (by rw [hveq, e0, e1] at hne; exact hne)
  · exact wpc_on_Arow2 1 (by norm_num) (by norm_num)
  · exact wpc_on_Arow0 2 (by norm_num) (by norm_num)
  · exact wpc_on_Acol2 1 (by norm_num) (by norm_num)
  · exact wpc_on_Acol2 2 (by norm_num) (by norm_num)






theorem wpc_not_noKingSeparation : ¬ ksc_NoKingSeparation wpc_fig8 (![1, 1] : Site 2) := by
  intro hns
  have hTsub : ({(![1,1]:Site 2)} : Set (Site 2)) ⊆ jil_offSupportInterior wpc_fig8 := by
    intro z hz; rw [Set.mem_singleton_iff] at hz; subst hz; exact wpc_fig8_mem_interior_11
  have hsub := hns {(![1,1]:Site 2)} (Set.mem_singleton _) hTsub wpc_fig8_singleton_saturated
  have h33 := hsub wpc_fig8_mem_interior_33
  rw [Set.mem_singleton_iff] at h33
  have : (3:ℤ) = 1 := by have := congrFun h33 0; simp only [Matrix.cons_val_zero] at this; exact this
  omega
















theorem wpc_cat_crossArcThick_false : ¬ cat_CrossArcThick wpc_fig8 (![1, 1] : Site 2) := by
  intro hres
  exact wpc_not_noKingSeparation
    (cat_noKingSeparation_of_fourThin wpc_fig8 wpc_fig8_mem_interior_11 wpc_fig8_fourThin hres)







theorem wpc_fig8_refutation_package :
    mci_FourThin wpc_fig8 ∧
    (![1, 1] : Site 2) ∈ jil_offSupportInterior wpc_fig8 ∧
    (![3, 3] : Site 2) ∈ jil_offSupportInterior wpc_fig8 ∧
    ¬ ksc_NoKingSeparation wpc_fig8 (![1, 1] : Site 2) ∧
    ¬ cat_CrossArcThick wpc_fig8 (![1, 1] : Site 2) :=
  ⟨wpc_fig8_fourThin, wpc_fig8_mem_interior_11, wpc_fig8_mem_interior_33,
   wpc_not_noKingSeparation, wpc_cat_crossArcThick_false⟩

end Lattice

end StatMech
