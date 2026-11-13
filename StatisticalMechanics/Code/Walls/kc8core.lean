/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















































































import Code.Walls.kc7core
import Code.Walls.kc6core
import Code.Walls.kc5_core
import Code.Walls.kc4_core
import Code.Lattice.OutsideConnected
import Code.Lattice.OutsideReachesClose
import Code.Lattice.JordanSeparationFull

open Set SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice

variable {a : Site 2}


















theorem kc8_infinite_of_reachesExterior (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {z : Site 2} (hzoff : z ∉ Vc.support)
    {e : Site 2} (heExt : e ∈ exterior 2 R)
    (hreach : (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e) :
    ∃ hzmem : z ∈ (oc_supportSet Vc)ᶜ,
      (((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).connectedComponentMk
        ⟨z, hzmem⟩).supp.Infinite := by
  have hzmem : z ∈ (oc_supportSet Vc)ᶜ := by simpa [oc_supportSet] using hzoff
  refine ⟨hzmem, ?_⟩
  obtain ⟨p, hp⟩ := (ffc_reachable_iff_offSupportWalk (B := oc_supportSet Vc) hzmem).mp hreach
  have hemem : e ∈ (oc_supportSet Vc)ᶜ := by
    have := hp e p.end_mem_support; simpa [oc_supportSet] using this
  have hindReach :
      ((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).Reachable ⟨z, hzmem⟩ ⟨e, hemem⟩ :=
    walk_induce_reachable (hypercubicLattice 2) ((oc_supportSet Vc)ᶜ) p (fun w hw => hp w hw)
      hzmem hemem
  have hcompEq :
      ((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).connectedComponentMk ⟨z, hzmem⟩ =
      ((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).connectedComponentMk ⟨e, hemem⟩ :=
    ConnectedComponent.sound hindReach
  rw [hcompEq]
  exact kc4_extComponent_infinite Vc R hsupp heExt hemem























theorem kc8_outsideOffSupportInfinite_of_offSupportReaches (Vc : (hypercubicLattice 2).Walk a a)
    (R : ℕ) (hsupp : oc_supportSet Vc ⊆ box 2 R)
    (hEsc : kc5_OffSupportReachesExterior Vc R) :
    kc5_OutsideOffSupportInfinite Vc := by
  intro z hzoff hzOut
  obtain ⟨e, heExt, hreach⟩ := hEsc z hzoff hzOut
  exact kc8_infinite_of_reachesExterior Vc R hsupp hzoff heExt hreach










theorem kc8_offSupportOutsideInfinite_of_offSupportReaches (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (R : ℕ)
    (hRbox : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
    (hbridge : kc6_OffSupportOutsideInK K a)
    (hEsc : kc5_OffSupportReachesExterior (mpl_orbitLoop K a) R) :
    kc7_OffSupportOutsideInfinite K a := by
  have hsupp : oc_supportSet (mpl_orbitLoop K a) ⊆ box 2 R := fun _ hp => hRbox hp
  have hres : kc5_OutsideOffSupportInfinite (mpl_orbitLoop K a) :=
    kc8_outsideOffSupportInfinite_of_offSupportReaches (mpl_orbitLoop K a) R hsupp hEsc
  intro z hzK hzsupp
  have hzOut : z ∉ jec_leftRegion (mpl_orbitLoop K a) := hbridge z hzK hzsupp
  exact hres z hzsupp hzOut

















theorem kc8_offSupportReaches_of_anyClear (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hall : ∀ z : Site 2, z ∉ Vc.support → z ∉ jec_leftRegion Vc →
      (∀ w ∈ (sw_vertSeg (z 0) (z 1) ((R : ℤ) + 1)).support, w ∉ Vc.support) ∨
      (∀ w ∈ (sw_vertSeg (z 0) (z 1) (-((R : ℤ) + 1))).support, w ∉ Vc.support) ∨
      (∀ w ∈ (sw_horizSeg (z 1) (z 0) ((R : ℤ) + 1)).support, w ∉ Vc.support) ∨
      (∀ w ∈ (sw_horizSeg (z 1) (z 0) (-((R : ℤ) + 1))).support, w ∉ Vc.support)) :
    kc5_OffSupportReachesExterior Vc R := by
  intro z hzoff hzOut
  exact orc_reachesExterior_of_anyClear Vc R (hall z hzoff hzOut)






theorem kc8_outsideOffSupportInfinite_of_anyClear (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R)
    (hall : ∀ z : Site 2, z ∉ Vc.support → z ∉ jec_leftRegion Vc →
      (∀ w ∈ (sw_vertSeg (z 0) (z 1) ((R : ℤ) + 1)).support, w ∉ Vc.support) ∨
      (∀ w ∈ (sw_vertSeg (z 0) (z 1) (-((R : ℤ) + 1))).support, w ∉ Vc.support) ∨
      (∀ w ∈ (sw_horizSeg (z 1) (z 0) ((R : ℤ) + 1)).support, w ∉ Vc.support) ∨
      (∀ w ∈ (sw_horizSeg (z 1) (z 0) (-((R : ℤ) + 1))).support, w ∉ Vc.support)) :
    kc5_OutsideOffSupportInfinite Vc :=
  kc8_outsideOffSupportInfinite_of_offSupportReaches Vc R hsupp
    (kc8_offSupportReaches_of_anyClear Vc R hall)

















theorem kc8_unitCell_support_coords (z : Site 2)
    (hz : z ∈ (mpl_orbitLoop unitCell ucBase).support) :
    (z 0 = -1 ∨ z 0 = 0) ∧ (z 1 = -1 ∨ z 1 = 0) := by
  rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges, jsf_unitCell_loop_edges] at hz
  rcases hz with hz | ⟨e, he, hmem⟩
  · have hzeq : z = (![0, 0] : Site 2) := hz
    subst hzeq; exact ⟨by right; rfl, by right; rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;>
    · rw [Sym2.mem_iff] at hmem
      rcases hmem with rfl | rfl <;> exact ⟨by simp, by simp⟩




theorem kc8_unitCell_supp_box :
    oc_supportSet (mpl_orbitLoop unitCell ucBase) ⊆ box 2 1 := by
  intro z hz
  rw [oc_mem_supportSet] at hz
  obtain ⟨h0, h1⟩ := kc8_unitCell_support_coords z hz
  intro i
  fin_cases i <;> simp <;> omega




theorem kc8_unitCell_coords_in_support (z : Site 2)
    (hc0 : z 0 = -1 ∨ z 0 = 0) (hc1 : z 1 = -1 ∨ z 1 = 0) :
    z ∈ (mpl_orbitLoop unitCell ucBase).support := by
  rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges, jsf_unitCell_loop_edges]
  right
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rcases hc0 with h0 | h0 <;> rcases hc1 with h1 | h1
  · refine ⟨s((![-1, -1] : Site 2), ![-1, 0]), Or.inr (Or.inr (Or.inl rfl)), ?_⟩
    have hzeq : z = (![-1, -1] : Site 2) := by ext i; fin_cases i <;> simp [h0, h1]
    rw [hzeq]; exact Sym2.mem_mk_left _ _
  · refine ⟨s((![-1, -1] : Site 2), ![-1, 0]), Or.inr (Or.inr (Or.inl rfl)), ?_⟩
    have hzeq : z = (![-1, 0] : Site 2) := by ext i; fin_cases i <;> simp [h0, h1]
    rw [hzeq]; exact Sym2.mem_mk_right _ _
  · refine ⟨s((![0, 0] : Site 2), ![0, -1]), Or.inl rfl, ?_⟩
    have hzeq : z = (![0, -1] : Site 2) := by ext i; fin_cases i <;> simp [h0, h1]
    rw [hzeq]; exact Sym2.mem_mk_right _ _
  · refine ⟨s((![0, 0] : Site 2), ![0, -1]), Or.inl rfl, ?_⟩
    have hzeq : z = (![0, 0] : Site 2) := by ext i; fin_cases i <;> simp [h0, h1]
    rw [hzeq]; exact Sym2.mem_mk_left _ _






theorem kc8_unitCell_anyClear (z : Site 2)
    (hz : z ∉ (mpl_orbitLoop unitCell ucBase).support) :
    (∀ w ∈ (sw_vertSeg (z 0) (z 1) (((1 : ℕ) : ℤ) + 1)).support,
        w ∉ (mpl_orbitLoop unitCell ucBase).support) ∨
    (∀ w ∈ (sw_vertSeg (z 0) (z 1) (-(((1 : ℕ) : ℤ) + 1))).support,
        w ∉ (mpl_orbitLoop unitCell ucBase).support) ∨
    (∀ w ∈ (sw_horizSeg (z 1) (z 0) (((1 : ℕ) : ℤ) + 1)).support,
        w ∉ (mpl_orbitLoop unitCell ucBase).support) ∨
    (∀ w ∈ (sw_horizSeg (z 1) (z 0) (-(((1 : ℕ) : ℤ) + 1))).support,
        w ∉ (mpl_orbitLoop unitCell ucBase).support) := by
  by_cases hcol : z 0 = -1 ∨ z 0 = 0
  · 
    refine Or.inr (Or.inr (Or.inl ?_))
    intro w hw hsupp
    rw [sw_horizSeg_mem_support] at hw
    obtain ⟨t, ht, rfl⟩ := hw
    obtain ⟨_, hc1⟩ := kc8_unitCell_support_coords _ hsupp
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hc1
    exact hz (kc8_unitCell_coords_in_support z hcol hc1)
  · 
    refine Or.inl ?_
    intro w hw hsupp
    rw [sw_vertSeg_mem_support] at hw
    obtain ⟨t, ht, rfl⟩ := hw
    obtain ⟨hc0, _⟩ := kc8_unitCell_support_coords _ hsupp
    simp only [Matrix.cons_val_zero] at hc0
    push Not at hcol; omega








theorem kc8_unitCell_offSupportReaches :
    kc5_OffSupportReachesExterior (mpl_orbitLoop unitCell ucBase) 1 := by
  refine kc8_offSupportReaches_of_anyClear (mpl_orbitLoop unitCell ucBase) 1 ?_
  intro z hzoff _hzOut
  simpa using kc8_unitCell_anyClear z hzoff








theorem kc8_unitCell_outsideOffSupportInfinite :
    kc5_OutsideOffSupportInfinite (mpl_orbitLoop unitCell ucBase) :=
  kc8_outsideOffSupportInfinite_of_offSupportReaches (mpl_orbitLoop unitCell ucBase) 1
    kc8_unitCell_supp_box kc8_unitCell_offSupportReaches










theorem kc8_unitCell_offSupportOutsideInfinite :
    kc7_OffSupportOutsideInfinite unitCell ucBase := by
  intro z hzK hzsupp
  
  have hzOut : z ∉ jec_leftRegion (mpl_orbitLoop unitCell ucBase) := by
    rw [← jsf_unitCell_eq_leftRegion]; exact hzK
  exact kc8_unitCell_outsideOffSupportInfinite z hzsupp hzOut











theorem kc8_exterior_satisfies_escape (Vc : (hypercubicLattice 2).Walk a a) {z : Site 2}
    (hz : z ∈ exterior 2 R) :
    ∃ e : Site 2, e ∈ exterior 2 R ∧
      (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e :=
  ⟨z, hz, SimpleGraph.Reachable.refl _⟩

end Walls

end StatMech
