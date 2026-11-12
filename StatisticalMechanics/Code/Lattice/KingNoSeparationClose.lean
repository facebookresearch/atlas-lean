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
import Code.Lattice.InteriorWindingClose
import Code.Lattice.SegmentDownClose
import Code.Lattice.MatchedConnectivityInterior
import Code.Lattice.RowLinkedClose
import Code.Lattice.KingSegmentDownClose
import Code.Lattice.KingDescentAgnosticClose
import Code.Lattice.KingStepConnectClose

open Set SimpleGraph Function

namespace StatMech

namespace Lattice














theorem kns_fourThin_noKingSeparation_examples :
    (mci_FourThin ksd_stair ∧ ksc_NoKingSeparation ksd_stair (![1, 1] : Site 2)) ∧
    (mci_FourThin kda_stairDR ∧ ksc_NoKingSeparation kda_stairDR (![3, 1] : Site 2)) :=
  ⟨⟨ksd_stair_fourThin, ksc_ksd_noKingSeparation⟩,
   ⟨kda_stairDR_fourThin, ksc_kda_noKingSeparation⟩⟩






theorem kns_fjord_not_fourThin_has_separation :
    ¬ mci_FourThin sdc_fjord ∧ ¬ ksc_NoKingSeparation sdc_fjord (![5, 1] : Site 2) :=
  ⟨mci_fjord_not_fourThin, ksc_fjord_noKingSeparation_false⟩






















theorem kns_offSupport_neighbor_interior {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z w : Site 2} (hz : z ∈ jil_offSupportInterior Vc)
    (hadj : (hypercubicLattice 2).Adj z w) (hwoff : w ∉ Vc.support) :
    w ∈ jil_offSupportInterior Vc :=
  mci_offSupport_neighbor_interior Vc hz hadj hwoff











theorem kns_lexBelow_axial_onSupport {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T) (hTsub : T ⊆ jil_offSupportInterior Vc)
    {q : Site 2} (hqI : q ∈ jil_offSupportInterior Vc) (hqnT : q ∉ T)
    (M : ℤ) (hmin : ∀ z ∈ jil_offSupportInterior Vc, z ∉ T →
        rlc_lexMeasure M q ≤ rlc_lexMeasure M z)
    (hqbox : (-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M))
    {w : Site 2} (hwadj : (hypercubicLattice 2).Adj q w)
    (hwbox : (-M < w 0 ∧ w 0 ≤ M) ∧ (-M < w 1 ∧ w 1 ≤ M))
    (hlex : w 1 < q 1 ∨ (w 1 = q 1 ∧ w 0 < q 0)) :
    w ∈ Vc.support := by
  by_contra hwoff
  
  have hwI : w ∈ jil_offSupportInterior Vc :=
    kns_offSupport_neighbor_interior Vc hqI hwadj hwoff
  
  
  have hwT : w ∈ T := by
    by_contra hwnT
    have hle := hmin w hwI hwnT
    have hlt : rlc_lexMeasure M w < rlc_lexMeasure M q :=
      rlc_lexMeasure_lt hqbox.1.1 hqbox.1.2 hqbox.2.1 hqbox.2.2
        hwbox.1.1 hwbox.1.2 hwbox.2.1 hwbox.2.2 hlex
    omega
  
  exact hqnT (ksc_saturated_axial Vc hsat hwT hqI hwadj.symm)





theorem kns_escape_axials_onSupport {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T) (hTsub : T ⊆ jil_offSupportInterior Vc)
    {q : Site 2} (hqI : q ∈ jil_offSupportInterior Vc) (hqnT : q ∉ T)
    (M : ℤ) (hmin : ∀ z ∈ jil_offSupportInterior Vc, z ∉ T →
        rlc_lexMeasure M q ≤ rlc_lexMeasure M z)
    (hqbox : (-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M))
    (hWbox : (-M < q 0 - 1 ∧ q 0 - 1 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M))
    (hSbox : (-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 - 1 ∧ q 1 - 1 ≤ M)) :
    (![q 0 - 1, q 1] : Site 2) ∈ Vc.support ∧ (![q 0, q 1 - 1] : Site 2) ∈ Vc.support := by
  have hq01 : q = ![q 0, q 1] := by ext i; fin_cases i <;> simp
  constructor
  · 
    refine kns_lexBelow_axial_onSupport Vc hsat hTsub hqI hqnT M hmin hqbox
      (w := (![q 0 - 1, q 1] : Site 2)) ?_ ?_ ?_
    · rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
    · simpa using hWbox
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      right; exact ⟨trivial, by omega⟩
  · 
    refine kns_lexBelow_axial_onSupport Vc hsat hTsub hqI hqnT M hmin hqbox
      (w := (![q 0, q 1 - 1] : Site 2)) ?_ ?_ ?_
    · rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
    · simpa using hSbox
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      left; omega






theorem kns_lexBelow_diag_corner {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T) (hTsub : T ⊆ jil_offSupportInterior Vc)
    {q : Site 2} (hqI : q ∈ jil_offSupportInterior Vc) (hqnT : q ∉ T)
    (M : ℤ) (hmin : ∀ z ∈ jil_offSupportInterior Vc, z ∉ T →
        rlc_lexMeasure M q ≤ rlc_lexMeasure M z)
    (hqbox : (-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M))
    (hCbox : (-M < q 0 - 1 ∧ q 0 - 1 ≤ M) ∧ (-M < q 1 - 1 ∧ q 1 - 1 ≤ M)) :
    (![q 0 - 1, q 1 - 1] : Site 2) ∈ Vc.support ∨
      (![q 0 - 1, q 1 - 1] : Site 2) ∉ jil_offSupportInterior Vc := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hCoff, hCI⟩ := hcon
  
  have hCnT : (![q 0 - 1, q 1 - 1] : Site 2) ∉ T → False := by
    intro hCnT
    have hle := hmin _ hCI hCnT
    have hlt : rlc_lexMeasure M (![q 0 - 1, q 1 - 1] : Site 2) < rlc_lexMeasure M q :=
      rlc_lexMeasure_lt hqbox.1.1 hqbox.1.2 hqbox.2.1 hqbox.2.2
        (by simpa using hCbox.1.1) (by simpa using hCbox.1.2)
        (by simpa using hCbox.2.1) (by simpa using hCbox.2.2)
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; left; omega)
    omega
  have hCT : (![q 0 - 1, q 1 - 1] : Site 2) ∈ T := by
    by_contra h; exact hCnT h
  
  have hq01 : q = ![q 0, q 1] := by ext i; fin_cases i <;> simp
  have hdiag : mci_kingGraph.Adj (![q 0 - 1, q 1 - 1] : Site 2) q := by
    rw [hq01]
    have := mci_kingAdj_diag (q 0 - 1) (q 1 - 1) 1 1 (Or.inl rfl) (Or.inl rfl)
    simpa using this
  exact hqnT (hsat _ _ hCT hqI hdiag)







theorem kns_lexBelow_diag_corner_SE {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T) (hTsub : T ⊆ jil_offSupportInterior Vc)
    {q : Site 2} (hqI : q ∈ jil_offSupportInterior Vc) (hqnT : q ∉ T)
    (M : ℤ) (hmin : ∀ z ∈ jil_offSupportInterior Vc, z ∉ T →
        rlc_lexMeasure M q ≤ rlc_lexMeasure M z)
    (hqbox : (-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M))
    (hCbox : (-M < q 0 + 1 ∧ q 0 + 1 ≤ M) ∧ (-M < q 1 - 1 ∧ q 1 - 1 ≤ M)) :
    (![q 0 + 1, q 1 - 1] : Site 2) ∈ Vc.support ∨
      (![q 0 + 1, q 1 - 1] : Site 2) ∉ jil_offSupportInterior Vc := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hCoff, hCI⟩ := hcon
  have hCT : (![q 0 + 1, q 1 - 1] : Site 2) ∈ T := by
    by_contra hCnT
    have hle := hmin _ hCI hCnT
    have hlt : rlc_lexMeasure M (![q 0 + 1, q 1 - 1] : Site 2) < rlc_lexMeasure M q :=
      rlc_lexMeasure_lt hqbox.1.1 hqbox.1.2 hqbox.2.1 hqbox.2.2
        (by simpa using hCbox.1.1) (by simpa using hCbox.1.2)
        (by simpa using hCbox.2.1) (by simpa using hCbox.2.2)
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; left; omega)
    omega
  have hq01 : q = ![q 0, q 1] := by ext i; fin_cases i <;> simp
  have hdiag : mci_kingGraph.Adj (![q 0 + 1, q 1 - 1] : Site 2) q := by
    rw [hq01]
    have := mci_kingAdj_diag (q 0 + 1) (q 1 - 1) (-1) 1 (Or.inr rfl) (Or.inl rfl)
    simpa using this
  exact hqnT (hsat _ _ hCT hqI hdiag)












theorem kns_right_mem_interior {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) {x y : ℤ}
    (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hright : (![x + 1, y] : Site 2) ∉ Vc.support) :
    (![x + 1, y] : Site 2) ∈ jil_offSupportInterior Vc := by
  have hadj : (hypercubicLattice 2).Adj (![x, y] : Site 2) ![x + 1, y] := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
  exact mci_offSupport_neighbor_interior Vc hz hadj hright











theorem kns_row_complete {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T) (hTsub : T ⊆ jil_offSupportInterior Vc)
    {lo hi y x₀ x₁ : ℤ}
    (hx₀T : (![x₀, y] : Site 2) ∈ T)
    (hloff : (![lo, y] : Site 2) ∉ Vc.support)
    (hx₀lo : lo ≤ x₀) (hx₀hi : x₀ ≤ hi) (hx₁lo : lo ≤ x₁) (hx₁hi : x₁ ≤ hi)
    (hrun : ∀ t : ℤ, lo ≤ t → t ≤ hi → (![t, y] : Site 2) ∉ Vc.support) :
    (![x₁, y] : Site 2) ∈ T := by
  obtain ⟨p, hp⟩ := jil_hsegment_reachable_offSupport {p | p ∈ Vc.support}
    (lo := lo) (hi := hi) (y := y) (x₁ := x₀) (x₂ := x₁)
    (by simpa using hloff) hx₀lo hx₀hi hx₁lo hx₁hi
    (by intro t ht ht'; simpa using hrun t ht ht')
  have hp' : ∀ z ∈ p.support, z ∉ Vc.support := by intro z hz; simpa using hp z hz
  have hx₀I : (![x₀, y] : Site 2) ∈ jil_offSupportInterior Vc := hTsub hx₀T
  have hint := mci_offSupport_walk_interior Vc p hp' hx₀I
  have hpk : ∀ w ∈ (p.mapLe mci_hyper_le_king).support, w ∈ jil_offSupportInterior Vc := by
    intro w hw
    rw [SimpleGraph.Walk.support_mapLe_eq_support mci_hyper_le_king p] at hw
    exact hint w hw
  exact ksc_saturated_absorbs_kingWalk Vc hsat (p.mapLe mci_hyper_le_king) hpk hx₀T













def kns_KingSeparation {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (seed : Site 2) : Prop :=
  ∃ T : Set (Site 2), seed ∈ T ∧ T ⊆ jil_offSupportInterior Vc ∧
    ksc_KingSaturated Vc T ∧ ∃ z ∈ jil_offSupportInterior Vc, z ∉ T





def kns_ThickPoint {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) : Prop :=
  ∃ u v : Site 2, u ∈ Vc.support ∧ v ∈ Vc.support ∧
    (hypercubicLattice 2).Adj u v ∧ s(u, v) ∉ Vc.edges





theorem kns_kingSeparation_iff_not_noKingSeparation {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) {seed : Site 2}
    (_hseedI : seed ∈ jil_offSupportInterior Vc) :
    kns_KingSeparation Vc seed ↔ ¬ ksc_NoKingSeparation Vc seed := by
  constructor
  · rintro ⟨T, hseedT, hTsub, hsat, z, hzI, hznT⟩ hns
    exact hznT (hns T hseedT hTsub hsat hzI)
  · intro hns
    rw [ksc_NoKingSeparation] at hns
    push Not at hns
    obtain ⟨T, hseedT, hTsub, hsat, hnsub⟩ := hns
    rw [Set.not_subset] at hnsub
    obtain ⟨z, hzI, hznT⟩ := hnsub
    exact ⟨T, hseedT, hTsub, hsat, z, hzI, hznT⟩




theorem kns_thickPoint_iff_not_fourThin {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    kns_ThickPoint Vc ↔ ¬ mci_FourThin Vc := by
  constructor
  · rintro ⟨u, v, hu, hv, hadj, hne⟩ hthin
    exact hne (hthin u v hu hv hadj)
  · intro hthin
    rw [mci_FourThin] at hthin
    push Not at hthin
    obtain ⟨u, v, hu, hv, hadj, hne⟩ := hthin
    exact ⟨u, v, hu, hv, hadj, hne⟩




















def kns_EscapeThickPoint {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (seed : Site 2) :
    Prop :=
  ∀ (T : Set (Site 2)), seed ∈ T → T ⊆ jil_offSupportInterior Vc → ksc_KingSaturated Vc T →
    ∀ (M : ℤ) (q : Site 2), q ∈ jil_offSupportInterior Vc → q ∉ T →
      (∀ z ∈ jil_offSupportInterior Vc, z ∉ T → rlc_lexMeasure M q ≤ rlc_lexMeasure M z) →
      (![q 0 - 1, q 1] : Site 2) ∈ Vc.support →
      (![q 0, q 1 - 1] : Site 2) ∈ Vc.support →
      kns_ThickPoint Vc





theorem kns_exists_lexMin_escape {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} {z : Site 2} (hzI : z ∈ jil_offSupportInterior Vc) (hznT : z ∉ T)
    (M : ℤ) :
    ∃ q ∈ jil_offSupportInterior Vc, q ∉ T ∧
      ∀ w ∈ jil_offSupportInterior Vc, w ∉ T → rlc_lexMeasure M q ≤ rlc_lexMeasure M w := by
  classical
  have hfin := rlc_offSupportInterior_finite Vc
  set S : Finset (Site 2) := hfin.toFinset.filter (fun w => w ∉ T) with hS
  have hzS : z ∈ S := by
    rw [hS, Finset.mem_filter]; exact ⟨hfin.mem_toFinset.mpr hzI, hznT⟩
  obtain ⟨q, hqS, hqmin⟩ := S.exists_min_image (rlc_lexMeasure M) ⟨z, hzS⟩
  rw [hS, Finset.mem_filter] at hqS
  refine ⟨q, hfin.mem_toFinset.mp hqS.1, hqS.2, ?_⟩
  intro w hwI hwnT
  exact hqmin w (by rw [hS, Finset.mem_filter]; exact ⟨hfin.mem_toFinset.mpr hwI, hwnT⟩)








theorem kns_kingSeparation_escape_structure {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hsep : kns_KingSeparation Vc seed) :
    ∃ (T : Set (Site 2)), seed ∈ T ∧ T ⊆ jil_offSupportInterior Vc ∧ ksc_KingSaturated Vc T ∧
      ∃ (M : ℤ) (q : Site 2), q ∈ jil_offSupportInterior Vc ∧ q ∉ T ∧
        (∀ z ∈ jil_offSupportInterior Vc, z ∉ T →
          rlc_lexMeasure M q ≤ rlc_lexMeasure M z) ∧
        (![q 0 - 1, q 1] : Site 2) ∈ Vc.support ∧
        (![q 0, q 1 - 1] : Site 2) ∈ Vc.support := by
  obtain ⟨T, hseedT, hTsub, hsat, z, hzI, hznT⟩ := hsep
  obtain ⟨M₀, hM₀⟩ := rlc_interior_bounded Vc
  set M : ℤ := M₀ + 1 with hM
  obtain ⟨q, hqI, hqnT, hmin⟩ := kns_exists_lexMin_escape Vc hzI hznT M
  
  have hqL : q ∈ jec_leftRegion Vc := (jil_mem_offSupportInterior Vc _ |>.mp hqI).2
  obtain ⟨⟨hq0a, hq0b⟩, ⟨hq1a, hq1b⟩⟩ := hM₀ _ hqL
  have hqbox : (-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M) := by
    rw [hM]; exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  have hWbox : (-M < q 0 - 1 ∧ q 0 - 1 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M) := by
    rw [hM]; exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  have hSbox : (-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 - 1 ∧ q 1 - 1 ≤ M) := by
    rw [hM]; exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  obtain ⟨hW, hSsup⟩ :=
    kns_escape_axials_onSupport Vc hsat hTsub hqI hqnT M hmin hqbox hWbox hSbox
  exact ⟨T, hseedT, hTsub, hsat, M, q, hqI, hqnT, hmin, hW, hSsup⟩








theorem kns_noKingSeparation_of_fourThin {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseedI : seed ∈ jil_offSupportInterior Vc) (hthin : mci_FourThin Vc)
    (hres : kns_EscapeThickPoint Vc seed) :
    ksc_NoKingSeparation Vc seed := by
  by_contra hns
  have hsep := (kns_kingSeparation_iff_not_noKingSeparation Vc hseedI).mpr hns
  obtain ⟨T, hseedT, hTsub, hsat, M, q, hqI, hqnT, hmin, hW, hSsup⟩ :=
    kns_kingSeparation_escape_structure Vc hsep
  have htp := hres T hseedT hTsub hsat M q hqI hqnT hmin hW hSsup
  exact (kns_thickPoint_iff_not_fourThin Vc).mp htp hthin










theorem kns_escapeThickPoint_of_noKingSeparation {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hns : ksc_NoKingSeparation Vc seed) :
    kns_EscapeThickPoint Vc seed := by
  intro T hseedT hTsub hsat M q hqI hqnT _hmin _hW _hSsup
  exact absurd (hns T hseedT hTsub hsat hqI) hqnT





theorem kns_kingRowLinked_of_fourThin {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseedI : seed ∈ jil_offSupportInterior Vc) (hthin : mci_FourThin Vc)
    (hres : kns_EscapeThickPoint Vc seed) :
    mci_KingRowLinked Vc seed :=
  ksc_kingRowLinked_of_noKingSeparation Vc hseedI
    (kns_noKingSeparation_of_fourThin Vc hseedI hthin hres)




theorem kns_kingInteriorConnected_of_fourThin {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z₀ : Site 2} (hz₀ : z₀ ∈ jil_offSupportInterior Vc) (hthin : mci_FourThin Vc)
    (hres : ∀ seed ∈ jil_offSupportInterior Vc, kns_EscapeThickPoint Vc seed) :
    mci_KingInteriorConnected Vc :=
  ⟨z₀, hz₀, kns_kingRowLinked_of_fourThin Vc hz₀ hthin (hres z₀ hz₀)⟩














theorem kns_fjord_thickPoint : kns_ThickPoint sdc_fjord := by
  refine ⟨(![3, 1] : Site 2), (![4, 1] : Site 2), mci_fjord_on_31, sdc_fjord_on_41, ?_,
    mci_fjord_no_row1_horizontal_edge⟩
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; decide





theorem kns_fjord_kingSeparation : kns_KingSeparation sdc_fjord (![5, 1] : Site 2) := by
  obtain ⟨hRPint, hRPsat, hRPproper⟩ := ksc_fjord_rp_is_king_separation
  exact ⟨iwc_RightPocket, iwc_mem_rightPocket_51, hRPint, hRPsat,
    (![1, 1] : Site 2), sdc_fjord_mem_interior_11,
    fun h => iwc_not_rightPocket_11 h⟩







theorem kns_fjord_escapeThickPoint : kns_EscapeThickPoint sdc_fjord (![5, 1] : Site 2) :=
  fun _ _ _ _ _ _ _ _ _ _ _ => kns_fjord_thickPoint






theorem kns_fjord_nonvacuous :
    kns_KingSeparation sdc_fjord (![5, 1] : Site 2) ∧ kns_ThickPoint sdc_fjord ∧
    kns_EscapeThickPoint sdc_fjord (![5, 1] : Site 2) ∧ ¬ mci_FourThin sdc_fjord :=
  ⟨kns_fjord_kingSeparation, kns_fjord_thickPoint, kns_fjord_escapeThickPoint,
   mci_fjord_not_fourThin⟩














theorem kns_ksd_escapeThickPoint : kns_EscapeThickPoint ksd_stair (![1, 1] : Site 2) := by
  intro T hseedT hTsub hsat M q hqI hqnT hmin hW hSsup
  
  exact absurd (ksc_ksd_noKingSeparation T hseedT hTsub hsat hqI) hqnT




theorem kns_kda_escapeThickPoint : kns_EscapeThickPoint kda_stairDR (![3, 1] : Site 2) := by
  intro T hseedT hTsub hsat M q hqI hqnT hmin hW hSsup
  exact absurd (ksc_kda_noKingSeparation T hseedT hTsub hsat hqI) hqnT

end Lattice

end StatMech
