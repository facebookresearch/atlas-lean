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
import Code.Lattice.KingNoSeparationClose

open Set SimpleGraph Function

namespace StatMech

namespace Lattice




theorem etp_adj_vert (x y : ℤ) :
    (hypercubicLattice 2).Adj (![x, y] : Site 2) ![x, y + 1] := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp


theorem etp_adj_horiz (x y : ℤ) :
    (hypercubicLattice 2).Adj (![x, y] : Site 2) ![x + 1, y] := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp















theorem etp_horiz_wall_upperGap_blocked {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T)
    {x y : ℤ} (hL : (![x - 1, y] : Site 2) ∈ T)
    (hR : (![x + 1, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hRnT : (![x + 1, y] : Site 2) ∉ T) :
    (![x, y + 1] : Site 2) ∉ jil_offSupportInterior Vc := by
  intro hUI
  
  have hUT : (![x, y + 1] : Site 2) ∈ T := by
    have h : (![(x - 1) + 1, y + 1] : Site 2) ∈ T :=
      ksc_saturated_diag Vc hsat (Or.inl rfl) (Or.inl rfl) hL (by simpa using hUI)
    simpa using h
  
  have hRT : (![x + 1, y] : Site 2) ∈ T := by
    have h : (![x + 1, (y + 1) + (-1)] : Site 2) ∈ T :=
      ksc_saturated_diag Vc hsat (Or.inl rfl) (Or.inr rfl) hUT (by simpa using hR)
    simpa using h
  exact hRnT hRT




theorem etp_horiz_wall_lowerGap_blocked {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T)
    {x y : ℤ} (hL : (![x - 1, y] : Site 2) ∈ T)
    (hR : (![x + 1, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hRnT : (![x + 1, y] : Site 2) ∉ T) :
    (![x, y - 1] : Site 2) ∉ jil_offSupportInterior Vc := by
  intro hDI
  have hDT : (![x, y - 1] : Site 2) ∈ T := by
    have h : (![(x - 1) + 1, y + (-1)] : Site 2) ∈ T :=
      ksc_saturated_diag Vc hsat (Or.inl rfl) (Or.inr rfl) hL (by simpa using hDI)
    simpa using h
  have hRT : (![x + 1, y] : Site 2) ∈ T := by
    have h : (![x + 1, (y - 1) + 1] : Site 2) ∈ T :=
      ksc_saturated_diag Vc hsat (Or.inl rfl) (Or.inl rfl) hDT (by simpa using hR)
    simpa using h
  exact hRnT hRT





theorem etp_horiz_wall_gaps_blocked {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T) (hTsub : T ⊆ jil_offSupportInterior Vc)
    {x y : ℤ} (hL : (![x - 1, y] : Site 2) ∈ T)
    (hR : (![x + 1, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hRnT : (![x + 1, y] : Site 2) ∉ T) :
    (![x, y] : Site 2) ∈ Vc.support ∧
      (![x, y + 1] : Site 2) ∉ jil_offSupportInterior Vc ∧
      (![x, y - 1] : Site 2) ∉ jil_offSupportInterior Vc :=
  ⟨ksc_separated_midOnSupport_horiz Vc hsat hTsub hL hR hRnT,
   etp_horiz_wall_upperGap_blocked Vc hsat hL hR hRnT,
   etp_horiz_wall_lowerGap_blocked Vc hsat hL hR hRnT⟩













theorem etp_thickPoint_of_swCorner {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {q : Site 2}
    (hW : (![q 0 - 1, q 1] : Site 2) ∈ Vc.support)
    (hS : (![q 0, q 1 - 1] : Site 2) ∈ Vc.support)
    (hC : (![q 0 - 1, q 1 - 1] : Site 2) ∈ Vc.support)
    (hnon : s((![q 0 - 1, q 1] : Site 2), (![q 0 - 1, q 1 - 1] : Site 2)) ∉ Vc.edges ∨
            s((![q 0, q 1 - 1] : Site 2), (![q 0 - 1, q 1 - 1] : Site 2)) ∉ Vc.edges) :
    kns_ThickPoint Vc := by
  rcases hnon with h | h
  · 
    refine ⟨(![q 0 - 1, q 1] : Site 2), (![q 0 - 1, q 1 - 1] : Site 2), hW, hC, ?_, h⟩
    have hadj := (etp_adj_vert (q 0 - 1) (q 1 - 1)).symm
    rw [show ((q 1 - 1) + 1 : ℤ) = q 1 by ring] at hadj
    exact hadj
  · 
    refine ⟨(![q 0, q 1 - 1] : Site 2), (![q 0 - 1, q 1 - 1] : Site 2), hS, hC, ?_, h⟩
    have hadj := (etp_adj_horiz (q 0 - 1) (q 1 - 1)).symm
    rw [show ((q 0 - 1) + 1 : ℤ) = q 0 by ring] at hadj
    exact hadj




theorem etp_swCorner_dichotomy {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T) (hTsub : T ⊆ jil_offSupportInterior Vc)
    {q : Site 2} (hqI : q ∈ jil_offSupportInterior Vc) (hqnT : q ∉ T)
    (M : ℤ) (hmin : ∀ z ∈ jil_offSupportInterior Vc, z ∉ T →
        rlc_lexMeasure M q ≤ rlc_lexMeasure M z)
    (hqbox : (-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M))
    (hCbox : (-M < q 0 - 1 ∧ q 0 - 1 ≤ M) ∧ (-M < q 1 - 1 ∧ q 1 - 1 ≤ M)) :
    (![q 0 - 1, q 1 - 1] : Site 2) ∈ Vc.support ∨
      (![q 0 - 1, q 1 - 1] : Site 2) ∉ jil_offSupportInterior Vc :=
  kns_lexBelow_diag_corner Vc hsat hTsub hqI hqnT M hmin hqbox hCbox

















def etp_EscapeWallThick {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (seed : Site 2) :
    Prop :=
  ∀ (T : Set (Site 2)), seed ∈ T → T ⊆ jil_offSupportInterior Vc → ksc_KingSaturated Vc T →
    ∀ (M : ℤ) (q : Site 2), q ∈ jil_offSupportInterior Vc → q ∉ T →
      (∀ z ∈ jil_offSupportInterior Vc, z ∉ T → rlc_lexMeasure M q ≤ rlc_lexMeasure M z) →
      (![q 0 - 1, q 1] : Site 2) ∈ Vc.support →
      (![q 0, q 1 - 1] : Site 2) ∈ Vc.support →
      
      ((![q 0 - 1, q 1 - 1] : Site 2) ∉ jil_offSupportInterior Vc ∧
        (![q 0 - 1, q 1 - 1] : Site 2) ∉ Vc.support) ∨
      ((![q 0 - 1, q 1 - 1] : Site 2) ∈ Vc.support ∧
        s((![q 0 - 1, q 1] : Site 2), (![q 0 - 1, q 1 - 1] : Site 2)) ∈ Vc.edges ∧
        s((![q 0, q 1 - 1] : Site 2), (![q 0 - 1, q 1 - 1] : Site 2)) ∈ Vc.edges) →
      kns_ThickPoint Vc






theorem etp_escape_structure_box {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hsep : kns_KingSeparation Vc seed) :
    ∃ (T : Set (Site 2)), seed ∈ T ∧ T ⊆ jil_offSupportInterior Vc ∧ ksc_KingSaturated Vc T ∧
      ∃ (M : ℤ) (q : Site 2), q ∈ jil_offSupportInterior Vc ∧ q ∉ T ∧
        (∀ z ∈ jil_offSupportInterior Vc, z ∉ T →
          rlc_lexMeasure M q ≤ rlc_lexMeasure M z) ∧
        (![q 0 - 1, q 1] : Site 2) ∈ Vc.support ∧
        (![q 0, q 1 - 1] : Site 2) ∈ Vc.support ∧
        ((-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M)) ∧
        ((-M < q 0 - 1 ∧ q 0 - 1 ≤ M) ∧ (-M < q 1 - 1 ∧ q 1 - 1 ≤ M)) := by
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
  have hCbox : (-M < q 0 - 1 ∧ q 0 - 1 ≤ M) ∧ (-M < q 1 - 1 ∧ q 1 - 1 ≤ M) := by
    rw [hM]; exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  obtain ⟨hW, hSsup⟩ :=
    kns_escape_axials_onSupport Vc hsat hTsub hqI hqnT M hmin hqbox hWbox hSbox
  exact ⟨T, hseedT, hTsub, hsat, M, q, hqI, hqnT, hmin, hW, hSsup, hqbox, hCbox⟩














theorem etp_noKingSeparation_of_fourThin {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseedI : seed ∈ jil_offSupportInterior Vc) (hthin : mci_FourThin Vc)
    (hres : etp_EscapeWallThick Vc seed) :
    ksc_NoKingSeparation Vc seed := by
  by_contra hns
  classical
  have hsep := (kns_kingSeparation_iff_not_noKingSeparation Vc hseedI).mpr hns
  obtain ⟨T, hseedT, hTsub, hsat, M, q, hqI, hqnT, hmin, hW, hS, hqbox, hCbox⟩ :=
    etp_escape_structure_box Vc hsep
  
  
  
  
  
  have hcorner := kns_lexBelow_diag_corner Vc hsat hTsub hqI hqnT M hmin hqbox hCbox
  have htp : kns_ThickPoint Vc := by
    by_cases hCsup : (![q 0 - 1, q 1 - 1] : Site 2) ∈ Vc.support
    · 
      by_cases hWC : s((![q 0 - 1, q 1] : Site 2), (![q 0 - 1, q 1 - 1] : Site 2)) ∈ Vc.edges
      · by_cases hSC : s((![q 0, q 1 - 1] : Site 2), (![q 0 - 1, q 1 - 1] : Site 2)) ∈ Vc.edges
        · exact hres T hseedT hTsub hsat M q hqI hqnT hmin hW hS (Or.inr ⟨hCsup, hWC, hSC⟩)
        · exact etp_thickPoint_of_swCorner Vc hW hS hCsup (Or.inr hSC)
      · exact etp_thickPoint_of_swCorner Vc hW hS hCsup (Or.inl hWC)
    · 
      have hCext : (![q 0 - 1, q 1 - 1] : Site 2) ∉ jil_offSupportInterior Vc := by
        rcases hcorner with h | h
        · exact absurd h hCsup
        · exact h
      exact hres T hseedT hTsub hsat M q hqI hqnT hmin hW hS (Or.inl ⟨hCext, hCsup⟩)
  exact (kns_thickPoint_iff_not_fourThin Vc).mp htp hthin








theorem etp_kingRowLinked_of_fourThin {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseedI : seed ∈ jil_offSupportInterior Vc) (hthin : mci_FourThin Vc)
    (hres : etp_EscapeWallThick Vc seed) :
    mci_KingRowLinked Vc seed :=
  ksc_kingRowLinked_of_noKingSeparation Vc hseedI
    (etp_noKingSeparation_of_fourThin Vc hseedI hthin hres)




theorem etp_kingInteriorConnected_of_fourThin {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z₀ : Site 2} (hz₀ : z₀ ∈ jil_offSupportInterior Vc) (hthin : mci_FourThin Vc)
    (hres : ∀ seed ∈ jil_offSupportInterior Vc, etp_EscapeWallThick Vc seed) :
    mci_KingInteriorConnected Vc :=
  ⟨z₀, hz₀, etp_kingRowLinked_of_fourThin Vc hz₀ hthin (hres z₀ hz₀)⟩









theorem etp_escapeWallThick_of_escapeThickPoint {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hktp : kns_EscapeThickPoint Vc seed) :
    etp_EscapeWallThick Vc seed := by
  intro T hseedT hTsub hsat M q hqI hqnT hmin hW hS _hcorner
  exact hktp T hseedT hTsub hsat M q hqI hqnT hmin hW hS















theorem etp_fjord_escapeWallThick : etp_EscapeWallThick sdc_fjord (![5, 1] : Site 2) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ => kns_fjord_thickPoint





theorem etp_fjord_nonvacuous :
    kns_KingSeparation sdc_fjord (![5, 1] : Site 2) ∧ kns_ThickPoint sdc_fjord ∧
    etp_EscapeWallThick sdc_fjord (![5, 1] : Site 2) ∧ ¬ mci_FourThin sdc_fjord :=
  ⟨kns_fjord_kingSeparation, kns_fjord_thickPoint, etp_fjord_escapeWallThick,
   mci_fjord_not_fourThin⟩




theorem etp_ksd_escapeWallThick : etp_EscapeWallThick ksd_stair (![1, 1] : Site 2) := by
  intro T hseedT hTsub hsat M q hqI hqnT _hmin _hW _hS _hcorner
  exact absurd (ksc_ksd_noKingSeparation T hseedT hTsub hsat hqI) hqnT



theorem etp_kda_escapeWallThick : etp_EscapeWallThick kda_stairDR (![3, 1] : Site 2) := by
  intro T hseedT hTsub hsat M q hqI hqnT _hmin _hW _hS _hcorner
  exact absurd (ksc_kda_noKingSeparation T hseedT hTsub hsat hqI) hqnT













theorem etp_kingRowLinked_summary {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseedI : seed ∈ jil_offSupportInterior Vc) (hthin : mci_FourThin Vc) :
    etp_EscapeWallThick Vc seed → mci_KingRowLinked Vc seed :=
  etp_kingRowLinked_of_fourThin Vc hseedI hthin

end Lattice

end StatMech
