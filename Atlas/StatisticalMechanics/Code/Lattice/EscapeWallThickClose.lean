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
import Code.Lattice.EscapeThickPointClose

open Set SimpleGraph Function

namespace StatMech

namespace Lattice












theorem ewt_escapeRow_notMem_of_run {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T) (hTsub : T ⊆ jil_offSupportInterior Vc)
    {q : Site 2} (hqnT : q ∉ T)
    {lo hi x₁ : ℤ}
    (hloff : (![lo, q 1] : Site 2) ∉ Vc.support)
    (hlolo : lo ≤ q 0) (hqhi : q 0 ≤ hi) (hx₁lo : lo ≤ x₁) (hx₁hi : x₁ ≤ hi)
    (hrun : ∀ t : ℤ, lo ≤ t → t ≤ hi → (![t, q 1] : Site 2) ∉ Vc.support) :
    (![x₁, q 1] : Site 2) ∉ T := by
  intro hx₁T
  have hq01 : q = ![q 0, q 1] := by ext i; fin_cases i <;> simp
  apply hqnT
  rw [hq01]
  exact kns_row_complete Vc hsat hTsub hx₁T hloff hx₁lo hx₁hi hlolo hqhi hrun

















theorem ewt_escapeRow_down_onSupport {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T)
    {q : Site 2}
    (M : ℤ) (hmin : ∀ z ∈ jil_offSupportInterior Vc, z ∉ T →
        rlc_lexMeasure M q ≤ rlc_lexMeasure M z)
    (hqbox : (-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M))
    {wx : ℤ}
    (hw : (![wx, q 1] : Site 2) ∈ jil_offSupportInterior Vc)
    (hwnT : (![wx, q 1] : Site 2) ∉ T)
    (hwbox : (-M < wx ∧ wx ≤ M) ∧ (-M < q 1 - 1 ∧ q 1 - 1 ≤ M)) :
    (![wx, q 1 - 1] : Site 2) ∈ Vc.support := by
  by_contra hoff
  
  have hdI : (![wx, q 1 - 1] : Site 2) ∈ jil_offSupportInterior Vc := by
    have := rlc_down_mem_interior Vc hw (by simpa using hoff)
    simpa using this
  
  
  have hdT : (![wx, q 1 - 1] : Site 2) ∈ T := by
    by_contra hdnT
    have hle := hmin _ hdI hdnT
    have hlt : rlc_lexMeasure M (![wx, q 1 - 1] : Site 2) < rlc_lexMeasure M q :=
      rlc_lexMeasure_lt hqbox.1.1 hqbox.1.2 hqbox.2.1 hqbox.2.2
        (by simpa using hwbox.1.1) (by simpa using hwbox.1.2)
        (by simpa using hwbox.2.1) (by simpa using hwbox.2.2)
        (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; left; omega)
    omega
  
  
  have hadj : (hypercubicLattice 2).Adj (![wx, q 1 - 1] : Site 2) (![wx, q 1] : Site 2) := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
  exact hwnT (ksc_saturated_axial Vc hsat hdT hw hadj)








theorem ewt_runBottom_onSupport {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T) (hTsub : T ⊆ jil_offSupportInterior Vc)
    {q : Site 2} (hqnT : q ∉ T)
    (M : ℤ) (hmin : ∀ z ∈ jil_offSupportInterior Vc, z ∉ T →
        rlc_lexMeasure M q ≤ rlc_lexMeasure M z)
    (hqbox : (-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M))
    (hq1box : -M < q 1 - 1 ∧ q 1 - 1 ≤ M)
    {lo hi : ℤ}
    (hloff : (![lo, q 1] : Site 2) ∉ Vc.support)
    (hlolo : lo ≤ q 0) (hqhi : q 0 ≤ hi)
    (hrun : ∀ t : ℤ, lo ≤ t → t ≤ hi → (![t, q 1] : Site 2) ∉ Vc.support)
    (hrunI : ∀ t : ℤ, lo ≤ t → t ≤ hi → (![t, q 1] : Site 2) ∈ jil_offSupportInterior Vc)
    {x : ℤ} (hxlo : lo ≤ x) (hxhi : x ≤ hi)
    (hxbox : -M < x ∧ x ≤ M) :
    (![x, q 1 - 1] : Site 2) ∈ Vc.support := by
  have hxI : (![x, q 1] : Site 2) ∈ jil_offSupportInterior Vc := hrunI x hxlo hxhi
  have hxnT : (![x, q 1] : Site 2) ∉ T :=
    ewt_escapeRow_notMem_of_run Vc hsat hTsub hqnT hloff hlolo hqhi hxlo hxhi hrun
  exact ewt_escapeRow_down_onSupport Vc hsat M hmin hqbox hxI hxnT ⟨hxbox, hq1box⟩














theorem ewt_vert_wall_rightGap_blocked {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T)
    {x y : ℤ} (hD : (![x, y - 1] : Site 2) ∈ T)
    (hU : (![x, y + 1] : Site 2) ∈ jil_offSupportInterior Vc)
    (hUnT : (![x, y + 1] : Site 2) ∉ T) :
    (![x + 1, y] : Site 2) ∉ jil_offSupportInterior Vc := by
  intro hRI
  have hRT : (![x + 1, y] : Site 2) ∈ T := by
    have h : (![x + 1, (y - 1) + 1] : Site 2) ∈ T :=
      ksc_saturated_diag Vc hsat (Or.inl rfl) (Or.inl rfl) hD (by simpa using hRI)
    simpa using h
  have hUT : (![x, y + 1] : Site 2) ∈ T := by
    have h : (![(x + 1) + (-1), y + 1] : Site 2) ∈ T :=
      ksc_saturated_diag Vc hsat (Or.inr rfl) (Or.inl rfl) hRT (by simpa using hU)
    simpa using h
  exact hUnT hUT





theorem ewt_vert_wall_leftGap_blocked {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T)
    {x y : ℤ} (hD : (![x, y - 1] : Site 2) ∈ T)
    (hU : (![x, y + 1] : Site 2) ∈ jil_offSupportInterior Vc)
    (hUnT : (![x, y + 1] : Site 2) ∉ T) :
    (![x - 1, y] : Site 2) ∉ jil_offSupportInterior Vc := by
  intro hLI
  have hLT : (![x - 1, y] : Site 2) ∈ T := by
    have h : (![x + (-1), (y - 1) + 1] : Site 2) ∈ T :=
      ksc_saturated_diag Vc hsat (Or.inr rfl) (Or.inl rfl) hD (by simpa using hLI)
    simpa using h
  have hUT : (![x, y + 1] : Site 2) ∈ T := by
    have h : (![(x - 1) + 1, y + 1] : Site 2) ∈ T :=
      ksc_saturated_diag Vc hsat (Or.inl rfl) (Or.inl rfl) hLT (by simpa using hU)
    simpa using h
  exact hUnT hUT






theorem ewt_vert_wall_gaps_blocked {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {T : Set (Site 2)} (hsat : ksc_KingSaturated Vc T) (hTsub : T ⊆ jil_offSupportInterior Vc)
    {x y : ℤ} (hD : (![x, y - 1] : Site 2) ∈ T)
    (hU : (![x, y + 1] : Site 2) ∈ jil_offSupportInterior Vc)
    (hUnT : (![x, y + 1] : Site 2) ∉ T) :
    (![x, y] : Site 2) ∈ Vc.support ∧
      (![x + 1, y] : Site 2) ∉ jil_offSupportInterior Vc ∧
      (![x - 1, y] : Site 2) ∉ jil_offSupportInterior Vc :=
  ⟨ksc_separated_midOnSupport_vert Vc hsat hTsub hD hU hUnT,
   ewt_vert_wall_rightGap_blocked Vc hsat hD hU hUnT,
   ewt_vert_wall_leftGap_blocked Vc hsat hD hU hUnT⟩


















def ewt_BottomWallThick {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (seed : Site 2) :
    Prop :=
  ∀ (T : Set (Site 2)), seed ∈ T → T ⊆ jil_offSupportInterior Vc → ksc_KingSaturated Vc T →
    ∀ (M : ℤ) (q : Site 2), q ∈ jil_offSupportInterior Vc → q ∉ T →
      (∀ z ∈ jil_offSupportInterior Vc, z ∉ T → rlc_lexMeasure M q ≤ rlc_lexMeasure M z) →
      ((-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M)) →
      (-M < q 1 - 1 ∧ q 1 - 1 ≤ M) →
      (![q 0 - 1, q 1] : Site 2) ∈ Vc.support →
      (![q 0, q 1 - 1] : Site 2) ∈ Vc.support →
      
      ((![q 0 - 1, q 1 - 1] : Site 2) ∉ jil_offSupportInterior Vc ∧
        (![q 0 - 1, q 1 - 1] : Site 2) ∉ Vc.support) ∨
      ((![q 0 - 1, q 1 - 1] : Site 2) ∈ Vc.support ∧
        s((![q 0 - 1, q 1] : Site 2), (![q 0 - 1, q 1 - 1] : Site 2)) ∈ Vc.edges ∧
        s((![q 0, q 1 - 1] : Site 2), (![q 0 - 1, q 1 - 1] : Site 2)) ∈ Vc.edges) →
      
      (∀ wx : ℤ, (-M < wx ∧ wx ≤ M) →
        (![wx, q 1] : Site 2) ∈ jil_offSupportInterior Vc →
        (![wx, q 1] : Site 2) ∉ T →
        (![wx, q 1 - 1] : Site 2) ∈ Vc.support) →
      kns_ThickPoint Vc





theorem ewt_escape_structure_rowbox {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hsep : kns_KingSeparation Vc seed) :
    ∃ (T : Set (Site 2)), seed ∈ T ∧ T ⊆ jil_offSupportInterior Vc ∧ ksc_KingSaturated Vc T ∧
      ∃ (M : ℤ) (q : Site 2), q ∈ jil_offSupportInterior Vc ∧ q ∉ T ∧
        (∀ z ∈ jil_offSupportInterior Vc, z ∉ T →
          rlc_lexMeasure M q ≤ rlc_lexMeasure M z) ∧
        (![q 0 - 1, q 1] : Site 2) ∈ Vc.support ∧
        (![q 0, q 1 - 1] : Site 2) ∈ Vc.support ∧
        ((-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M)) ∧
        (-M < q 1 - 1 ∧ q 1 - 1 ≤ M) ∧
        (-M < q 0 - 1 ∧ q 0 - 1 ≤ M) := by
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
  have hq1box : -M < q 1 - 1 ∧ q 1 - 1 ≤ M := by rw [hM]; exact ⟨by omega, by omega⟩
  have hq0box : -M < q 0 - 1 ∧ q 0 - 1 ≤ M := by rw [hM]; exact ⟨by omega, by omega⟩
  obtain ⟨hW, hSsup⟩ :=
    kns_escape_axials_onSupport Vc hsat hTsub hqI hqnT M hmin hqbox hWbox hSbox
  exact ⟨T, hseedT, hTsub, hsat, M, q, hqI, hqnT, hmin, hW, hSsup, hqbox, hq1box, hq0box⟩








theorem ewt_noKingSeparation_of_fourThin {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseedI : seed ∈ jil_offSupportInterior Vc) (hthin : mci_FourThin Vc)
    (hres : ewt_BottomWallThick Vc seed) :
    ksc_NoKingSeparation Vc seed := by
  by_contra hns
  classical
  have hsep := (kns_kingSeparation_iff_not_noKingSeparation Vc hseedI).mpr hns
  obtain ⟨T, hseedT, hTsub, hsat, M, q, hqI, hqnT, hmin, hW, hS, hqbox, hq1box, hq0box⟩ :=
    ewt_escape_structure_rowbox Vc hsep
  
  have hbottom : ∀ wx : ℤ, (-M < wx ∧ wx ≤ M) →
      (![wx, q 1] : Site 2) ∈ jil_offSupportInterior Vc →
      (![wx, q 1] : Site 2) ∉ T →
      (![wx, q 1 - 1] : Site 2) ∈ Vc.support := by
    intro wx hwxbox hwI hwnT
    exact ewt_escapeRow_down_onSupport Vc hsat M hmin hqbox hwI hwnT ⟨hwxbox, hq1box⟩
  have htp : kns_ThickPoint Vc := by
    by_cases hCsup : (![q 0 - 1, q 1 - 1] : Site 2) ∈ Vc.support
    · by_cases hWC : s((![q 0 - 1, q 1] : Site 2), (![q 0 - 1, q 1 - 1] : Site 2)) ∈ Vc.edges
      · by_cases hSC : s((![q 0, q 1 - 1] : Site 2), (![q 0 - 1, q 1 - 1] : Site 2)) ∈ Vc.edges
        · exact hres T hseedT hTsub hsat M q hqI hqnT hmin hqbox hq1box hW hS
            (Or.inr ⟨hCsup, hWC, hSC⟩) hbottom
        · exact etp_thickPoint_of_swCorner Vc hW hS hCsup (Or.inr hSC)
      · exact etp_thickPoint_of_swCorner Vc hW hS hCsup (Or.inl hWC)
    · 
      have hCbox : (-M < q 0 - 1 ∧ q 0 - 1 ≤ M) ∧ (-M < q 1 - 1 ∧ q 1 - 1 ≤ M) :=
        ⟨hq0box, hq1box⟩
      have hcorner := kns_lexBelow_diag_corner Vc hsat hTsub hqI hqnT M hmin hqbox hCbox
      have hCext : (![q 0 - 1, q 1 - 1] : Site 2) ∉ jil_offSupportInterior Vc := by
        rcases hcorner with h | h
        · exact absurd h hCsup
        · exact h
      exact hres T hseedT hTsub hsat M q hqI hqnT hmin hqbox hq1box hW hS
        (Or.inl ⟨hCext, hCsup⟩) hbottom
  exact (kns_thickPoint_iff_not_fourThin Vc).mp htp hthin







theorem ewt_kingRowLinked_of_fourThin {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseedI : seed ∈ jil_offSupportInterior Vc) (hthin : mci_FourThin Vc)
    (hres : ewt_BottomWallThick Vc seed) :
    mci_KingRowLinked Vc seed :=
  ksc_kingRowLinked_of_noKingSeparation Vc hseedI
    (ewt_noKingSeparation_of_fourThin Vc hseedI hthin hres)









theorem ewt_bottomWallThick_of_escapeWallThick {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hetp : etp_EscapeWallThick Vc seed) :
    ewt_BottomWallThick Vc seed := by
  intro T hseedT hTsub hsat M q hqI hqnT hmin _hqbox _hq1box hW hS hcorner _hbottom
  exact hetp T hseedT hTsub hsat M q hqI hqnT hmin hW hS hcorner






theorem ewt_bottomWallThick_of_escapeThickPoint {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hktp : kns_EscapeThickPoint Vc seed) :
    ewt_BottomWallThick Vc seed := by
  intro T hseedT hTsub hsat M q hqI hqnT hmin _hqbox _hq1box hW hS _hcorner _hbottom
  exact hktp T hseedT hTsub hsat M q hqI hqnT hmin hW hS














theorem ewt_fjord_bottomWallThick : ewt_BottomWallThick sdc_fjord (![5, 1] : Site 2) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => kns_fjord_thickPoint




theorem ewt_fjord_nonvacuous :
    kns_KingSeparation sdc_fjord (![5, 1] : Site 2) ∧ kns_ThickPoint sdc_fjord ∧
    ewt_BottomWallThick sdc_fjord (![5, 1] : Site 2) ∧ ¬ mci_FourThin sdc_fjord :=
  ⟨kns_fjord_kingSeparation, kns_fjord_thickPoint, ewt_fjord_bottomWallThick,
   mci_fjord_not_fourThin⟩



theorem ewt_ksd_bottomWallThick : ewt_BottomWallThick ksd_stair (![1, 1] : Site 2) := by
  intro T hseedT hTsub hsat M q hqI hqnT _hmin _hqbox _hq1box _hW _hS _hcorner _hbottom
  exact absurd (ksc_ksd_noKingSeparation T hseedT hTsub hsat hqI) hqnT


theorem ewt_kda_bottomWallThick : ewt_BottomWallThick kda_stairDR (![3, 1] : Site 2) := by
  intro T hseedT hTsub hsat M q hqI hqnT _hmin _hqbox _hq1box _hW _hS _hcorner _hbottom
  exact absurd (ksc_kda_noKingSeparation T hseedT hTsub hsat hqI) hqnT

















theorem ewt_kingRowLinked_summary {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hseedI : seed ∈ jil_offSupportInterior Vc) (hthin : mci_FourThin Vc) :
    ewt_BottomWallThick Vc seed → mci_KingRowLinked Vc seed :=
  ewt_kingRowLinked_of_fourThin Vc hseedI hthin

end Lattice

end StatMech
