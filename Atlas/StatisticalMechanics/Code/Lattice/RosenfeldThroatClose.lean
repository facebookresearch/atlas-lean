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
import Code.Lattice.EscapeWallThickClose
import Code.Lattice.GlobalThickPointClose
import Code.Lattice.CrossArcThickClose
import Code.Lattice.WindingPinchClose
import Code.Lattice.PeierlsCycleClose

open Set SimpleGraph Function

namespace StatMech

namespace Lattice



















theorem rtc_thickPoint_of_eastThroat {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hcyc : Vc.IsCycle) {e y : ℤ}
    (hE : (![e, y] : Site 2) ∈ Vc.support)
    (hSeed : (![e + 1, y] : Site 2) ∈ Vc.support)
    (hUp : (![e, y + 1] : Site 2) ∈ Vc.support)
    (hDn : (![e, y - 1] : Site 2) ∈ Vc.support) :
    kns_ThickPoint Vc := by
  refine pcy_thickPoint_of_three_support_neighbors Vc hcyc hE
    (v₁ := (![e + 1, y] : Site 2)) (v₂ := (![e, y + 1] : Site 2)) (v₃ := (![e, y - 1] : Site 2))
    ?_ ?_ ?_ hSeed hUp hDn ?_ ?_ ?_
  · rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
  · rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
  · rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
  · intro h; have := congrFun h 0; simp only [Matrix.cons_val_zero] at this; omega
  · intro h; have := congrFun h 0; simp only [Matrix.cons_val_zero] at this; omega
  · intro h; have := congrFun h 1
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at this; omega






theorem rtc_thickPoint_of_seedWall_nonConsec {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {e y : ℤ}
    (hE : (![e, y] : Site 2) ∈ Vc.support)
    (hSeed : (![e + 1, y] : Site 2) ∈ Vc.support)
    (hnon : s((![e, y] : Site 2), (![e + 1, y] : Site 2)) ∉ Vc.edges) :
    kns_ThickPoint Vc :=
  gtp_thickPoint_of_adj_horiz Vc hE hSeed hnon





theorem rtc_thickPoint_of_upWall_nonConsec {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {e y : ℤ}
    (hE : (![e, y] : Site 2) ∈ Vc.support)
    (hUp : (![e, y + 1] : Site 2) ∈ Vc.support)
    (hnon : s((![e, y] : Site 2), (![e, y + 1] : Site 2)) ∉ Vc.edges) :
    kns_ThickPoint Vc :=
  gtp_thickPoint_of_adj_vert Vc hE hUp hnon

























theorem rtc_eastThroat_discharge {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hcyc : Vc.IsCycle) {e y : ℤ}
    (hE : (![e, y] : Site 2) ∈ Vc.support)
    (hSeed : (![e + 1, y] : Site 2) ∈ Vc.support)
    (hUp : (![e, y + 1] : Site 2) ∈ Vc.support)
    (hSE : (![e, y - 1] : Site 2) ∈ Vc.support ∨
            (![e, y - 1] : Site 2) ∉ jil_offSupportInterior Vc) :
    kns_ThickPoint Vc ∨
      ((![e, y - 1] : Site 2) ∉ jil_offSupportInterior Vc ∧
        (![e, y - 1] : Site 2) ∉ Vc.support ∧
        s((![e, y] : Site 2), (![e + 1, y] : Site 2)) ∈ Vc.edges ∧
        s((![e, y] : Site 2), (![e, y + 1] : Site 2)) ∈ Vc.edges) := by
  by_cases hDnSup : (![e, y - 1] : Site 2) ∈ Vc.support
  · 
    exact Or.inl (rtc_thickPoint_of_eastThroat Vc hcyc hE hSeed hUp hDnSup)
  · 
    have hDnExt : (![e, y - 1] : Site 2) ∉ jil_offSupportInterior Vc := by
      rcases hSE with h | h
      · exact absurd h hDnSup
      · exact h
    by_cases hseedEdge : s((![e, y] : Site 2), (![e + 1, y] : Site 2)) ∈ Vc.edges
    · by_cases hupEdge : s((![e, y] : Site 2), (![e, y + 1] : Site 2)) ∈ Vc.edges
      · exact Or.inr ⟨hDnExt, hDnSup, hseedEdge, hupEdge⟩
      · exact Or.inl (rtc_thickPoint_of_upWall_nonConsec Vc hE hUp hupEdge)
    · exact Or.inl (rtc_thickPoint_of_seedWall_nonConsec Vc hE hSeed hseedEdge)



















def rtc_CrossArcThick {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (seed : Site 2) : Prop :=
  Vc.IsCycle →
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
      (∀ (e : ℤ), q 0 < e → (![e, q 1] : Site 2) ∈ Vc.support →
        (∀ x : ℤ, q 0 ≤ x → x < e → (![x, q 1] : Site 2) ∈ jil_offSupportInterior Vc) →
        (![e - 1, q 1 - 1] : Site 2) ∈ Vc.support →
        
        (![e + 1, q 1] : Site 2) ∈ Vc.support →
        (![e, q 1 + 1] : Site 2) ∈ Vc.support →
        ((![e, q 1 - 1] : Site 2) ∉ jil_offSupportInterior Vc ∧
          (![e, q 1 - 1] : Site 2) ∉ Vc.support) ∨
        ((![e, q 1 - 1] : Site 2) ∈ Vc.support ∧
          s((![e, q 1] : Site 2), (![e, q 1 - 1] : Site 2)) ∈ Vc.edges ∧
          s((![e - 1, q 1 - 1] : Site 2), (![e, q 1 - 1] : Site 2)) ∈ Vc.edges) →
        kns_ThickPoint Vc)






theorem rtc_crossArcThick_of_pcy {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hpcy : pcy_CrossArcThick Vc seed) : rtc_CrossArcThick Vc seed := by
  intro hcyc T hseedT hTsub hsat M q hqI hqnT hmin hqbox hq1box hW hS hSWclause hbottom
    e he₁ he₂ he₃ hbotCorner _hSeed _hUp hSEclause
  exact hpcy hcyc T hseedT hTsub hsat M q hqI hqnT hmin hqbox hq1box hW hS hSWclause hbottom
    e he₁ he₂ he₃ hbotCorner hSEclause





theorem rtc_crossArcThick_of_crossArcThick {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hcat : cat_CrossArcThick Vc seed) : rtc_CrossArcThick Vc seed := by
  intro _hcyc T hseedT hTsub hsat M q hqI hqnT hmin hqbox hq1box hW hS hSWclause hbottom
    e he₁ he₂ he₃ hbotCorner _hSeed _hUp hSEclause
  exact hcat T hseedT hTsub hsat M q hqI hqnT hmin hqbox hq1box hW hS hSWclause hbottom
    e he₁ he₂ he₃ hbotCorner hSEclause


















theorem rtc_eastClause_discharged {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hcyc : Vc.IsCycle) {q : Site 2} {e : ℤ}
    (hE : (![e, q 1] : Site 2) ∈ Vc.support)
    (hSeed : (![e + 1, q 1] : Site 2) ∈ Vc.support)
    (hUp : (![e, q 1 + 1] : Site 2) ∈ Vc.support)
    (hSEclause :
      ((![e, q 1 - 1] : Site 2) ∉ jil_offSupportInterior Vc ∧
        (![e, q 1 - 1] : Site 2) ∉ Vc.support) ∨
      ((![e, q 1 - 1] : Site 2) ∈ Vc.support ∧
        s((![e, q 1] : Site 2), (![e, q 1 - 1] : Site 2)) ∈ Vc.edges ∧
        s((![e - 1, q 1 - 1] : Site 2), (![e, q 1 - 1] : Site 2)) ∈ Vc.edges)) :
    kns_ThickPoint Vc ∨
      ((![e, q 1 - 1] : Site 2) ∉ jil_offSupportInterior Vc ∧
        (![e, q 1 - 1] : Site 2) ∉ Vc.support ∧
        s((![e, q 1] : Site 2), (![e + 1, q 1] : Site 2)) ∈ Vc.edges ∧
        s((![e, q 1] : Site 2), (![e, q 1 + 1] : Site 2)) ∈ Vc.edges) := by
  have hSE : (![e, q 1 - 1] : Site 2) ∈ Vc.support ∨
      (![e, q 1 - 1] : Site 2) ∉ jil_offSupportInterior Vc := by
    rcases hSEclause with ⟨hext, _⟩ | ⟨hsup, _, _⟩
    · exact Or.inr hext
    · exact Or.inl hsup
  exact rtc_eastThroat_discharge Vc hcyc hE hSeed hUp hSE














theorem rtc_fjord_eastThroat (hcyc : sdc_fjord.IsCycle) : kns_ThickPoint sdc_fjord := by
  obtain ⟨h31, _, _, _, h30, h32, h41, _, _, _⟩ := pcy_fjord_throat_three_neighbors
  exact rtc_thickPoint_of_eastThroat sdc_fjord hcyc (e := 3) (y := 1) h31 h41 h32 h30








theorem rtc_fjord_crossArcThick : rtc_CrossArcThick sdc_fjord (![5, 1] : Site 2) := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  exact kns_fjord_thickPoint





theorem rtc_fjord_nonvacuous :
    kns_KingSeparation sdc_fjord (![5, 1] : Site 2) ∧ kns_ThickPoint sdc_fjord ∧
    rtc_CrossArcThick sdc_fjord (![5, 1] : Site 2) ∧ ¬ mci_FourThin sdc_fjord :=
  ⟨kns_fjord_kingSeparation, kns_fjord_thickPoint, rtc_fjord_crossArcThick,
   mci_fjord_not_fourThin⟩






theorem rtc_ksd_crossArcThick : rtc_CrossArcThick ksd_stair (![1, 1] : Site 2) :=
  rtc_crossArcThick_of_crossArcThick ksd_stair cat_ksd_crossArcThick


theorem rtc_kda_crossArcThick : rtc_CrossArcThick kda_stairDR (![3, 1] : Site 2) :=
  rtc_crossArcThick_of_crossArcThick kda_stairDR cat_kda_crossArcThick










theorem rtc_kingRowLinked_of_fourThin_cycle {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hcyc : Vc.IsCycle) (hseedI : seed ∈ jil_offSupportInterior Vc)
    (hthin : mci_FourThin Vc) (hpcy : pcy_CrossArcThick Vc seed) :
    mci_KingRowLinked Vc seed :=
  pcy_kingRowLinked_of_fourThin_cycle Vc hcyc hseedI hthin hpcy

















theorem rtc_summary {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) {seed : Site 2}
    (hcyc : Vc.IsCycle) (hseedI : seed ∈ jil_offSupportInterior Vc) (hthin : mci_FourThin Vc) :
    pcy_CrossArcThick Vc seed → rtc_CrossArcThick Vc seed ∧ mci_KingRowLinked Vc seed :=
  fun hpcy => ⟨rtc_crossArcThick_of_pcy Vc hpcy,
    rtc_kingRowLinked_of_fourThin_cycle Vc hcyc hseedI hthin hpcy⟩

end Lattice

end StatMech
