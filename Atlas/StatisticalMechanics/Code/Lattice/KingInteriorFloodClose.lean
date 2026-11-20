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

open Set SimpleGraph Function

namespace StatMech

namespace Lattice








theorem kif_kingAdj_left (x y : ℤ) : mci_kingGraph.Adj (![x, y] : Site 2) ![x - 1, y] := by
  refine ⟨by simp, by simp, ?_⟩
  intro h; have := congrFun h 0; simp only [Matrix.cons_val_zero] at this; omega


theorem kif_kingAdj_down (x y : ℤ) : mci_kingGraph.Adj (![x, y] : Site 2) ![x, y - 1] := by
  refine ⟨by simp, by simp, ?_⟩
  intro h; have := congrFun h 1
  simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at this; omega



theorem kif_kingAdj_right (x y : ℤ) : mci_kingGraph.Adj (![x, y] : Site 2) ![x + 1, y] := by
  refine ⟨by simp, by simp, ?_⟩
  intro h; have := congrFun h 0; simp only [Matrix.cons_val_zero] at this; omega












def kif_KingDownLink {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (seed : Site 2) (M : ℤ) :
    Prop :=
  ∀ z ∈ jil_offSupportInterior Vc, z ≠ seed →
    ∃ z' ∈ jil_offSupportInterior Vc,
      rlc_lexMeasure M z' < rlc_lexMeasure M z ∧
      ∃ p : mci_kingGraph.Walk z z', ∀ w ∈ p.support, w ∈ jil_offSupportInterior Vc







theorem kif_kingRowLinked_of_kingDownLink {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (M : ℤ) (hdl : kif_KingDownLink Vc seed M) :
    mci_KingRowLinked Vc seed := by
  have key : ∀ n : ℕ, ∀ z ∈ jil_offSupportInterior Vc, rlc_lexMeasure M z = n →
      ∃ p : mci_kingGraph.Walk z seed, ∀ w ∈ p.support, w ∈ jil_offSupportInterior Vc := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro z hz hn
      by_cases hzs : z = seed
      · cases hzs
        exact ⟨SimpleGraph.Walk.nil, by
          intro w hw
          rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw
          cases hw; exact hz⟩
      · obtain ⟨z', hz', hlt, p, hp⟩ := hdl z hz hzs
        rw [hn] at hlt
        obtain ⟨q, hq⟩ := ih (rlc_lexMeasure M z') hlt z' hz' rfl
        refine ⟨p.append q, ?_⟩
        intro w hw
        rw [SimpleGraph.Walk.support_append, List.mem_append] at hw
        rcases hw with h | h
        · exact hp w h
        · exact hq w (List.mem_of_mem_tail h)
  intro z hz
  exact key (rlc_lexMeasure M z) z hz rfl









theorem kif_descend_via_leftStep {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (M : ℤ) (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
    {x y : ℤ}
    (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hleft : (![x - 1, y] : Site 2) ∉ Vc.support) :
    ∃ z' ∈ jil_offSupportInterior Vc,
      rlc_lexMeasure M z' < rlc_lexMeasure M (![x, y] : Site 2) ∧
      ∃ p : mci_kingGraph.Walk (![x, y] : Site 2) z',
        ∀ w ∈ p.support, w ∈ jil_offSupportInterior Vc := by
  have hz' : (![x - 1, y] : Site 2) ∈ jil_offSupportInterior Vc :=
    rlc_left_mem_interior Vc hz hleft
  refine ⟨![x - 1, y], hz', ?_, ?_⟩
  · have hzL := (jil_mem_offSupportInterior Vc _ |>.mp hz).2
    have hz'L := (jil_mem_offSupportInterior Vc _ |>.mp hz').2
    obtain ⟨⟨hb0a, hb0b⟩, ⟨hb1a, hb1b⟩⟩ := hMb _ hzL
    obtain ⟨⟨hd0a, hd0b⟩, ⟨hd1a, hd1b⟩⟩ := hMb _ hz'L
    refine rlc_lexMeasure_lt hb0a hb0b hb1a hb1b (by simpa using hd0a) (by simpa using hd0b)
      (by simpa using hd1a) (by simpa using hd1b) ?_
    right; simp
  · refine ⟨SimpleGraph.Walk.cons (kif_kingAdj_left x y) SimpleGraph.Walk.nil, ?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h
    · subst h; exact hz
    · subst h; exact hz'




theorem kif_descend_via_downStep {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (M : ℤ) (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
    {x y : ℤ}
    (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hdown : (![x, y - 1] : Site 2) ∉ Vc.support) :
    ∃ z' ∈ jil_offSupportInterior Vc,
      rlc_lexMeasure M z' < rlc_lexMeasure M (![x, y] : Site 2) ∧
      ∃ p : mci_kingGraph.Walk (![x, y] : Site 2) z',
        ∀ w ∈ p.support, w ∈ jil_offSupportInterior Vc := by
  have hz' : (![x, y - 1] : Site 2) ∈ jil_offSupportInterior Vc :=
    rlc_down_mem_interior Vc hz hdown
  refine ⟨![x, y - 1], hz', ?_, ?_⟩
  · have hzL := (jil_mem_offSupportInterior Vc _ |>.mp hz).2
    have hz'L := (jil_mem_offSupportInterior Vc _ |>.mp hz').2
    obtain ⟨⟨hb0a, hb0b⟩, ⟨hb1a, hb1b⟩⟩ := hMb _ hzL
    obtain ⟨⟨hd0a, hd0b⟩, ⟨hd1a, hd1b⟩⟩ := hMb _ hz'L
    refine rlc_lexMeasure_lt hb0a hb0b hb1a hb1b (by simpa using hd0a) (by simpa using hd0b)
      (by simpa using hd1a) (by simpa using hd1b) ?_
    left; simp
  · refine ⟨SimpleGraph.Walk.cons (kif_kingAdj_down x y) SimpleGraph.Walk.nil, ?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h
    · subst h; exact hz
    · subst h; exact hz'









theorem kif_descend_via_diagDR {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (M : ℤ) (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
    {x y : ℤ}
    (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (helbow : (![x + 1, y] : Site 2) ∉ Vc.support)
    (hdiag : (![x + 1, y - 1] : Site 2) ∉ Vc.support) :
    ∃ z' ∈ jil_offSupportInterior Vc,
      rlc_lexMeasure M z' < rlc_lexMeasure M (![x, y] : Site 2) ∧
      ∃ p : mci_kingGraph.Walk (![x, y] : Site 2) z',
        ∀ w ∈ p.support, w ∈ jil_offSupportInterior Vc := by
  
  have helbowI : (![x + 1, y] : Site 2) ∈ jil_offSupportInterior Vc := by
    have hadj : (hypercubicLattice 2).Adj (![x, y] : Site 2) ![x + 1, y] := by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
    exact mci_offSupport_neighbor_interior Vc hz hadj helbow
  
  have hdiagI : (![x + 1, y - 1] : Site 2) ∈ jil_offSupportInterior Vc := by
    have hadj : (hypercubicLattice 2).Adj (![x + 1, y] : Site 2) ![x + 1, y - 1] := by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
    exact mci_offSupport_neighbor_interior Vc helbowI hadj hdiag
  refine ⟨![x + 1, y - 1], hdiagI, ?_, ?_⟩
  · have hzL := (jil_mem_offSupportInterior Vc _ |>.mp hz).2
    have hz'L := (jil_mem_offSupportInterior Vc _ |>.mp hdiagI).2
    obtain ⟨⟨hb0a, hb0b⟩, ⟨hb1a, hb1b⟩⟩ := hMb _ hzL
    obtain ⟨⟨hd0a, hd0b⟩, ⟨hd1a, hd1b⟩⟩ := hMb _ hz'L
    refine rlc_lexMeasure_lt hb0a hb0b hb1a hb1b (by simpa using hd0a) (by simpa using hd0b)
      (by simpa using hd1a) (by simpa using hd1b) ?_
    left; simp
  · have hadj2 : mci_kingGraph.Adj (![x + 1, y] : Site 2) ![x + 1, y - 1] :=
      kif_kingAdj_down (x + 1) y
    refine ⟨SimpleGraph.Walk.cons (kif_kingAdj_right x y)
      (SimpleGraph.Walk.cons hadj2 SimpleGraph.Walk.nil), ?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_nil] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h | h
    · subst h; exact hz
    · subst h; exact helbowI
    · subst h; exact hdiagI










theorem kif_run_kingWalk_interior {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y cx : ℤ}
    (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hxcx : x ≤ cx)
    (hrun : ∀ t : ℤ, x ≤ t → t ≤ cx → (![t, y] : Site 2) ∉ Vc.support) :
    ∃ p : mci_kingGraph.Walk (![x, y] : Site 2) ![cx, y],
      ∀ w ∈ p.support, w ∈ jil_offSupportInterior Vc := by
  have hxoff : (![x, y] : Site 2) ∉ Vc.support := (jil_mem_offSupportInterior Vc _ |>.mp hz).1
  obtain ⟨preach, hpreach⟩ :=
    jil_hsegment_reachable_offSupport {p | p ∈ Vc.support} (lo := x) (hi := cx) (y := y)
      (x₁ := x) (x₂ := cx) (by simpa using hxoff) le_rfl hxcx hxcx le_rfl
      (by intro t ht ht'; simpa using hrun t ht ht')
  have hpreach' : ∀ w ∈ preach.support, w ∉ Vc.support := by
    intro w hw; have := hpreach w hw; simpa using this
  have hint := mci_offSupport_walk_interior Vc preach hpreach' hz
  refine ⟨preach.mapLe mci_hyper_le_king, ?_⟩
  intro w hw
  rw [SimpleGraph.Walk.support_mapLe_eq_support mci_hyper_le_king preach] at hw
  exact hint w hw






theorem kif_descend_via_segmentDown {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (M : ℤ) (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
    {x y cx : ℤ}
    (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hxcx : x ≤ cx)
    (hrun : ∀ t : ℤ, x ≤ t → t ≤ cx → (![t, y] : Site 2) ∉ Vc.support)
    (hcdown : (![cx, y - 1] : Site 2) ∉ Vc.support) :
    ∃ z' ∈ jil_offSupportInterior Vc,
      rlc_lexMeasure M z' < rlc_lexMeasure M (![x, y] : Site 2) ∧
      ∃ p : mci_kingGraph.Walk (![x, y] : Site 2) z',
        ∀ w ∈ p.support, w ∈ jil_offSupportInterior Vc := by
  obtain ⟨pw, hpw⟩ := kif_run_kingWalk_interior Vc hz hxcx hrun
  have hc : (![cx, y] : Site 2) ∈ jil_offSupportInterior Vc :=
    hpw _ pw.end_mem_support
  have hz' : (![cx, y - 1] : Site 2) ∈ jil_offSupportInterior Vc :=
    rlc_down_mem_interior Vc hc hcdown
  refine ⟨![cx, y - 1], hz', ?_, ?_⟩
  · have hzL := (jil_mem_offSupportInterior Vc _ |>.mp hz).2
    have hz'L := (jil_mem_offSupportInterior Vc _ |>.mp hz').2
    obtain ⟨⟨hb0a, hb0b⟩, ⟨hb1a, hb1b⟩⟩ := hMb _ hzL
    obtain ⟨⟨hd0a, hd0b⟩, ⟨hd1a, hd1b⟩⟩ := hMb _ hz'L
    refine rlc_lexMeasure_lt hb0a hb0b hb1a hb1b (by simpa using hd0a) (by simpa using hd0b)
      (by simpa using hd1a) (by simpa using hd1b) ?_
    left; simp
  · refine ⟨pw.append (SimpleGraph.Walk.cons (kif_kingAdj_down cx y) SimpleGraph.Walk.nil), ?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_append, List.mem_append] at hw
    rcases hw with h | h
    · exact hpw w h
    · have hmem := List.mem_of_mem_tail h
      rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h1 | h1
      · subst h1; exact hc
      · subst h1; exact hz'








theorem kif_descend_via_segmentDiagDR {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (M : ℤ) (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
    {x y cx : ℤ}
    (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hxcx : x ≤ cx)
    (hrun : ∀ t : ℤ, x ≤ t → t ≤ cx → (![t, y] : Site 2) ∉ Vc.support)
    (helbow : (![cx + 1, y] : Site 2) ∉ Vc.support)
    (hdiag : (![cx + 1, y - 1] : Site 2) ∉ Vc.support) :
    ∃ z' ∈ jil_offSupportInterior Vc,
      rlc_lexMeasure M z' < rlc_lexMeasure M (![x, y] : Site 2) ∧
      ∃ p : mci_kingGraph.Walk (![x, y] : Site 2) z',
        ∀ w ∈ p.support, w ∈ jil_offSupportInterior Vc := by
  obtain ⟨pw, hpw⟩ := kif_run_kingWalk_interior Vc hz hxcx hrun
  have hc : (![cx, y] : Site 2) ∈ jil_offSupportInterior Vc :=
    hpw _ pw.end_mem_support
  
  have helbowI : (![cx + 1, y] : Site 2) ∈ jil_offSupportInterior Vc := by
    have hadj : (hypercubicLattice 2).Adj (![cx, y] : Site 2) ![cx + 1, y] := by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
    exact mci_offSupport_neighbor_interior Vc hc hadj helbow
  have hdiagI : (![cx + 1, y - 1] : Site 2) ∈ jil_offSupportInterior Vc := by
    have hadj : (hypercubicLattice 2).Adj (![cx + 1, y] : Site 2) ![cx + 1, y - 1] := by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
    exact mci_offSupport_neighbor_interior Vc helbowI hadj hdiag
  refine ⟨![cx + 1, y - 1], hdiagI, ?_, ?_⟩
  · 
    
    have hzL := (jil_mem_offSupportInterior Vc _ |>.mp hz).2
    have hz'L := (jil_mem_offSupportInterior Vc _ |>.mp hdiagI).2
    obtain ⟨⟨hb0a, hb0b⟩, ⟨hb1a, hb1b⟩⟩ := hMb _ hzL
    obtain ⟨⟨hd0a, hd0b⟩, ⟨hd1a, hd1b⟩⟩ := hMb _ hz'L
    refine rlc_lexMeasure_lt hb0a hb0b hb1a hb1b (by simpa using hd0a) (by simpa using hd0b)
      (by simpa using hd1a) (by simpa using hd1b) ?_
    left; simp
  · 
    have hadj2 : mci_kingGraph.Adj (![cx + 1, y] : Site 2) ![cx + 1, y - 1] :=
      kif_kingAdj_down (cx + 1) y
    refine ⟨pw.append (SimpleGraph.Walk.cons (kif_kingAdj_right cx y)
      (SimpleGraph.Walk.cons hadj2 SimpleGraph.Walk.nil)), ?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_append, List.mem_append] at hw
    rcases hw with h | h
    · exact hpw w h
    · 
      rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_nil] at h
      simp only [List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h1 | h1
      · subst h1; exact helbowI
      · subst h1; exact hdiagI

























def kif_KingSegmentDown {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (seed : Site 2) : Prop :=
  ∀ z ∈ jil_offSupportInterior Vc, z ≠ seed →
    (![z 0 - 1, z 1] : Site 2) ∈ Vc.support →
    ∃ cx : ℤ, z 0 ≤ cx ∧
      (∀ t : ℤ, z 0 ≤ t → t ≤ cx → (![t, z 1] : Site 2) ∉ Vc.support) ∧
      ((![cx, z 1 - 1] : Site 2) ∉ Vc.support ∨
        ((![cx + 1, z 1] : Site 2) ∉ Vc.support ∧
          (![cx + 1, z 1 - 1] : Site 2) ∉ Vc.support))






theorem kif_kingDownLink_of_kingSegmentDown {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (M : ℤ)
    (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
    (hres : kif_KingSegmentDown Vc seed) :
    kif_KingDownLink Vc seed M := by
  intro z hz hzs
  have hzeq : z = ![z 0, z 1] := by ext i; fin_cases i <;> simp
  by_cases hleft : (![z 0 - 1, z 1] : Site 2) ∈ Vc.support
  · 
    obtain ⟨cx, hxcx, hrun, hdesc⟩ := hres z hz hzs hleft
    rw [hzeq] at hz ⊢
    rcases hdesc with hdown | ⟨helbow, hdiag⟩
    · exact kif_descend_via_segmentDown Vc M hMb (x := z 0) (y := z 1) (cx := cx) hz
        (by simpa using hxcx)
        (by intro t ht ht'; have := hrun t (by simpa using ht) ht'; simpa using this)
        (by simpa using hdown)
    · exact kif_descend_via_segmentDiagDR Vc M hMb (x := z 0) (y := z 1) (cx := cx) hz
        (by simpa using hxcx)
        (by intro t ht ht'; have := hrun t (by simpa using ht) ht'; simpa using this)
        (by simpa using helbow) (by simpa using hdiag)
  · 
    rw [hzeq] at hz hleft ⊢
    have hl : (![(![z 0, z 1] : Site 2) 0 - 1, (![z 0, z 1] : Site 2) 1] : Site 2)
        ∉ Vc.support := by simpa using hleft
    exact kif_descend_via_leftStep Vc M hMb hz hl






theorem kif_kingRowLinked_of_kingSegmentDown {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (M : ℤ)
    (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
    (hres : kif_KingSegmentDown Vc seed) :
    mci_KingRowLinked Vc seed :=
  kif_kingRowLinked_of_kingDownLink Vc M (kif_kingDownLink_of_kingSegmentDown Vc M hMb hres)







theorem kif_kingInteriorConnected_of_kingSegmentDown {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) {z₀ : Site 2} (hz₀ : z₀ ∈ jil_offSupportInterior Vc)
    (hres : ∀ seed : Site 2, kif_KingSegmentDown Vc seed) :
    mci_KingInteriorConnected Vc := by
  obtain ⟨M, hMb⟩ := rlc_interior_bounded Vc
  obtain ⟨seed, hseed, _⟩ := rlc_exists_lexMin_seed Vc hz₀ M
  exact ⟨seed, hseed, kif_kingRowLinked_of_kingSegmentDown Vc M hMb (hres seed)⟩














theorem kif_kingSegmentDown_body_of_downOffSupport {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z : Site 2} (hzoff : z ∉ Vc.support) (hdown : (![z 0, z 1 - 1] : Site 2) ∉ Vc.support) :
    ∃ cx : ℤ, z 0 ≤ cx ∧
      (∀ t : ℤ, z 0 ≤ t → t ≤ cx → (![t, z 1] : Site 2) ∉ Vc.support) ∧
      ((![cx, z 1 - 1] : Site 2) ∉ Vc.support ∨
        ((![cx + 1, z 1] : Site 2) ∉ Vc.support ∧
          (![cx + 1, z 1 - 1] : Site 2) ∉ Vc.support)) := by
  obtain ⟨cx, hxcx, hrun, hcdown⟩ :=
    rlc_segmentDown_body_of_downOffSupport Vc hzoff hdown
  exact ⟨cx, hxcx, hrun, Or.inl hcdown⟩









theorem kif_kingSegmentDown_body_via_diagDR {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z0 z1 : ℤ}
    (hzoff : (![z0, z1] : Site 2) ∉ Vc.support)
    (helbow : (![z0 + 1, z1] : Site 2) ∉ Vc.support)
    (hdiag : (![z0 + 1, z1 - 1] : Site 2) ∉ Vc.support) :
    ∃ cx : ℤ, z0 ≤ cx ∧
      (∀ t : ℤ, z0 ≤ t → t ≤ cx → (![t, z1] : Site 2) ∉ Vc.support) ∧
      ((![cx, z1 - 1] : Site 2) ∉ Vc.support ∨
        ((![cx + 1, z1] : Site 2) ∉ Vc.support ∧
          (![cx + 1, z1 - 1] : Site 2) ∉ Vc.support)) := by
  refine ⟨z0, le_rfl, ?_, Or.inr ⟨helbow, hdiag⟩⟩
  intro t ht ht'
  have : t = z0 := le_antisymm ht' ht
  subst this
  exact hzoff












theorem kif_fjord_on_70 : (![7, 0] : Site 2) ∈ sdc_fjord.support := by
  unfold sdc_fjord
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse]
  right; right; right; right; right; left
  exact sdc_vsegUp_mem' 7 0 4 0 (by norm_num) (by norm_num)






theorem kif_fjord_body_false :
    ¬ ∃ cx : ℤ, (5 : ℤ) ≤ cx ∧
        (∀ t : ℤ, (5 : ℤ) ≤ t → t ≤ cx → (![t, 1] : Site 2) ∉ sdc_fjord.support) ∧
        ((![cx, 1 - 1] : Site 2) ∉ sdc_fjord.support ∨
          ((![cx + 1, 1] : Site 2) ∉ sdc_fjord.support ∧
            (![cx + 1, 1 - 1] : Site 2) ∉ sdc_fjord.support)) := by
  rintro ⟨cx, hxcx, hrun, hdesc⟩
  
  have hcx6 : cx ≤ 6 := by
    by_contra hcon
    push Not at hcon
    exact hrun 7 (by norm_num) (by omega) sdc_fjord_on_71
  have hcx5 : cx = 5 ∨ cx = 6 := by omega
  rcases hdesc with hdown | ⟨_helbow, hdiag⟩
  · 
    have : (![cx, (1 : ℤ) - 1] : Site 2) ∈ sdc_fjord.support := by
      rcases hcx5 with h | h <;> subst h
      · simpa using sdc_fjord_on_50
      · simpa using sdc_fjord_on_60
    exact hdown this
  · 
    have : (![cx + 1, (1 : ℤ) - 1] : Site 2) ∈ sdc_fjord.support := by
      rcases hcx5 with h | h <;> subst h
      · simpa using sdc_fjord_on_60
      · simpa using kif_fjord_on_70
    exact hdiag this







theorem kif_fjord_kingSegmentDown_false :
    ∃ (seed : Site 2), seed ∈ jil_offSupportInterior sdc_fjord ∧
      ¬ kif_KingSegmentDown sdc_fjord seed := by
  obtain ⟨M, hMb⟩ := rlc_interior_bounded sdc_fjord
  obtain ⟨seed, hseed, hmin⟩ :=
    rlc_exists_lexMin_seed sdc_fjord sdc_fjord_mem_interior_11 M
  refine ⟨seed, hseed, ?_⟩
  intro hres
  have hbox11 := hMb _ sdc_fjord_interior_11
  have hbox51 := hMb _ sdc_fjord_interior_51
  have hlt : rlc_lexMeasure M (![1, 1] : Site 2) < rlc_lexMeasure M (![5, 1] : Site 2) := by
    obtain ⟨⟨h0a, h0b⟩, ⟨h1a, h1b⟩⟩ := hbox11
    obtain ⟨⟨g0a, g0b⟩, ⟨g1a, g1b⟩⟩ := hbox51
    refine rlc_lexMeasure_lt (z := (![5, 1] : Site 2)) (z' := (![1, 1] : Site 2))
      (by simpa using g0a) (by simpa using g0b) (by simpa using g1a) (by simpa using g1b)
      (by simpa using h0a) (by simpa using h0b) (by simpa using h1a) (by simpa using h1b)
      (Or.inr ⟨by norm_num, by norm_num⟩)
  have hseedne : seed ≠ (![5, 1] : Site 2) := by
    intro heq
    have := hmin _ sdc_fjord_mem_interior_11
    rw [heq] at this
    omega
  have hleft : (![(![5, 1] : Site 2) 0 - 1, (![5, 1] : Site 2) 1] : Site 2) ∈ sdc_fjord.support := by
    simpa using sdc_fjord_on_41
  obtain ⟨cx, hxcx, hrun, hdesc⟩ :=
    hres (![5, 1] : Site 2) sdc_fjord_mem_interior_51 (fun h => hseedne h.symm) hleft
  refine kif_fjord_body_false ⟨cx, by simpa using hxcx, ?_, ?_⟩
  · intro t ht ht'
    have := hrun t (by simpa using ht) ht'
    simpa using this
  · rcases hdesc with hdown | ⟨helbow, hdiag⟩
    · exact Or.inl (by simpa using hdown)
    · exact Or.inr ⟨by simpa using helbow, by simpa using hdiag⟩

end Lattice

end StatMech
