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
import Code.Lattice.OrbitExteriorEven
import Code.Lattice.JordanInteriorLib

open Set SimpleGraph Function

namespace StatMech

namespace Lattice










theorem rlc_rayCount_zero_left (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (h : ∀ p ∈ w.support, z 0 ≤ p 0) :
    jec_rayCount z w = 0 :=
  jec_rayCount_eq_zero_of_right z w h





theorem rlc_rayCount_zero_below (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (h : ∀ p ∈ w.support, z 1 ≤ p 1) :
    jec_rayCount z w = 0 := by
  classical
  rw [jec_rayCount, List.countP_eq_zero]
  intro e he; obtain ⟨u, v⟩ := e
  have hu := h u (w.fst_mem_support_of_mem_edges he)
  have hv := h v (w.snd_mem_support_of_mem_edges he)
  simp only [decide_eq_true_eq]; rw [jec_rayEdge_mk]; omega



theorem rlc_rayCount_zero_above (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (h : ∀ p ∈ w.support, p 1 ≤ z 1 - 1) :
    jec_rayCount z w = 0 := by
  classical
  rw [jec_rayCount, List.countP_eq_zero]
  intro e he; obtain ⟨u, v⟩ := e
  have hu := h u (w.fst_mem_support_of_mem_edges he)
  have hv := h v (w.snd_mem_support_of_mem_edges he)
  simp only [decide_eq_true_eq]; rw [jec_rayEdge_mk]; omega






theorem rlc_support_bound {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    ∃ M : ℤ, ∀ p ∈ Vc.support, |p 0| ≤ M ∧ |p 1| ≤ M := by
  classical
  refine ⟨((Vc.support.map (fun p => max (p 0).natAbs (p 1).natAbs)).foldr max 0 : ℕ), ?_⟩
  intro p hp
  set N : ℕ := (Vc.support.map (fun p => max (p 0).natAbs (p 1).natAbs)).foldr max 0 with hN
  have hmem : max (p 0).natAbs (p 1).natAbs ∈
      Vc.support.map (fun p => max (p 0).natAbs (p 1).natAbs) := List.mem_map_of_mem hp
  have hle : max (p 0).natAbs (p 1).natAbs ≤ N := by
    rw [hN]; exact List.le_max_of_le hmem (le_refl _)
  have h0 : (p 0).natAbs ≤ N := le_trans (le_max_left _ _) hle
  have h1 : (p 1).natAbs ≤ N := le_trans (le_max_right _ _) hle
  refine ⟨?_, ?_⟩
  · rw [Int.abs_eq_natAbs]; exact_mod_cast h0
  · rw [Int.abs_eq_natAbs]; exact_mod_cast h1






theorem rlc_interior_bounded {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    ∃ M : ℤ, ∀ z ∈ jec_leftRegion Vc,
      (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M) := by
  obtain ⟨M, hM⟩ := rlc_support_bound Vc
  refine ⟨M + 1, ?_⟩
  intro z hz
  rw [jec_mem_leftRegion] at hz
  
  have hcol : ∀ p ∈ Vc.support, -M ≤ p 0 ∧ p 0 ≤ M := by
    intro p hp; have := (hM p hp).1; rw [abs_le] at this; exact this
  have hrow : ∀ p ∈ Vc.support, -M ≤ p 1 ∧ p 1 ≤ M := by
    intro p hp; have := (hM p hp).2; rw [abs_le] at this; exact this
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · 
    by_contra hcon
    push Not at hcon
    exact hz (by
      rw [rlc_rayCount_zero_left z Vc (fun p hp => by have := (hcol p hp).1; omega)]
      exact ⟨0, rfl⟩)
  · 
    by_contra hcon
    push Not at hcon
    exact hz (jec_ray_even_far Vc z (fun p hp => by have := (hcol p hp).2; omega))
  · 
    by_contra hcon
    push Not at hcon
    exact hz (by
      rw [rlc_rayCount_zero_below z Vc (fun p hp => by have := (hrow p hp).1; omega)]
      exact ⟨0, rfl⟩)
  · 
    by_contra hcon
    push Not at hcon
    exact hz (by
      rw [rlc_rayCount_zero_above z Vc (fun p hp => by have := (hrow p hp).2; omega)]
      exact ⟨0, rfl⟩)



theorem rlc_offSupportInterior_finite {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    (jil_offSupportInterior Vc).Finite := by
  obtain ⟨M, hM⟩ := rlc_interior_bounded Vc
  apply Set.Finite.subset
    (Set.Finite.pi (fun _ : Fin 2 => Set.finite_Icc (-(M : ℤ) - 1) (M : ℤ)))
  intro z hz
  have hzL : z ∈ jec_leftRegion Vc := (jil_mem_offSupportInterior Vc z |>.mp hz).2
  obtain ⟨⟨h0a, h0b⟩, ⟨h1a, h1b⟩⟩ := hM z hzL
  intro i _
  rw [Set.mem_Icc]
  fin_cases i <;> simp <;> constructor <;> omega











noncomputable def rlc_lexMeasure (M : ℤ) (z : Site 2) : ℕ :=
  (z 1 + M).toNat * (2 * M + 2).toNat + (z 0 + M).toNat





theorem rlc_lexMeasure_lt {M : ℤ} {z z' : Site 2}
    (hz0 : -M < z 0) (hz0' : z 0 ≤ M) (hz1 : -M < z 1) (hz1' : z 1 ≤ M)
    (hz'0 : -M < z' 0) (hz'0' : z' 0 ≤ M) (hz'1 : -M < z' 1) (_hz'1' : z' 1 ≤ M)
    (hlex : z' 1 < z 1 ∨ (z' 1 = z 1 ∧ z' 0 < z 0)) :
    rlc_lexMeasure M z' < rlc_lexMeasure M z := by
  unfold rlc_lexMeasure
  set W : ℕ := (2 * M + 2).toNat with hW
  have hWpos : (z 0 + M).toNat < W := by omega
  have hWpos' : (z' 0 + M).toNat < W := by omega
  rcases hlex with h | ⟨h1, h0⟩
  · have hrow : (z' 1 + M).toNat < (z 1 + M).toNat := by omega
    calc (z' 1 + M).toNat * W + (z' 0 + M).toNat
        < (z' 1 + M).toNat * W + W := by omega
      _ = ((z' 1 + M).toNat + 1) * W := by ring
      _ ≤ (z 1 + M).toNat * W := Nat.mul_le_mul_right W hrow
      _ ≤ (z 1 + M).toNat * W + (z 0 + M).toNat := by omega
  · have hr : (z' 1 + M).toNat = (z 1 + M).toNat := by omega
    rw [hr]
    have : (z' 0 + M).toNat < (z 0 + M).toNat := by omega
    omega




theorem rlc_exists_lexMin_seed {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z₀ : Site 2} (hz₀ : z₀ ∈ jil_offSupportInterior Vc) (M : ℤ) :
    ∃ seed ∈ jil_offSupportInterior Vc,
      ∀ z ∈ jil_offSupportInterior Vc,
        rlc_lexMeasure M seed ≤ rlc_lexMeasure M z := by
  classical
  have hfin := rlc_offSupportInterior_finite Vc
  have hne : (jil_offSupportInterior Vc).Nonempty := ⟨z₀, hz₀⟩
  obtain ⟨seed, hseed, hmin⟩ :=
    hfin.toFinset.exists_min_image (rlc_lexMeasure M)
      (by rw [Set.Finite.toFinset_nonempty]; exact hne)
  refine ⟨seed, (hfin.mem_toFinset).mp hseed, ?_⟩
  intro z hz
  exact hmin z (hfin.mem_toFinset.mpr hz)













theorem rlc_down_mem_interior {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) {x y : ℤ}
    (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hdown : (![x, y - 1] : Site 2) ∉ Vc.support) :
    (![x, y - 1] : Site 2) ∈ jil_offSupportInterior Vc := by
  obtain ⟨hzsup, hzint⟩ := (jil_mem_offSupportInterior Vc _).mp hz
  have hadj : (hypercubicLattice 2).Adj (![x, y] : Site 2) ![x, y - 1] := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
  have hpar := jec_localConstancy Vc hadj hzsup hdown
  rw [jil_mem_offSupportInterior]
  refine ⟨hdown, ?_⟩
  rw [jec_mem_leftRegion] at hzint ⊢
  intro h; exact hzint (hpar.mpr h)





theorem rlc_left_mem_interior {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) {x y : ℤ}
    (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hleft : (![x - 1, y] : Site 2) ∉ Vc.support) :
    (![x - 1, y] : Site 2) ∈ jil_offSupportInterior Vc := by
  obtain ⟨hzsup, hzint⟩ := (jil_mem_offSupportInterior Vc _).mp hz
  have hadj : (hypercubicLattice 2).Adj (![x, y] : Site 2) ![x - 1, y] := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
  have hpar := jec_localConstancy Vc hadj hzsup hleft
  rw [jil_mem_offSupportInterior]
  refine ⟨hleft, ?_⟩
  rw [jec_mem_leftRegion] at hzint ⊢
  intro h; exact hzint (hpar.mpr h)












def rlc_DownLink {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (seed : Site 2) (M : ℤ) :
    Prop :=
  ∀ z ∈ jil_offSupportInterior Vc, z ≠ seed →
    ∃ z' ∈ jil_offSupportInterior Vc,
      rlc_lexMeasure M z' < rlc_lexMeasure M z ∧
      ∃ p : (hypercubicLattice 2).Walk z z', ∀ w ∈ p.support, w ∉ Vc.support




theorem rlc_descend_via_leftStep {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (M : ℤ) (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
    {x y : ℤ}
    (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hleft : (![x - 1, y] : Site 2) ∉ Vc.support) :
    ∃ z' ∈ jil_offSupportInterior Vc,
      rlc_lexMeasure M z' < rlc_lexMeasure M (![x, y] : Site 2) ∧
      ∃ p : (hypercubicLattice 2).Walk (![x, y] : Site 2) z', ∀ w ∈ p.support, w ∉ Vc.support := by
  have hz' : (![x - 1, y] : Site 2) ∈ jil_offSupportInterior Vc :=
    rlc_left_mem_interior Vc hz hleft
  refine ⟨![x - 1, y], hz', ?_, ?_⟩
  · have hzL : (![x, y] : Site 2) ∈ jec_leftRegion Vc :=
      (jil_mem_offSupportInterior Vc _ |>.mp hz).2
    have hz'L : (![x - 1, y] : Site 2) ∈ jec_leftRegion Vc :=
      (jil_mem_offSupportInterior Vc _ |>.mp hz').2
    obtain ⟨⟨hb0a, hb0b⟩, ⟨hb1a, hb1b⟩⟩ := hMb _ hzL
    obtain ⟨⟨hd0a, hd0b⟩, ⟨hd1a, hd1b⟩⟩ := hMb _ hz'L
    refine rlc_lexMeasure_lt hb0a hb0b hb1a hb1b ?_ ?_ ?_ ?_ ?_
    · simpa using hd0a
    · simpa using hd0b
    · simpa using hd1a
    · simpa using hd1b
    · right; simp
  · have hadj : (hypercubicLattice 2).Adj (![x, y] : Site 2) ![x - 1, y] := by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
    refine ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil, ?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h
    · subst h; exact (jil_mem_offSupportInterior Vc _ |>.mp hz).1
    · subst h; exact hleft







theorem rlc_descend_via_downStep {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (M : ℤ) (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
    {x y cx : ℤ}
    (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (preach : (hypercubicLattice 2).Walk (![x, y] : Site 2) ![cx, y])
    (hpreach : ∀ w ∈ preach.support, w ∉ Vc.support)
    (hc : (![cx, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hcdown : (![cx, y - 1] : Site 2) ∉ Vc.support) :
    ∃ z' ∈ jil_offSupportInterior Vc,
      rlc_lexMeasure M z' < rlc_lexMeasure M (![x, y] : Site 2) ∧
      ∃ p : (hypercubicLattice 2).Walk (![x, y] : Site 2) z', ∀ w ∈ p.support, w ∉ Vc.support := by
  have hz' : (![cx, y - 1] : Site 2) ∈ jil_offSupportInterior Vc :=
    rlc_down_mem_interior Vc hc hcdown
  refine ⟨![cx, y - 1], hz', ?_, ?_⟩
  · have hzL : (![x, y] : Site 2) ∈ jec_leftRegion Vc :=
      (jil_mem_offSupportInterior Vc _ |>.mp hz).2
    have hz'L : (![cx, y - 1] : Site 2) ∈ jec_leftRegion Vc :=
      (jil_mem_offSupportInterior Vc _ |>.mp hz').2
    obtain ⟨⟨hb0a, hb0b⟩, ⟨hb1a, hb1b⟩⟩ := hMb _ hzL
    obtain ⟨⟨hd0a, hd0b⟩, ⟨hd1a, hd1b⟩⟩ := hMb _ hz'L
    refine rlc_lexMeasure_lt hb0a hb0b hb1a hb1b ?_ ?_ ?_ ?_ ?_
    · simpa using hd0a
    · simpa using hd0b
    · simpa using hd1a
    · simpa using hd1b
    · left; simp
  · have hadj : (hypercubicLattice 2).Adj (![cx, y] : Site 2) ![cx, y - 1] := by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
    refine ⟨preach.append (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil), ?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_append, List.mem_append] at hw
    rcases hw with h | h
    · exact hpreach w h
    · have hmem := List.mem_of_mem_tail h
      rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h1 | h1
      · subst h1; exact (jil_mem_offSupportInterior Vc _ |>.mp hc).1
      · subst h1; exact hcdown








theorem rlc_descend_via_segmentDown {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (M : ℤ) (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
    {x y cx : ℤ}
    (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hxcx : x ≤ cx)
    (hrun : ∀ t : ℤ, x ≤ t → t ≤ cx → (![t, y] : Site 2) ∉ Vc.support)
    (hcdown : (![cx, y - 1] : Site 2) ∉ Vc.support) :
    ∃ z' ∈ jil_offSupportInterior Vc,
      rlc_lexMeasure M z' < rlc_lexMeasure M (![x, y] : Site 2) ∧
      ∃ p : (hypercubicLattice 2).Walk (![x, y] : Site 2) z', ∀ w ∈ p.support, w ∉ Vc.support := by
  have hxoff : (![x, y] : Site 2) ∉ Vc.support := (jil_mem_offSupportInterior Vc _ |>.mp hz).1
  obtain ⟨preach, hpreach⟩ :=
    jil_hsegment_reachable_offSupport {p | p ∈ Vc.support} (lo := x) (hi := cx) (y := y)
      (x₁ := x) (x₂ := cx) (by simpa using hxoff) le_rfl hxcx hxcx le_rfl
      (by intro t ht ht'; simpa using hrun t ht ht')
  have hxL : (![x, y] : Site 2) ∈ jec_leftRegion Vc := (jil_mem_offSupportInterior Vc _ |>.mp hz).2
  have hcL : (![cx, y] : Site 2) ∈ jec_leftRegion Vc :=
    jil_hsegment_subset_leftRegion Vc le_rfl hxcx hxcx le_rfl
      (by intro t ht ht'; simpa using hrun t ht ht') hxL
  have hcoff : (![cx, y] : Site 2) ∉ Vc.support := by simpa using hrun cx hxcx le_rfl
  have hc : (![cx, y] : Site 2) ∈ jil_offSupportInterior Vc :=
    (jil_mem_offSupportInterior Vc _).mpr ⟨hcoff, hcL⟩
  have hpreach' : ∀ w ∈ preach.support, w ∉ Vc.support := by
    intro w hw; have := hpreach w hw; simpa using this
  exact rlc_descend_via_downStep Vc M hMb hz preach hpreach' hc hcdown



















def rlc_LeftEndDescends {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (seed : Site 2) (M : ℤ) : Prop :=
  ∀ z ∈ jil_offSupportInterior Vc, z ≠ seed →
    (![z 0 - 1, z 1] : Site 2) ∈ Vc.support →
    ∃ z' ∈ jil_offSupportInterior Vc,
      rlc_lexMeasure M z' < rlc_lexMeasure M z ∧
      ∃ p : (hypercubicLattice 2).Walk z z', ∀ w ∈ p.support, w ∉ Vc.support




theorem rlc_downLink_of_leftEndDescends {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (M : ℤ)
    (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
    (hres : rlc_LeftEndDescends Vc seed M) :
    rlc_DownLink Vc seed M := by
  intro z hz hzs
  by_cases hleft : (![z 0 - 1, z 1] : Site 2) ∈ Vc.support
  · exact hres z hz hzs hleft
  · have hzeq : z = ![z 0, z 1] := by ext i; fin_cases i <;> simp
    rw [hzeq] at hz hleft ⊢
    have hl : (![(![z 0, z 1] : Site 2) 0 - 1, (![z 0, z 1] : Site 2) 1] : Site 2)
        ∉ Vc.support := by
      simpa using hleft
    exact rlc_descend_via_leftStep Vc M hMb hz hl






theorem rlc_rowLinked_of_downLink {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (M : ℤ) (hdl : rlc_DownLink Vc seed M) :
    jil_RowLinked Vc seed := by
  have key : ∀ n : ℕ, ∀ z ∈ jil_offSupportInterior Vc, rlc_lexMeasure M z = n →
      ∃ p : (hypercubicLattice 2).Walk z seed, ∀ w ∈ p.support, w ∉ Vc.support := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro z hz hn
      by_cases hzs : z = seed
      · cases hzs
        refine ⟨SimpleGraph.Walk.nil, ?_⟩
        intro w hw
        rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw
        cases hw
        exact (jil_mem_offSupportInterior Vc seed |>.mp hz).1
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






theorem rlc_rowLinked_of_leftEndDescends {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (M : ℤ)
    (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
    (hres : rlc_LeftEndDescends Vc seed M) :
    jil_RowLinked Vc seed :=
  rlc_rowLinked_of_downLink Vc M (rlc_downLink_of_leftEndDescends Vc M hMb hres)

















def rlc_SegmentDown {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (seed : Site 2) : Prop :=
  ∀ z ∈ jil_offSupportInterior Vc, z ≠ seed →
    (![z 0 - 1, z 1] : Site 2) ∈ Vc.support →
    ∃ cx : ℤ, z 0 ≤ cx ∧
      (∀ t : ℤ, z 0 ≤ t → t ≤ cx → (![t, z 1] : Site 2) ∉ Vc.support) ∧
      (![cx, z 1 - 1] : Site 2) ∉ Vc.support






theorem rlc_leftEndDescends_of_segmentDown {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (M : ℤ)
    (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
    (hres : rlc_SegmentDown Vc seed) :
    rlc_LeftEndDescends Vc seed M := by
  intro z hz hzs hleft
  obtain ⟨cx, hxcx, hrun, hcdown⟩ := hres z hz hzs hleft
  have hzeq : z = ![z 0, z 1] := by ext i; fin_cases i <;> simp
  rw [hzeq] at hz ⊢
  have key := rlc_descend_via_segmentDown Vc M hMb (x := z 0) (y := z 1) (cx := cx) hz
    (by simpa using hxcx)
    (by intro t ht ht'; have := hrun t (by simpa using ht) ht'; simpa using this)
    (by simpa using hcdown)
  simpa using key








theorem rlc_rowLinked_of_segmentDown {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (M : ℤ)
    (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
    (hres : rlc_SegmentDown Vc seed) :
    jil_RowLinked Vc seed :=
  rlc_rowLinked_of_leftEndDescends Vc M hMb (rlc_leftEndDescends_of_segmentDown Vc M hMb hres)






theorem rlc_exists_rowLinked_seed_of_segmentDown {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z₀ : Site 2} (hz₀ : z₀ ∈ jil_offSupportInterior Vc)
    (hres : ∀ seed : Site 2, rlc_SegmentDown Vc seed) :
    ∃ seed ∈ jil_offSupportInterior Vc, jil_RowLinked Vc seed := by
  obtain ⟨M, hMb⟩ := rlc_interior_bounded Vc
  obtain ⟨seed, hseed, _⟩ := rlc_exists_lexMin_seed Vc hz₀ M
  exact ⟨seed, hseed, rlc_rowLinked_of_segmentDown Vc M hMb (hres seed)⟩














theorem rlc_segmentDown_body_of_downOffSupport {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z : Site 2} (hzoff : z ∉ Vc.support) (hdown : (![z 0, z 1 - 1] : Site 2) ∉ Vc.support) :
    ∃ cx : ℤ, z 0 ≤ cx ∧
      (∀ t : ℤ, z 0 ≤ t → t ≤ cx → (![t, z 1] : Site 2) ∉ Vc.support) ∧
      (![cx, z 1 - 1] : Site 2) ∉ Vc.support := by
  refine ⟨z 0, le_rfl, ?_, hdown⟩
  intro t ht ht'
  have : t = z 0 := le_antisymm ht' ht
  subst this
  have hzeq : z = ![z 0, z 1] := by ext i; fin_cases i <;> simp
  rw [hzeq] at hzoff
  simpa using hzoff






theorem rlc_segmentDown_of_downOffSupport {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (seed : Site 2)
    (hdown : ∀ z ∈ jil_offSupportInterior Vc, z ≠ seed →
      (![z 0 - 1, z 1] : Site 2) ∈ Vc.support → (![z 0, z 1 - 1] : Site 2) ∉ Vc.support) :
    rlc_SegmentDown Vc seed := by
  intro z hz hzs hleft
  exact rlc_segmentDown_body_of_downOffSupport Vc
    (jil_mem_offSupportInterior Vc z |>.mp hz).1 (hdown z hz hzs hleft)






theorem rlc_segmentDown_body_multiCell {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z0 z1 : ℤ}
    (h0 : (![z0, z1] : Site 2) ∉ Vc.support)
    (h1 : (![z0 + 1, z1] : Site 2) ∉ Vc.support)
    (hd : (![z0 + 1, z1 - 1] : Site 2) ∉ Vc.support) :
    ∃ cx : ℤ, z0 < cx ∧
      (∀ t : ℤ, z0 ≤ t → t ≤ cx → (![t, z1] : Site 2) ∉ Vc.support) ∧
      (![cx, z1 - 1] : Site 2) ∉ Vc.support := by
  refine ⟨z0 + 1, by omega, ?_, hd⟩
  intro t ht ht'
  have : t = z0 ∨ t = z0 + 1 := by omega
  rcases this with h | h <;> subst h
  · exact h0
  · exact h1





theorem rlc_downLink_witness_ne {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (M : ℤ) (hdl : rlc_DownLink Vc seed M)
    {z : Site 2} (hz : z ∈ jil_offSupportInterior Vc) (hzs : z ≠ seed) :
    ∃ z' ∈ jil_offSupportInterior Vc, z' ≠ z ∧
      ∃ p : (hypercubicLattice 2).Walk z z', ∀ w ∈ p.support, w ∉ Vc.support := by
  obtain ⟨z', hz', hlt, p, hp⟩ := hdl z hz hzs
  refine ⟨z', hz', ?_, p, hp⟩
  intro hcon; rw [hcon] at hlt; exact (lt_irrefl _ hlt)

end Lattice

end StatMech
