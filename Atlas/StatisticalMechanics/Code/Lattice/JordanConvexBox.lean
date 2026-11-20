/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















































































import Mathlib
import Code.Lattice.PathVisitsRow
import Code.Universality.HVIntersection
import Code.Lattice.JordanStripInduction
import Code.Lattice.ArcMonotonise

open Set SimpleGraph

namespace StatMech

namespace Lattice

open StatMech.RSW.Box
open StatMech.Universality









theorem jcb_upcross {a b : Site 2} (W : (hypercubicLattice 2).Walk a b)
    {c d : ℤ} (hac : a 1 = c) (hbd : b 1 = d)
    (s : ℤ) (hs1 : c < s) (hs2 : s ≤ d) :
    ∃ i, 1 ≤ i ∧ i ≤ W.length ∧ (W.getVert i) 1 = s ∧ (W.getVert (i - 1)) 1 = s - 1 := by
  classical
  set g : ℕ → ℤ := fun i => (W.getVert i) 1 with hg
  have hg0 : g 0 = c := by simp only [hg, W.getVert_zero, hac]
  have hgL : g W.length = d := by simp only [hg, W.getVert_length, hbd]
  have hstep : ∀ i, i < W.length → (g (i + 1) - g i).natAbs ≤ 1 := by
    intro i hi
    have hadj := W.adj_getVert_succ hi
    have := pvr_adj_coord_diff_le_one hadj 1
    simp only [hg]; omega
  have hex : ∃ i, s ≤ g i := ⟨W.length, by rw [hgL]; exact hs2⟩
  set i := Nat.find hex with hi
  have hspec : s ≤ g i := Nat.find_spec hex
  have hmin : ∀ j, j < i → ¬ (s ≤ g j) := fun j hj => Nat.find_min hex hj
  have hi1 : 1 ≤ i := by
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · exfalso; rw [h0] at hspec; rw [hg0] at hspec; omega
    · omega
  have hiL : i ≤ W.length := Nat.find_le (by rw [hgL]; exact hs2)
  have hstepi : (g ((i - 1) + 1) - g (i - 1)).natAbs ≤ 1 := hstep (i - 1) (by omega)
  have heq : (i - 1) + 1 = i := by omega
  rw [heq] at hstepi
  have hpred : g (i - 1) ≤ s - 1 := by
    have := hmin (i - 1) (by omega); push Not at this; omega
  have hgi : g i = s := by omega
  exact ⟨i, hi1, hiL, hgi, by show g (i - 1) = s - 1; omega⟩



theorem jcb_vstep_col (u v : Site 2) (hadj : (hypercubicLattice 2).Adj u v)
    (hrow : u 1 - v 1 = 1 ∨ u 1 - v 1 = -1) : u 0 = v 0 := by
  rcases jsi_adj_cases u v hadj with ⟨_, _⟩ | ⟨hcoleq, _⟩
  · omega
  · exact hcoleq











theorem jcb_rowMonotone_subpath {a b : Site 2} (W : (hypercubicLattice 2).Walk a b)
    {c d : ℤ} (hac : a 1 = c) (hbd : b 1 = d) (_hcd : c ≤ d) :
    ∃ Up : ℤ → ℕ,
      (∀ s, c < s → s ≤ d → 1 ≤ Up s ∧ Up s ≤ W.length ∧
        (W.getVert (Up s)) 1 = s ∧ (W.getVert (Up s - 1)) 1 = s - 1) ∧
      (∀ s t, c < s → s < t → t ≤ d → Up s < Up t) := by
  classical
  set g : ℕ → ℤ := fun i => (W.getVert i) 1 with hg
  have hg0 : g 0 = c := by simp only [hg, W.getVert_zero, hac]
  have hgL : g W.length = d := by simp only [hg, W.getVert_length, hbd]
  have hstep : ∀ k, k < W.length → (g (k + 1) - g k).natAbs ≤ 1 := by
    intro k hk
    have hadj := W.adj_getVert_succ hk
    have := pvr_adj_coord_diff_le_one hadj 1
    simp only [hg]; omega
  have hex : ∀ s : ℤ, c < s → s ≤ d → ∃ i, s ≤ g i :=
    fun s _ hs2 => ⟨W.length, by rw [hgL]; exact hs2⟩
  
  have hval : ∀ s (hs1 : c < s) (hs2 : s ≤ d), g (Nat.find (hex s hs1 hs2)) = s := by
    intro s hs1 hs2
    set j := Nat.find (hex s hs1 hs2) with hj
    have hspec : s ≤ g j := Nat.find_spec (hex s hs1 hs2)
    have hmin : ∀ k, k < j → ¬ (s ≤ g k) := fun k hk => Nat.find_min (hex s hs1 hs2) hk
    have hjL : j ≤ W.length := Nat.find_le (by rw [hgL]; exact hs2)
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · exfalso; rw [h0, hg0] at hspec; omega
      · omega
    have hstepj : (g ((j - 1) + 1) - g (j - 1)).natAbs ≤ 1 := hstep (j - 1) (by omega)
    have heqj : (j - 1) + 1 = j := by omega
    rw [heqj] at hstepj
    have hpred : g (j - 1) ≤ s - 1 := by
      have := hmin (j - 1) (by omega); push Not at this; omega
    omega
  refine ⟨fun s => if h : c < s ∧ s ≤ d then Nat.find (hex s h.1 h.2) else 0, ?_, ?_⟩
  · 
    intro s hs1 hs2
    simp only []
    have hdif : (if h : c < s ∧ s ≤ d then Nat.find (hex s h.1 h.2) else 0)
        = Nat.find (hex s hs1 hs2) := by rw [dif_pos ⟨hs1, hs2⟩]
    rw [hdif]
    set j := Nat.find (hex s hs1 hs2) with hj
    have hspec : s ≤ g j := Nat.find_spec (hex s hs1 hs2)
    have hmin : ∀ k, k < j → ¬ (s ≤ g k) := fun k hk => Nat.find_min (hex s hs1 hs2) hk
    have hjL : j ≤ W.length := Nat.find_le (by rw [hgL]; exact hs2)
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · exfalso; rw [h0, hg0] at hspec; omega
      · omega
    have hstepj : (g ((j - 1) + 1) - g (j - 1)).natAbs ≤ 1 := hstep (j - 1) (by omega)
    have heqj : (j - 1) + 1 = j := by omega
    rw [heqj] at hstepj
    have hpred : g (j - 1) ≤ s - 1 := by
      have := hmin (j - 1) (by omega); push Not at this; omega
    have hgj : g j = s := by omega
    exact ⟨hj1, hjL, hgj, by show g (j - 1) = s - 1; omega⟩
  · 
    intro s t hs1 hst htd
    simp only []
    have hds : (if h : c < s ∧ s ≤ d then Nat.find (hex s h.1 h.2) else 0)
        = Nat.find (hex s hs1 (by omega)) := by rw [dif_pos ⟨hs1, by omega⟩]
    have hdt : (if h : c < t ∧ t ≤ d then Nat.find (hex t h.1 h.2) else 0)
        = Nat.find (hex t (by omega) htd) := by rw [dif_pos ⟨by omega, htd⟩]
    rw [hds, hdt]
    set js := Nat.find (hex s hs1 (by omega)) with hjs
    set jt := Nat.find (hex t (by omega) htd) with hjt
    have hgjs : g js = s := hval s hs1 (by omega)
    have hspect : t ≤ g jt := Nat.find_spec (hex t (by omega) htd)
    have hle : js ≤ jt := Nat.find_min' (hex s hs1 (by omega)) (by omega : s ≤ g jt)
    have hne : js ≠ jt := by intro h; rw [h] at hgjs; omega
    omega














theorem jcb_upcross_pair (ω : ConfigSpace (Sym2 (Site 2))) {m m' c d : ℤ}
    {xB yT : Site 2} (hxB : xB ∈ rect m m' c d) (hyT : yT ∈ rect m m' c d)
    (hxBc : xB 1 = c) (hyTd : yT 1 = d)
    (hcV : ConnectedWithin 2 ω (rect m m' c d) ⟨xB, hxB⟩ ⟨yT, hyT⟩)
    (s : ℤ) (hs1 : c < s) (hs2 : s ≤ d) :
    ∃ k : ℤ, m ≤ k ∧ k ≤ m' ∧
      jsi_cell k s ∈ overlapComp ω m m' c d xB hxB ∧
      jsi_cell k (s - 1) ∈ overlapComp ω m m' c d xB hxB := by
  classical
  obtain ⟨W⟩ := hcV
  set V := W.map (amo_proj ω (rect m m' c d)) with hV
  obtain ⟨i, hi1, hiL, hrow_i, hrow_pred⟩ :=
    jcb_upcross V (c := c) (d := d)
      (by show (xB : Site 2) 1 = c; exact hxBc)
      (by show (yT : Site 2) 1 = d; exact hyTd) s hs1 hs2
  set p := V.getVert i with hp
  set q := V.getVert (i - 1) with hq
  have hadj : (hypercubicLattice 2).Adj q p := by
    have h := V.adj_getVert_succ (i := i - 1) (by omega)
    have heq : (i - 1) + 1 = i := by omega
    rw [heq] at h; rw [hp, hq]; exact h
  have hcol : q 0 = p 0 := by
    apply jcb_vstep_col q p hadj
    right; rw [hrow_pred, hrow_i]; omega
  have hps : p ∈ V.support := by rw [hp]; exact V.getVert_mem_support i
  have hqs : q ∈ V.support := by rw [hq]; exact V.getVert_mem_support (i - 1)
  have hcomp : ∀ z, z ∈ V.support →
      z ∈ overlapComp ω m m' c d xB hxB ∧ z ∈ rect m m' c d := by
    intro z hz
    rw [hV, SimpleGraph.Walk.support_map, List.mem_map] at hz
    obtain ⟨zz, hzzs, hzze⟩ := hz
    have hzzconn : ConnectedWithin 2 ω (rect m m' c d) ⟨xB, hxB⟩ zz :=
      amo_connectedWithin_of_mem_support ω (rect m m' c d) W hzzs
    have hzz : z = (zz : Site 2) := by rw [← hzze]; rfl
    rw [hzz]; exact ⟨⟨zz.2, hzzconn⟩, zz.2⟩
  obtain ⟨hpcomp, hprect⟩ := hcomp p hps
  obtain ⟨hqcomp, _hqrect⟩ := hcomp q hqs
  refine ⟨p 0, (mem_rect.mp hprect).1, (mem_rect.mp hprect).2.1, ?_, ?_⟩
  · have hcell : jsi_cell (p 0) s = p := by
      funext j; fin_cases j
      · rfl
      · show (s : ℤ) = p 1; rw [hrow_i]
    rw [hcell]; exact hpcomp
  · have hcell : jsi_cell (p 0) (s - 1) = q := by
      funext j; fin_cases j
      · show (p 0 : ℤ) = q 0; rw [hcol]
      · show (s - 1 : ℤ) = q 1; rw [hrow_pred]
    rw [hcell]; exact hqcomp



















theorem jcb_rowData_of_vCrossing (ω : ConfigSpace (Sym2 (Site 2))) {m m' c d : ℤ}
    {xB yT : Site 2} (hxB : xB ∈ rect m m' c d) (hyT : yT ∈ rect m m' c d)
    (hxBc : xB 1 = c) (hyTd : yT 1 = d)
    (hcV : ConnectedWithin 2 ω (rect m m' c d) ⟨xB, hxB⟩ ⟨yT, hyT⟩) :
    ∃ col : ℤ → ℤ,
      (∀ r, c ≤ r → r ≤ d → m ≤ col r) ∧
      (∀ r, c ≤ r → r ≤ d → col r ≤ m') ∧
      (∀ r, c ≤ r → r ≤ d → jsi_cell (col r) r ∈ overlapComp ω m m' c d xB hxB) ∧
      (∀ r, c < r → r ≤ d → jsi_cell (col (r - 1)) r ∈ overlapComp ω m m' c d xB hxB) ∧
      col (c - 1) = col c := by
  classical
  have hcd : c ≤ d := by have := mem_rect.mp hxB; omega
  rcases eq_or_lt_of_le hcd with hcd_eq | hcd_lt
  · 
    subst hcd_eq
    have hxBrect := mem_rect.mp hxB
    have hxBcomp : (xB : Site 2) ∈ overlapComp ω m m' c c xB hxB :=
      ⟨hxB, connectedWithin_refl _ _ _⟩
    refine ⟨fun _ => xB 0, ?_, ?_, ?_, ?_, rfl⟩
    · intro r _ _; exact hxBrect.1
    · intro r _ _; exact hxBrect.2.1
    · intro r hcr hrc
      have hr : r = c := by omega
      subst hr
      have hcell : jsi_cell (xB 0) r = xB := by
        funext j; fin_cases j
        · rfl
        · show (r : ℤ) = xB 1; rw [hxBc]
      rw [hcell]; exact hxBcomp
    · intro r hcr hrc; omega
  
  
  choose! f hfb1 hfb2 hf1 hf2 using fun s (hs : c < s ∧ s ≤ d) =>
    jcb_upcross_pair ω hxB hyT hxBc hyTd hcV s hs.1 hs.2
  
  set col : ℤ → ℤ := fun r => f (max (c + 1) (min d (r + 1))) with hcol
  have hclamp : ∀ r, c < max (c + 1) (min d (r + 1)) ∧ max (c + 1) (min d (r + 1)) ≤ d := by
    intro r; exact ⟨by omega, by omega⟩
  have hcol_mid : ∀ r, c ≤ r → r + 1 ≤ d → col r = f (r + 1) := by
    intro r hcr hrd; simp only [hcol]; congr 1; omega
  have hcol_top : ∀ r, d ≤ r → col r = f d := by
    intro r hr; simp only [hcol]; congr 1; omega
  refine ⟨col, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hcr hrd; simp only [hcol]; exact hfb1 _ (hclamp r)
  · intro r hcr hrd; simp only [hcol]; exact hfb2 _ (hclamp r)
  · 
    intro r hcr hrd
    by_cases h : r < d
    · rw [hcol_mid r hcr (by omega)]
      have hyp : c < r + 1 ∧ r + 1 ≤ d := ⟨by omega, by omega⟩
      have hh := hf2 (r + 1) hyp
      have he : (r + 1) - 1 = r := by ring
      rw [he] at hh; exact hh
    · have hrd' : r = d := by omega
      subst hrd'
      rw [hcol_top r (le_refl r)]
      have hyp : c < r ∧ r ≤ r := ⟨by omega, le_refl r⟩
      exact hf1 r hyp
  · 
    intro r hcr hrd
    rw [hcol_mid (r - 1) (by omega) (by omega)]
    have he : (r - 1) + 1 = r := by ring
    rw [he]
    have hyp : c < r ∧ r ≤ d := ⟨by omega, hrd⟩
    exact hf1 r hyp
  · 
    simp only [hcol]; congr 1; omega











def jcb_monotoneArc_of_rowData {P : Set (Site 2)} {m m' c d : ℤ}
    (hcd : c ≤ d) (col : ℤ → ℤ)
    (hlo : ∀ r, c ≤ r → r ≤ d → m ≤ col r)
    (hhi : ∀ r, c ≤ r → r ≤ d → col r ≤ m')
    (hon : ∀ r, c ≤ r → r ≤ d → jsi_cell (col r) r ∈ P)
    (hcorner : ∀ r, c < r → r ≤ d → jsi_cell (col (r - 1)) r ∈ P)
    (hc1 : col (c - 1) = col c)
    (hshift : ∀ r : ℤ,
      col (r + 1) - col r = 1 ∨ col (r + 1) - col r = 0 ∨ col (r + 1) - col r = -1) :
    JsiMonotoneArc P m m' c d where
  col := col
  band_lo := hlo
  band_hi := hhi
  shift := fun r _ _ => hshift r
  on_arc := by
    intro z hcz hzd hzcol _ _
    have hcell : jsi_cell (col (z 1)) (z 1) = z := by
      funext j; fin_cases j
      · show col (z 1) = z 0; rw [hzcol]
      · rfl
    rw [← hcell]; exact hon (z 1) hcz hzd
  cd := hcd
  shift_all := hshift
  corner := by
    intro z hcz hzd hzcol _ _
    have hcell : jsi_cell (col (z 1 - 1)) (z 1) = z := by
      funext j; fin_cases j
      · show col (z 1 - 1) = z 0; rw [hzcol]
      · rfl
    rw [← hcell]
    rcases eq_or_lt_of_le hcz with heq | hlt
    · rw [← heq, hc1]; exact hon c (le_refl c) hcd
    · exact hcorner (z 1) hlt hzd















theorem jcb_separatingSide_of_vCrossing {P : Set (Site 2)} {α β m m' c d : ℤ}
    (hαm : α ≤ m) (hm'β : m' < β) (hcd : c ≤ d) (col : ℤ → ℤ)
    (hlo : ∀ r, c ≤ r → r ≤ d → m ≤ col r)
    (hhi : ∀ r, c ≤ r → r ≤ d → col r ≤ m')
    (hon : ∀ r, c ≤ r → r ≤ d → jsi_cell (col r) r ∈ P)
    (hcorner : ∀ r, c < r → r ≤ d → jsi_cell (col (r - 1)) r ∈ P)
    (hc1 : col (c - 1) = col c)
    (hshift : ∀ r : ℤ,
      col (r + 1) - col r = 1 ∨ col (r + 1) - col r = 0 ∨ col (r + 1) - col r = -1) :
    ArcSeparatingSet P α β c d :=
  jsi_separatingSide hαm hm'β
    (jcb_monotoneArc_of_rowData hcd col hlo hhi hon hcorner hc1 hshift).toJsiRowArc











def JcbColShift (ω : ConfigSpace (Sym2 (Site 2))) (m m' c d : ℤ)
    (xB : Site 2) (hxB : xB ∈ rect m m' c d) : Prop :=
  ∃ col : ℤ → ℤ,
    (∀ r, c ≤ r → r ≤ d → m ≤ col r) ∧
    (∀ r, c ≤ r → r ≤ d → col r ≤ m') ∧
    (∀ r, c ≤ r → r ≤ d → jsi_cell (col r) r ∈ overlapComp ω m m' c d xB hxB) ∧
    (∀ r, c < r → r ≤ d → jsi_cell (col (r - 1)) r ∈ overlapComp ω m m' c d xB hxB) ∧
    col (c - 1) = col c ∧
    (∀ r : ℤ, col (r + 1) - col r = 1 ∨ col (r + 1) - col r = 0 ∨ col (r + 1) - col r = -1)













theorem jcb_vsFix_arc_sides_of_vCrossing (ω : ConfigSpace (Sym2 (Site 2))) {α β m m' c d : ℤ}
    (hαm : α ≤ m) (hm'β : m' < β)
    (hres : ∀ (xB : Site 2) (hxB : xB ∈ rect m m' c d),
      JcbColShift ω m m' c d xB hxB) :
    StatMech.Universality.vsFix_arc_sides ω α β m m' c d := by
  intro _hαm' _hmm' _hm'β' xB hxB hxBbot yT hyT hcV
  have hcd : c ≤ d := by have := mem_rect.mp hxB; omega
  obtain ⟨col, hlo, hhi, hon, hcorner, hc1, hshift⟩ := hres xB hxB
  have hsep : ArcSeparatingSet (overlapComp ω m m' c d xB hxB) α β c d :=
    jcb_separatingSide_of_vCrossing hαm hm'β hcd col hlo hhi hon hcorner hc1 hshift
  obtain ⟨S, hSleft, hSright, hSedge⟩ := hsep
  exact ⟨S, hSleft, hSright, hSedge⟩







theorem jcb_colShift_of_shift (ω : ConfigSpace (Sym2 (Site 2))) {m m' c d : ℤ}
    {xB yT : Site 2} (hxB : xB ∈ rect m m' c d) (hyT : yT ∈ rect m m' c d)
    (hxBc : xB 1 = c) (hyTd : yT 1 = d)
    (hcV : ConnectedWithin 2 ω (rect m m' c d) ⟨xB, hxB⟩ ⟨yT, hyT⟩)
    (col : ℤ → ℤ)
    (hcol : col = (jcb_rowData_of_vCrossing ω hxB hyT hxBc hyTd hcV).choose)
    (hshift : ∀ r : ℤ,
      col (r + 1) - col r = 1 ∨ col (r + 1) - col r = 0 ∨ col (r + 1) - col r = -1) :
    JcbColShift ω m m' c d xB hxB := by
  obtain ⟨hlo, hhi, hon, hcorner, hc1⟩ :=
    (jcb_rowData_of_vCrossing ω hxB hyT hxBc hyTd hcV).choose_spec
  subst hcol
  exact ⟨_, hlo, hhi, hon, hcorner, hc1, hshift⟩

end Lattice

end StatMech
