/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























































































import Mathlib
import Code.Walls.jc2_runframe
import Code.Walls.jc2_thickshelf
import Code.Walls.jc3_shelfcell

open SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice

















def jc5_earCell (c : Site 2) (len : ℤ) : Site 2 := c + ![len, 0]

@[simp] theorem jc5_earCell_eq (c : Site 2) (len : ℤ) :
    jc5_earCell c len = c + ![len, 0] := rfl


theorem jc5_earCell_eq_runRightEnd (c : Site 2) (len : ℤ) :
    jc5_earCell c len = jc3_runRightEnd c len := rfl



theorem jc5_earCell_coord1 (c : Site 2) (len : ℤ) :
    (jc5_earCell c len) 1 = c 1 := by
  rw [jc5_earCell_eq]
  simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]; ring



def jc5_earUp (c : Site 2) (len : ℤ) : Site 2 := jc5_earCell c len + ![0, 1]



def jc5_earRight (c : Site 2) (len : ℤ) : Site 2 := jc5_earCell c len + ![1, 0]




def jc5_earShelf (c : Site 2) (len : ℤ) : Site 2 := jc5_earCell c len + ![0, -1]



theorem jc5_earUp_eq (c : Site 2) (len : ℤ) :
    jc5_earUp c len = c + ![len, 1] := by
  unfold jc5_earUp jc5_earCell
  funext i; fin_cases i <;> · simp only [Pi.add_apply]; simp




theorem jc5_earRight_eq (c : Site 2) (len : ℤ) :
    jc5_earRight c len = c + ![len + 1, 0] := by
  unfold jc5_earRight jc5_earCell
  funext i; fin_cases i <;> · simp only [Pi.add_apply]; simp; try ring



theorem jc5_earShelf_eq (c : Site 2) (len : ℤ) :
    jc5_earShelf c len = c + ![len, -1] := by
  unfold jc5_earShelf jc5_earCell
  funext i; fin_cases i <;> · simp only [Pi.add_apply]; simp


theorem jc5_earShelf_eq_downCell (c : Site 2) (len : ℤ) :
    jc5_earShelf c len = jc3_downCell c len := by
  rw [jc5_earShelf_eq, jc3_downCell_eq]










theorem jc5_earUp_nmem (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (hframe : jc2_RunFrame K c len) : jc5_earUp c len ∉ K := by
  rw [jc5_earUp_eq]
  exact hframe.no_up len





theorem jc5_earRight_nmem (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (hframe : jc2_RunFrame K c len) : jc5_earRight c len ∉ K := by
  rw [jc5_earRight_eq]
  exact hframe.right_out






theorem jc5_earShelf_mem (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (hthick : jc2_FullyThick K c len) (hlen : 0 ≤ len) : jc5_earShelf c len ∈ K := by
  rw [jc5_earShelf_eq_downCell]
  exact jc3_downCell_mem K c len hthick hlen











theorem jc5_earShelf_ne_ear (c : Site 2) (len : ℤ) :
    jc5_earShelf c len ≠ jc5_earCell c len := by
  rw [jc5_earShelf_eq_downCell, jc5_earCell_eq_runRightEnd]
  exact jc3_downCell_ne_runRightEnd c len




theorem jc5_earShelf_mem_diff (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (hthick : jc2_FullyThick K c len) (hlen : 0 ≤ len) :
    jc5_earShelf c len ∈ K \ {jc5_earCell c len} :=
  ⟨jc5_earShelf_mem K c len hthick hlen,
   by simpa only [Set.mem_singleton_iff] using jc5_earShelf_ne_ear c len⟩





theorem jc5_earShelf_adj_ear (c : Site 2) (len : ℤ) :
    (hypercubicLattice 2).Adj (jc5_earCell c len) (jc5_earShelf c len) := by
  rw [jc5_earCell_eq_runRightEnd, jc5_earShelf_eq_downCell]
  exact jc3_downCell_adj_runRightEnd c len





















structure jc5_EarFrame (K : Set (Site 2)) (c : Site 2) (len : ℤ) : Prop where
  
  isFramedRun : jc2_RunFrame K c len
  
  ear_up_out : jc5_earUp c len ∉ K
  
  ear_right_out : jc5_earRight c len ∉ K
  

  ear_shelf_in : jc5_earShelf c len ∈ K




theorem jc5_EarFrame.isExtreme {K : Set (Site 2)} {c : Site 2} {len : ℤ}
    (h : jc5_EarFrame K c len) : IsExtremeCell K c :=
  h.isFramedRun.isExtreme





theorem jc5_EarFrame.no_run_up {K : Set (Site 2)} {c : Site 2} {len : ℤ}
    (h : jc5_EarFrame K c len) : ∀ j : ℤ, (c + ![j, 1]) ∉ K :=
  h.isFramedRun.no_up


theorem jc5_EarFrame.len_nonneg {K : Set (Site 2)} {c : Site 2} {len : ℤ}
    (h : jc5_EarFrame K c len) : 0 ≤ len :=
  h.isFramedRun.len_nonneg


theorem jc5_EarFrame.ear_mem {K : Set (Site 2)} {c : Site 2} {len : ℤ}
    (h : jc5_EarFrame K c len) : jc5_earCell c len ∈ K :=
  h.isFramedRun.run_mem len h.len_nonneg (le_refl len)


theorem jc5_EarFrame.shelf_mem_diff {K : Set (Site 2)} {c : Site 2} {len : ℤ}
    (h : jc5_EarFrame K c len) :
    jc5_earShelf c len ∈ K \ {jc5_earCell c len} :=
  ⟨h.ear_shelf_in,
   by simpa only [Set.mem_singleton_iff] using jc5_earShelf_ne_ear c len⟩














theorem jc5_earFrame_of_runFrame (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (hframe : jc2_RunFrame K c len) (hthick : jc2_FullyThick K c len) :
    jc5_EarFrame K c len where
  isFramedRun := hframe
  ear_up_out := jc5_earUp_nmem K c len hframe
  ear_right_out := jc5_earRight_nmem K c len hframe
  ear_shelf_in := jc5_earShelf_mem K c len hthick hframe.len_nonneg






theorem jc5_earFrame_of_extremeCell (K : Set (Site 2)) (hK : K.Finite) (c : Site 2)
    (hc : IsExtremeCell K c) (hthick : jc2_FullyThick K c (jc_runMax K c : ℤ)) :
    jc5_EarFrame K c (jc_runMax K c : ℤ) :=
  jc5_earFrame_of_runFrame K c (jc_runMax K c : ℤ)
    (jc2_runFrame_of_extremeCell K hK c hc) hthick













theorem jc5_earFrame (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty)
    (hthick : ∀ c, IsExtremeCell K c → jc2_FullyThick K c (jc_runMax K c : ℤ)) :
    ∃ c len, jc5_EarFrame K c len := by
  obtain ⟨c, hc⟩ := exists_extremeCell K hK hne
  exact ⟨c, (jc_runMax K c : ℤ), jc5_earFrame_of_extremeCell K hK c hc (hthick c hc)⟩






theorem jc5_earFrame_explicit (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (hframe : jc2_RunFrame K c len) (hthick : jc2_FullyThick K c len) :
    jc5_earCell c len ∈ K ∧
      jc5_earUp c len ∉ K ∧
      jc5_earRight c len ∉ K ∧
      jc5_earShelf c len ∈ K ∧
      jc5_earShelf c len ∈ K \ {jc5_earCell c len} ∧
      (hypercubicLattice 2).Adj (jc5_earCell c len) (jc5_earShelf c len) := by
  have h := jc5_earFrame_of_runFrame K c len hframe hthick
  exact ⟨h.ear_mem, h.ear_up_out, h.ear_right_out, h.ear_shelf_in,
    h.shelf_mem_diff, jc5_earShelf_adj_ear c len⟩





theorem jc5_earFrame_convexCorner (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (hframe : jc2_RunFrame K c len) (hthick : jc2_FullyThick K c len) :
    (jc5_earCell c len + ![0, 1] ∉ K) ∧
      (jc5_earCell c len + ![1, 0] ∉ K) ∧
      (jc5_earCell c len + ![0, -1] ∈ K) := by
  have h := jc5_earFrame_of_runFrame K c len hframe hthick
  exact ⟨h.ear_up_out, h.ear_right_out, h.ear_shelf_in⟩











theorem jc5_block2_isTopRowRun : jc_IsTopRowRun jc2_block2 (![0, 1] : Site 2) 1 where
  isExtreme := by
    refine ⟨?_, ?_⟩
    · exact ⟨by left; simp, by right; simp⟩
    · intro v hv
      
      obtain ⟨hv0, hv1⟩ := hv
      unfold lexKey
      rw [Prod.Lex.toLex_le_toLex]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rcases hv1 with h1 | h1
      · left; omega
      · rcases hv0 with h0 | h0
        · right; refine ⟨by omega, ?_⟩; omega
        · right; refine ⟨by omega, ?_⟩; omega
  len_nonneg := by norm_num
  run_mem := by
    intro j hj0 hj1
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · refine ⟨?_, ?_⟩
      · left; simp only [Pi.add_apply, Matrix.cons_val_zero]; ring
      · right; simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]; ring
    · refine ⟨?_, ?_⟩
      · right; simp only [Pi.add_apply, Matrix.cons_val_zero]; ring
      · right; simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]; ring
  right_stop := by
    
    intro h
    obtain ⟨h0, _⟩ := h
    revert h0
    simp only [Pi.add_apply, Matrix.cons_val_zero]
    norm_num


theorem jc5_block2_runFrame : jc2_RunFrame jc2_block2 (![0, 1] : Site 2) 1 := by
  obtain ⟨hnoup, hleft, hright⟩ :=
    jc_runFrame jc2_block2 (![0, 1] : Site 2) 1 jc5_block2_isTopRowRun
  exact ⟨jc5_block2_isTopRowRun, hnoup, hleft, hright⟩






theorem jc5_block2_earFrame : jc5_EarFrame jc2_block2 (![0, 1] : Site 2) 1 :=
  jc5_earFrame_of_runFrame jc2_block2 (![0, 1] : Site 2) 1
    jc5_block2_runFrame jc2_block2_fullyThick




theorem jc5_block2_convexCorner :
    (jc5_earCell (![0, 1] : Site 2) 1 + ![0, 1] ∉ jc2_block2) ∧
      (jc5_earCell (![0, 1] : Site 2) 1 + ![1, 0] ∉ jc2_block2) ∧
      (jc5_earCell (![0, 1] : Site 2) 1 + ![0, -1] ∈ jc2_block2) :=
  jc5_earFrame_convexCorner jc2_block2 (![0, 1] : Site 2) 1
    jc5_block2_runFrame jc2_block2_fullyThick




























end Walls

end StatMech
