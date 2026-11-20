/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



















































































import Mathlib
import Code.Walls.jc_runnoup
import Code.Walls.jc2_thickshelf

open SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice











def jc3_runRightEnd (c : Site 2) (len : ℤ) : Site 2 := c + ![len, 0]



def jc3_downCell (c : Site 2) (len : ℤ) : Site 2 := jc3_runRightEnd c len + ![0, -1]

@[simp] theorem jc3_runRightEnd_def (c : Site 2) (len : ℤ) :
    jc3_runRightEnd c len = c + ![len, 0] := rfl





theorem jc3_downCell_eq (c : Site 2) (len : ℤ) :
    jc3_downCell c len = c + ![len, -1] := by
  unfold jc3_downCell jc3_runRightEnd
  funext i; fin_cases i <;> · simp only [Pi.add_apply]; simp



theorem jc3_downCell_coord1 (c : Site 2) (len : ℤ) :
    (jc3_downCell c len) 1 = c 1 - 1 := by
  rw [jc3_downCell_eq]
  simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]; ring



theorem jc3_runRightEnd_coord1 (c : Site 2) (len : ℤ) :
    (jc3_runRightEnd c len) 1 = c 1 := by
  rw [jc3_runRightEnd_def]
  simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]; ring









theorem jc3_downCell_ne_runRightEnd (c : Site 2) (len : ℤ) :
    jc3_downCell c len ≠ jc3_runRightEnd c len := by
  intro h
  have h1 : (jc3_downCell c len) 1 = (jc3_runRightEnd c len) 1 := congrFun h 1
  rw [jc3_downCell_coord1, jc3_runRightEnd_coord1] at h1
  omega














theorem jc3_downCell_mem (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (hthick : jc2_FullyThick K c len) (hlen : 0 ≤ len) :
    jc3_downCell c len ∈ K := by
  rw [jc3_downCell_eq]
  exact jc2_shelf_right_end K c len hthick hlen









theorem jc3_downCell_mem_diff (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (hthick : jc2_FullyThick K c len) (hlen : 0 ≤ len) :
    jc3_downCell c len ∈ K \ {jc3_runRightEnd c len} :=
  ⟨jc3_downCell_mem K c len hthick hlen,
   by simpa only [Set.mem_singleton_iff] using jc3_downCell_ne_runRightEnd c len⟩






theorem jc3_downCell_adj_runRightEnd (c : Site 2) (len : ℤ) :
    (hypercubicLattice 2).Adj (jc3_runRightEnd c len) (jc3_downCell c len) := by
  rw [jc3_runRightEnd_def, jc3_downCell_eq]
  exact jc2_shelf_adj_run c len




















theorem jc3_shelfCell (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (hthick : jc2_FullyThick K c len) (hlen : 0 ≤ len) :
    jc3_downCell c len = c + ![len, -1] ∧
      jc3_downCell c len ∈ K ∧
      jc3_downCell c len ≠ jc3_runRightEnd c len ∧
      jc3_downCell c len ∈ K \ {jc3_runRightEnd c len} ∧
      (hypercubicLattice 2).Adj (jc3_runRightEnd c len) (jc3_downCell c len) :=
  ⟨jc3_downCell_eq c len,
   jc3_downCell_mem K c len hthick hlen,
   jc3_downCell_ne_runRightEnd c len,
   jc3_downCell_mem_diff K c len hthick hlen,
   jc3_downCell_adj_runRightEnd c len⟩









theorem jc3_rerouteTarget_in_clip (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (hthick : jc2_FullyThick K c len) (hlen : 0 ≤ len) :
    jc3_downCell c len ∈ K \ {jc3_runRightEnd c len} ∧
      (hypercubicLattice 2).Adj (jc3_runRightEnd c len) (jc3_downCell c len) :=
  ⟨jc3_downCell_mem_diff K c len hthick hlen,
   jc3_downCell_adj_runRightEnd c len⟩












theorem jc3_block2_downCell_mem :
    jc3_downCell (![0, 1] : Site 2) 1 ∈ jc2_block2 :=
  jc3_downCell_mem jc2_block2 (![0, 1] : Site 2) 1 jc2_block2_fullyThick (by norm_num)





theorem jc3_block2_downCell_mem_diff :
    jc3_downCell (![0, 1] : Site 2) 1 ∈
      jc2_block2 \ {jc3_runRightEnd (![0, 1] : Site 2) 1} :=
  jc3_downCell_mem_diff jc2_block2 (![0, 1] : Site 2) 1 jc2_block2_fullyThick (by norm_num)

end Walls

end StatMech
