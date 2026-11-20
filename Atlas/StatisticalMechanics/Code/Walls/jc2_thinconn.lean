/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































import Mathlib
import Code.Walls.jc_runnoup
import Code.Walls.jc_leafremoval
import Code.Walls.jc_core

open SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice




















theorem jc2_thinFingerClip_cellConnected (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (hconn : CellConnected K) (hrun : jc_IsTopRowRun K c len) (hlen : 1 ≤ len)
    (hthin : (c + ![len, 0] : Site 2) + ![0, -1] ∉ K) :
    CellConnected (K \ {(c + ![len, 0] : Site 2)}) :=
  jc_cellConnected_diff_of_pendant K (c + ![len, 0]) hconn
    (jc_rightEnd_pendant_of_down_nmem K c len hrun hlen hthin)






theorem jc2_thinFingerClip_cellConnected' (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (r : Site 2) (hr : r = c + ![len, 0]) (hconn : CellConnected K)
    (hrun : jc_IsTopRowRun K c len) (hlen : 1 ≤ len) (hthin : (r + ![0, -1] : Site 2) ∉ K) :
    CellConnected (K \ {r}) := by
  subst hr
  exact jc2_thinFingerClip_cellConnected K c len hconn hrun hlen hthin






theorem jc2_thinConn (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (hconn : CellConnected K) (hrun : jc_IsTopRowRun K c len) (hlen : 1 ≤ len)
    (hthin : (c + ![len, -1] : Site 2) ∉ K) :
    CellConnected (K \ {(c + ![len, 0] : Site 2)}) := by
  apply jc2_thinFingerClip_cellConnected K c len hconn hrun hlen
  
  have hcell : (c + ![len, 0] : Site 2) + ![0, -1] = c + ![len, -1] := by
    funext i; fin_cases i <;> · simp only [Pi.add_apply]; simp
  rw [hcell]
  exact hthin











theorem jc2_jc_domino_eq_domino : jc_domino = domino := rfl



theorem jc2_domino_cellConnected : CellConnected domino :=
  jc2_jc_domino_eq_domino ▸ jc_domino_cellConnected






theorem jc2_domino_thinConn :
    CellConnected (domino \ {(![0, 0] : Site 2) + ![1, 0]}) := by
  apply jc2_thinFingerClip_cellConnected domino (![0, 0] : Site 2) 1
    jc2_domino_cellConnected jc_domino_isTopRowRun (by norm_num)
  
  apply not_mem_domino
  intro h
  rcases h with ⟨_, h1⟩ | ⟨_, h1⟩ <;>
    · revert h1
      simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
      omega

end Walls

end StatMech
