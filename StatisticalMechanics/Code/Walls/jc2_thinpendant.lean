/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


































































import Mathlib
import Code.Walls.jc_runnoup
import Code.Walls.jc_leafremoval
import Code.Lattice.EarContraction

open SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice











theorem jc2_adj_cases (v w : Site 2) (hadj : (hypercubicLattice 2).Adj v w) :
    v = w + ![1, 0] ∨ v = w + ![-1, 0] ∨ v = w + ![0, 1] ∨ v = w + ![0, -1] :=
  adj_neighbor_cases v w hadj


theorem jc2_shift_add (c : Site 2) (i j : ℤ) :
    (c + ![i, 0] : Site 2) + ![j, 0] = c + ![i + j, 0] := by
  funext k; fin_cases k <;> · simp only [Pi.add_apply]; simp <;> ring























theorem jc2_thinPendant (K : Set (Site 2)) (c : Site 2) (L : ℤ)
    (hrun : jc_IsTopRowRun K c L) (hlen : 1 ≤ L)
    (hdown : (c + ![L, 0] : Site 2) + ![0, -1] ∉ K) :
    jc_IsPendantCell K (c + ![L, 0]) := by
  set r : Site 2 := c + ![L, 0] with hr
  
  have hleftK : (c + ![L - 1, 0] : Site 2) ∈ K :=
    hrun.run_mem (L - 1) (by omega) (by omega)
  
  have hleftEq : (r + ![(-1 : ℤ), 0] : Site 2) = c + ![L - 1, 0] := by
    rw [hr, jc2_shift_add]; congr 2
  
  have hleftAdj : (hypercubicLattice 2).Adj r (c + ![L - 1, 0]) := by
    rw [hr, hypercubicLattice_adj, Fin.sum_univ_two]
    have e0 : ((c + ![L, 0] : Site 2) 0 - (c + ![L - 1, 0] : Site 2) 0) = 1 := by
      simp only [Pi.add_apply, Matrix.cons_val_zero]; ring
    have e1 : ((c + ![L, 0] : Site 2) 1 - (c + ![L - 1, 0] : Site 2) 1) = 0 := by
      simp only [Pi.add_apply, Matrix.cons_val_one]; ring
    rw [e0, e1]; decide
  refine ⟨hrun.run_mem L (by omega) (le_refl L), c + ![L - 1, 0],
    ⟨hleftK, hleftAdj⟩, ?_⟩
  
  rintro w ⟨hwK, hadj⟩
  rcases jc2_adj_cases w r hadj.symm with hw | hw | hw | hw
  · 
    exfalso
    have hright : (r + ![1, 0] : Site 2) = c + ![L + 1, 0] := by rw [hr, jc2_shift_add]
    rw [hright] at hw
    exact hrun.right_stop (hw ▸ hwK)
  · 
    rw [hw, hleftEq]
  · 
    exfalso
    have hup : (r + ![0, 1] : Site 2) ∉ K := by
      rw [hr]
      rw [show (c + ![L, 0] : Site 2) + ![0, 1] = c + ![L, 1] by
        funext k; fin_cases k <;> · simp only [Pi.add_apply]; simp]
      exact jc_run_no_up K c L hrun L
    exact hup (hw ▸ hwK)
  · 
    exact absurd (hw ▸ hwK) hdown





theorem jc2_thinPendant_explicit (K : Set (Site 2)) (c : Site 2) (L : ℤ)
    (hrun : jc_IsTopRowRun K c L) (hlen : 1 ≤ L)
    (hdown : (c + ![L, 0] : Site 2) + ![0, -1] ∉ K) :
    (c + ![L, 0] : Site 2) ∈ K ∧
      (c + ![L - 1, 0] : Site 2) ∈ K ∧
      (hypercubicLattice 2).Adj (c + ![L, 0]) (c + ![L - 1, 0]) ∧
      ∀ w : Site 2, w ∈ K ∧ (hypercubicLattice 2).Adj (c + ![L, 0]) w →
        w = c + ![L - 1, 0] := by
  obtain ⟨hmem, u, ⟨huK, huAdj⟩, huniq⟩ := jc2_thinPendant K c L hrun hlen hdown
  
  have hleftK : (c + ![L - 1, 0] : Site 2) ∈ K :=
    hrun.run_mem (L - 1) (by omega) (by omega)
  have hleftAdj : (hypercubicLattice 2).Adj (c + ![L, 0]) (c + ![L - 1, 0]) := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]
    have e0 : ((c + ![L, 0] : Site 2) 0 - (c + ![L - 1, 0] : Site 2) 0) = 1 := by
      simp only [Pi.add_apply, Matrix.cons_val_zero]; ring
    have e1 : ((c + ![L, 0] : Site 2) 1 - (c + ![L - 1, 0] : Site 2) 1) = 0 := by
      simp only [Pi.add_apply, Matrix.cons_val_one]; ring
    rw [e0, e1]; decide
  have hu_eq : c + ![L - 1, 0] = u := huniq _ ⟨hleftK, hleftAdj⟩
  refine ⟨hmem, hleftK, hleftAdj, ?_⟩
  intro w hw
  rw [huniq w hw, ← hu_eq]












theorem jc2_domino_thinPendant :
    jc_IsPendantCell domino ((![0, 0] : Site 2) + ![1, 0]) := by
  apply jc2_thinPendant domino (![0, 0] : Site 2) 1 jc_domino_isTopRowRun (by norm_num)
  
  apply not_mem_domino
  refine fun h => ?_
  rcases h with ⟨_, h1⟩ | ⟨_, h1⟩ <;>
    · simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h1
      omega






theorem jc2_unitCell_runFrame_smoke :
    jc_IsTopRowRun unitCell (![0, 0] : Site 2) 0 :=
  jc_unitCell_isTopRowRun

end Walls

end StatMech
