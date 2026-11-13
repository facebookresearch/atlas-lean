/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















































































import Mathlib
import Code.Walls.jc_steplocal
import Code.Walls.jc_turnpreserveengine
import Code.Walls.jc_orbitinvariant
import Code.Walls.jc_footprintreduction
import Code.Walls.jc_earanchor
import Code.Walls.jc_toprowrun
import Code.Walls.jc_runnoup
import Code.Walls.jc_leafremoval
import Code.Lattice.HypercubicLattice
import Code.Lattice.PlanarDual
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.DartOrbit
import Code.Lattice.TurningNumber
import Code.Lattice.CornerBalance
import Code.Lattice.EarRemoval
import Code.Lattice.EarExistence
import Code.Lattice.EarContraction
import Code.Lattice.BalanceContraction
import Code.Lattice.GaussBonnetEar
import Code.Lattice.BalancePreservingContraction
import Code.Lattice.NoDiagTouchClose

open SimpleGraph Function Set

namespace StatMech

namespace Walls

open StatMech.Lattice



















theorem jc_adj_cases (v w : Site 2) (hadj : (hypercubicLattice 2).Adj v w) :
    v = w + ![1, 0] ∨ v = w + ![-1, 0] ∨ v = w + ![0, 1] ∨ v = w + ![0, -1] :=
  adj_neighbor_cases v w hadj


theorem jc_shift_add (c : Site 2) (i j : ℤ) :
    (c + ![i, 0] : Site 2) + ![j, 0] = c + ![i + j, 0] := by
  funext k; fin_cases k <;> · simp only [Pi.add_apply]; simp <;> ring














theorem jc_rightEnd_pendant_of_down_nmem (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (hrun : jc_IsTopRowRun K c len) (hlen : 1 ≤ len)
    (hdown : (c + ![len, 0] : Site 2) + ![0, -1] ∉ K) :
    jc_IsPendantCell K (c + ![len, 0]) := by
  set r : Site 2 := c + ![len, 0] with hr
  
  have hleftK : (c + ![len - 1, 0] : Site 2) ∈ K :=
    hrun.run_mem (len - 1) (by omega) (by omega)
  
  have hleftEq : (r + ![(-1 : ℤ), 0] : Site 2) = c + ![len - 1, 0] := by
    rw [hr, jc_shift_add]; congr 2
  
  have hleftAdj : (hypercubicLattice 2).Adj r (c + ![len - 1, 0]) := by
    rw [hr, hypercubicLattice_adj, Fin.sum_univ_two]
    have e0 : ((c + ![len, 0] : Site 2) 0 - (c + ![len - 1, 0] : Site 2) 0) = 1 := by
      simp only [Pi.add_apply, Matrix.cons_val_zero]; ring
    have e1 : ((c + ![len, 0] : Site 2) 1 - (c + ![len - 1, 0] : Site 2) 1) = 0 := by
      simp only [Pi.add_apply, Matrix.cons_val_one]; ring
    rw [e0, e1]; decide
  refine ⟨hrun.run_mem len (by omega) (le_refl len), c + ![len - 1, 0],
    ⟨hleftK, hleftAdj⟩, ?_⟩
  
  rintro w ⟨hwK, hadj⟩
  rcases jc_adj_cases w r hadj.symm with hw | hw | hw | hw
  · 
    exfalso
    have : (r + ![1, 0] : Site 2) = c + ![len + 1, 0] := by rw [hr, jc_shift_add]
    rw [this] at hw
    exact hrun.right_stop (hw ▸ hwK)
  · 
    rw [hw, hleftEq]
  · 
    exfalso
    have hup : (r + ![0, 1] : Site 2) ∉ K := by
      rw [hr]
      rw [show (c + ![len, 0] : Site 2) + ![0, 1] = c + ![len, 1] by
        funext k; fin_cases k <;> · simp only [Pi.add_apply]; simp]
      exact jc_run_no_up K c len hrun len
    exact hup (hw ▸ hwK)
  · 
    exact absurd (hw ▸ hwK) hdown







theorem jc_cellConnected_diff_rightEnd (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (hconn : CellConnected K) (hrun : jc_IsTopRowRun K c len) (hlen : 1 ≤ len)
    (hdown : (c + ![len, 0] : Site 2) + ![0, -1] ∉ K) :
    CellConnected (K \ {(c + ![len, 0] : Site 2)}) :=
  jc_cellConnected_diff_of_pendant K (c + ![len, 0]) hconn
    (jc_rightEnd_pendant_of_down_nmem K c len hrun hlen hdown)















theorem jc_balancePreservingContraction_of_saturating
    (h : jc_BalanceSaturatingContraction) : BalancePreservingContraction :=
  jc_footprintReduction h






theorem jc_core_iff_saturating :
    BalancePreservingContraction ↔ jc_BalanceSaturatingContraction :=
  jc_footprintReduction_iff















theorem jc_turningIsFullRevolution_of_saturating (h : jc_BalanceSaturatingContraction)
    (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty)
    (a : {e : Dart // IsBoundaryDart K e}) : TurningIsFullRevolution K a :=
  turningIsFullRevolution_of_contraction (jc_balancePreservingContraction_of_saturating h)
    K hK hne a






theorem jc_starHull_turningIsFullRevolution_of_saturating (h : jc_BalanceSaturatingContraction)
    (K : Set (Site 2)) (hSK : (ndt_StarHull K).Finite) (hne : (ndt_StarHull K).Nonempty)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    TurningIsFullRevolution (ndt_StarHull K) a :=
  gbe_totalTurn_eq_four_of_contraction K hSK hne a
    (jc_balancePreservingContraction_of_saturating h)






theorem jc_starHull_totalTurn_eq_four_of_saturating (h : jc_BalanceSaturatingContraction)
    (K : Set (Site 2)) (hSK : (ndt_StarHull K).Finite) (hne : (ndt_StarHull K).Nonempty)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = 4 ∨
      totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4 :=
  jc_starHull_turningIsFullRevolution_of_saturating h K hSK hne a









theorem jc_unitCell_core_balanceIsFour : BalanceIsFour unitCell ucBase :=
  unitCell_balanceIsFour






theorem jc_domino_core_witness :
    ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty)
      (a' : {e : Dart // IsBoundaryDart K' e}),
      K'.ncard < domino.ncard ∧ cornerBalance K' a' = cornerBalance domino dmBase :=
  jc_domino_saturating_witness





theorem jc_domino_rightEnd_pendant :
    jc_IsPendantCell domino ((![0, 0] : Site 2) + ![1, 0]) := by
  apply jc_rightEnd_pendant_of_down_nmem domino (![0, 0] : Site 2) 1 jc_domino_isTopRowRun
    (by norm_num)
  
  apply not_mem_domino
  intro h
  rcases h with ⟨_, h1⟩ | ⟨_, h1⟩ <;>
    · revert h1
      simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
      omega

end Walls

end StatMech
