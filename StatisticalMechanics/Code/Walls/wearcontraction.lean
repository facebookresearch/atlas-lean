/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










































































import Mathlib
import Code.Walls.jc4_core
import Code.Lattice.EarExistence
import Code.Lattice.EarContraction
import Code.Lattice.BalanceContraction

open SimpleGraph Function Set

namespace StatMech

namespace Walls

open StatMech.Lattice















theorem wear_balancePreservingContraction_of_merge (h : jc4_SaturatingMerge) :
    BalancePreservingContraction :=
  jc4_balancePreservingContraction_of_merge h





theorem wear_cornerBalance_eq_four_of_merge (h : jc4_SaturatingMerge)
    (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty)
    (a : {e : Dart // IsBoundaryDart K e}) :
    cornerBalance K a = 4 ∨ cornerBalance K a = -4 :=
  balanceIsFour_of_contraction (wear_balancePreservingContraction_of_merge h) K hK hne a






theorem wear_revCount_pm_one_of_merge (h : jc4_SaturatingMerge)
    (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty)
    (a : {e : Dart // IsBoundaryDart K e}) :
    revCount K a = 1 ∨ revCount K a = -1 :=
  (balanceIsFour_iff_revCount_pm_one K a).mp
    (wear_cornerBalance_eq_four_of_merge h K hK hne a)





theorem wear_starHull_totalTurn_eq_four_of_merge (h : jc4_SaturatingMerge)
    (K : Set (Site 2)) (hSK : (ndt_StarHull K).Finite) (hne : (ndt_StarHull K).Nonempty)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = 4 ∨
      totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4 :=
  jc4_starHull_totalTurn_eq_four_of_merge h K hSK hne a
















theorem wear_extremeCell_convex_up_left (K : Set (Site 2)) (c : Site 2)
    (hc : IsExtremeCell K c) :
    c + ![0, 1] ∉ K ∧ c + ![-1, 0] ∉ K :=
  ⟨extremeCell_up_nmem K c hc, extremeCell_left_nmem K c hc⟩






theorem wear_extremeCell_neighbor_right_or_down (K : Set (Site 2)) (c v : Site 2)
    (hc : IsExtremeCell K c) (hv : v ∈ K) (hadj : (hypercubicLattice 2).Adj v c) :
    v = c + ![1, 0] ∨ v = c + ![0, -1] :=
  extremeCell_neighbor_right_or_down K c v hc hv hadj















theorem wear_pendant_contraction (K : Set (Site 2)) (c : Site 2) (hc : c ∈ K)
    (hconn : CellConnected K)
    [Fintype ↑(((hypercubicLattice 2).induce K).neighborSet (⟨c, hc⟩ : K))]
    (hdeg : ((hypercubicLattice 2).induce K).degree (⟨c, hc⟩ : K) = 1) :
    CellConnected (K \ {c}) :=
  cellConnected_diff_of_degree_one K c hc hconn hdeg









theorem wear_unitCell_cornerBalance :
    cornerBalance unitCell ucBase = 4 ∨ cornerBalance unitCell ucBase = -4 :=
  Or.inr (unitCell_cornerBalance ucBase (Or.inl rfl))




theorem wear_domino_cornerBalance :
    cornerBalance domino dmBase = 4 ∨ cornerBalance domino dmBase = -4 :=
  Or.inr bpc_domino_cornerBalance








theorem wear_extremeCell_can_be_cutVertex :
    IsExtremeCell cutWitness ![1, 1] ∧ CellConnected cutWitness ∧
      ¬ CellConnected (cutWitness \ {![1, 1]}) :=
  ⟨cutWitness_extreme, cutWitness_cellConnected, cutWitness_diff_not_cellConnected⟩























end Walls

end StatMech
