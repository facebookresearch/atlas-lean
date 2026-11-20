/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.Sharpness.DeltaBound
import Code.Walls.ghggrahamclose

open Finset SimpleGraph
open scoped BigOperators symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

namespace StatMech.FrontierA

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy
open StatMech.Sharpness.RandomCurrent

variable {V : Type*} [Fintype V] [DecidableEq V]



def grahamAllThreeConnected (G : SimpleGraph V) (m : Current V)
    (i j k l : V) : Prop :=
  CurrentConnected G m i j ∧ CurrentConnected G m i k ∧
    CurrentConnected G m i l



theorem fourSources_symmDiff_pair
    {i j k l : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    ({i, j, k, l} : Finset V) ∆ {i, j} = {k, l} := by
  ext x
  simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  constructor <;> intro hx
  · rcases hx with ⟨hx, hnot⟩ | ⟨hx, hnot⟩
    · rcases hx with rfl | rfl | rfl | rfl <;> simp_all
    · exact (hnot (by tauto)).elim
  · rcases hx with rfl | rfl <;> simp_all [eq_comm]


theorem gatedSourcePairSum_true
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (A B : Finset V) :
    gatedSourcePairSum G beta J A B (fun _ => True) =
      sourcePairSum G beta J A B := by
  unfold gatedSourcePairSum sourcePairSum
  apply tsum_congr
  rintro ⟨p, q⟩
  simp




theorem grahamPairProduct_eq_connectedMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {i j k l : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    currentSum G beta J {i, j} * currentSum G beta J {k, l} =
      gatedSourcePairSum G beta J {i, j, k, l} ∅
        (fun m => CurrentConnected G m i j) := by
  rw [mul_comm]
  rw [← sourcePairSum_eq_mul]
  rw [← gatedSourcePairSum_true]
  have hswitch := gatedSourcePairSum_switching G beta J
    ({i, j, k, l} : Finset V) hij (fun _ => True)
  rw [fourSources_symmDiff_pair hij hik hil hjk hjl hkl] at hswitch
  simpa only [true_and] using hswitch



theorem grahamCurrent_one_or_three
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset -> Nat)
    {i j k l : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hsrc : sources G (ofEdgeFun G m) = {i, j, k, l}) :
    #(({j, k, l} : Finset V).filter
        (fun x => CurrentConnected G (ofEdgeFun G m) i x)) = 1 ∨
      #(({j, k, l} : Finset V).filter
        (fun x => CurrentConnected G (ofEdgeFun G m) i x)) = 3 := by
  let U : Finset (Copy G m) := Finset.univ
  have hsrcU : RandomCurrent.sources (endsM G m) U = {i, j, k, l} := by
    rw [sources_eq, profileFlux_univ]
    exact hsrc
  have h := StatMech.Walls.ghg_one_or_three (endsM G m) U
    (fun e _ => endsM_not_isDiag G m e) hsrcU hij hik hil hjk hjl hkl
  simpa only [U, connK_univ_iff] using h


theorem grahamFourSource_indicator_cancellation
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset -> Nat)
    {i j k l : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hsrc : sources G (ofEdgeFun G m) = {i, j, k, l}) :
    (1 : Real) - (if CurrentConnected G (ofEdgeFun G m) i j then 1 else 0) -
        (if CurrentConnected G (ofEdgeFun G m) i k then 1 else 0) -
        (if CurrentConnected G (ofEdgeFun G m) i l then 1 else 0) =
      -2 * (if grahamAllThreeConnected G (ofEdgeFun G m) i j k l then 1 else 0) := by
  have hcount := grahamCurrent_one_or_three G m hij hik hil hjk hjl hkl hsrc
  by_cases hj : CurrentConnected G (ofEdgeFun G m) i j <;>
    by_cases hk : CurrentConnected G (ofEdgeFun G m) i k <;>
    by_cases hl : CurrentConnected G (ofEdgeFun G m) i l
  all_goals
    simp only [Finset.filter_insert, Finset.filter_singleton,
      hj, hk, hl, if_true, if_false] at hcount
    simp [hjk, hjl, hkl] at hcount
    try norm_num [grahamAllThreeConnected, hj, hk, hl] at hcount ⊢




theorem grahamWeightedFourSource_cancellation
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {i j k l : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    gatedSourcePairSum G beta J {i, j, k, l} ∅ (fun _ => True) -
        gatedSourcePairSum G beta J {i, j, k, l} ∅
          (fun m => CurrentConnected G m i j) -
        gatedSourcePairSum G beta J {i, j, k, l} ∅
          (fun m => CurrentConnected G m i k) -
        gatedSourcePairSum G beta J {i, j, k, l} ∅
          (fun m => CurrentConnected G m i l) =
      -2 * gatedSourcePairSum G beta J {i, j, k, l} ∅
        (fun m => grahamAllThreeConnected G m i j k l) := by
  let P0 : Current V -> Prop := fun _ => True
  let Pj : Current V -> Prop := fun m => CurrentConnected G m i j
  let Pk : Current V -> Prop := fun m => CurrentConnected G m i k
  let Pl : Current V -> Prop := fun m => CurrentConnected G m i l
  let P3 : Current V -> Prop := fun m => grahamAllThreeConnected G m i j k l
  have s0 := summable_gatedSourcePairSummand G beta J {i, j, k, l} ∅ P0
  have sj := summable_gatedSourcePairSummand G beta J {i, j, k, l} ∅ Pj
  have sk := summable_gatedSourcePairSummand G beta J {i, j, k, l} ∅ Pk
  have sl := summable_gatedSourcePairSummand G beta J {i, j, k, l} ∅ Pl
  unfold gatedSourcePairSum
  change (∑' pq, _) - (∑' pq, _) - (∑' pq, _) - (∑' pq, _) = _
  rw [← s0.tsum_sub sj, ← (s0.sub sj).tsum_sub sk,
    ← ((s0.sub sj).sub sk).tsum_sub sl, ← tsum_mul_left]
  apply tsum_congr
  rintro ⟨p, q⟩
  let m := ofEdgeFun G (fun e => p e + q e)
  by_cases hp : sources G (ofEdgeFun G p) = {i, j, k, l}
  · by_cases hq : sources G (ofEdgeFun G q) = ∅
    · have hsrc : sources G m = {i, j, k, l} := by
        dsimp [m]
        rw [← ofEdgeFun_add G p q, sources_add, hp, hq]
        ext x
        simp [Finset.mem_symmDiff]
      have hcoeff := grahamFourSource_indicator_cancellation G
        (fun e => p e + q e) hij hik hil hjk hjl hkl hsrc
      dsimp [P0, Pj, Pk, Pl, P3]
      simp only [hp, hq, if_true]
      calc
        _ = weight G beta J (ofEdgeFun G p) * weight G beta J (ofEdgeFun G q) *
            ((1 : Real) -
              (if CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) i j then 1 else 0) -
              (if CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) i k then 1 else 0) -
              (if CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) i l then 1 else 0)) := by ring
        _ = weight G beta J (ofEdgeFun G p) * weight G beta J (ofEdgeFun G q) *
            (-2 * (if grahamAllThreeConnected G
              (ofEdgeFun G (fun e => p e + q e)) i j k l then 1 else 0)) := by rw [hcoeff]
        _ = _ := by ring
    · simp [hq]
  · simp [hp]



theorem grahamCurrentSum_ursell4_eq_allThree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {i j k l : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    currentSum G beta J {i, j, k, l} * currentSum G beta J ∅ -
        currentSum G beta J {i, j} * currentSum G beta J {k, l} -
        currentSum G beta J {i, k} * currentSum G beta J {j, l} -
        currentSum G beta J {i, l} * currentSum G beta J {j, k} =
      -2 * gatedSourcePairSum G beta J {i, j, k, l} ∅
        (fun m => grahamAllThreeConnected G m i j k l) := by
  rw [← sourcePairSum_eq_mul, ← gatedSourcePairSum_true]
  rw [grahamPairProduct_eq_connectedMass G beta J hij hik hil hjk hjl hkl]
  rw [grahamPairProduct_eq_connectedMass G beta J hik hij hil hjk.symm hkl hjl]
  rw [show ({i, k, j, l} : Finset V) = {i, j, k, l} by
    ext x; simp [or_comm, or_left_comm]]
  rw [grahamPairProduct_eq_connectedMass G beta J hil hij hik hjl.symm hkl.symm hjk]
  rw [show ({i, l, j, k} : Finset V) = {i, j, k, l} by
    ext x; simp [or_comm, or_left_comm]]
  exact grahamWeightedFourSource_cancellation G beta J hij hik hil hjk hjl hkl

end StatMech.FrontierA
