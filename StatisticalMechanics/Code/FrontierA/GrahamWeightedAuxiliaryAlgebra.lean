/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierA.GrahamWeightedFourCurrent
import Code.Walls.gc37hdom

open Finset SimpleGraph
open scoped BigOperators symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

namespace StatMech.FrontierA

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]



theorem gc37_sourcePairConnSum_eq_gated
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (A B : Finset V) (u v : V) :
    StatMech.Walls.gc37_sourcePairConnSum G beta J A B u v =
      gatedSourcePairSum G beta J A B
        (fun n => CurrentConnected G n u v) := by
  unfold StatMech.Walls.gc37_sourcePairConnSum gatedSourcePairSum
  rfl



theorem graham_two_connections_iff_allThree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p q : ↥G.edgeFinset -> Nat)
    {i j k l : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hp : sources G (ofEdgeFun G p) = {i, j, k, l})
    (hq : sources G (ofEdgeFun G q) = ∅) :
    (CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) i k ∧
        CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) k l) ↔
      grahamAllThreeConnected G (ofEdgeFun G (fun e => p e + q e)) i j k l := by
  let n := ofEdgeFun G (fun e => p e + q e)
  have hsrc : sources G n = {i, j, k, l} := by
    dsimp [n]
    rw [← ofEdgeFun_add G p q, sources_add, hp, hq]
    ext x
    simp [Finset.mem_symmDiff]
  constructor
  · rintro ⟨hikC, hklC⟩
    have hilC : CurrentConnected G n i l :=
      CurrentConnected.trans G hikC hklC
    have hcount := grahamCurrent_one_or_three G (fun e => p e + q e)
      hij hik hil hjk hjl hkl hsrc
    have hjC : CurrentConnected G n i j := by
      by_contra hnj
      change CurrentConnected G n i k at hikC
      change CurrentConnected G n i l at hilC
      have hcard : #(({j, k, l} : Finset V).filter
          (fun x => CurrentConnected G n i x)) = 2 := by
        simp only [Finset.filter_insert, Finset.filter_singleton,
          hnj, hikC, hilC, if_true, if_false]
        simp [hkl]
      rw [hcard] at hcount
      omega
    exact ⟨hjC, hikC, hilC⟩
  · rintro ⟨hijC, hikC, hilC⟩
    exact ⟨hikC, CurrentConnected.trans G (CurrentConnected.symm G hikC) hilC⟩



theorem grahamAllThreeMass_eq_pairConnectionMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {i j k l : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    gatedSourcePairSum G beta J {i, j, k, l} ∅
        (fun n => grahamAllThreeConnected G n i j k l) =
      StatMech.Walls.gc37_sourcePairConnSum G beta J {i, j} {k, l} i k := by
  have hswitch := gatedSourcePairSum_switching G beta J
    ({i, j, k, l} : Finset V) hkl
    (fun n => CurrentConnected G n i k)
  have hsd : ({i, j, k, l} : Finset V) ∆ {k, l} = {i, j} := by
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    by_cases hxi : x = i <;> by_cases hxj : x = j <;>
      by_cases hxk : x = k <;> by_cases hxl : x = l <;> simp_all [eq_comm]
  rw [hsd] at hswitch
  rw [gc37_sourcePairConnSum_eq_gated]
  rw [hswitch]
  apply gatedSourcePairSum_congr_sources
  intro p q hp hq
  exact (graham_two_connections_iff_allThree G p q
    hij hik hil hjk hjl hkl hp hq).symm



theorem grahamAuxConnectionMass_eq_currentSums
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {i j m : V} (hij : i ≠ j) (him : i ≠ m) (hjm : j ≠ m) :
    StatMech.Walls.gc37_sourcePairConnSum G beta J {i, j} ∅ i m =
      currentSum G beta J {i, m} * currentSum G beta J {j, m} := by
  rw [gc37_sourcePairConnSum_eq_gated]
  have hswitch := gatedSourcePairSum_switching G beta J
    ({i, j} : Finset V) him (fun _ => True)
  have hsd : ({i, j} : Finset V) ∆ {i, m} = {j, m} := by
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    constructor <;> intro hx
    · rcases hx with ⟨hx, hn⟩ | ⟨hx, hn⟩
      · rcases hx with rfl | rfl <;> simp_all [eq_comm]
      · rcases hx with rfl | rfl <;> simp_all [eq_comm]
    · rcases hx with rfl | rfl <;> simp_all [eq_comm]
  rw [hsd] at hswitch
  rw [mul_comm]
  rw [← sourcePairSum_eq_mul]
  rw [← gatedSourcePairSum_true]
  simpa only [true_and] using hswitch.symm





theorem grahamAuxiliary_disconnection_decomposition
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (i j k l m : V) :
    let Z := currentSum G beta J ∅
    let Cik := StatMech.Walls.gc37_sourcePairConnSum G beta J {i, j} {k, l} i k
    let Cim := StatMech.Walls.gc37_sourcePairConnSum G beta J {i, j} ∅ i m
    let Ckm := StatMech.Walls.gc37_sourcePairConnSum G beta J {k, l} ∅ k m
    let Dik := sourcePairDisconnSum G beta J {i, j} {k, l} i k
    let Dim := sourcePairDisconnSum G beta J {i, j} ∅ i m
    let Dkm := sourcePairDisconnSum G beta J {k, l} ∅ k m
    (-2 * Z ^ 2 * Cik + 2 * Cim * Ckm =
      2 * Z ^ 2 * Dik -
        2 * Dim * currentSum G beta J {k, l} * Z -
        2 * Cim * Dkm) := by
  dsimp
  have hik := StatMech.Walls.gc37_sourcePairSum_conn_add_disconn
    G beta J {i, j} {k, l} i k
  have him := StatMech.Walls.gc37_sourcePairSum_conn_add_disconn
    G beta J {i, j} ∅ i m
  have hkm := StatMech.Walls.gc37_sourcePairSum_conn_add_disconn
    G beta J {k, l} ∅ k m
  rw [sourcePairSum_eq_mul] at hik him hkm
  have hDik : sourcePairDisconnSum G beta J {i, j} {k, l} i k =
      currentSum G beta J {i, j} * currentSum G beta J {k, l} -
        StatMech.Walls.gc37_sourcePairConnSum G beta J {i, j} {k, l} i k := by
    linarith [hik]
  have hDim : sourcePairDisconnSum G beta J {i, j} ∅ i m =
      currentSum G beta J {i, j} * currentSum G beta J ∅ -
        StatMech.Walls.gc37_sourcePairConnSum G beta J {i, j} ∅ i m := by
    linarith [him]
  have hDkm : sourcePairDisconnSum G beta J {k, l} ∅ k m =
      currentSum G beta J {k, l} * currentSum G beta J ∅ -
        StatMech.Walls.gc37_sourcePairConnSum G beta J {k, l} ∅ k m := by
    linarith [hkm]
  rw [hDik, hDim, hDkm]
  ring



theorem grahamCurrentSum_preEq22
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {i j k l m : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (him : i ≠ m) (hjm : j ≠ m) (hkm : k ≠ m) (hlm : l ≠ m) :
    let Z := currentSum G beta J ∅
    Z ^ 2 *
        (currentSum G beta J {i, j, k, l} * Z -
          currentSum G beta J {i, j} * currentSum G beta J {k, l} -
          currentSum G beta J {i, k} * currentSum G beta J {j, l} -
          currentSum G beta J {i, l} * currentSum G beta J {j, k}) +
        2 * (currentSum G beta J {i, m} * currentSum G beta J {j, m}) *
          (currentSum G beta J {k, m} * currentSum G beta J {l, m}) =
      2 * Z ^ 2 * sourcePairDisconnSum G beta J {i, j} {k, l} i k -
        2 * sourcePairDisconnSum G beta J {i, j} ∅ i m *
          currentSum G beta J {k, l} * Z -
        2 * StatMech.Walls.gc37_sourcePairConnSum G beta J {i, j} ∅ i m *
          sourcePairDisconnSum G beta J {k, l} ∅ k m := by
  dsimp
  rw [grahamCurrentSum_ursell4_eq_allThree G beta J hij hik hil hjk hjl hkl]
  rw [grahamAllThreeMass_eq_pairConnectionMass G beta J hij hik hil hjk hjl hkl]
  rw [← grahamAuxConnectionMass_eq_currentSums G beta J hij him hjm]
  rw [← grahamAuxConnectionMass_eq_currentSums G beta J hkl hkm hlm]
  have h := grahamAuxiliary_disconnection_decomposition G beta J i j k l m
  dsimp at h
  ring_nf at h ⊢
  exact h

end StatMech.FrontierA
