/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.FrontierA.GrahamWeightedAuxiliaryAlgebra
import Code.FrontierA.GrahamWeightedSurvivorSwitching
import Code.FrontierA.GrahamWeightedFirstGKSDropGlobal
import Code.FrontierA.GrahamWeightedSecondGKSDropGlobal

open Finset SimpleGraph
open scoped BigOperators symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

namespace StatMech.FrontierA

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem gatedSourcePairSum_split
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (A B : Finset V) (P Q : Current V -> Prop)
    [DecidablePred P] [DecidablePred Q] :
    gatedSourcePairSum G beta J A B P =
      gatedSourcePairSum G beta J A B (fun n => P n ∧ Q n) +
        gatedSourcePairSum G beta J A B (fun n => P n ∧ ¬ Q n) := by
  unfold gatedSourcePairSum
  rw [← Summable.tsum_add
    (summable_gatedSourcePairSummand G beta J A B (fun n => P n ∧ Q n))
    (summable_gatedSourcePairSummand G beta J A B (fun n => P n ∧ ¬ Q n))]
  apply tsum_congr
  rintro ⟨p, q⟩
  let n := ofEdgeFun G (fun e => p e + q e)
  by_cases hp : sources G (ofEdgeFun G p) = A <;>
    by_cases hq : sources G (ofEdgeFun G q) = B <;>
    by_cases hP : P n <;> by_cases hQ : Q n <;>
    simp [n, hp, hq, hP, hQ]



theorem grahamFirstDisconnection_partition
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l m : V) :
    sourcePairDisconnSum G beta J {i, j} ∅ i m =
      gatedSourcePairSum G beta J {i, j} ∅
          (fun n => ¬ CurrentConnected G n i m ∧
            (CurrentConnected G n i k ∨ CurrentConnected G n i l)) +
        grahamFirstRemainderMass G beta J i j k l m := by
  have h := gatedSourcePairSum_split G beta J {i, j} ∅
    (fun n => ¬ CurrentConnected G n i m)
    (fun n => CurrentConnected G n i k ∨ CurrentConnected G n i l)
  rw [show sourcePairDisconnSum G beta J {i, j} ∅ i m =
      gatedSourcePairSum G beta J {i, j} ∅
        (fun n => ¬ CurrentConnected G n i m) by rfl]
  rw [h]
  congr 1
  unfold grahamFirstRemainderMass
  apply gatedSourcePairSum_congr_sources
  intro p q hp hq
  simp only [not_or]



theorem grahamSecondDisconnection_partition
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l m : V) :
    sourcePairDisconnSum G beta J {k, l} ∅ k m =
      gatedSourcePairSum G beta J {k, l} ∅
          (fun n => ¬ CurrentConnected G n k m ∧
            (CurrentConnected G n k i ∨ CurrentConnected G n k j)) +
        grahamSecondRemainderMass G beta J i j k l m := by
  have h := gatedSourcePairSum_split G beta J {k, l} ∅
    (fun n => ¬ CurrentConnected G n k m)
    (fun n => CurrentConnected G n k i ∨ CurrentConnected G n k j)
  rw [show sourcePairDisconnSum G beta J {k, l} ∅ k m =
      gatedSourcePairSum G beta J {k, l} ∅
        (fun n => ¬ CurrentConnected G n k m) by rfl]
  rw [h]
  congr 1
  unfold grahamSecondRemainderMass
  apply gatedSourcePairSum_congr_sources
  intro p q hp hq
  simp only [not_or]



theorem grahamMixedDisconnection_partition
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (i j k l m : V) :
    sourcePairDisconnSum G beta J {i, j} {k, l} i k =
      grahamFirstMixedRemainderMass G beta J i j k l m +
        grahamSecondMixedRemainderMass G beta J i j k l m := by
  have h := gatedSourcePairSum_split G beta J {i, j} {k, l}
    (fun n => ¬ CurrentConnected G n i k)
    (fun n => ¬ CurrentConnected G n i m)
  rw [show sourcePairDisconnSum G beta J {i, j} {k, l} i k =
      gatedSourcePairSum G beta J {i, j} {k, l}
        (fun n => ¬ CurrentConnected G n i k) by rfl]
  rw [h]
  congr 1
  · unfold grahamFirstMixedRemainderMass
    apply gatedSourcePairSum_congr_sources
    intro p q hp hq
    tauto
  · unfold grahamSecondMixedRemainderMass
    apply gatedSourcePairSum_congr_sources
    intro p q hp hq
    tauto




theorem grahamEq22_exact_refinement
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {i j k l m : V} (hij : i ≠ j) (him : i ≠ m) (hjm : j ≠ m) :
    let Z := currentSum G beta J ∅
    let Cim := StatMech.Walls.gc37_sourcePairConnSum
      G beta J {i, j} ∅ i m
    let S1 := gatedSourcePairSum G beta J {i, j} ∅
      (fun n => ¬ CurrentConnected G n i m ∧
        (CurrentConnected G n i k ∨ CurrentConnected G n i l))
    let S2 := gatedSourcePairSum G beta J {k, l} ∅
      (fun n => ¬ CurrentConnected G n k m ∧
        (CurrentConnected G n k i ∨ CurrentConnected G n k j))
    2 * Z ^ 2 * sourcePairDisconnSum G beta J {i, j} {k, l} i k -
        2 * sourcePairDisconnSum G beta J {i, j} ∅ i m *
          currentSum G beta J {k, l} * Z -
        2 * Cim * sourcePairDisconnSum G beta J {k, l} ∅ k m =
      -2 * Z * currentSum G beta J {k, l} * S1 -
        2 * Cim * S2 -
        2 * Z * (currentSum G beta J {k, l} *
          grahamFirstRemainderMass G beta J i j k l m -
          Z * grahamFirstMixedRemainderMass G beta J i j k l m) -
        2 * ((currentSum G beta J {i, m} * currentSum G beta J {j, m}) *
          grahamSecondRemainderMass G beta J i j k l m -
          Z ^ 2 * grahamSecondMixedRemainderMass G beta J i j k l m) := by
  dsimp
  rw [grahamFirstDisconnection_partition G beta J i j k l m]
  rw [grahamSecondDisconnection_partition G beta J i j k l m]
  rw [grahamMixedDisconnection_partition G beta J i j k l m]
  rw [grahamAuxConnectionMass_eq_currentSums G beta J hij him hjm]
  ring



theorem grahamEq22_survivor_upper_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    {i j k l m : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (him : i ≠ m) (hjk : j ≠ k) (hjl : j ≠ l) (hjm : j ≠ m)
    (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m) :
    let Z := currentSum G beta J ∅
    let Cim := StatMech.Walls.gc37_sourcePairConnSum
      G beta J {i, j} ∅ i m
    let S1 := gatedSourcePairSum G beta J {i, j} ∅
      (fun n => ¬ CurrentConnected G n i m ∧
        (CurrentConnected G n i k ∨ CurrentConnected G n i l))
    let S2 := gatedSourcePairSum G beta J {k, l} ∅
      (fun n => ¬ CurrentConnected G n k m ∧
        (CurrentConnected G n k i ∨ CurrentConnected G n k j))
    2 * Z ^ 2 * sourcePairDisconnSum G beta J {i, j} {k, l} i k -
        2 * sourcePairDisconnSum G beta J {i, j} ∅ i m *
          currentSum G beta J {k, l} * Z -
        2 * Cim * sourcePairDisconnSum G beta J {k, l} ∅ k m ≤
      -2 * Z * currentSum G beta J {k, l} * S1 - 2 * Cim * S2 := by
  dsimp
  rw [grahamEq22_exact_refinement G beta J hij him hjm]
  have hZ := StatMech.Ising.acr_currentSum_nonneg G beta J hbeta hJ ∅
  have hdrop1 := grahamFirstGlobalGKSDrop_nonneg G beta J hbeta hJ
    (i := i) (j := j) (k := k) (l := l) (m := m) hij hkl
  have hdrop2 := grahamSecondGlobalGKSDrop_nonneg G beta J hbeta hJ
    (i := i) (j := j) (k := k) (l := l) (m := m)
    hij hik hil him hjk hjl hjm hkl hkm hlm
  nlinarith



theorem grahamEq22_mixed_disconnection_upper_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    {i j k l m : V}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (him : i ≠ m) (hjk : j ≠ k) (hjl : j ≠ l) (hjm : j ≠ m)
    (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m) :
    let Z := currentSum G beta J ∅
    let Cim := StatMech.Walls.gc37_sourcePairConnSum
      G beta J {i, j} ∅ i m
    2 * Z ^ 2 * sourcePairDisconnSum G beta J {i, j} {k, l} i k -
        2 * sourcePairDisconnSum G beta J {i, j} ∅ i m *
          currentSum G beta J {k, l} * Z -
        2 * Cim * sourcePairDisconnSum G beta J {k, l} ∅ k m ≤
      -2 * Z * currentSum G beta J {k, l} *
          sourcePairDisconnSum G beta J {i, k} {k, j} i m -
        2 * Cim * sourcePairDisconnSum G beta J {k, i} {i, l} k m := by
  dsimp
  let S1 := gatedSourcePairSum G beta J {i, j} ∅
    (fun n => ¬ CurrentConnected G n i m ∧
      (CurrentConnected G n i k ∨ CurrentConnected G n i l))
  let S2 := gatedSourcePairSum G beta J {k, l} ∅
    (fun n => ¬ CurrentConnected G n k m ∧
      (CurrentConnected G n k i ∨ CurrentConnected G n k j))
  have hbase := grahamEq22_survivor_upper_bound G beta J hbeta hJ
    hij hik hil him hjk hjl hjm hkl hkm hlm
  dsimp only at hbase
  have hS1 := grahamFirstSurvivor_switching_lower_bound
    G beta J hbeta hJ (i := i) (j := j) (k := k) (l := l) (m := m)
      hij hik hjk
  have hS2 := grahamSecondSurvivor_switching_lower_bound
    G beta J hbeta hJ (i := i) (j := j) (k := k) (l := l) (m := m)
      hik hkl hil
  have hZ := StatMech.Ising.acr_currentSum_nonneg G beta J hbeta hJ ∅
  have hkl0 := StatMech.Ising.acr_currentSum_nonneg
    G beta J hbeta hJ {k, l}
  have hCim : 0 ≤ StatMech.Walls.gc37_sourcePairConnSum
      G beta J {i, j} ∅ i m := by
    rw [grahamAuxConnectionMass_eq_currentSums G beta J hij him hjm]
    exact mul_nonneg
      (StatMech.Ising.acr_currentSum_nonneg G beta J hbeta hJ {i, m})
      (StatMech.Ising.acr_currentSum_nonneg G beta J hbeta hJ {j, m})
  change sourcePairDisconnSum G beta J {i, k} {k, j} i m ≤ S1 at hS1
  change sourcePairDisconnSum G beta J {k, i} {i, l} k m ≤ S2 at hS2
  have hc1 : -2 * currentSum G beta J ∅ *
      currentSum G beta J {k, l} ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hZ) hkl0
  have hc2 : -2 * StatMech.Walls.gc37_sourcePairConnSum
      G beta J {i, j} ∅ i m ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) hCim
  have hS1' := mul_le_mul_of_nonpos_left hS1 hc1
  have hS2' := mul_le_mul_of_nonpos_left hS2 hc2
  exact hbase.trans (by
    dsimp [S1, S2] at hS1' hS2' ⊢
    linarith)

end StatMech.FrontierA
