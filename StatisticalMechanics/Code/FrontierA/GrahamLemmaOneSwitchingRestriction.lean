/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamWeightedEq22Refinement










open Finset SimpleGraph
open scoped symmDiff
open Classical

namespace StatMech.FrontierA

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem pair_symmDiff_shared_right {j k l : V}
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    ({j, l} : Finset V) ∆ {k, l} = {j, k} := by
  ext x
  simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  aesop



theorem grahamMixedDisconnection_eq_connectedRestriction
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {j k l m : V} (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    sourcePairDisconnSum G beta J {j, k} {k, l} k m =
      gatedSourcePairSum G beta J {j, l} ∅
        (fun n => ¬ CurrentConnected G n k m ∧ CurrentConnected G n k l) := by
  let P : Current V -> Prop := fun n => ¬ CurrentConnected G n k m
  have hswitch := gatedSourcePairSum_switching G beta J
    ({j, l} : Finset V) hkl P
  rw [pair_symmDiff_shared_right hjk hjl hkl] at hswitch
  rw [show sourcePairDisconnSum G beta J {j, k} {k, l} k m =
      gatedSourcePairSum G beta J {j, k} {k, l} P by rfl]
  simpa only [P] using hswitch



theorem grahamVacuumDisconnection_eq_mixed_add_remainder
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {j k l m : V} (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    sourcePairDisconnSum G beta J {j, l} ∅ k m =
      sourcePairDisconnSum G beta J {j, k} {k, l} k m +
        gatedSourcePairSum G beta J {j, l} ∅
          (fun n => ¬ CurrentConnected G n k m ∧ ¬ CurrentConnected G n k l) := by
  have hsplit := gatedSourcePairSum_split G beta J {j, l} ∅
    (fun n => ¬ CurrentConnected G n k m)
    (fun n => CurrentConnected G n k l)
  rw [show sourcePairDisconnSum G beta J {j, l} ∅ k m =
      gatedSourcePairSum G beta J {j, l} ∅
        (fun n => ¬ CurrentConnected G n k m) by rfl]
  rw [hsplit, ← grahamMixedDisconnection_eq_connectedRestriction G beta J hjk hjl hkl]





theorem grahamVacuumProduct_eq_mixed_add_restriction
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {j k l m : V} (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    sourcePairDisconnSum G beta J {j, l} ∅ k m *
        currentSum G beta J ∅ ^ 2 =
      sourcePairDisconnSum G beta J {j, k} {k, l} k m *
          currentSum G beta J ∅ ^ 2 +
        gatedSourcePairSum G beta J {j, l} ∅
            (fun n => ¬ CurrentConnected G n k m ∧
              ¬ CurrentConnected G n k l) *
          currentSum G beta J ∅ ^ 2 := by
  rw [grahamVacuumDisconnection_eq_mixed_add_remainder
    G beta J hjk hjl hkl]
  ring





theorem grahamMixedProduct_le_vacuumProduct
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    {j k l m : V} (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    sourcePairDisconnSum G beta J {j, k} {k, l} k m *
        currentSum G beta J ∅ ^ 2 ≤
      sourcePairDisconnSum G beta J {j, l} ∅ k m *
        currentSum G beta J ∅ ^ 2 := by
  have hrem : 0 ≤ gatedSourcePairSum G beta J {j, l} ∅
      (fun n => ¬ CurrentConnected G n k m ∧
        ¬ CurrentConnected G n k l) :=
    gatedSourcePairSum_nonneg G beta J hbeta hJ _ _ _
  rw [grahamVacuumProduct_eq_mixed_add_restriction
    G beta J hjk hjl hkl]
  exact le_add_of_nonneg_right (mul_nonneg hrem (sq_nonneg _))







theorem grahamWeightedLemmaOne_iff_remainder_absorbed
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {j k l m : V} (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    sourcePairDisconnSum G beta J {j, k} ∅ k m *
          sourcePairDisconnSum G beta J {k, l} ∅ k m <=
        sourcePairDisconnSum G beta J {j, k} {k, l} k m *
          currentSum G beta J ∅ ^ 2 ↔
      sourcePairDisconnSum G beta J {j, k} ∅ k m *
            sourcePairDisconnSum G beta J {k, l} ∅ k m +
          gatedSourcePairSum G beta J {j, l} ∅
              (fun n => ¬ CurrentConnected G n k m ∧
                ¬ CurrentConnected G n k l) *
            currentSum G beta J ∅ ^ 2 <=
        sourcePairDisconnSum G beta J {j, l} ∅ k m *
          currentSum G beta J ∅ ^ 2 := by
  rw [grahamVacuumDisconnection_eq_mixed_add_remainder
    G beta J hjk hjl hkl]
  constructor <;> intro h <;> linarith

end StatMech.FrontierA
