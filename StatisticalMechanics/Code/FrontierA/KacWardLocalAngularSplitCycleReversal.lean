/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardLocalAngularSplitSpinor
import Code.FrontierA.KacWardReversibleCycleCoefficient





namespace StatMech.FrontierA

open SimpleGraph
open scoped BigOperators


theorem kwLocalAngularSplitGraphLoop_rev_valid
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G)
    {n : Nat} [NeZero n]
    (loop : Fin n → (kwOrderedDartPortSplitGraph G
      (data.order)).Dart)
    (hvalid : kwGraphLoopNonbacktracking
      (kwOrderedDartPortSplitGraph G (data.order)) loop) :
    kwGraphLoopNonbacktracking
      (kwOrderedDartPortSplitGraph G (data.order))
      (kwGraphLoopRev loop) := by
  intro k
  let j : Fin n := -(k + 1)
  have hj : j + 1 = -k := by
    dsimp only [j]
    abel
  have hstep := hvalid j
  change (loop (-k)).symm.snd = (loop (-(k + 1))).symm.fst ∧
    (loop (-k)).symm.edge ≠ (loop (-(k + 1))).symm.edge
  rw [show -k = j + 1 from hj.symm]
  refine ⟨hstep.1.symm, ?_⟩
  simpa only [SimpleGraph.Dart.edge_symm] using hstep.2.symm


theorem kwLocalAngularSplitSpinorLoop_rev_eq_inv
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G)
    {n : Nat} [NeZero n]
    (loop : Fin n → (kwOrderedDartPortSplitGraph G
      (data.order)).Dart)
    (hvalid : kwGraphLoopNonbacktracking
      (kwOrderedDartPortSplitGraph G (data.order)) loop) :
    kwLoopPhaseProduct (kwLocalAngularSplitSpinorPhase data)
        (kwGraphLoopRev loop) =
      (kwLoopPhaseProduct (kwLocalAngularSplitSpinorPhase data) loop)⁻¹ := by
  classical
  unfold kwLoopPhaseProduct
  have hterm (k : Fin n) :
      kwLocalAngularSplitSpinorPhase data
          (kwGraphLoopRev loop k) (kwGraphLoopRev loop (k + 1)) =
        (kwLocalAngularSplitSpinorPhase data
          (loop (-(k + 1))) (loop (-k)))⁻¹ := by
    let j : Fin n := -(k + 1)
    have hj : j + 1 = -k := by
      dsimp only [j]
      abel
    have hstep := hvalid j
    rw [kwGraphLoopRev_apply, kwGraphLoopRev_apply]
    rw [show -k = j + 1 from hj.symm]
    exact kwLocalAngularSplitSpinorPhase_reverse data
      (loop j) (loop (j + 1)) hstep.1 hstep.2
  rw [Finset.prod_congr rfl (fun k _ => hterm k),
    <- Finset.prod_inv_distrib]
  let e : Fin n ≃ Fin n :=
    (Equiv.addRight (1 : Fin n)).trans (Equiv.neg (Fin n))
  let f : Fin n → Complex := fun k ↦
    (kwLocalAngularSplitSpinorPhase data
      (loop k) (loop (k + 1)))⁻¹
  calc
    (∏ k : Fin n, (kwLocalAngularSplitSpinorPhase data
        (loop (-(k + 1))) (loop (-k)))⁻¹) =
        ∏ k : Fin n, f (e k) := by
      apply Finset.prod_congr rfl
      intro k _
      have he : e k = -(k + 1) := rfl
      simp only [f, he]
      rw [show -(k + 1) + 1 = -k by abel]
    _ = ∏ k : Fin n, f k := Equiv.prod_comp e f


theorem kwLocalAngularSplitSpinorLoopScalar_loopRev
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G)
    {n : Nat} [NeZero n]
    (loop : Fin n → (kwOrderedDartPortSplitGraph G
      (data.order)).Dart)
    (hvalid : kwGraphLoopNonbacktracking
      (kwOrderedDartPortSplitGraph G (data.order)) loop) :
    kwGraphLoopScalar
        (kwOrderedDartPortSplitGraph G (data.order))
        (kwLocalAngularSplitSpinorPhase data) (kwGraphLoopRev loop) =
      kwGraphLoopScalar
        (kwOrderedDartPortSplitGraph G (data.order))
        (kwLocalAngularSplitSpinorPhase data) loop := by
  let split := kwOrderedDartPortSplitGraph G (data.order)
  have hrevValid := kwLocalAngularSplitGraphLoop_rev_valid data loop hvalid
  rw [kwGraphLoopScalar_eq_adjacency_mul_phaseProduct,
    kwGraphLoopScalar_eq_adjacency_mul_phaseProduct]
  have hadj : kwGraphLoopAdjacency split loop = 1 := by
    unfold kwGraphLoopAdjacency
    apply Finset.prod_eq_one
    intro k _
    rw [if_pos (hvalid k)]
  have hadjRev : kwGraphLoopAdjacency split (kwGraphLoopRev loop) = 1 := by
    unfold kwGraphLoopAdjacency
    apply Finset.prod_eq_one
    intro k _
    rw [if_pos (hrevValid k)]
  rw [hadj, hadjRev, one_mul, one_mul,
    kwLocalAngularSplitSpinorLoop_rev_eq_inv data loop hvalid]
  let z := kwLoopPhaseProduct (kwLocalAngularSplitSpinorPhase data) loop
  have hzsq : z ^ 2 = 1 :=
    kwLocalAngularSplitSpinorLoop_sq data loop hvalid
  have hz : z ≠ 0 := by
    intro hz
    rw [hz] at hzsq
    norm_num at hzsq
  change z⁻¹ = z
  apply (mul_left_cancel₀ hz)
  rw [mul_inv_cancel₀ hz]
  simpa only [pow_two] using hzsq.symm



theorem kwLocalAngularSplitLoopScalar_loopRev
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G)
    {n : Nat} [NeZero n]
    (loop : Fin n → (kwOrderedDartPortSplitGraph G
      (data.order)).Dart)
    (hvalid : kwGraphLoopNonbacktracking
      (kwOrderedDartPortSplitGraph G (data.order)) loop) :
    kwGraphLoopScalar
        (kwOrderedDartPortSplitGraph G (data.order))
        (kwLocalAngularSplitPhase data) (kwGraphLoopRev loop) =
      kwGraphLoopScalar
        (kwOrderedDartPortSplitGraph G (data.order))
        (kwLocalAngularSplitPhase data) loop := by
  rw [<- kwGraphLoopScalar_phaseGauge
      (kwOrderedDartPortSplitGraph G (data.order))
      (kwLocalAngularSplitPhase data)
      (kwLocalAngularSplitSpinorGauge data)
      (kwLocalAngularSplitSpinorGauge_ne_zero data) (kwGraphLoopRev loop),
    <- kwGraphLoopScalar_phaseGauge
      (kwOrderedDartPortSplitGraph G (data.order))
      (kwLocalAngularSplitPhase data)
      (kwLocalAngularSplitSpinorGauge data)
      (kwLocalAngularSplitSpinorGauge_ne_zero data) loop]
  exact kwLocalAngularSplitSpinorLoopScalar_loopRev data loop hvalid



theorem kwLocalAngularSplit_loopReversalInvariant
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) :
    KWGraphLoopReversalInvariant
      (kwOrderedDartPortSplitGraph G (data.order))
      (kwLocalAngularSplitPhase data) := by
  intro n inst loop hvalid
  exact kwLocalAngularSplitLoopScalar_loopRev data loop hvalid

end StatMech.FrontierA
