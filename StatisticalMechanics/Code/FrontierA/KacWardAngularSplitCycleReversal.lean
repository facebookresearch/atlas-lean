/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardAngularSplitSpinor
import Code.FrontierA.KacWardReversibleCycleCoefficient











namespace StatMech.FrontierA

open SimpleGraph
open scoped BigOperators


theorem kwAngularSplitGraphLoop_rev_valid
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    {n : Nat} [NeZero n]
    (loop : Fin n → (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Dart)
    (hvalid : kwGraphLoopNonbacktracking
      (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)) loop) :
    kwGraphLoopNonbacktracking
      (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
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


theorem kwAngularSplitSpinorLoop_rev_eq_inv
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    {n : Nat} [NeZero n]
    (loop : Fin n → (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Dart)
    (hvalid : kwGraphLoopNonbacktracking
      (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)) loop) :
    kwLoopPhaseProduct (kwAngularSplitSpinorPhase embedding)
        (kwGraphLoopRev loop) =
      (kwLoopPhaseProduct (kwAngularSplitSpinorPhase embedding) loop)⁻¹ := by
  classical
  unfold kwLoopPhaseProduct
  have hterm (k : Fin n) :
      kwAngularSplitSpinorPhase embedding
          (kwGraphLoopRev loop k) (kwGraphLoopRev loop (k + 1)) =
        (kwAngularSplitSpinorPhase embedding
          (loop (-(k + 1))) (loop (-k)))⁻¹ := by
    let j : Fin n := -(k + 1)
    have hj : j + 1 = -k := by
      dsimp only [j]
      abel
    have hstep := hvalid j
    rw [kwGraphLoopRev_apply, kwGraphLoopRev_apply]
    rw [show -k = j + 1 from hj.symm]
    exact kwAngularSplitSpinorPhase_reverse embedding
      (loop j) (loop (j + 1)) hstep.1 hstep.2
  rw [Finset.prod_congr rfl (fun k _ => hterm k),
    <- Finset.prod_inv_distrib]
  let e : Fin n ≃ Fin n :=
    (Equiv.addRight (1 : Fin n)).trans (Equiv.neg (Fin n))
  let f : Fin n → Complex := fun k ↦
    (kwAngularSplitSpinorPhase embedding
      (loop k) (loop (k + 1)))⁻¹
  calc
    (∏ k : Fin n, (kwAngularSplitSpinorPhase embedding
        (loop (-(k + 1))) (loop (-k)))⁻¹) =
        ∏ k : Fin n, f (e k) := by
      apply Finset.prod_congr rfl
      intro k _
      have he : e k = -(k + 1) := rfl
      simp only [f, he]
      rw [show -(k + 1) + 1 = -k by abel]
    _ = ∏ k : Fin n, f k := Equiv.prod_comp e f


theorem kwAngularSplitSpinorLoopScalar_loopRev
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    {n : Nat} [NeZero n]
    (loop : Fin n → (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Dart)
    (hvalid : kwGraphLoopNonbacktracking
      (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)) loop) :
    kwGraphLoopScalar
        (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
        (kwAngularSplitSpinorPhase embedding) (kwGraphLoopRev loop) =
      kwGraphLoopScalar
        (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
        (kwAngularSplitSpinorPhase embedding) loop := by
  let split := kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)
  have hrevValid := kwAngularSplitGraphLoop_rev_valid embedding loop hvalid
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
    kwAngularSplitSpinorLoop_rev_eq_inv embedding loop hvalid]
  let z := kwLoopPhaseProduct (kwAngularSplitSpinorPhase embedding) loop
  have hzsq : z ^ 2 = 1 :=
    kwAngularSplitSpinorLoop_sq embedding loop hvalid
  have hz : z ≠ 0 := by
    intro hz
    rw [hz] at hzsq
    norm_num at hzsq
  change z⁻¹ = z
  apply (mul_left_cancel₀ hz)
  rw [mul_inv_cancel₀ hz]
  simpa only [pow_two] using hzsq.symm



theorem kwAngularSplitLoopScalar_loopRev
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    {n : Nat} [NeZero n]
    (loop : Fin n → (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Dart)
    (hvalid : kwGraphLoopNonbacktracking
      (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)) loop) :
    kwGraphLoopScalar
        (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
        (kwAngularSplitPhase embedding) (kwGraphLoopRev loop) =
      kwGraphLoopScalar
        (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
        (kwAngularSplitPhase embedding) loop := by
  rw [<- kwGraphLoopScalar_phaseGauge
      (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
      (kwAngularSplitPhase embedding)
      (kwAngularSplitSpinorGauge embedding)
      (kwAngularSplitSpinorGauge_ne_zero embedding) (kwGraphLoopRev loop),
    <- kwGraphLoopScalar_phaseGauge
      (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
      (kwAngularSplitPhase embedding)
      (kwAngularSplitSpinorGauge embedding)
      (kwAngularSplitSpinorGauge_ne_zero embedding) loop]
  exact kwAngularSplitSpinorLoopScalar_loopRev embedding loop hvalid



theorem kwAngularSplit_loopReversalInvariant
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) :
    KWGraphLoopReversalInvariant
      (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
      (kwAngularSplitPhase embedding) := by
  intro n inst loop hvalid
  exact kwAngularSplitLoopScalar_loopRev embedding loop hvalid

end StatMech.FrontierA
