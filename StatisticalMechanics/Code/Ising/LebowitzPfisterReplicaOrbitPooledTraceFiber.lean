/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitPooledGateSplit
import Code.Ising.LebowitzPfisterReplicaOrbitBalancedSourceTrace










open Finset
open scoped symmDiff

namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy
open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaPooledTraceFiberDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _



noncomputable def lpReplicaDecoratedOrbitAtomFixedRowGateData
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hfixed : B.map lpReplicaCurrentReflect.toEmbedding = B)
    (z : LPReplicaDecoratedOrbitAtom G sites A B q) :
    {tag : Copy (lpReplicaCurrentGraph G sites) z.1.1.1 -> LPReplicaRowTag //
      LPReplicaRowGate G sites z.1.1.1 A B tag} := by
  let m := z.1.1.1
  let a := z.1.2.1.1
  let Sa := z.1.2.2.1.1
  let Sb := z.1.2.2.2.1
  let P0 := z.2.1.1
  have ha : a <= m := z.1.2.1.2
  have hSa : Sa ∈ lpReplicaDisconnProfileFamily G sites A a :=
    z.1.2.2.1.2
  have hSb : Sb ∈ lpReplicaDisconnProfileFamily G sites B
      (lpReplicaReflectedResidual G sites m a) :=
    z.1.2.2.2.2
  have hP0 : profileFlux (lpReplicaCurrentGraph G sites) m P0 = a :=
    (Finset.mem_filter.mp z.2.1.2).2
  let tag := lpReplicaOrbitCollisionSplitTag G sites m a P0 hP0 Sa Sb
  have hgate := lpReplicaRowGate_orbitCollisionSplitTag
    G sites m a ha P0 hP0 Sa Sb A B hSa hSb
  refine ⟨tag, ?_⟩
  simpa only [m, a, Sa, Sb, P0, tag, hfixed] using hgate



noncomputable def lpReplicaDecoratedOrbitAtomPooledTraceState
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hfixed : B.map lpReplicaCurrentReflect.toEmbedding = B)
    (z : LPReplicaDecoratedOrbitAtom G sites A B q) :
    LPReplicaPooledSelectedSlotState G sites q :=
  let d := lpReplicaDecoratedOrbitAtomFixedRowGateData
    G sites A B q hfixed z
  let e := endsM (lpReplicaCurrentGraph G sites) z.1.1.1
  let K := lpReplicaRowCopies G sites z.1.1.1 d.1 true
  let P := edgeComponent e K
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
  lpReplicaPooledSelectedSlotMove G sites q
    (lpReplicaPooledSelectedSlotStateOfCopies
      G sites z.1.1.1 q z.1.1.2 P z.2.2)


abbrev LPReplicaOffdiagPooledTraceIndex
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :=
  LPReplicaPooledSelectedSlotState G sites q ⊕
    LPReplicaPooledSelectedSlotState G sites q




abbrev LPReplicaOffdiagPooledIntermediateAtom
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :=
  LPReplicaDecoratedOrbitAtom G sites
      (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i) ∅ q ⊕
    LPReplicaDecoratedOrbitAtom G sites
      (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j) ∅ q


noncomputable def lpReplicaOffdiagPooledTargetLeftIntermediate
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaDecoratedOrbitAtom G sites
      (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i)
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) q) :
    LPReplicaDecoratedOrbitAtom G sites
      (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i) ∅ q := by
  classical
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  have hfixed : (Sj ∆ T).map
      lpReplicaCurrentReflect.toEmbedding = Sj ∆ T := by
    simpa only [Sj, T] using
      lpReplicaCurrentReflect_seam_symmDiff_ghost G sites j
  let d := lpReplicaDecoratedOrbitAtomFixedRowGateData
    G sites Si (Sj ∆ T) q hfixed y
  let m := y.1.1.1
  let e := endsM (lpReplicaCurrentGraph G sites) m
  let K := lpReplicaRowCopies G sites m d.1 true
  let P := edgeComponent e K
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
  let target := lpReplicaCollisionProfile G sites
    (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
    (profileFlux (lpReplicaCurrentGraph G sites) m P)
  let pooled := lpReplicaPooledSelectedSlotStateOfCopies
    G sites m q y.1.1.2 P y.2.2
  let repaired := lpReplicaPooledSelectedSlotMove G sites q pooled
  let movedTag := lpReplicaPartialReflectTagRaw G sites m P d.1
  have hs := lpReplicaRowGate_pooledTargetSplit
    G sites i j m q y.1.1.2 d.1 y.2.2 d.2
  have hs' : repaired.profile = target ∧
      ((lpReplicaPooledSelectedOrbitLabelEquivSlotState
        G sites q).symm repaired).2.2.1 =
          lpReplicaProfileOrbitLabelPartialReflectCopies
            G sites q m y.1.1.2 P y.2.2 ∧
      LPReplicaRowGate G sites target Si ∅ movedTag := by
    simpa only [e, K, P, target, pooled, repaired, movedTag, Si, Sj, T]
      using hs
  let Lrepaired := ((lpReplicaPooledSelectedOrbitLabelEquivSlotState
    G sites q).symm repaired).2.2.1
  let Ltarget : LPReplicaProfileOrbitLabel G sites q target :=
    cast (congrArg (LPReplicaProfileOrbitLabel G sites q) hs'.1) Lrepaired
  have horbit : lpReplicaSymmetrizedProfile G sites target = q := by
    exact hs'.1 ▸ repaired.orbit
  simpa only [Si] using lpReplicaDecoratedOrbitAtomOfRowGate
    G sites target q movedTag Si ∅ horbit hs'.2.2 Ltarget


noncomputable def lpReplicaOffdiagPooledTargetRightIntermediate
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaDecoratedOrbitAtom G sites
      (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j)
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) q) :
    LPReplicaDecoratedOrbitAtom G sites
      (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j) ∅ q :=
  lpReplicaOffdiagPooledTargetLeftIntermediate G sites j i q y


noncomputable def lpReplicaOffdiagPooledTargetIntermediate
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    LPReplicaOffdiagDecoratedTarget G sites i j q ->
      LPReplicaOffdiagPooledIntermediateAtom G sites i j q
  | Sum.inl y => Sum.inl
      (lpReplicaOffdiagPooledTargetLeftIntermediate G sites i j q y)
  | Sum.inr y => Sum.inr
      (lpReplicaOffdiagPooledTargetRightIntermediate G sites i j q y)


noncomputable def lpReplicaOffdiagPooledSourceIntermediate
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    LPReplicaOffdiagPooledIntermediateAtom G sites i j q := by
  classical
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  let B := Si ∆ Sj ∆ T
  have hfixed : B.map lpReplicaCurrentReflect.toEmbedding = B := by
    simpa only [B, Si, Sj, T] using
      lpReplicaCurrentReflect_offdiagSource G sites i j
  let d := lpReplicaDecoratedOrbitAtomFixedRowGateData
    G sites ∅ B q hfixed z
  let m := z.1.1.1
  let e := endsM (lpReplicaCurrentGraph G sites) m
  let K := lpReplicaRowCopies G sites m d.1 true
  let P := edgeComponent e K
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
  let target := lpReplicaCollisionProfile G sites
    (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
    (profileFlux (lpReplicaCurrentGraph G sites) m P)
  let pooled := lpReplicaPooledSelectedSlotStateOfCopies
    G sites m q z.1.1.2 P z.2.2
  let repaired := lpReplicaPooledSelectedSlotMove G sites q pooled
  let movedTag := lpReplicaPartialReflectTagRaw G sites m P d.1
  have hs := lpReplicaRowGate_pooledFirstSplit
    G sites hsite hij m q z.1.1.2 d.1 z.2.2 d.2
  have hs' : repaired.profile = target ∧
      ((lpReplicaPooledSelectedOrbitLabelEquivSlotState
        G sites q).symm repaired).2.2.1 =
          lpReplicaProfileOrbitLabelPartialReflectCopies
            G sites q m z.1.1.2 P z.2.2 ∧
      ((LPReplicaRowGate G sites target ∅ Si movedTag ∧
          B ∆ Si = Sj ∆ T) ∨
        (LPReplicaRowGate G sites target ∅ Sj movedTag ∧
          B ∆ Sj = Si ∆ T)) := by
    simpa only [e, K, P, target, pooled, repaired, movedTag,
      Si, Sj, T, B] using hs
  let Lrepaired := ((lpReplicaPooledSelectedOrbitLabelEquivSlotState
    G sites q).symm repaired).2.2.1
  let Ltarget : LPReplicaProfileOrbitLabel G sites q target :=
    cast (congrArg (LPReplicaProfileOrbitLabel G sites q) hs'.1) Lrepaired
  have horbit : lpReplicaSymmetrizedProfile G sites target = q := by
    exact hs'.1 ▸ repaired.orbit
  by_cases hi : LPReplicaRowGate G sites target ∅ Si movedTag
  · have hswap := lpReplicaRowGate_swapRows
      G sites target ∅ Si movedTag hi
    exact Sum.inl (by
      simpa only [Si] using lpReplicaDecoratedOrbitAtomOfRowGate
        G sites target q (lpReplicaSwapRowsTag movedTag)
          Si ∅ horbit hswap Ltarget)
  · have hj : LPReplicaRowGate G sites target ∅ Sj movedTag := by
      rcases hs'.2.2 with hsLeft | hsRight
      · exact False.elim (hi hsLeft.1)
      · exact hsRight.1
    have hswap := lpReplicaRowGate_swapRows
      G sites target ∅ Sj movedTag hj
    exact Sum.inr (by
      simpa only [Sj] using lpReplicaDecoratedOrbitAtomOfRowGate
        G sites target q (lpReplicaSwapRowsTag movedTag)
          Sj ∅ horbit hswap Ltarget)


noncomputable def lpReplicaOffdiagPooledSourceIntermediateFiber
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOffdiagPooledIntermediateAtom G sites i j q) :
    Finset (LPReplicaOffdiagDecoratedSource G sites i j q) := by
  classical
  exact Finset.univ.filter fun z =>
    lpReplicaOffdiagPooledSourceIntermediate
      G sites hsite hij q z = u


noncomputable def lpReplicaOffdiagPooledTargetIntermediateFiber
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOffdiagPooledIntermediateAtom G sites i j q) :
    Finset (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
  classical
  exact Finset.univ.filter fun y =>
    lpReplicaOffdiagPooledTargetIntermediate G sites i j q y = u

theorem lpReplicaOffdiagPooledSource_card_eq_sum_intermediateFibers
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) =
      ∑ u : LPReplicaOffdiagPooledIntermediateAtom G sites i j q,
        (lpReplicaOffdiagPooledSourceIntermediateFiber
          G sites hsite hij q u).card := by
  classical
  rw [← Finset.card_univ]
  simpa only [lpReplicaOffdiagPooledSourceIntermediateFiber] using
    Finset.card_eq_sum_card_fiberwise (s :=
      (Finset.univ : Finset
        (LPReplicaOffdiagDecoratedSource G sites i j q)))
      (t := (Finset.univ : Finset
        (LPReplicaOffdiagPooledIntermediateAtom G sites i j q))) (by
          intro z _
          exact Finset.mem_univ
            (lpReplicaOffdiagPooledSourceIntermediate
              G sites hsite hij q z))

theorem lpReplicaOffdiagPooledTarget_card_eq_sum_intermediateFibers
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype.card (LPReplicaOffdiagDecoratedTarget G sites i j q) =
      ∑ u : LPReplicaOffdiagPooledIntermediateAtom G sites i j q,
        (lpReplicaOffdiagPooledTargetIntermediateFiber
          G sites i j q u).card := by
  classical
  rw [← Finset.card_univ]
  simpa only [lpReplicaOffdiagPooledTargetIntermediateFiber] using
    Finset.card_eq_sum_card_fiberwise (s :=
      (Finset.univ : Finset
        (LPReplicaOffdiagDecoratedTarget G sites i j q)))
      (t := (Finset.univ : Finset
        (LPReplicaOffdiagPooledIntermediateAtom G sites i j q))) (by
          intro y _
          exact Finset.mem_univ
            (lpReplicaOffdiagPooledTargetIntermediate G sites i j q y))



theorem lpReplicaOffdiagOrbitAtomCardInequality_of_pooledIntermediateInjections
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hinj : ∀ u : LPReplicaOffdiagPooledIntermediateAtom G sites i j q,
      ∃ move :
          {z // z ∈ lpReplicaOffdiagPooledSourceIntermediateFiber
            G sites hsite hij q u} ->
          {y // y ∈ lpReplicaOffdiagPooledTargetIntermediateFiber
            G sites i j q u},
        Function.Injective move) :
    LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
  have hcard : Fintype.card
      (LPReplicaOffdiagDecoratedSource G sites i j q) <=
      Fintype.card (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
    rw [lpReplicaOffdiagPooledSource_card_eq_sum_intermediateFibers
        G sites hsite hij q,
      lpReplicaOffdiagPooledTarget_card_eq_sum_intermediateFibers]
    apply Finset.sum_le_sum
    intro u _
    obtain ⟨move, hmove⟩ := hinj u
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective move hmove
  dsimp only [LPReplicaOffdiagOrbitAtomCardInequality]
  rw [← card_lpReplicaDecoratedOrbitAtom,
    ← card_lpReplicaDecoratedOrbitAtom,
    ← card_lpReplicaDecoratedOrbitAtom]
  simpa only [LPReplicaOffdiagDecoratedSource,
    LPReplicaOffdiagDecoratedTarget, Fintype.card_sum] using hcard



noncomputable def lpReplicaOffdiagPooledSourceTraceIndex
    (G : SimpleGraph V) (sites : I -> V)
    (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    LPReplicaOffdiagPooledTraceIndex G sites q := by
  classical
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  let B := Si ∆ Sj ∆ T
  have hfixed : B.map lpReplicaCurrentReflect.toEmbedding = B := by
    simpa only [B, Si, Sj, T] using
      lpReplicaCurrentReflect_offdiagSource G sites i j
  let d := lpReplicaDecoratedOrbitAtomFixedRowGateData
    G sites ∅ B q hfixed z
  let e := endsM (lpReplicaCurrentGraph G sites) z.1.1.1
  let K := lpReplicaRowCopies G sites z.1.1.1 d.1 true
  let P := edgeComponent e K
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
  let target := lpReplicaCollisionProfile G sites
    (profileFlux (lpReplicaCurrentGraph G sites) z.1.1.1
      (Finset.univ \ P))
    (profileFlux (lpReplicaCurrentGraph G sites) z.1.1.1 P)
  let movedTag := lpReplicaPartialReflectTagRaw
    G sites z.1.1.1 P d.1
  let repaired := lpReplicaDecoratedOrbitAtomPooledTraceState
    G sites ∅ B q hfixed z
  if LPReplicaRowGate G sites target ∅ Si movedTag then
    exact Sum.inl repaired
  else
    exact Sum.inr repaired


noncomputable def lpReplicaOffdiagPooledTargetTraceIndex
    (G : SimpleGraph V) (sites : I -> V)
    (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) :
    LPReplicaOffdiagPooledTraceIndex G sites q := by
  classical
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  cases y with
  | inl y =>
      have hfixed : (Sj ∆ T).map
          lpReplicaCurrentReflect.toEmbedding = Sj ∆ T := by
        simpa only [Sj, T] using
          lpReplicaCurrentReflect_seam_symmDiff_ghost G sites j
      exact Sum.inl (lpReplicaDecoratedOrbitAtomPooledTraceState
        G sites Si (Sj ∆ T) q hfixed y)
  | inr y =>
      have hfixed : (Si ∆ T).map
          lpReplicaCurrentReflect.toEmbedding = Si ∆ T := by
        simpa only [Si, T] using
          lpReplicaCurrentReflect_seam_symmDiff_ghost G sites i
      exact Sum.inr (lpReplicaDecoratedOrbitAtomPooledTraceState
        G sites Sj (Si ∆ T) q hfixed y)


noncomputable def lpReplicaOffdiagPooledSourceTraceFiber
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOffdiagPooledTraceIndex G sites q) :
    Finset (LPReplicaOffdiagDecoratedSource G sites i j q) := by
  classical
  exact Finset.univ.filter fun z =>
    lpReplicaOffdiagPooledSourceTraceIndex G sites i j q z = u


noncomputable def lpReplicaOffdiagPooledTargetTraceFiber
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOffdiagPooledTraceIndex G sites q) :
    Finset (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
  classical
  exact Finset.univ.filter fun y =>
    lpReplicaOffdiagPooledTargetTraceIndex G sites i j q y = u

theorem lpReplicaOffdiagPooledSource_card_eq_sum_traceFibers
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) =
      ∑ u : LPReplicaOffdiagPooledTraceIndex G sites q,
        (lpReplicaOffdiagPooledSourceTraceFiber
          G sites i j q u).card := by
  classical
  rw [← Finset.card_univ]
  simpa only [lpReplicaOffdiagPooledSourceTraceFiber] using
    Finset.card_eq_sum_card_fiberwise (s :=
      (Finset.univ : Finset
        (LPReplicaOffdiagDecoratedSource G sites i j q)))
      (t := (Finset.univ : Finset
        (LPReplicaOffdiagPooledTraceIndex G sites q))) (by
          intro z _
          exact Finset.mem_univ
            (lpReplicaOffdiagPooledSourceTraceIndex G sites i j q z))

theorem lpReplicaOffdiagPooledTarget_card_eq_sum_traceFibers
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype.card (LPReplicaOffdiagDecoratedTarget G sites i j q) =
      ∑ u : LPReplicaOffdiagPooledTraceIndex G sites q,
        (lpReplicaOffdiagPooledTargetTraceFiber
          G sites i j q u).card := by
  classical
  rw [← Finset.card_univ]
  simpa only [lpReplicaOffdiagPooledTargetTraceFiber] using
    Finset.card_eq_sum_card_fiberwise (s :=
      (Finset.univ : Finset
        (LPReplicaOffdiagDecoratedTarget G sites i j q)))
      (t := (Finset.univ : Finset
        (LPReplicaOffdiagPooledTraceIndex G sites q))) (by
          intro y _
          exact Finset.mem_univ
            (lpReplicaOffdiagPooledTargetTraceIndex G sites i j q y))



theorem lpReplicaOffdiagPooledDecoratedCard_of_traceFiberCards
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : ∀ u : LPReplicaOffdiagPooledTraceIndex G sites q,
      (lpReplicaOffdiagPooledSourceTraceFiber G sites i j q u).card <=
        (lpReplicaOffdiagPooledTargetTraceFiber G sites i j q u).card) :
    Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) <=
      Fintype.card (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
  rw [lpReplicaOffdiagPooledSource_card_eq_sum_traceFibers,
    lpReplicaOffdiagPooledTarget_card_eq_sum_traceFibers]
  exact Finset.sum_le_sum fun u _ => hcard u



theorem lpReplicaOffdiagOrbitAtomCardInequality_of_pooledTraceFiberInjections
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hinj : ∀ u : LPReplicaOffdiagPooledTraceIndex G sites q,
      ∃ move :
          {z // z ∈ lpReplicaOffdiagPooledSourceTraceFiber
            G sites i j q u} ->
          {y // y ∈ lpReplicaOffdiagPooledTargetTraceFiber
            G sites i j q u},
        Function.Injective move) :
    LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
  have hcard : Fintype.card
      (LPReplicaOffdiagDecoratedSource G sites i j q) <=
      Fintype.card (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
    apply lpReplicaOffdiagPooledDecoratedCard_of_traceFiberCards
    intro u
    obtain ⟨move, hmove⟩ := hinj u
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective move hmove
  dsimp only [LPReplicaOffdiagOrbitAtomCardInequality]
  rw [← card_lpReplicaDecoratedOrbitAtom,
    ← card_lpReplicaDecoratedOrbitAtom,
    ← card_lpReplicaDecoratedOrbitAtom]
  simpa only [LPReplicaOffdiagDecoratedSource,
    LPReplicaOffdiagDecoratedTarget, Fintype.card_sum] using hcard














def LPReplicaAggregateDecoratedSource
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :=
  Sigma fun i : I => Sigma fun j : I =>
    Fin (if i = j then 0 else 1) ×
      LPReplicaOffdiagDecoratedSource G sites i j q

noncomputable instance instFintypeLPReplicaAggregateDecoratedSource
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype (LPReplicaAggregateDecoratedSource G sites q) := by
  unfold LPReplicaAggregateDecoratedSource
  infer_instance





def LPReplicaAggregateDecoratedTarget
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :=
  Fin 2 × Sigma fun i : I => Sigma fun j : I =>
    LPReplicaDecoratedOrbitAtom G sites
      (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i)
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) q

noncomputable instance instFintypeLPReplicaAggregateDecoratedTarget
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype (LPReplicaAggregateDecoratedTarget G sites q) := by
  unfold LPReplicaAggregateDecoratedTarget
  infer_instance

theorem card_lpReplicaAggregateDecoratedSource
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype.card (LPReplicaAggregateDecoratedSource G sites q) =
      ∑ i : I, ∑ j : I, if i = j then 0 else
        Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) := by
  classical
  unfold LPReplicaAggregateDecoratedSource
  change Fintype.card
      (Sigma fun i : I => Sigma fun j : I =>
        Fin (if i = j then 0 else 1) ×
          LPReplicaOffdiagDecoratedSource G sites i j q) = _
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro j _
  rw [Fintype.card_prod]
  by_cases hij : i = j <;> simp [hij]

theorem card_lpReplicaAggregateDecoratedTarget
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype.card (LPReplicaAggregateDecoratedTarget G sites q) =
      ∑ i : I, ∑ j : I, 2 * Fintype.card
        (LPReplicaDecoratedOrbitAtom G sites
          (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i)
          (lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
            lpMatchingGhostSource
              (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
              lpReplicaCurrentGhost1) q) := by
  classical
  unfold LPReplicaAggregateDecoratedTarget
  change Fintype.card
      (Fin 2 × Sigma fun i : I => Sigma fun j : I =>
        LPReplicaDecoratedOrbitAtom G sites
          (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i)
          (lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
            lpMatchingGhostSource
              (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
              lpReplicaCurrentGhost1) q) = _
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_sigma]
  simp_rw [Fintype.card_sigma]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]



def LPReplicaAggregateDecoratedInjection
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) : Prop :=
  ∃ move : LPReplicaAggregateDecoratedSource G sites q ->
      LPReplicaAggregateDecoratedTarget G sites q,
    Function.Injective move

theorem lpReplicaAggregateDecoratedCard_of_injection
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hinj : LPReplicaAggregateDecoratedInjection G sites q) :
    Fintype.card (LPReplicaAggregateDecoratedSource G sites q) <=
      Fintype.card (LPReplicaAggregateDecoratedTarget G sites q) := by
  obtain ⟨move, hmove⟩ := hinj
  exact Fintype.card_le_of_injective move hmove




theorem lpReplicaAggregateProfileOrbitInequality_of_aggregateDecoratedInjections
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (hinj : ∀ q, LPReplicaAggregateDecoratedInjection G sites q) :
    LPReplicaAggregateProfileOrbitInequality G sites beta J hf r := by
  classical
  intro q
  have hcard := lpReplicaAggregateDecoratedCard_of_injection
    G sites q (hinj q)
  rw [card_lpReplicaAggregateDecoratedSource,
    card_lpReplicaAggregateDecoratedTarget] at hcard
  have hcardReal :
      (∑ i : I, ∑ j : I, if i = j then 0 else
          (Fintype.card
            (LPReplicaOffdiagDecoratedSource G sites i j q) : Real)) <=
        ∑ i : I, ∑ j : I, 2 *
          (Fintype.card
            (LPReplicaDecoratedOrbitAtom G sites
              (lpMatchingSeamSource
                (lpReplicaCurrentLeft sites)
                (lpReplicaCurrentRight sites) i)
              (lpMatchingSeamSource
                  (lpReplicaCurrentLeft sites)
                  (lpReplicaCurrentRight sites) j ∆
                lpMatchingGhostSource
                  (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
                  lpReplicaCurrentGhost1) q) : Real) := by
    exact_mod_cast hcard
  have hbase := lpReplicaProfileOrbitBaseWeight_nonneg
    G sites beta J hf r hbeta hJ hhf hr q
  have hweighted := mul_le_mul_of_nonneg_right hcardReal hbase
  simp_rw [lpReplicaProfileOrbitMass_eq_card_atoms_mul_base,
    <- card_lpReplicaDecoratedOrbitAtom]
  simpa only [Finset.sum_mul, Finset.mul_sum, mul_assoc,
    ite_mul, zero_mul] using hweighted

end

end StatMech.Ising
