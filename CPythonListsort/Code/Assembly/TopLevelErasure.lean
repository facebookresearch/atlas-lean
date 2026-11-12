/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.FoundNewRunSafety
import Code.Assembly.MergeForceCollapseSafety
import Code.Assembly.TopLevelErasureHi

/-!
# Raw-domain erasure for the traced merge chain

These lemmas deliberately have no safety, layout, values-mode, or liveness
premises.  They only state that deleting access traces recovers the reviewed
raw evaluators, including on inputs which the evaluators reject.
-/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

private theorem topLevelErase_bind_reachable
    {α β : Type*}
    (traced : TraceResult α) (raw : Option α)
    (nextTraced : α → TraceResult β) (next : α → Option β)
    (hsource : traced.erase = raw)
    (hnext : ∀ value, raw = some value →
      (nextTraced value).erase = next value) :
    (traced.bind nextTraced).erase = raw.bind next := by
  rw [TraceResult.erase_bind, hsource]
  cases hraw : raw with
  | none => simp
  | some value => simpa [hraw] using hnext value hraw

/-- Raw-domain erasure for the recursive `merge_lo` phase driver. -/
theorem erase_mergeLoLoopTraced (fuel : Nat)
    (machine : MergeLoMachine κ ν) (phase : MergeLoPhase) :
    (mergeLoLoopTraced? fuel machine phase).erase =
      mergeLoLoop? fuel machine phase := by
  induction fuel generalizing machine phase with
  | zero => cases phase <;> rfl
  | succ fuel ih =>
      cases phase with
      | ordinary aCount bCount =>
          simp only [mergeLoLoopTraced?, mergeLoLoop?]
          split
          · rfl
          · apply topLevelErase_bind_reachable
              (TraceResult.tempPayloadRead? machine.state.a
                (Int.ofNat machine.aPos))
              (mergeLoTempRead? machine.state.a machine.aPos)
              _ _ ((TraceResult.erase_tempPayloadRead _ _).trans
                (mergeTempRead_ofNat _ _))
            intro firstA _
            apply topLevelErase_bind_reachable
              (TraceResult.sortSliceKeysRead? machine.state.data machine.bPos)
              (machine.state.data.read? machine.bPos)
              _ _ (TraceResult.erase_sortSliceKeysRead _ _)
            intro firstB _
            by_cases hcompare :
                iflt machine.state.key_compare firstB.key firstA.key = true
            · simp only [hcompare, if_true]
              apply topLevelErase_bind_reachable
                (mergeLoCopyBIncrTraced? machine)
                (mergeLoCopyBIncr? machine)
                _ _ (erase_mergeLoCopyBIncrTraced machine)
              intro nextMachine _
              by_cases hfinished : nextMachine.nb = 0
              · simp only [hfinished, if_true]
                exact erase_mergeLoSucceedTraced _
              · simp only [hfinished, if_false]
                by_cases hthreshold :
                    mergeLoCountAtLeastWord (bCount + 1)
                      nextMachine.minGallop = true
                · simp only [hthreshold, if_true]
                  exact ih _ _
                · simp only [hthreshold]
                  exact ih _ _
            · simp only [hcompare]
              apply topLevelErase_bind_reachable
                (mergeLoCopyAIncrTraced? machine)
                (mergeLoCopyAIncr? machine)
                _ _ (erase_mergeLoCopyAIncrTraced machine)
              intro nextMachine _
              by_cases hfinished : nextMachine.na = 1
              · simp only [hfinished, if_true]
                exact erase_mergeLoCopyBTraced _
              · simp only [hfinished, if_false]
                by_cases hthreshold :
                    mergeLoCountAtLeastWord (aCount + 1)
                      nextMachine.minGallop = true
                · simp only [hthreshold, if_true]
                  exact ih _ _
                · simp only [hthreshold]
                  exact ih _ _
      | galloping =>
          simp only [mergeLoLoopTraced?, mergeLoLoop?]
          apply erase_mergeLoGallopRoundTraced
          intro nextMachine aCount bCount
          split <;> exact ih _ _

/-- Unconditional raw-domain erasure for the complete traced `merge_lo`
evaluator, including rejected entry guards and allocation-guard failure. -/
theorem erase_mergeLoTraced
    (state : MergeState κ ν) (ssa ssb : Int) (na nb : Nat) :
    (mergeLoTraced? state ssa ssb na nb).erase =
      mergeLo? state ssa ssb na nb := by
  unfold mergeLoTraced? mergeLo?
  split
  · by_cases hguard :
        (mergeGetmem state (BitVec.ofNat 64 na)).outcome = .guardRejected
    · simp only [hguard, if_true]
      rfl
    · simp only [hguard, if_false]
      apply topLevelErase_bind_reachable
        (mainToTempMemcpyTraced? (.lo .initialDataToTemp)
          mergeLoInitialDataToTempPermit na
          (mergeGetmem state (BitVec.ofNat 64 na)).state 0 ssa)
        (mergeLoMemcpyDataToTemp? .initialDataToTemp rfl na
          (mergeGetmem state (BitVec.ofNat 64 na)).state 0 ssa)
        _ _ (erase_mergeLoInitialDataToTempTraced na
          (mergeGetmem state (BitVec.ofNat 64 na)).state 0 ssa)
      intro copied _
      let machine : MergeLoMachine κ ν :=
        { state := copied
          dest := ssa
          aPos := 0
          bPos := ssb
          na := na
          nb := nb
          minGallop := copied.min_gallop }
      apply topLevelErase_bind_reachable
        (mergeLoCopyBIncrTraced? machine)
        (mergeLoCopyBIncr? machine)
        _ _ (erase_mergeLoCopyBIncrTraced machine)
      intro nextMachine _
      by_cases hfinishedB : nextMachine.nb = 0
      · simp only [hfinishedB, if_true]
        exact erase_mergeLoSucceedTraced _
      · simp only [hfinishedB, if_false]
        by_cases hfinishedA : nextMachine.na = 1
        · simp only [hfinishedA, if_true]
          exact erase_mergeLoCopyBTraced _
        · simp only [hfinishedA, if_false]
          exact erase_mergeLoLoopTraced _ _ _
  · rfl

/-- Erasing the finishing stage selected by merge-at preparation recovers the
reviewed raw dispatcher for each of its three constructors. -/
theorem erase_finishMergeAtPreparationTraced
    (prepared : MergeAtPreparation κ ν) :
    (finishMergeAtPreparationTraced? prepared).erase =
      finishMergeAtPreparation? prepared := by
  cases prepared with
  | finished result => rfl
  | mergeLo call =>
      unfold finishMergeAtPreparation?
      simp only [finishMergeAtPreparationTraced?, TraceResult.erase_map,
        TraceResult.erase_recordSuccessMemoryEvent, erase_mergeLoTraced]
      cases mergeLo? call.state call.ssa call.ssb call.na call.nb <;> rfl
  | mergeHi call =>
      unfold finishMergeAtPreparation?
      simp only [finishMergeAtPreparationTraced?, TraceResult.erase_map,
        TraceResult.erase_recordSuccessMemoryEvent, erase_mergeHiTraced]
      cases mergeHi? call.state call.ssa call.ssb call.na call.nb <;> rfl

/-- Unconditional raw-domain erasure for the complete traced `merge_at`
evaluator. -/
theorem erase_mergeAtTraced (state : MergeState κ ν) (i : Nat) :
    (mergeAtTraced? state i).erase = mergeAt? state i := by
  unfold mergeAtTraced? mergeAt?
  rw [TraceResult.erase_bind, erase_prepareMergeAtTraced]
  cases hprepared : prepareMergeAt? state i with
  | none => simp
  | some prepared =>
      simp only [Option.bind_some,
        mergeAt_bindOptionAcross_some]
      exact erase_finishMergeAtPreparationTraced prepared

end CPythonListsort
