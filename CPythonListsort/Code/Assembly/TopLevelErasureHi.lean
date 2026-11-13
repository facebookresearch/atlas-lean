/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.MergeHiSafety

/-!
# Raw-domain erasure for `merge_hi`

These structural lemmas have no safety, layout, liveness, or comparator-law
premises.  They state only that deleting the genuine access trace recovers the
reviewed raw evaluator on its full modeled domain.
-/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

private theorem mergeHiErase_bind_reachable
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

/-- Raw-domain erasure for the recursive `merge_hi` phase driver. -/
theorem erase_mergeHiLoopTraced (fuel : Nat) (cursor : MergeHiCursor κ ν) :
    (mergeHiLoopTraced? fuel cursor).erase = mergeHiLoop? fuel cursor := by
  induction fuel generalizing cursor with
  | zero =>
      simp only [mergeHiLoopTraced?, mergeHiLoop?]
      by_cases hTerminal : cursor.na = 0 ∨ cursor.nb = 0
      · rw [if_pos hTerminal, if_pos hTerminal, erase_mergeHiSucceedTraced]
      · rw [if_neg hTerminal, if_neg hTerminal]
        by_cases hCopyA : cursor.nb = 1
        · rw [if_pos hCopyA, if_pos hCopyA, erase_mergeHiCopyATraced]
        · rw [if_neg hCopyA, if_neg hCopyA,
            erase_mergeHiFuelExhaustedTraced]
  | succ fuel ih =>
      simp only [mergeHiLoopTraced?, mergeHiLoop?]
      by_cases hTerminal : cursor.na = 0 ∨ cursor.nb = 0
      · rw [if_pos hTerminal, if_pos hTerminal, erase_mergeHiSucceedTraced]
      · rw [if_neg hTerminal, if_neg hTerminal]
        by_cases hCopyA : cursor.nb = 1
        · rw [if_pos hCopyA, if_pos hCopyA, erase_mergeHiCopyATraced]
        · rw [if_neg hCopyA, if_neg hCopyA]
          cases hPhase : cursor.phase with
          | straight aCount bCount =>
              apply mergeHiErase_bind_reachable
                (TraceResult.tempPayloadRead? cursor.state.a cursor.ssb)
                (mergeHiTempRead? cursor.state.a cursor.ssb) _ _
                ((TraceResult.erase_tempPayloadRead _ _).trans
                  (mergeTempRead_eq_mergeHiTempRead _ _))
              intro right _
              apply mergeHiErase_bind_reachable
                (TraceResult.sortSliceKeysRead? cursor.state.data cursor.ssa)
                (cursor.state.data.read? cursor.ssa) _ _
                (TraceResult.erase_sortSliceKeysRead _ _)
              intro left _
              by_cases hCompare :
                  iflt cursor.state.key_compare right.key left.key = true
              · simp only [hCompare, if_true]
                apply mergeHiErase_bind_reachable
                  (mergeHiCopyDataDecrTraced? cursor.state cursor.dest
                    cursor.ssa)
                  (mergeHiCopyDataDecr? cursor.state cursor.dest cursor.ssa)
                  _ _ (erase_mergeHiCopyDataDecrTraced _ _ _)
                intro copied _
                exact ih _
              · simp only [hCompare]
                apply mergeHiErase_bind_reachable
                  (mergeHiCopyTempDecrTraced? cursor.state cursor.dest
                    cursor.ssb)
                  (mergeHiCopyTempDecr? cursor.state cursor.dest cursor.ssb)
                  _ _ (erase_mergeHiCopyTempDecrTraced _ _ _)
                intro copied _
                exact ih _
          | galloping aCount bCount =>
              exact erase_mergeHiGallopRoundTraced cursor
                (mergeHiLoopTraced? fuel) (mergeHiLoop? fuel) ih

private def mergeHiTracedAllocatedTail? (state : MergeState κ ν)
    (ssa ssb : Int) (na nb : Nat) : TraceResult (MergeHiResult κ ν) :=
  (mainToTempMemcpyTraced? (.hi .initialDataToTemp)
    mergeHiInitialDataToTempPermit nb state 0 ssb).bind fun state =>
      let dest := ssb + Int.ofNat (nb - 1)
      let ssaCursor := ssa + Int.ofNat (na - 1)
      (mergeHiCopyDataDecrTraced? state dest ssaCursor).bind fun copied =>
        let cursor : MergeHiCursor κ ν :=
          { state := copied.state
            dest := copied.dst
            ssa := copied.src
            ssb := Int.ofNat (nb - 1)
            basea := ssa
            na := na - 1
            nb := nb
            minGallop := copied.state.min_gallop
            phase := .straight 0 0 }
        mergeHiLoopTraced? (na + nb) cursor

private def mergeHiAllocatedTail? (state : MergeState κ ν)
    (ssa ssb : Int) (na nb : Nat) : Option (MergeHiResult κ ν) := do
  let state ← mergeHiMemcpyDataToTemp? .initialDataToTemp rfl nb state 0 ssb
  let dest := ssb + Int.ofNat (nb - 1)
  let ssaCursor := ssa + Int.ofNat (na - 1)
  let copied ← mergeHiCopyDataDecr? state dest ssaCursor
  let cursor : MergeHiCursor κ ν :=
    { state := copied.state
      dest := copied.dst
      ssa := copied.src
      ssb := Int.ofNat (nb - 1)
      basea := ssa
      na := na - 1
      nb := nb
      minGallop := copied.state.min_gallop
      phase := .straight 0 0 }
  mergeHiLoop? (na + nb) cursor

private theorem erase_mergeHiTracedAllocatedTail (state : MergeState κ ν)
    (ssa ssb : Int) (na nb : Nat) :
    (mergeHiTracedAllocatedTail? state ssa ssb na nb).erase =
      mergeHiAllocatedTail? state ssa ssb na nb := by
  unfold mergeHiTracedAllocatedTail? mergeHiAllocatedTail?
  apply mergeHiErase_bind_reachable
    (mainToTempMemcpyTraced? (.hi .initialDataToTemp)
      mergeHiInitialDataToTempPermit nb state 0 ssb)
    (mergeHiMemcpyDataToTemp? .initialDataToTemp rfl nb state 0 ssb)
    _ _
  · exact (erase_mainToTempMemcpyTraced _ _ _ _ _ _).trans
      (mainToTempMemcpy_eq_mergeHiMemcpyDataToTemp _ _ _ _ _ _)
  · intro copiedTemp _
    apply mergeHiErase_bind_reachable
      (mergeHiCopyDataDecrTraced? copiedTemp
        (ssb + Int.ofNat (nb - 1)) (ssa + Int.ofNat (na - 1)))
      (mergeHiCopyDataDecr? copiedTemp
        (ssb + Int.ofNat (nb - 1)) (ssa + Int.ofNat (na - 1)))
      _ _ (erase_mergeHiCopyDataDecrTraced _ _ _)
    intro copied _
    exact erase_mergeHiLoopTraced (na + nb) _

/-- Full-domain erasure for the public traced `merge_hi` evaluator. -/
theorem erase_mergeHiTraced (state : MergeState κ ν) (ssa ssb : Int)
    (na nb : Nat) :
    (mergeHiTraced? state ssa ssb na nb).erase =
      mergeHi? state ssa ssb na nb := by
  by_cases hInput :
      0 < na ∧ 0 < nb ∧ na ≤ PY_SSIZE_T_MAX ∧ nb ≤ PY_SSIZE_T_MAX ∧
        ssa + Int.ofNat na = ssb
  · let allocated := mergeGetmem state (BitVec.ofNat 64 nb)
    have htraced :
        mergeHiTraced? state ssa ssb na nb =
          match allocated.outcome with
          | .guardRejected =>
              TraceResult.pure
                { state := allocated.state
                  returnCode := -1
                  fuelExhausted := false }
          | .reused | .grown =>
              mergeHiTracedAllocatedTail? allocated.state ssa ssb na nb := by
      rw [mergeHiTraced?, if_pos hInput]
      rfl
    have hraw :
        mergeHi? state ssa ssb na nb =
          match allocated.outcome with
          | .guardRejected =>
              some
                { state := allocated.state
                  returnCode := -1
                  fuelExhausted := false }
          | .reused | .grown =>
              mergeHiAllocatedTail? allocated.state ssa ssb na nb := by
      rw [mergeHi?, if_pos hInput]
      rfl
    rw [htraced, hraw]
    cases allocated.outcome with
    | guardRejected => rfl
    | reused => exact erase_mergeHiTracedAllocatedTail _ _ _ _ _
    | grown => exact erase_mergeHiTracedAllocatedTail _ _ _ _ _
  · rw [mergeHiTraced?, mergeHi?, if_neg hInput, if_neg hInput]
    rfl

end CPythonListsort
