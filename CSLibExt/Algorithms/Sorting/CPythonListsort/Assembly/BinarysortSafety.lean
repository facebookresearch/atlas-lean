/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.SortSliceSafety
import Code.Transcription.Binarysort
import Mathlib

/-!
# `binarysort` safety

This module instruments CPython's stable binary insertion sort directly from
the traced `SortSlice` primitives.  The trace follows the source phases: read
the key pivot, probe binary-search midpoints, shift keys from right to left,
write the key pivot, and then (when values storage is present) read, shift, and
write the synchronized payloads.  Explicit fuel exhaustion remains observable
but is proved unreachable on source-admitted calls.

Version-one delta: the pinned C `IFLT` can jump to `fail` when comparison
raises, while this snapshot model's `BoolComparator` is pure and total.  The
traced evaluator therefore has no comparator-failure result or comparator
event; exact erasure below is to the reviewed Lean transcription on that
explicitly narrower comparator model.
-/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- Traced binary-search phase.  A zero-fuel active interval marks exhaustion;
otherwise each iteration records exactly its midpoint key read before taking
the comparator-selected recursive branch. -/
def binarysortSearchTraced? :
    Nat → BoolComparator κ → SortSlice κ ν → Int → SortSliceEntry κ ν →
      Nat → Nat → TraceResult BinarySearchResult
  | 0, _, _, _, _, left, right =>
      let result : BinarySearchResult :=
        { position := left, fuelExhausted := decide (left < right) }
      if left < right then
        (TraceResult.pure result).markFuelExhausted
      else
        TraceResult.pure result
  | fuel + 1, lt, slice, base, pivot, left, right =>
      if left < right then
        let middle := (left + right) / 2
        (TraceResult.sortSliceKeysRead? slice
          (base + Int.ofNat middle)).bind fun entry =>
            if iflt lt pivot.key entry.key then
              binarysortSearchTraced? fuel lt slice base pivot left middle
            else
              binarysortSearchTraced? fuel lt slice base pivot (middle + 1) right
      else
        TraceResult.pure { position := left, fuelExhausted := false }

/-- Key shift and pivot insertion, followed by the synchronized-values phase
when the explicit C pointer mode says that phase exists.  Each physical phase
starts from the same paired-store snapshot because either phase's primitive
erases to the transcription's single atomic paired movement. -/
def binarysortShiftInsertTraced? (valuesPresent : Bool)
    (slice : SortSlice κ ν) (base : Int) (ok position : Nat)
    (pivot : SortSliceEntry κ ν) : TraceResult (SortSlice κ ν) :=
  let count := ok - position
  let dst := base + Int.ofNat (position + 1)
  let src := base + Int.ofNat position
  let pivotIndex := base + Int.ofNat ok
  let insertIndex := base + Int.ofNat position
  (SortSlice.memmoveBackwardKeysTraced? count slice dst src).bind fun keyShifted =>
    (TraceResult.sortSliceKeysWrite? keyShifted insertIndex pivot).bind fun keyResult =>
      if valuesPresent then
        (TraceResult.sortSliceValuesRead? slice pivotIndex).bind fun valuePivot =>
          (SortSlice.memmoveBackwardValuesTraced? count slice dst src).bind
            fun valueShifted =>
              TraceResult.sortSliceValuesWrite? valueShifted insertIndex valuePivot
      else
        TraceResult.pure keyResult

/-- Traced outer insertion loop. -/
def binarysortLoopTraced? :
    Nat → MergeState κ ν → SortSlice κ ν → Int → Nat → Nat →
      TraceResult (BinarysortResult κ ν)
  | 0, _, slice, _, n, ok =>
      let result : BinarysortResult κ ν :=
        { slice := slice, fuelExhausted := decide (ok < n) }
      if ok < n then
        (TraceResult.pure result).markFuelExhausted
      else
        TraceResult.pure result
  | fuel + 1, state, slice, base, n, ok =>
      if ok < n then
        (TraceResult.sortSliceKeysRead? slice
          (base + Int.ofNat ok)).bind fun pivot =>
            (binarysortSearchTraced? (ok + 1) state.key_compare slice base pivot
              0 ok).bind fun search =>
                if search.fuelExhausted then
                  TraceResult.pure { slice := slice, fuelExhausted := true }
                else
                  (binarysortShiftInsertTraced? state.a.hasValues slice base ok
                    search.position pivot).bind fun updated =>
                      binarysortLoopTraced? fuel state updated base n (ok + 1)
      else
        TraceResult.pure { slice := slice, fuelExhausted := false }

/-- Fully traced binary insertion sort, with the same assertion-domain guard
and `ok = 0` normalization as the reviewed transcription. -/
def binarysortTraced? (state : MergeState κ ν) (slice : SortSlice κ ν)
    (base : Int) (n ok : Nat) : TraceResult (BinarysortResult κ ν) :=
  if 1 ≤ n ∧ ok ≤ n ∧ n ≤ MAX_MINRUN.toNat then
    let ok := if ok = 0 then 1 else ok
    binarysortLoopTraced? n state slice base n ok
  else
    TraceResult.failure

/-! ## Merge-memory event freedom -/

private theorem binarysortSearchTraced_memoryEvents_eq_nil
    (fuel : Nat) (lt : BoolComparator κ) (slice : SortSlice κ ν)
    (base : Int) (pivot : SortSliceEntry κ ν) (left right : Nat) :
    (binarysortSearchTraced? fuel lt slice base pivot left
      right).trace.memoryEvents = [] := by
  induction fuel generalizing left right with
  | zero =>
      by_cases hactive : left < right
      · simp [binarysortSearchTraced?, hactive,
          TraceResult.markFuelExhausted, TraceResult.pure,
          AccessTrace.empty, AccessTrace.compose, AccessTrace.exhausted]
      · simp [binarysortSearchTraced?, hactive, TraceResult.pure,
          AccessTrace.empty]
  | succ fuel ih =>
      rw [binarysortSearchTraced?]
      by_cases hactive : left < right
      · rw [if_pos hactive]
        apply TraceResult.memoryEvents_bind_eq_nil
        · rfl
        · intro entry
          by_cases hcomparison : iflt lt pivot.key entry.key = true
          · rw [if_pos hcomparison]
            exact ih left ((left + right) / 2)
          · rw [if_neg hcomparison]
            exact ih (((left + right) / 2) + 1) right
      · rw [if_neg hactive]
        rfl

private theorem copyKeysFromTraced_memoryEvents_eq_nil
    (destination source : SortSlice κ ν) (dst src : Int) :
    (SortSlice.copyKeysFromTraced? destination source dst
      src).trace.memoryEvents = [] := by
  unfold SortSlice.copyKeysFromTraced?
  apply TraceResult.memoryEvents_bind_eq_nil
  · rfl
  · intro entry
    rfl

private theorem copyValuesFromTraced_memoryEvents_eq_nil
    (destination source : SortSlice κ ν) (dst src : Int) :
    (SortSlice.copyValuesFromTraced? destination source dst
      src).trace.memoryEvents = [] := by
  unfold SortSlice.copyValuesFromTraced?
  apply TraceResult.memoryEvents_bind_eq_nil
  · rfl
  · intro entry
    rfl

private theorem memmoveBackwardKeysTraced_memoryEvents_eq_nil
    (count : Nat) (slice : SortSlice κ ν) (dst src : Int) :
    (SortSlice.memmoveBackwardKeysTraced? count slice dst
      src).trace.memoryEvents = [] := by
  induction count generalizing slice with
  | zero => rfl
  | succ count ih =>
      rw [SortSlice.memmoveBackwardKeysTraced?]
      apply TraceResult.memoryEvents_bind_eq_nil
      · exact copyKeysFromTraced_memoryEvents_eq_nil _ _ _ _
      · intro updated
        exact ih updated

private theorem memmoveBackwardValuesTraced_memoryEvents_eq_nil
    (count : Nat) (slice : SortSlice κ ν) (dst src : Int) :
    (SortSlice.memmoveBackwardValuesTraced? count slice dst
      src).trace.memoryEvents = [] := by
  induction count generalizing slice with
  | zero => rfl
  | succ count ih =>
      rw [SortSlice.memmoveBackwardValuesTraced?]
      apply TraceResult.memoryEvents_bind_eq_nil
      · exact copyValuesFromTraced_memoryEvents_eq_nil _ _ _ _
      · intro updated
        exact ih updated

private theorem binarysortShiftInsertTraced_memoryEvents_eq_nil
    (valuesPresent : Bool) (slice : SortSlice κ ν) (base : Int)
    (ok position : Nat) (pivot : SortSliceEntry κ ν) :
    (binarysortShiftInsertTraced? valuesPresent slice base ok position
      pivot).trace.memoryEvents = [] := by
  unfold binarysortShiftInsertTraced?
  apply TraceResult.memoryEvents_bind_eq_nil
  · exact memmoveBackwardKeysTraced_memoryEvents_eq_nil _ _ _ _
  · intro keyShifted
    apply TraceResult.memoryEvents_bind_eq_nil
    · rfl
    · intro keyResult
      cases valuesPresent
      · rfl
      · apply TraceResult.memoryEvents_bind_eq_nil
        · rfl
        · intro valuePivot
          apply TraceResult.memoryEvents_bind_eq_nil
          · exact memmoveBackwardValuesTraced_memoryEvents_eq_nil _ _ _ _
          · intro valueShifted
            rfl

private theorem binarysortLoopTraced_memoryEvents_eq_nil
    (fuel : Nat) (state : MergeState κ ν) (slice : SortSlice κ ν)
    (base : Int) (n ok : Nat) :
    (binarysortLoopTraced? fuel state slice base n ok).trace.memoryEvents =
      [] := by
  induction fuel generalizing slice ok with
  | zero =>
      by_cases hactive : ok < n
      · simp [binarysortLoopTraced?, hactive, TraceResult.markFuelExhausted,
          TraceResult.pure, AccessTrace.empty, AccessTrace.compose,
          AccessTrace.exhausted]
      · simp [binarysortLoopTraced?, hactive, TraceResult.pure,
          AccessTrace.empty]
  | succ fuel ih =>
      rw [binarysortLoopTraced?]
      by_cases hactive : ok < n
      · rw [if_pos hactive]
        apply TraceResult.memoryEvents_bind_eq_nil
        · rfl
        · intro pivot
          apply TraceResult.memoryEvents_bind_eq_nil
          · exact binarysortSearchTraced_memoryEvents_eq_nil _ _ _ _ _ _ _
          · intro search
            by_cases hexhausted : search.fuelExhausted = true
            · rw [if_pos hexhausted]
              rfl
            · rw [if_neg hexhausted]
              apply TraceResult.memoryEvents_bind_eq_nil
              · exact binarysortShiftInsertTraced_memoryEvents_eq_nil _ _ _ _ _ _
              · intro updated
                exact ih updated (ok + 1)
      · rw [if_neg hactive]
        rfl

/-- The complete `binarysort` wrapper cannot emit a merge-memory boundary on
any admitted, rejected, comparator-selected, or fuel-exhaustion path. -/
theorem binarysortTraced_memoryEvents_eq_nil
    (state : MergeState κ ν) (slice : SortSlice κ ν) (base : Int)
    (n ok : Nat) :
    (binarysortTraced? state slice base n ok).trace.memoryEvents = [] := by
  unfold binarysortTraced?
  by_cases hadmitted : 1 ≤ n ∧ ok ≤ n ∧ n ≤ MAX_MINRUN.toNat
  · rw [if_pos hadmitted]
    exact binarysortLoopTraced_memoryEvents_eq_nil _ _ _ _ _ _
  · rw [if_neg hadmitted]
    rfl

/-! ## Logical-policy event freedom -/

private theorem binarysortSearchTraced_policyEvents_eq_nil
    (fuel : Nat) (lt : BoolComparator κ) (slice : SortSlice κ ν)
    (base : Int) (pivot : SortSliceEntry κ ν) (left right : Nat) :
    (binarysortSearchTraced? fuel lt slice base pivot left
      right).trace.policyEvents = [] := by
  induction fuel generalizing left right with
  | zero =>
      by_cases hactive : left < right
      · simp [binarysortSearchTraced?, hactive,
          TraceResult.markFuelExhausted, TraceResult.pure,
          AccessTrace.empty, AccessTrace.compose, AccessTrace.exhausted]
      · simp [binarysortSearchTraced?, hactive, TraceResult.pure,
          AccessTrace.empty]
  | succ fuel ih =>
      rw [binarysortSearchTraced?]
      by_cases hactive : left < right
      · rw [if_pos hactive]
        apply TraceResult.policyEvents_bind_eq_nil
        · rfl
        · intro entry
          by_cases hcomparison : iflt lt pivot.key entry.key = true
          · rw [if_pos hcomparison]
            exact ih left ((left + right) / 2)
          · rw [if_neg hcomparison]
            exact ih (((left + right) / 2) + 1) right
      · rw [if_neg hactive]
        rfl

private theorem memmoveBackwardKeysTraced_policyEvents_eq_nil
    (count : Nat) (slice : SortSlice κ ν) (dst src : Int) :
    (SortSlice.memmoveBackwardKeysTraced? count slice dst
      src).trace.policyEvents = [] := by
  induction count generalizing slice with
  | zero => rfl
  | succ count ih =>
      rw [SortSlice.memmoveBackwardKeysTraced?]
      apply TraceResult.policyEvents_bind_eq_nil
      · unfold SortSlice.copyKeysFromTraced?
        apply TraceResult.policyEvents_bind_eq_nil <;> intros <;> rfl
      · intro updated
        exact ih updated

private theorem memmoveBackwardValuesTraced_policyEvents_eq_nil
    (count : Nat) (slice : SortSlice κ ν) (dst src : Int) :
    (SortSlice.memmoveBackwardValuesTraced? count slice dst
      src).trace.policyEvents = [] := by
  induction count generalizing slice with
  | zero => rfl
  | succ count ih =>
      rw [SortSlice.memmoveBackwardValuesTraced?]
      apply TraceResult.policyEvents_bind_eq_nil
      · unfold SortSlice.copyValuesFromTraced?
        apply TraceResult.policyEvents_bind_eq_nil <;> intros <;> rfl
      · intro updated
        exact ih updated

private theorem binarysortShiftInsertTraced_policyEvents_eq_nil
    (valuesPresent : Bool) (slice : SortSlice κ ν) (base : Int)
    (ok position : Nat) (pivot : SortSliceEntry κ ν) :
    (binarysortShiftInsertTraced? valuesPresent slice base ok position
      pivot).trace.policyEvents = [] := by
  unfold binarysortShiftInsertTraced?
  apply TraceResult.policyEvents_bind_eq_nil
  · exact memmoveBackwardKeysTraced_policyEvents_eq_nil _ _ _ _
  · intro keyShifted
    apply TraceResult.policyEvents_bind_eq_nil
    · rfl
    · intro keyResult
      cases valuesPresent
      · rfl
      · apply TraceResult.policyEvents_bind_eq_nil
        · rfl
        · intro valuePivot
          apply TraceResult.policyEvents_bind_eq_nil
          · exact memmoveBackwardValuesTraced_policyEvents_eq_nil _ _ _ _
          · intro valueShifted
            rfl

private theorem binarysortLoopTraced_policyEvents_eq_nil
    (fuel : Nat) (state : MergeState κ ν) (slice : SortSlice κ ν)
    (base : Int) (n ok : Nat) :
    (binarysortLoopTraced? fuel state slice base n ok).trace.policyEvents =
      [] := by
  induction fuel generalizing slice ok with
  | zero =>
      by_cases hactive : ok < n
      · simp [binarysortLoopTraced?, hactive, TraceResult.markFuelExhausted,
          TraceResult.pure, AccessTrace.empty, AccessTrace.compose,
          AccessTrace.exhausted]
      · simp [binarysortLoopTraced?, hactive, TraceResult.pure,
          AccessTrace.empty]
  | succ fuel ih =>
      rw [binarysortLoopTraced?]
      by_cases hactive : ok < n
      · rw [if_pos hactive]
        apply TraceResult.policyEvents_bind_eq_nil
        · rfl
        · intro pivot
          apply TraceResult.policyEvents_bind_eq_nil
          · exact binarysortSearchTraced_policyEvents_eq_nil _ _ _ _ _ _ _
          · intro search
            by_cases hexhausted : search.fuelExhausted = true
            · rw [if_pos hexhausted]
              rfl
            · rw [if_neg hexhausted]
              apply TraceResult.policyEvents_bind_eq_nil
              · exact binarysortShiftInsertTraced_policyEvents_eq_nil _ _ _ _ _ _
              · intro updated
                exact ih updated (ok + 1)
      · rw [if_neg hactive]
        rfl

/-- The complete binary-insertion helper cannot emit a formed-run or
logical-merge event on any admitted or rejected branch. -/
theorem binarysortTraced_policyEvents_eq_nil
    (state : MergeState κ ν) (slice : SortSlice κ ν) (base : Int)
    (n ok : Nat) :
    (binarysortTraced? state slice base n ok).trace.policyEvents = [] := by
  unfold binarysortTraced?
  by_cases hadmitted : 1 ≤ n ∧ ok ≤ n ∧ n ≤ MAX_MINRUN.toNat
  · rw [if_pos hadmitted]
    exact binarysortLoopTraced_policyEvents_eq_nil _ _ _ _ _ _
  · rw [if_neg hadmitted]
    rfl

/-! ## Exact erasure -/

@[simp]
theorem erase_binarysortSearchTraced (fuel : Nat) (lt : BoolComparator κ)
    (slice : SortSlice κ ν) (base : Int) (pivot : SortSliceEntry κ ν)
    (left right : Nat) :
    (binarysortSearchTraced? fuel lt slice base pivot left right).erase =
      binarysortSearch? fuel lt slice base pivot left right := by
  induction fuel generalizing left right with
  | zero =>
      by_cases hactive : left < right <;>
        simp [binarysortSearchTraced?, binarysortSearch?, hactive]
  | succ fuel ih =>
      by_cases hactive : left < right
      · let middle := (left + right) / 2
        simp only [binarysortSearchTraced?, binarysortSearch?, hactive, if_true,
          TraceResult.erase_bind, TraceResult.erase_sortSliceKeysRead]
        cases hread : slice.read? (base + Int.ofNat middle) with
        | none => simp [binarysortBindOptionAcross]
        | some entry =>
            by_cases hlt : lt pivot.key entry.key = true <;>
              simp [binarysortBindOptionAcross, iflt, hlt, ih]
      · simp [binarysortSearchTraced?, binarysortSearch?, hactive]

private theorem memmove_backward_eq (slice : SortSlice κ ν) (base : Int)
    (position count : Nat) :
    slice.memmove? (base + Int.ofNat (position + 1))
        (base + Int.ofNat position) count =
      SortSlice.memmoveBackward? count slice
        (base + Int.ofNat (position + 1)) (base + Int.ofNat position) := by
  simp [SortSlice.memmove?, SortSlice.memmoveDirection]

/-- Erasing the source-ordered physical phases recovers the transcription's
single paired-store move and pivot write whenever the pivot was read from the
same source cell. -/
theorem erase_binarysortShiftInsertTraced_of_pivot
    (valuesPresent : Bool) (slice : SortSlice κ ν) (base : Int)
    (ok position : Nat) (pivot : SortSliceEntry κ ν)
    (hpivot : slice.read? (base + Int.ofNat ok) = some pivot) :
    (binarysortShiftInsertTraced? valuesPresent slice base ok position
        pivot).erase =
      (do
        let shifted ← slice.memmove?
          (base + Int.ofNat (position + 1))
          (base + Int.ofNat position) (ok - position)
        shifted.write? (base + Int.ofNat position) pivot) := by
  unfold binarysortShiftInsertTraced?
  simp only [TraceResult.erase_bind,
    SortSlice.erase_memmoveBackwardKeysTraced,
    TraceResult.erase_sortSliceKeysWrite]
  rw [memmove_backward_eq]
  cases hshift : SortSlice.memmoveBackward? (ok - position) slice
      (base + Int.ofNat (position + 1)) (base + Int.ofNat position) with
  | none => simp
  | some shifted =>
      have hshift' :
          SortSlice.memmoveBackward? (ok - position) slice
              (base + (position : Int) + 1) (base + (position : Int)) =
            some shifted := by
        simpa [Int.ofNat_eq_natCast, add_assoc] using hshift
      have hshift'' :
          SortSlice.memmoveBackward? (ok - position) slice
              (base + ((position : Int) + 1)) (base + (position : Int)) =
            some shifted := by
        simpa [add_assoc] using hshift'
      cases hwrite : shifted.write? (base + Int.ofNat position) pivot with
      | none =>
          have hwrite' : shifted.write? (base + (position : Int)) pivot = none := by
            simpa [Int.ofNat_eq_natCast] using hwrite
          simp [hwrite']
      | some inserted =>
          have hwrite' :
              shifted.write? (base + (position : Int)) pivot = some inserted := by
            simpa [Int.ofNat_eq_natCast] using hwrite
          cases valuesPresent
          · simp [hwrite']
          · have hpivot' :
                slice.read? (base + (ok : Int)) = some pivot := by
              simpa [Int.ofNat_eq_natCast] using hpivot
            simp [hpivot', hshift'', hwrite']

@[simp]
theorem erase_binarysortLoopTraced (fuel : Nat) (state : MergeState κ ν)
    (slice : SortSlice κ ν) (base : Int) (n ok : Nat) :
    (binarysortLoopTraced? fuel state slice base n ok).erase =
      binarysortLoop? fuel state slice base n ok := by
  induction fuel generalizing slice ok with
  | zero =>
      by_cases hactive : ok < n <;>
        simp [binarysortLoopTraced?, binarysortLoop?, hactive]
  | succ fuel ih =>
      by_cases hactive : ok < n
      · rw [binarysortLoopTraced?, binarysortLoop?, if_pos hactive,
          if_pos hactive]
        simp only [TraceResult.erase_bind,
          TraceResult.erase_sortSliceKeysRead]
        cases hpivot : slice.read? (base + Int.ofNat ok) with
        | none => simp [binarysortBindOptionAcross]
        | some pivot =>
            simp only [Option.bind_some, binarysortBindOptionAcross]
            rw [erase_binarysortSearchTraced]
            cases hsearch : binarysortSearch? (ok + 1) state.key_compare slice
                base pivot 0 ok with
            | none => simp
            | some search =>
                simp only [Option.bind_some]
                cases hexhausted : search.fuelExhausted
                · simp only [Bool.false_eq_true, if_false,
                    TraceResult.erase_bind]
                  rw [erase_binarysortShiftInsertTraced_of_pivot _ _ _ _ _ _
                    hpivot]
                  simp [ih, Option.bind_assoc]
                · simp
      · simp [binarysortLoopTraced?, binarysortLoop?, hactive]

/-- Tracing is an instrumentation-only refinement on the full raw input
domain, including rejected assertion-domain calls and synthetic fuel branches. -/
@[simp]
theorem erase_binarysortTraced (state : MergeState κ ν)
    (slice : SortSlice κ ν) (base : Int) (n ok : Nat) :
    (binarysortTraced? state slice base n ok).erase =
      binarysort? state slice base n ok := by
  unfold binarysortTraced? binarysort?
  by_cases hadmitted : 1 ≤ n ∧ ok ≤ n ∧ n ≤ MAX_MINRUN.toNat
  · simp [hadmitted, erase_binarysortLoopTraced]
  · simp [hadmitted]

/-! ## Compositional trace safety -/

/-- The four trace obligations carried through binarysort's nested loops. -/
structure BinarysortTraceSafe (execution : TraceResult α) : Prop where
  fuel : execution.trace.fuelExhausted = false
  noPushes : execution.trace.pushDepths = []
  bounds : execution.trace.allAccessesInBounds
  tempLive : execution.trace.tempPayloadAccessesLive

namespace BinarysortTraceSafe

theorem bind_result_of_eq_some (current : TraceResult α)
    (next : α → TraceResult β) (value : α)
    (hresult : current.result = some value) :
    (current.bind next).result = (next value).result := by
  change (current.bind next).erase = (next value).erase
  rw [TraceResult.erase_bind]
  change current.result.bind (fun item => (next item).result) = _
  rw [hresult]
  rfl

theorem pure (value : α) : BinarysortTraceSafe (TraceResult.pure value) := by
  exact
    { fuel := rfl
      noPushes := rfl
      bounds := AccessTrace.allAccessesInBounds_empty
      tempLive := AccessTrace.tempPayloadAccessesLive_empty }

theorem bind (current : TraceResult α) (next : α → TraceResult β)
    (value : α) (hresult : current.result = some value)
    (hcurrent : BinarysortTraceSafe current)
    (hnext : BinarysortTraceSafe (next value)) :
    BinarysortTraceSafe (current.bind next) := by
  constructor
  · simp [TraceResult.trace_bind, hresult, hcurrent.fuel, hnext.fuel]
  · simp [TraceResult.trace_bind, hresult, AccessTrace.compose,
      hcurrent.noPushes, hnext.noPushes]
  · rw [TraceResult.trace_bind, hresult,
      AccessTrace.allAccessesInBounds_compose]
    exact ⟨hcurrent.bounds, hnext.bounds⟩
  · rw [TraceResult.trace_bind, hresult,
      AccessTrace.tempPayloadAccessesLive_compose]
    exact ⟨hcurrent.tempLive, hnext.tempLive⟩

end BinarysortTraceSafe

private theorem keysRead_safe (slice : SortSlice κ ν) (index : Int)
    (hindex : SortSlice.IndexInBounds slice index) :
    BinarysortTraceSafe (TraceResult.sortSliceKeysRead? slice index) := by
  constructor
  · simp [TraceResult.trace_sortSliceKeysRead, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_sortSliceKeysRead, AccessTrace.singletonAccess]
  · rw [TraceResult.trace_sortSliceKeysRead]
    simpa [AccessTrace.allAccessesInBounds, AccessTrace.singletonAccess,
      AccessEvent.InBounds, SortSlice.IndexInBounds] using hindex
  · simp [TraceResult.trace_sortSliceKeysRead,
      AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
      AccessEvent.TempPayloadLive]

private theorem valuesRead_safe (slice : SortSlice κ ν) (index : Int)
    (hindex : SortSlice.IndexInBounds slice index) :
    BinarysortTraceSafe (TraceResult.sortSliceValuesRead? slice index) := by
  constructor
  · simp [TraceResult.trace_sortSliceValuesRead, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_sortSliceValuesRead, AccessTrace.singletonAccess]
  · rw [TraceResult.trace_sortSliceValuesRead]
    simpa [AccessTrace.allAccessesInBounds, AccessTrace.singletonAccess,
      AccessEvent.InBounds, SortSlice.IndexInBounds] using hindex
  · simp [TraceResult.trace_sortSliceValuesRead,
      AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
      AccessEvent.TempPayloadLive]

private theorem keysWrite_safe (slice : SortSlice κ ν) (index : Int)
    (entry : SortSliceEntry κ ν)
    (hindex : SortSlice.IndexInBounds slice index) :
    BinarysortTraceSafe (TraceResult.sortSliceKeysWrite? slice index entry) := by
  constructor
  · simp [TraceResult.trace_sortSliceKeysWrite, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_sortSliceKeysWrite, AccessTrace.singletonAccess]
  · rw [TraceResult.trace_sortSliceKeysWrite]
    simpa [AccessTrace.allAccessesInBounds, AccessTrace.singletonAccess,
      AccessEvent.InBounds, SortSlice.IndexInBounds] using hindex
  · simp [TraceResult.trace_sortSliceKeysWrite,
      AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
      AccessEvent.TempPayloadLive]

private theorem valuesWrite_safe (slice : SortSlice κ ν) (index : Int)
    (entry : SortSliceEntry κ ν)
    (hindex : SortSlice.IndexInBounds slice index) :
    BinarysortTraceSafe (TraceResult.sortSliceValuesWrite? slice index entry) := by
  constructor
  · simp [TraceResult.trace_sortSliceValuesWrite, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_sortSliceValuesWrite, AccessTrace.singletonAccess]
  · rw [TraceResult.trace_sortSliceValuesWrite]
    simpa [AccessTrace.allAccessesInBounds, AccessTrace.singletonAccess,
      AccessEvent.InBounds, SortSlice.IndexInBounds] using hindex
  · simp [TraceResult.trace_sortSliceValuesWrite,
      AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
      AccessEvent.TempPayloadLive]

private structure BinarysortTraceMetadata (execution : TraceResult α) : Prop where
  fuel : execution.trace.fuelExhausted = false
  noPushes : execution.trace.pushDepths = []
  tempLive : execution.trace.tempPayloadAccessesLive

namespace BinarysortTraceMetadata

private theorem pure (value : α) :
    BinarysortTraceMetadata (TraceResult.pure value) := by
  exact ⟨rfl, rfl, AccessTrace.tempPayloadAccessesLive_empty⟩

private theorem bind (current : TraceResult α) (next : α → TraceResult β)
    (hcurrent : BinarysortTraceMetadata current)
    (hnext : ∀ value, BinarysortTraceMetadata (next value)) :
    BinarysortTraceMetadata (current.bind next) := by
  cases hresult : current.result with
  | none =>
      constructor
      · simpa [TraceResult.trace_bind, hresult] using hcurrent.fuel
      · simpa [TraceResult.trace_bind, hresult] using hcurrent.noPushes
      · simpa [TraceResult.trace_bind, hresult] using hcurrent.tempLive
  | some value =>
      have hfollowing := hnext value
      constructor
      · simp [TraceResult.trace_bind, hresult, hcurrent.fuel,
          hfollowing.fuel]
      · simp [TraceResult.trace_bind, hresult, AccessTrace.compose,
          hcurrent.noPushes, hfollowing.noPushes]
      · rw [TraceResult.trace_bind, hresult,
          AccessTrace.tempPayloadAccessesLive_compose]
        exact ⟨hcurrent.tempLive, hfollowing.tempLive⟩

private theorem keysRead (slice : SortSlice κ ν) (index : Int) :
    BinarysortTraceMetadata (TraceResult.sortSliceKeysRead? slice index) := by
  constructor
  · simp [TraceResult.trace_sortSliceKeysRead, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_sortSliceKeysRead, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_sortSliceKeysRead,
      AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
      AccessEvent.TempPayloadLive]

private theorem valuesRead (slice : SortSlice κ ν) (index : Int) :
    BinarysortTraceMetadata (TraceResult.sortSliceValuesRead? slice index) := by
  constructor
  · simp [TraceResult.trace_sortSliceValuesRead, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_sortSliceValuesRead, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_sortSliceValuesRead,
      AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
      AccessEvent.TempPayloadLive]

private theorem keysWrite (slice : SortSlice κ ν) (index : Int)
    (entry : SortSliceEntry κ ν) :
    BinarysortTraceMetadata
      (TraceResult.sortSliceKeysWrite? slice index entry) := by
  constructor
  · simp [TraceResult.trace_sortSliceKeysWrite, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_sortSliceKeysWrite, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_sortSliceKeysWrite,
      AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
      AccessEvent.TempPayloadLive]

private theorem valuesWrite (slice : SortSlice κ ν) (index : Int)
    (entry : SortSliceEntry κ ν) :
    BinarysortTraceMetadata
      (TraceResult.sortSliceValuesWrite? slice index entry) := by
  constructor
  · simp [TraceResult.trace_sortSliceValuesWrite, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_sortSliceValuesWrite, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_sortSliceValuesWrite,
      AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
      AccessEvent.TempPayloadLive]

private theorem copyKeys (destination source : SortSlice κ ν)
    (dst src : Int) :
    BinarysortTraceMetadata
      (SortSlice.copyKeysFromTraced? destination source dst src) := by
  apply bind _ _ (keysRead source src)
  intro entry
  exact keysWrite destination dst entry

private theorem copyValues (destination source : SortSlice κ ν)
    (dst src : Int) :
    BinarysortTraceMetadata
      (SortSlice.copyValuesFromTraced? destination source dst src) := by
  apply bind _ _ (valuesRead source src)
  intro entry
  exact valuesWrite destination dst entry

end BinarysortTraceMetadata

private theorem memmoveBackwardKeysTraced_metadata
    (count : Nat) (slice : SortSlice κ ν) (dst src : Int) :
    BinarysortTraceMetadata
      (SortSlice.memmoveBackwardKeysTraced? count slice dst src) := by
  induction count generalizing slice with
  | zero => exact BinarysortTraceMetadata.pure slice
  | succ count ih =>
      apply BinarysortTraceMetadata.bind _ _
        (BinarysortTraceMetadata.copyKeys slice slice
          (dst + Int.ofNat count) (src + Int.ofNat count))
      intro updated
      exact ih updated

private theorem memmoveBackwardValuesTraced_metadata
    (count : Nat) (slice : SortSlice κ ν) (dst src : Int) :
    BinarysortTraceMetadata
      (SortSlice.memmoveBackwardValuesTraced? count slice dst src) := by
  induction count generalizing slice with
  | zero => exact BinarysortTraceMetadata.pure slice
  | succ count ih =>
      apply BinarysortTraceMetadata.bind _ _
        (BinarysortTraceMetadata.copyValues slice slice
          (dst + Int.ofNat count) (src + Int.ofNat count))
      intro updated
      exact ih updated

private theorem memmoveBackwardKeysTraced_traceSafe
    (count : Nat) (slice : SortSlice κ ν) (dst src : Int)
    (hdst : SortSlice.RangeInBounds slice dst count)
    (hsrc : SortSlice.RangeInBounds slice src count) :
    ∃ updated,
      (SortSlice.memmoveBackwardKeysTraced? count slice dst src).result =
          some updated ∧
        BinarysortTraceSafe
          (SortSlice.memmoveBackwardKeysTraced? count slice dst src) ∧
        updated.entries.size = slice.entries.size := by
  rcases SortSlice.memmoveBackwardKeysTraced_safe count slice dst src hdst hsrc with
    ⟨updated, hresult, hbounds, hsize⟩
  rcases memmoveBackwardKeysTraced_metadata count slice dst src with
    ⟨hfuel, hpushes, hlive⟩
  exact ⟨updated, hresult, ⟨hfuel, hpushes, hbounds, hlive⟩, hsize⟩

private theorem memmoveBackwardValuesTraced_traceSafe
    (count : Nat) (slice : SortSlice κ ν) (dst src : Int)
    (hdst : SortSlice.RangeInBounds slice dst count)
    (hsrc : SortSlice.RangeInBounds slice src count) :
    ∃ updated,
      (SortSlice.memmoveBackwardValuesTraced? count slice dst src).result =
          some updated ∧
        BinarysortTraceSafe
          (SortSlice.memmoveBackwardValuesTraced? count slice dst src) ∧
        updated.entries.size = slice.entries.size := by
  rcases SortSlice.memmoveBackwardValuesTraced_safe count slice dst src hdst hsrc with
    ⟨updated, hresult, hbounds, hsize⟩
  rcases memmoveBackwardValuesTraced_metadata count slice dst src with
    ⟨hfuel, hpushes, hlive⟩
  exact ⟨updated, hresult, ⟨hfuel, hpushes, hbounds, hlive⟩, hsize⟩

/-! ## Binary-search safety and fuel adequacy -/

private theorem indexInBounds_of_range_offset
    (slice : SortSlice κ ν) (base : Int) (n offset : Nat)
    (hrange : SortSlice.RangeInBounds slice base n)
    (hoffset : offset < n) :
    SortSlice.IndexInBounds slice (base + Int.ofNat offset) := by
  rcases hrange with ⟨hbase, hend⟩
  constructor
  · exact add_nonneg hbase (Int.natCast_nonneg _)
  · have hoffsetInt : Int.ofNat offset < Int.ofNat n :=
      (Int.ofNat_lt).2 hoffset
    omega

private theorem read_result_of_indexInBounds (slice : SortSlice κ ν)
    (index : Int) (hindex : SortSlice.IndexInBounds slice index) :
    ∃ entry,
      (TraceResult.sortSliceKeysRead? slice index).result = some entry ∧
        slice.read? index = some entry := by
  rcases SortSlice.read_eq_some_of_indexInBounds slice index hindex with
    ⟨entry, hread⟩
  refine ⟨entry, ?_, hread⟩
  change (TraceResult.sortSliceKeysRead? slice index).erase = some entry
  simpa using hread

/-- Complete result contract for one binary-search call. -/
structure BinarysortSearchSafetyPost
    (fuel : Nat) (lt : BoolComparator κ) (slice : SortSlice κ ν)
    (base : Int) (pivot : SortSliceEntry κ ν) (left right : Nat)
    (result : BinarySearchResult) : Prop where
  resultEq :
    (binarysortSearchTraced? fuel lt slice base pivot left right).result =
      some result
  resultFuel : result.fuelExhausted = false
  traceSafe :
    BinarysortTraceSafe
      (binarysortSearchTraced? fuel lt slice base pivot left right)
  positionLower : left ≤ result.position
  positionUpper : result.position ≤ right

/-- Interval width is a sufficient fuel measure: every active comparison
strictly shrinks the unknown interval, so `right - left` units suffice. -/
theorem binarysortSearchTraced_safe
    (fuel : Nat) (lt : BoolComparator κ) (slice : SortSlice κ ν)
    (base : Int) (pivot : SortSliceEntry κ ν) (left right n : Nat)
    (hrange : SortSlice.RangeInBounds slice base n)
    (hle : left ≤ right) (hright : right ≤ n)
    (hwidth : right - left ≤ fuel) :
    ∃ result,
      BinarysortSearchSafetyPost fuel lt slice base pivot left right result := by
  induction fuel generalizing left right with
  | zero =>
      have heq : left = right := by omega
      subst right
      let result : BinarySearchResult :=
        { position := left, fuelExhausted := false }
      refine ⟨result, ?_⟩
      exact
        { resultEq := by
            simp [binarysortSearchTraced?, TraceResult.pure, result]
          resultFuel := rfl
          traceSafe := by
            simpa [binarysortSearchTraced?, result] using
              (BinarysortTraceSafe.pure result)
          positionLower := Nat.le_refl _
          positionUpper := Nat.le_refl _ }
  | succ fuel ih =>
      by_cases hactive : left < right
      · let middle := (left + right) / 2
        have hmiddleLower : left ≤ middle := by
          dsimp [middle]
          omega
        have hmiddleUpper : middle < right := by
          dsimp [middle]
          omega
        have hmiddleN : middle < n := lt_of_lt_of_le hmiddleUpper hright
        have hindex :=
          indexInBounds_of_range_offset slice base n middle hrange hmiddleN
        rcases read_result_of_indexInBounds slice (base + Int.ofNat middle)
            hindex with ⟨entry, hreadResult, hread⟩
        have hreadSafe := keysRead_safe slice (base + Int.ofNat middle) hindex
        by_cases hlt : lt pivot.key entry.key = true
        · have hnextWidth : middle - left ≤ fuel := by
            dsimp [middle]
            omega
          rcases ih left middle hmiddleLower (Nat.le_trans
              hmiddleUpper.le hright) hnextWidth with ⟨result, hpost⟩
          have htrace : BinarysortTraceSafe
              ((TraceResult.sortSliceKeysRead? slice
                (base + Int.ofNat middle)).bind fun current =>
                  if iflt lt pivot.key current.key then
                    binarysortSearchTraced? fuel lt slice base pivot left middle
                  else
                    binarysortSearchTraced? fuel lt slice base pivot
                      (middle + 1) right) :=
            BinarysortTraceSafe.bind _ _ entry hreadResult hreadSafe
              (by simpa [iflt, hlt] using hpost.traceSafe)
          refine ⟨result, ?_⟩
          exact
            { resultEq := by
                unfold binarysortSearchTraced?
                rw [if_pos hactive]
                dsimp only
                rw [BinarysortTraceSafe.bind_result_of_eq_some _ _ entry
                  hreadResult]
                simpa [middle, iflt, hlt] using hpost.resultEq
              resultFuel := hpost.resultFuel
              traceSafe := by
                simpa [binarysortSearchTraced?, hactive, middle, iflt, hlt]
                  using htrace
              positionLower := hpost.positionLower
              positionUpper := Nat.le_trans hpost.positionUpper hmiddleUpper.le }
        · have hnextWidth : right - (middle + 1) ≤ fuel := by
            dsimp [middle]
            omega
          rcases ih (middle + 1) right (Nat.succ_le_of_lt hmiddleUpper)
              hright hnextWidth with ⟨result, hpost⟩
          have htrace : BinarysortTraceSafe
              ((TraceResult.sortSliceKeysRead? slice
                (base + Int.ofNat middle)).bind fun current =>
                  if iflt lt pivot.key current.key then
                    binarysortSearchTraced? fuel lt slice base pivot left middle
                  else
                    binarysortSearchTraced? fuel lt slice base pivot
                      (middle + 1) right) :=
            BinarysortTraceSafe.bind _ _ entry hreadResult hreadSafe
              (by simpa [iflt, hlt] using hpost.traceSafe)
          refine ⟨result, ?_⟩
          exact
            { resultEq := by
                unfold binarysortSearchTraced?
                rw [if_pos hactive]
                dsimp only
                rw [BinarysortTraceSafe.bind_result_of_eq_some _ _ entry
                  hreadResult]
                simpa [middle, iflt, hlt] using hpost.resultEq
              resultFuel := hpost.resultFuel
              traceSafe := by
                simpa [binarysortSearchTraced?, hactive, middle, iflt, hlt]
                  using htrace
              positionLower := Nat.le_trans hmiddleLower
                (Nat.le_trans (Nat.le_succ middle) hpost.positionLower)
              positionUpper := hpost.positionUpper }
      · have heq : left = right := Nat.le_antisymm hle (Nat.le_of_not_gt hactive)
        subst right
        let result : BinarySearchResult :=
          { position := left, fuelExhausted := false }
        refine ⟨result, ?_⟩
        exact
          { resultEq := by
              simp [binarysortSearchTraced?, TraceResult.pure, result]
            resultFuel := rfl
            traceSafe := by
              simpa [binarysortSearchTraced?, result] using
                (BinarysortTraceSafe.pure result)
            positionLower := Nat.le_refl _
            positionUpper := Nat.le_refl _ }

/-! ## Shift-and-insert safety -/

private theorem shiftSourceRange
    (slice : SortSlice κ ν) (base : Int) (n ok position : Nat)
    (hrange : SortSlice.RangeInBounds slice base n)
    (hposition : position ≤ ok) (hok : ok ≤ n) :
    SortSlice.RangeInBounds slice (base + Int.ofNat position)
      (ok - position) := by
  rcases hrange with ⟨hbase, hend⟩
  constructor
  · exact add_nonneg hbase (Int.natCast_nonneg _)
  · have hsumNat : position + (ok - position) = ok :=
      Nat.add_sub_of_le hposition
    have hsumInt :
        Int.ofNat position + Int.ofNat (ok - position) = Int.ofNat ok := by
      simpa using congrArg Int.ofNat hsumNat
    have hokn : Int.ofNat ok ≤ Int.ofNat n := (Int.ofNat_le).2 hok
    calc
      base + Int.ofNat position + Int.ofNat (ok - position) =
          base + Int.ofNat ok := by rw [add_assoc, hsumInt]
      _ ≤ base + Int.ofNat n := by
        simpa [add_comm] using add_le_add_left hokn base
      _ ≤ Int.ofNat slice.entries.size := hend

private theorem shiftDestinationRange
    (slice : SortSlice κ ν) (base : Int) (n ok position : Nat)
    (hrange : SortSlice.RangeInBounds slice base n)
    (hposition : position ≤ ok) (hok : ok < n) :
    SortSlice.RangeInBounds slice (base + Int.ofNat (position + 1))
      (ok - position) := by
  rcases hrange with ⟨hbase, hend⟩
  constructor
  · exact add_nonneg hbase (Int.natCast_nonneg _)
  · have hsumNat : position + 1 + (ok - position) = ok + 1 := by omega
    have hsumInt :
        Int.ofNat (position + 1) + Int.ofNat (ok - position) =
          Int.ofNat (ok + 1) := by
      simpa using congrArg Int.ofNat hsumNat
    have hokn : Int.ofNat (ok + 1) ≤ Int.ofNat n :=
      (Int.ofNat_le).2 (Nat.succ_le_iff.mpr hok)
    calc
      base + Int.ofNat (position + 1) + Int.ofNat (ok - position) =
          base + Int.ofNat (ok + 1) := by rw [add_assoc, hsumInt]
      _ ≤ base + Int.ofNat n := by
        simpa [add_comm] using add_le_add_left hokn base
      _ ≤ Int.ofNat slice.entries.size := hend

/-- Complete contract for the source-ordered key/value shift and insertion. -/
structure BinarysortShiftInsertSafetyPost
    (valuesPresent : Bool) (before : SortSlice κ ν) (base : Int)
    (n ok position : Nat) (pivot : SortSliceEntry κ ν)
    (after : SortSlice κ ν) : Prop where
  resultEq :
    (binarysortShiftInsertTraced? valuesPresent before base ok position
      pivot).result = some after
  traceSafe :
    BinarysortTraceSafe
      (binarysortShiftInsertTraced? valuesPresent before base ok position pivot)
  exactErasure :
    (binarysortShiftInsertTraced? valuesPresent before base ok position
      pivot).erase = do
        let shifted ← before.memmove?
          (base + Int.ofNat (position + 1))
          (base + Int.ofNat position) (ok - position)
        shifted.write? (base + Int.ofNat position) pivot
  valuesMode : SortSlice.ValuesModeInvariant valuesPresent after
  entriesSize : after.entries.size = before.entries.size
  range : SortSlice.RangeInBounds after base n

/-- The right-to-left shift and both insertion writes are safe whenever the
pivot and insertion position come from the current sorted prefix. -/
theorem binarysortShiftInsertTraced_safe
    (valuesPresent : Bool) (slice : SortSlice κ ν) (base : Int)
    (n ok position : Nat) (pivot : SortSliceEntry κ ν)
    (hrange : SortSlice.RangeInBounds slice base n)
    (hposition : position ≤ ok) (hok : ok < n)
    (hmode : SortSlice.ValuesModeInvariant valuesPresent slice)
    (hpivot : slice.read? (base + Int.ofNat ok) = some pivot) :
    ∃ after,
      BinarysortShiftInsertSafetyPost valuesPresent slice base n ok position
        pivot after := by
  let count := ok - position
  let dst := base + Int.ofNat (position + 1)
  let src := base + Int.ofNat position
  let insertIndex := base + Int.ofNat position
  have hdst : SortSlice.RangeInBounds slice dst count := by
    simpa [dst, count] using shiftDestinationRange slice base n ok position
      hrange hposition hok
  have hsrc : SortSlice.RangeInBounds slice src count := by
    simpa [src, count] using shiftSourceRange slice base n ok position hrange
      hposition hok.le
  have hinsert : SortSlice.IndexInBounds slice insertIndex := by
    apply indexInBounds_of_range_offset slice base n position hrange
    exact lt_of_le_of_lt hposition hok
  have hpivotMode := hmode.read_matches_of_eq_some hpivot
  rcases memmoveBackwardKeysTraced_traceSafe count slice dst src hdst hsrc with
    ⟨keyShifted, hkeyShift, hkeyShiftSafe, hkeyShiftSize⟩
  have hkeyMove :
      SortSlice.memmoveBackward? count slice dst src = some keyShifted := by
    rw [← SortSlice.erase_memmoveBackwardKeysTraced]
    exact hkeyShift
  have hkeyShiftMode :
      SortSlice.ValuesModeInvariant valuesPresent keyShifted :=
    hmode.memmoveBackward_preserved_of_eq_some count hkeyMove
  have hinsertShifted : SortSlice.IndexInBounds keyShifted insertIndex :=
    hinsert.of_size_eq hkeyShiftSize
  rcases SortSlice.write_eq_some_of_indexInBounds keyShifted insertIndex pivot
      hinsertShifted with ⟨keyResult, hkeyWriteRaw⟩
  have hkeyWrite :
      (TraceResult.sortSliceKeysWrite? keyShifted insertIndex pivot).result =
        some keyResult := by
    change (TraceResult.sortSliceKeysWrite? keyShifted insertIndex pivot).erase =
      some keyResult
    simpa using hkeyWriteRaw
  have hkeyWriteSafe := keysWrite_safe keyShifted insertIndex pivot hinsertShifted
  have hkeyPhaseSafe : BinarysortTraceSafe
      ((SortSlice.memmoveBackwardKeysTraced? count slice dst src).bind
        fun shifted =>
          TraceResult.sortSliceKeysWrite? shifted insertIndex pivot) :=
    BinarysortTraceSafe.bind _ _ keyShifted hkeyShift hkeyShiftSafe hkeyWriteSafe
  have hkeyPhaseResult :
      ((SortSlice.memmoveBackwardKeysTraced? count slice dst src).bind
        fun shifted =>
          TraceResult.sortSliceKeysWrite? shifted insertIndex pivot).result =
        some keyResult :=
    (BinarysortTraceSafe.bind_result_of_eq_some _ _ keyShifted hkeyShift).trans
      hkeyWrite
  have hkeyResultMode :
      SortSlice.ValuesModeInvariant valuesPresent keyResult :=
    hkeyShiftMode.write_preserved_of_eq_some hpivotMode hkeyWriteRaw
  have hkeyResultSize : keyResult.entries.size = slice.entries.size :=
    (SortSlice.write_entries_size_of_eq_some keyShifted keyResult insertIndex pivot
      hkeyWriteRaw).trans hkeyShiftSize
  have hkeyResultRange : SortSlice.RangeInBounds keyResult base n :=
    hrange.of_size_eq hkeyResultSize
  cases valuesPresent with
  | false =>
      have hfalseAfterWriteSafe : BinarysortTraceSafe
          ((TraceResult.sortSliceKeysWrite? keyShifted insertIndex pivot).bind
            fun keyResult => TraceResult.pure keyResult) :=
        BinarysortTraceSafe.bind _ _ keyResult hkeyWrite hkeyWriteSafe
          (BinarysortTraceSafe.pure keyResult)
      have hfalseAfterWriteResult :
          ((TraceResult.sortSliceKeysWrite? keyShifted insertIndex pivot).bind
            fun keyResult => TraceResult.pure keyResult).result =
              some keyResult := by
        rw [BinarysortTraceSafe.bind_result_of_eq_some _ _ keyResult hkeyWrite]
        rfl
      have hfalseSafe : BinarysortTraceSafe
          ((SortSlice.memmoveBackwardKeysTraced? count slice dst src).bind
            fun shifted =>
              (TraceResult.sortSliceKeysWrite? shifted insertIndex pivot).bind
                fun keyResult => TraceResult.pure keyResult) :=
        BinarysortTraceSafe.bind _ _ keyShifted hkeyShift hkeyShiftSafe
          hfalseAfterWriteSafe
      have hfalseResult :
          ((SortSlice.memmoveBackwardKeysTraced? count slice dst src).bind
            fun shifted =>
              (TraceResult.sortSliceKeysWrite? shifted insertIndex pivot).bind
                fun keyResult => TraceResult.pure keyResult).result =
            some keyResult := by
        rw [BinarysortTraceSafe.bind_result_of_eq_some _ _ keyShifted hkeyShift]
        exact hfalseAfterWriteResult
      refine ⟨keyResult, ?_⟩
      exact
        { resultEq := by
            simpa [binarysortShiftInsertTraced?, count, dst, src, insertIndex]
              using hfalseResult
          traceSafe := by
            simpa [binarysortShiftInsertTraced?, count, dst, src, insertIndex]
              using hfalseSafe
          exactErasure :=
            erase_binarysortShiftInsertTraced_of_pivot false slice base ok position
              pivot hpivot
          valuesMode := hkeyResultMode
          entriesSize := hkeyResultSize
          range := hkeyResultRange }
  | true =>
      have hpivotIndex : SortSlice.IndexInBounds slice
          (base + Int.ofNat ok) :=
        indexInBounds_of_range_offset slice base n ok hrange hok
      have hvalueRead :
          (TraceResult.sortSliceValuesRead? slice
            (base + Int.ofNat ok)).result = some pivot := by
        change (TraceResult.sortSliceValuesRead? slice
          (base + Int.ofNat ok)).erase = some pivot
        simpa using hpivot
      have hvalueReadSafe := valuesRead_safe slice
        (base + Int.ofNat ok) hpivotIndex
      have hvalueShift :
          (SortSlice.memmoveBackwardValuesTraced? count slice dst src).result =
            some keyShifted := by
        change
          (SortSlice.memmoveBackwardValuesTraced? count slice dst src).erase =
            some keyShifted
        rw [SortSlice.erase_memmoveBackwardValuesTraced]
        exact hkeyMove
      rcases memmoveBackwardValuesTraced_traceSafe count slice dst src hdst hsrc with
        ⟨valueShifted, hvalueShift', hvalueShiftSafe', hvalueShiftSize⟩
      have hvalueShiftedEq : valueShifted = keyShifted := by
        rw [hvalueShift] at hvalueShift'
        exact Option.some.inj hvalueShift'.symm
      subst valueShifted
      have hvalueWrite :
          (TraceResult.sortSliceValuesWrite? keyShifted insertIndex pivot).result =
            some keyResult := by
        change
          (TraceResult.sortSliceValuesWrite? keyShifted insertIndex pivot).erase =
            some keyResult
        simpa using hkeyWriteRaw
      have hvalueWriteSafe :=
        valuesWrite_safe keyShifted insertIndex pivot hinsertShifted
      have hvalueTailSafe : BinarysortTraceSafe
          ((TraceResult.sortSliceValuesRead? slice
            (base + Int.ofNat ok)).bind fun valuePivot =>
              (SortSlice.memmoveBackwardValuesTraced? count slice dst src).bind
                fun shifted =>
                  TraceResult.sortSliceValuesWrite? shifted insertIndex
                    valuePivot) := by
        apply BinarysortTraceSafe.bind _ _ pivot hvalueRead hvalueReadSafe
        exact BinarysortTraceSafe.bind _ _ keyShifted hvalueShift
          hvalueShiftSafe' hvalueWriteSafe
      have hvalueTailResult :
          ((TraceResult.sortSliceValuesRead? slice
            (base + Int.ofNat ok)).bind fun valuePivot =>
              (SortSlice.memmoveBackwardValuesTraced? count slice dst src).bind
                fun shifted =>
                  TraceResult.sortSliceValuesWrite? shifted insertIndex
                    valuePivot).result = some keyResult := by
        rw [BinarysortTraceSafe.bind_result_of_eq_some _ _ pivot hvalueRead]
        rw [BinarysortTraceSafe.bind_result_of_eq_some _ _ keyShifted hvalueShift]
        exact hvalueWrite
      have hafterKeyWriteSafe : BinarysortTraceSafe
          ((TraceResult.sortSliceKeysWrite? keyShifted insertIndex pivot).bind
            fun _ =>
              (TraceResult.sortSliceValuesRead? slice
                (base + Int.ofNat ok)).bind fun valuePivot =>
                  (SortSlice.memmoveBackwardValuesTraced? count slice dst src).bind
                    fun shifted =>
                      TraceResult.sortSliceValuesWrite? shifted insertIndex
                        valuePivot) :=
        BinarysortTraceSafe.bind _ _ keyResult hkeyWrite hkeyWriteSafe
          hvalueTailSafe
      have hafterKeyWriteResult :
          ((TraceResult.sortSliceKeysWrite? keyShifted insertIndex pivot).bind
            fun _ =>
              (TraceResult.sortSliceValuesRead? slice
                (base + Int.ofNat ok)).bind fun valuePivot =>
                  (SortSlice.memmoveBackwardValuesTraced? count slice dst src).bind
                    fun shifted =>
                      TraceResult.sortSliceValuesWrite? shifted insertIndex
                        valuePivot).result = some keyResult := by
        rw [BinarysortTraceSafe.bind_result_of_eq_some _ _ keyResult hkeyWrite]
        exact hvalueTailResult
      have hfullSafe : BinarysortTraceSafe
          ((SortSlice.memmoveBackwardKeysTraced? count slice dst src).bind
            fun keyShifted =>
              (TraceResult.sortSliceKeysWrite? keyShifted insertIndex pivot).bind
                fun _ =>
                  (TraceResult.sortSliceValuesRead? slice
                    (base + Int.ofNat ok)).bind fun valuePivot =>
                      (SortSlice.memmoveBackwardValuesTraced? count slice dst src).bind
                        fun valueShifted =>
                          TraceResult.sortSliceValuesWrite? valueShifted
                            insertIndex valuePivot) :=
        BinarysortTraceSafe.bind _ _ keyShifted hkeyShift hkeyShiftSafe
          hafterKeyWriteSafe
      have hfullResult :
          ((SortSlice.memmoveBackwardKeysTraced? count slice dst src).bind
            fun keyShifted =>
              (TraceResult.sortSliceKeysWrite? keyShifted insertIndex pivot).bind
                fun _ =>
                  (TraceResult.sortSliceValuesRead? slice
                    (base + Int.ofNat ok)).bind fun valuePivot =>
                      (SortSlice.memmoveBackwardValuesTraced? count slice dst src).bind
                        fun valueShifted =>
                          TraceResult.sortSliceValuesWrite? valueShifted
                            insertIndex valuePivot).result = some keyResult := by
        rw [BinarysortTraceSafe.bind_result_of_eq_some _ _ keyShifted hkeyShift]
        exact hafterKeyWriteResult
      refine ⟨keyResult, ?_⟩
      exact
        { resultEq := by
            simpa [binarysortShiftInsertTraced?, count, dst, src, insertIndex]
              using hfullResult
          traceSafe := by
            simpa [binarysortShiftInsertTraced?, count, dst, src, insertIndex]
              using hfullSafe
          exactErasure :=
            erase_binarysortShiftInsertTraced_of_pivot true slice base ok position
              pivot hpivot
          valuesMode := hkeyResultMode
          entriesSize := hkeyResultSize
          range := hkeyResultRange }

/-! ## Outer-loop and public safety -/

private structure BinarysortLoopSafetyPost
    (fuel : Nat) (state : MergeState κ ν) (before : SortSlice κ ν)
    (base : Int) (n ok : Nat) (result : BinarysortResult κ ν) : Prop where
  resultEq :
    (binarysortLoopTraced? fuel state before base n ok).result = some result
  resultFuel : result.fuelExhausted = false
  traceSafe :
    BinarysortTraceSafe (binarysortLoopTraced? fuel state before base n ok)
  valuesMode :
    SortSlice.ValuesModeInvariant state.a.hasValues result.slice
  sizeEq : result.slice.entries.size = before.entries.size
  range : SortSlice.RangeInBounds result.slice base n

private theorem binarysortLoopTraced_safe
    (fuel : Nat) (state : MergeState κ ν) (slice : SortSlice κ ν)
    (base : Int) (n ok : Nat)
    (hok : ok ≤ n) (hremaining : n - ok ≤ fuel)
    (hrange : SortSlice.RangeInBounds slice base n)
    (hmode : SortSlice.ValuesModeInvariant state.a.hasValues slice) :
    ∃ result,
      BinarysortLoopSafetyPost fuel state slice base n ok result := by
  induction fuel generalizing slice ok with
  | zero =>
      have heq : ok = n := by omega
      subst ok
      let result : BinarysortResult κ ν :=
        { slice := slice, fuelExhausted := false }
      refine ⟨result, ?_⟩
      exact
        { resultEq := by
            simp [binarysortLoopTraced?, TraceResult.pure, result]
          resultFuel := rfl
          traceSafe := by
            simpa [binarysortLoopTraced?, result] using
              (BinarysortTraceSafe.pure result)
          valuesMode := hmode
          sizeEq := rfl
          range := hrange }
  | succ fuel ih =>
      by_cases hactive : ok < n
      · have hpivotIndex : SortSlice.IndexInBounds slice
            (base + Int.ofNat ok) :=
          indexInBounds_of_range_offset slice base n ok hrange hactive
        rcases read_result_of_indexInBounds slice (base + Int.ofNat ok)
            hpivotIndex with ⟨pivot, hpivotResult, hpivot⟩
        have hpivotSafe := keysRead_safe slice (base + Int.ofNat ok) hpivotIndex
        rcases binarysortSearchTraced_safe (ok + 1) state.key_compare slice base
            pivot 0 ok n hrange (Nat.zero_le _) hactive.le (by omega) with
          ⟨search, hsearch⟩
        rcases binarysortShiftInsertTraced_safe state.a.hasValues slice base n ok
            search.position pivot hrange hsearch.positionUpper hactive hmode
            hpivot with ⟨updated, hshift⟩
        have hnextOk : ok + 1 ≤ n := Nat.succ_le_iff.mpr hactive
        have hnextRemaining : n - (ok + 1) ≤ fuel := by omega
        rcases ih updated (ok + 1) hnextOk hnextRemaining hshift.range
            hshift.valuesMode with ⟨result, hrest⟩
        have hshiftRestSafe : BinarysortTraceSafe
            ((binarysortShiftInsertTraced? state.a.hasValues slice base ok
              search.position pivot).bind fun updated =>
                binarysortLoopTraced? fuel state updated base n (ok + 1)) :=
          BinarysortTraceSafe.bind _ _ updated hshift.resultEq hshift.traceSafe
            hrest.traceSafe
        have hafterSearchSafe : BinarysortTraceSafe
            ((binarysortSearchTraced? (ok + 1) state.key_compare slice base pivot
              0 ok).bind fun current =>
                if current.fuelExhausted then
                  TraceResult.pure
                    ({ slice := slice, fuelExhausted := true } :
                      BinarysortResult κ ν)
                else
                  (binarysortShiftInsertTraced? state.a.hasValues slice base ok
                    current.position pivot).bind fun updated =>
                      binarysortLoopTraced? fuel state updated base n (ok + 1)) :=
          BinarysortTraceSafe.bind _ _ search hsearch.resultEq hsearch.traceSafe
            (by simpa [hsearch.resultFuel] using hshiftRestSafe)
        have hfullSafe : BinarysortTraceSafe
            ((TraceResult.sortSliceKeysRead? slice
              (base + Int.ofNat ok)).bind fun pivot =>
                (binarysortSearchTraced? (ok + 1) state.key_compare slice base
                  pivot 0 ok).bind fun search =>
                    if search.fuelExhausted then
                      TraceResult.pure
                        ({ slice := slice, fuelExhausted := true } :
                          BinarysortResult κ ν)
                    else
                      (binarysortShiftInsertTraced? state.a.hasValues slice base
                        ok search.position pivot).bind fun updated =>
                          binarysortLoopTraced? fuel state updated base n
                            (ok + 1)) :=
          BinarysortTraceSafe.bind _ _ pivot hpivotResult hpivotSafe
            hafterSearchSafe
        have hshiftRestResult :
            ((binarysortShiftInsertTraced? state.a.hasValues slice base ok
              search.position pivot).bind fun updated =>
                binarysortLoopTraced? fuel state updated base n
                  (ok + 1)).result = some result := by
          rw [BinarysortTraceSafe.bind_result_of_eq_some _ _ updated
            hshift.resultEq]
          exact hrest.resultEq
        have hafterSearchResult :
            ((binarysortSearchTraced? (ok + 1) state.key_compare slice base pivot
              0 ok).bind fun current =>
                if current.fuelExhausted then
                  TraceResult.pure
                    ({ slice := slice, fuelExhausted := true } :
                      BinarysortResult κ ν)
                else
                  (binarysortShiftInsertTraced? state.a.hasValues slice base ok
                    current.position pivot).bind fun updated =>
                      binarysortLoopTraced? fuel state updated base n
                        (ok + 1)).result = some result := by
          rw [BinarysortTraceSafe.bind_result_of_eq_some _ _ search
            hsearch.resultEq]
          simpa [hsearch.resultFuel] using hshiftRestResult
        have hfullResult :
            ((TraceResult.sortSliceKeysRead? slice
              (base + Int.ofNat ok)).bind fun pivot =>
                (binarysortSearchTraced? (ok + 1) state.key_compare slice base
                  pivot 0 ok).bind fun search =>
                    if search.fuelExhausted then
                      TraceResult.pure
                        ({ slice := slice, fuelExhausted := true } :
                          BinarysortResult κ ν)
                    else
                      (binarysortShiftInsertTraced? state.a.hasValues slice base
                        ok search.position pivot).bind fun updated =>
                          binarysortLoopTraced? fuel state updated base n
                            (ok + 1)).result = some result := by
          rw [BinarysortTraceSafe.bind_result_of_eq_some _ _ pivot hpivotResult]
          exact hafterSearchResult
        refine ⟨result, ?_⟩
        exact
          { resultEq := by
              simpa [binarysortLoopTraced?, hactive] using hfullResult
            resultFuel := hrest.resultFuel
            traceSafe := by
              simpa [binarysortLoopTraced?, hactive] using hfullSafe
            valuesMode := hrest.valuesMode
            sizeEq := hrest.sizeEq.trans hshift.entriesSize
            range := hrest.range }
      · have heq : ok = n := Nat.le_antisymm hok (Nat.le_of_not_gt hactive)
        subst ok
        let result : BinarysortResult κ ν :=
          { slice := slice, fuelExhausted := false }
        refine ⟨result, ?_⟩
        exact
          { resultEq := by
              simp [binarysortLoopTraced?, TraceResult.pure, result]
            resultFuel := rfl
            traceSafe := by
              simpa [binarysortLoopTraced?, result] using
                (BinarysortTraceSafe.pure result)
            valuesMode := hmode
            sizeEq := rfl
            range := hrange }

/-- Public binarysort safety certificate consumed by the top-level scan. -/
structure BinarysortSafetyPost
    (state : MergeState κ ν) (before : SortSlice κ ν) (base : Int)
    (n ok : Nat) (result : BinarysortResult κ ν) : Prop where
  resultEq : (binarysortTraced? state before base n ok).result = some result
  resultFuel : result.fuelExhausted = false
  traceFuel :
    (binarysortTraced? state before base n ok).trace.fuelExhausted = false
  noPushes : (binarysortTraced? state before base n ok).trace.pushDepths = []
  accessesInBounds :
    (binarysortTraced? state before base n ok).trace.allAccessesInBounds
  tempAccessesLive :
    (binarysortTraced? state before base n ok).trace.tempPayloadAccessesLive
  exactErasure :
    (binarysortTraced? state before base n ok).erase =
      binarysort? state before base n ok
  valuesMode :
    SortSlice.ValuesModeInvariant state.a.hasValues result.slice
  sizeEq : result.slice.entries.size = before.entries.size
  range : SortSlice.RangeInBounds result.slice base n

/-- Every source-admitted call succeeds, terminates within the source-supplied
`n` fuel, preserves representation mode and extent, and records only in-bounds
key/value accesses.  No ordering law is assumed of the Boolean comparator. -/
theorem binarysort_safe
    (state : MergeState κ ν) (slice : SortSlice κ ν) (base : Int)
    (n ok : Nat) (hnPositive : 1 ≤ n) (hok : ok ≤ n)
    (hnMax : n ≤ MAX_MINRUN.toNat)
    (hrange : SortSlice.RangeInBounds slice base n)
    (hmode : SortSlice.ValuesModeInvariant state.a.hasValues slice) :
    ∃ result, BinarysortSafetyPost state slice base n ok result := by
  let normalizedOk := if ok = 0 then 1 else ok
  have hnormalized : normalizedOk ≤ n := by
    dsimp [normalizedOk]
    split
    · exact hnPositive
    · exact hok
  have hremaining : n - normalizedOk ≤ n := Nat.sub_le _ _
  rcases binarysortLoopTraced_safe n state slice base n normalizedOk hnormalized
      hremaining hrange hmode with ⟨result, hloop⟩
  have hadmitted : 1 ≤ n ∧ ok ≤ n ∧ n ≤ MAX_MINRUN.toNat :=
    ⟨hnPositive, hok, hnMax⟩
  refine ⟨result, ?_⟩
  exact
    { resultEq := by
        simpa [binarysortTraced?, hadmitted, normalizedOk] using hloop.resultEq
      resultFuel := hloop.resultFuel
      traceFuel := by
        simpa [binarysortTraced?, hadmitted, normalizedOk] using
          hloop.traceSafe.fuel
      noPushes := by
        simpa [binarysortTraced?, hadmitted, normalizedOk] using
          hloop.traceSafe.noPushes
      accessesInBounds := by
        simpa [binarysortTraced?, hadmitted, normalizedOk] using
          hloop.traceSafe.bounds
      tempAccessesLive := by
        simpa [binarysortTraced?, hadmitted, normalizedOk] using
          hloop.traceSafe.tempLive
      exactErasure := erase_binarysortTraced state slice base n ok
      valuesMode := hloop.valuesMode
      sizeEq := hloop.sizeEq
      range := hloop.range }

/-! ## Source-order and call-site pins -/

/-- Every active search iteration probes the arithmetic midpoint, and that
midpoint is a valid key-array index in the caller's range.  The two successor
intervals are strictly smaller and fit the predecessor fuel budget. -/
theorem binarysort_midpoint_callsite_geometry
    (slice : SortSlice κ ν) (base : Int) (n left right fuel : Nat)
    (hrange : SortSlice.RangeInBounds slice base n)
    (hactive : left < right) (hright : right ≤ n)
    (hnMax : n ≤ MAX_MINRUN.toNat)
    (hwidth : right - left ≤ fuel + 1) :
    let middle := (left + right) / 2
    left ≤ middle ∧ middle < right ∧
      SortSlice.IndexInBounds slice (base + Int.ofNat middle) ∧
      middle - left ≤ fuel ∧ right - (middle + 1) ≤ fuel ∧
      left + right ≤ 2 * MAX_MINRUN.toNat ∧
      left + right ≤ PY_SSIZE_T_MAX := by
  dsimp only
  have hmiddleLower : left ≤ (left + right) / 2 := by omega
  have hmiddleUpper : (left + right) / 2 < right := by omega
  have hsumSmall : left + right ≤ 2 * MAX_MINRUN.toNat := by omega
  have hsumWord : left + right ≤ PY_SSIZE_T_MAX := by
    apply hsumSmall.trans
    have hmaxMinrun : MAX_MINRUN.toNat = 64 := by decide
    rw [hmaxMinrun]
    norm_num [PY_SSIZE_T_MAX]
  refine ⟨hmiddleLower, hmiddleUpper, ?_, by omega, by omega, hsumSmall,
    hsumWord⟩
  exact indexInBounds_of_range_offset slice base n ((left + right) / 2)
    hrange (lt_of_lt_of_le hmiddleUpper hright)

/-- An active binary-search step records its midpoint key read first, then the
complete trace of exactly the comparator-selected smaller interval.  Comparator
evaluation itself is deliberately not an access event. -/
theorem binarysortSearchTraced_step_trace_order
    (fuel : Nat) (lt : BoolComparator κ) (slice : SortSlice κ ν)
    (base : Int) (pivot entry : SortSliceEntry κ ν) (left right : Nat)
    (hactive : left < right)
    (hread :
      (TraceResult.sortSliceKeysRead? slice
        (base + Int.ofNat ((left + right) / 2))).result = some entry) :
    (binarysortSearchTraced? (fuel + 1) lt slice base pivot left right).trace =
      (TraceResult.sortSliceKeysRead? slice
        (base + Int.ofNat ((left + right) / 2))).trace.compose
          (if iflt lt pivot.key entry.key then
            (binarysortSearchTraced? fuel lt slice base pivot left
              ((left + right) / 2)).trace
          else
            (binarysortSearchTraced? fuel lt slice base pivot
              ((left + right) / 2 + 1) right).trace) := by
  change
    (if left < right then
      (TraceResult.sortSliceKeysRead? slice
        (base + Int.ofNat ((left + right) / 2))).bind fun current =>
          if iflt lt pivot.key current.key then
            binarysortSearchTraced? fuel lt slice base pivot left
              ((left + right) / 2)
          else
            binarysortSearchTraced? fuel lt slice base pivot
              ((left + right) / 2 + 1) right
    else
      TraceResult.pure { position := left, fuelExhausted := false }).trace = _
  rw [if_pos hactive]
  simp only [TraceResult.trace_bind, hread]
  by_cases hcomparison : iflt lt pivot.key entry.key = true
  · simp only [hcomparison, if_true]
  · simp only [hcomparison, Bool.false_eq_true, if_false]

/-- Geometry for the source's overlapping one-slot right shift: both ranges,
the insertion cell, and the saved-pivot cell are valid. -/
theorem binarysort_shift_callsite_geometry
    (slice : SortSlice κ ν) (base : Int) (n ok position : Nat)
    (hrange : SortSlice.RangeInBounds slice base n)
    (hposition : position ≤ ok) (hok : ok < n) :
    SortSlice.RangeInBounds slice (base + Int.ofNat position)
        (ok - position) ∧
      SortSlice.RangeInBounds slice (base + Int.ofNat (position + 1))
        (ok - position) ∧
      SortSlice.IndexInBounds slice (base + Int.ofNat position) ∧
      SortSlice.IndexInBounds slice (base + Int.ofNat ok) := by
  exact
    ⟨shiftSourceRange slice base n ok position hrange hposition hok.le,
      shiftDestinationRange slice base n ok position hrange hposition hok,
      indexInBounds_of_range_offset slice base n position hrange
        (lt_of_le_of_lt hposition hok),
      indexInBounds_of_range_offset slice base n ok hrange hok⟩

/-- A nonempty key shift starts at offset `count`, the highest source/destination
pair, then recurses on the lower `count` cells. -/
theorem binarysortKeyShiftTraced_high_to_low
    (count : Nat) (slice : SortSlice κ ν) (dst src : Int)
    (hdst : SortSlice.RangeInBounds slice dst (count + 1))
    (hsrc : SortSlice.RangeInBounds slice src (count + 1)) :
    ∃ first,
      (SortSlice.copyKeysFromTraced? slice slice
        (dst + Int.ofNat count) (src + Int.ofNat count)).result = some first ∧
      (SortSlice.memmoveBackwardKeysTraced? (count + 1) slice dst src).trace.accesses =
        SortSlice.keyCopyAccesses slice.entries.size slice.entries.size
          (dst + Int.ofNat count) (src + Int.ofNat count) ++
        (SortSlice.memmoveBackwardKeysTraced? count first dst src).trace.accesses := by
  have hdstLast := hdst.last
  have hsrcLast := hsrc.last
  rcases SortSlice.copyFrom_eq_some_of_bounds slice slice
      (dst + Int.ofNat count) (src + Int.ofNat count) hdstLast hsrcLast with
    ⟨first, hcopy⟩
  have hfirst :
      (SortSlice.copyKeysFromTraced? slice slice
        (dst + Int.ofNat count) (src + Int.ofNat count)).result = some first := by
    change (SortSlice.copyKeysFromTraced? slice slice
      (dst + Int.ofNat count) (src + Int.ofNat count)).erase = some first
    simpa using hcopy
  refine ⟨first, hfirst, ?_⟩
  simp only [SortSlice.memmoveBackwardKeysTraced?, TraceResult.trace_bind,
    hfirst, AccessTrace.compose]
  rw [SortSlice.copyKeysFromTraced_accesses slice slice
    (dst + Int.ofNat count) (src + Int.ofNat count) hdstLast hsrcLast]

/-- The synchronized-values shift has the identical high-to-low index order. -/
theorem binarysortValuesShiftTraced_high_to_low
    (count : Nat) (slice : SortSlice κ ν) (dst src : Int)
    (hdst : SortSlice.RangeInBounds slice dst (count + 1))
    (hsrc : SortSlice.RangeInBounds slice src (count + 1)) :
    ∃ first,
      (SortSlice.copyValuesFromTraced? slice slice
        (dst + Int.ofNat count) (src + Int.ofNat count)).result = some first ∧
      (SortSlice.memmoveBackwardValuesTraced? (count + 1) slice dst src).trace.accesses =
        SortSlice.valuesCopyAccesses slice.entries.size slice.entries.size
          (dst + Int.ofNat count) (src + Int.ofNat count) ++
        (SortSlice.memmoveBackwardValuesTraced? count first dst src).trace.accesses := by
  have hdstLast := hdst.last
  have hsrcLast := hsrc.last
  rcases SortSlice.copyFrom_eq_some_of_bounds slice slice
      (dst + Int.ofNat count) (src + Int.ofNat count) hdstLast hsrcLast with
    ⟨first, hcopy⟩
  have hfirst :
      (SortSlice.copyValuesFromTraced? slice slice
        (dst + Int.ofNat count) (src + Int.ofNat count)).result = some first := by
    change (SortSlice.copyValuesFromTraced? slice slice
      (dst + Int.ofNat count) (src + Int.ofNat count)).erase = some first
    simpa using hcopy
  refine ⟨first, hfirst, ?_⟩
  simp only [SortSlice.memmoveBackwardValuesTraced?, TraceResult.trace_bind,
    hfirst, AccessTrace.compose]
  rw [SortSlice.copyValuesFromTraced_accesses slice slice
    (dst + Int.ofNat count) (src + Int.ofNat count) hdstLast hsrcLast]

/-- In values mode the full insertion trace is ordered as key shift, key pivot
write, value pivot read, value shift, and value pivot write. -/
theorem binarysortShiftInsertTraced_values_phase_order
    (slice keyShifted keyResult valueShifted : SortSlice κ ν)
    (base : Int) (ok position : Nat) (pivot valuePivot : SortSliceEntry κ ν)
    (hkeyShift :
      (SortSlice.memmoveBackwardKeysTraced? (ok - position) slice
        (base + Int.ofNat (position + 1))
        (base + Int.ofNat position)).result = some keyShifted)
    (hkeyWrite :
      (TraceResult.sortSliceKeysWrite? keyShifted
        (base + Int.ofNat position) pivot).result = some keyResult)
    (hvalueRead :
      (TraceResult.sortSliceValuesRead? slice
        (base + Int.ofNat ok)).result = some valuePivot)
    (hvalueShift :
      (SortSlice.memmoveBackwardValuesTraced? (ok - position) slice
        (base + Int.ofNat (position + 1))
        (base + Int.ofNat position)).result = some valueShifted) :
    (binarysortShiftInsertTraced? true slice base ok position pivot).trace =
      (SortSlice.memmoveBackwardKeysTraced? (ok - position) slice
        (base + Int.ofNat (position + 1))
        (base + Int.ofNat position)).trace.compose
        ((TraceResult.sortSliceKeysWrite? keyShifted
          (base + Int.ofNat position) pivot).trace.compose
          ((TraceResult.sortSliceValuesRead? slice
            (base + Int.ofNat ok)).trace.compose
            ((SortSlice.memmoveBackwardValuesTraced? (ok - position) slice
              (base + Int.ofNat (position + 1))
              (base + Int.ofNat position)).trace.compose
              (TraceResult.sortSliceValuesWrite? valueShifted
                (base + Int.ofNat position) valuePivot).trace))) := by
  change
    ((SortSlice.memmoveBackwardKeysTraced? (ok - position) slice
      (base + Int.ofNat (position + 1))
      (base + Int.ofNat position)).bind fun currentKeyShifted =>
        (TraceResult.sortSliceKeysWrite? currentKeyShifted
          (base + Int.ofNat position) pivot).bind fun keyResult =>
            if true then
              (TraceResult.sortSliceValuesRead? slice
                (base + Int.ofNat ok)).bind fun currentValuePivot =>
                  (SortSlice.memmoveBackwardValuesTraced? (ok - position) slice
                    (base + Int.ofNat (position + 1))
                    (base + Int.ofNat position)).bind fun currentValueShifted =>
                      TraceResult.sortSliceValuesWrite? currentValueShifted
                        (base + Int.ofNat position) currentValuePivot
            else TraceResult.pure keyResult).trace = _
  simp only [TraceResult.trace_bind, hkeyShift, hkeyWrite, if_true,
    hvalueRead, hvalueShift]

/-- One successful outer iteration observes the pivot, the complete search,
the complete shift/insert, and the recursive iteration trace in that order. -/
theorem binarysortLoopTraced_iteration_trace_order
    (fuel : Nat) (state : MergeState κ ν) (slice updated : SortSlice κ ν)
    (base : Int) (n ok : Nat) (pivot : SortSliceEntry κ ν)
    (search : BinarySearchResult)
    (hpivot :
      (TraceResult.sortSliceKeysRead? slice
        (base + Int.ofNat ok)).result = some pivot)
    (hsearch :
      (binarysortSearchTraced? (ok + 1) state.key_compare slice base pivot
        0 ok).result = some search)
    (hsearchFuel : search.fuelExhausted = false)
    (hshift :
      (binarysortShiftInsertTraced? state.a.hasValues slice base ok
        search.position pivot).result = some updated)
    (hactive : ok < n) :
    (binarysortLoopTraced? (fuel + 1) state slice base n ok).trace =
      (TraceResult.sortSliceKeysRead? slice
        (base + Int.ofNat ok)).trace.compose
        ((binarysortSearchTraced? (ok + 1) state.key_compare slice base pivot
          0 ok).trace.compose
          ((binarysortShiftInsertTraced? state.a.hasValues slice base ok
            search.position pivot).trace.compose
            (binarysortLoopTraced? fuel state updated base n
              (ok + 1)).trace)) := by
  change
    (if ok < n then
      (TraceResult.sortSliceKeysRead? slice
        (base + Int.ofNat ok)).bind fun currentPivot =>
          (binarysortSearchTraced? (ok + 1) state.key_compare slice base
            currentPivot 0 ok).bind fun currentSearch =>
              if currentSearch.fuelExhausted then
                TraceResult.pure
                  ({ slice := slice, fuelExhausted := true } :
                    BinarysortResult κ ν)
              else
                (binarysortShiftInsertTraced? state.a.hasValues slice base ok
                  currentSearch.position currentPivot).bind fun currentUpdated =>
                    binarysortLoopTraced? fuel state currentUpdated base n
                      (ok + 1)
    else
      TraceResult.pure
        ({ slice := slice, fuelExhausted := false } :
          BinarysortResult κ ν)).trace = _
  rw [if_pos hactive]
  simp only [TraceResult.trace_bind, hpivot, hsearch, hsearchFuel,
    Bool.false_eq_true, if_false, hshift]

/-! ## Anti-vacuity regressions -/

/-- The synthetic zero-fuel search branch is observably exhausted whenever its
interval is still active. -/
theorem binarysortSearchTraced_zero_active
    (lt : BoolComparator κ) (slice : SortSlice κ ν) (base : Int)
    (pivot : SortSliceEntry κ ν) (left right : Nat) (hactive : left < right) :
    (binarysortSearchTraced? 0 lt slice base pivot left right).result.map
        (fun result => result.fuelExhausted) = some true ∧
      (binarysortSearchTraced? 0 lt slice base pivot left right).trace.fuelExhausted =
        true := by
  simp [binarysortSearchTraced?, hactive, TraceResult.pure,
    TraceResult.markFuelExhausted, AccessTrace.compose, AccessTrace.exhausted]

/-- The synthetic zero-fuel outer-loop branch is likewise observable rather
than a dead match arm. -/
theorem binarysortLoopTraced_zero_active
    (state : MergeState κ ν) (slice : SortSlice κ ν) (base : Int)
    (n ok : Nat) (hactive : ok < n) :
    (binarysortLoopTraced? 0 state slice base n ok).result.map
        (fun result => result.fuelExhausted) = some true ∧
      (binarysortLoopTraced? 0 state slice base n ok).trace.fuelExhausted =
        true := by
  simp [binarysortLoopTraced?, hactive, TraceResult.pure,
    TraceResult.markFuelExhausted, AccessTrace.compose, AccessTrace.exhausted]

private def binarysortRegressionSlice : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 3, value := some 30 },
        { key := 4, value := some 40 },
        { key := 1, value := some 10 }] }

private def binarysortEqualRegressionSlice : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 1, value := some 10 },
        { key := 2, value := some 20 },
        { key := 2, value := some 21 }] }

private def binarysortSingletonRegressionSlice : SortSlice Nat Nat :=
  { entries := #[{ key := 1, value := some 10 }] }

private def binarysortPairRegressionSlice : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 2, value := some 20 },
        { key := 1, value := some 10 }] }

private def binarysortUnkeyedRegressionSlice : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 2, value := none },
        { key := 1, value := none }] }

private def binarysortTaggedEqualRegressionSlice : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 1, value := some 10 },
        { key := 1, value := some 11 },
        { key := 2, value := some 20 },
        { key := 1, value := some 12 }] }

private def binarysortRegressionState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 3
    basekeys := 0
    data := binarysortEqualRegressionSlice
    a := { cells := #[], backing := .inline, hasValues := true }
    alloced := 0
    pending := #[]
    key_compare := fun left right => decide (left < right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

private def binarysortSingletonRegressionState : MergeState Nat Nat :=
  { binarysortRegressionState with
    listlen := 1
    data := binarysortSingletonRegressionSlice }

private def binarysortPairRegressionState : MergeState Nat Nat :=
  { binarysortRegressionState with
    listlen := 2
    data := binarysortPairRegressionSlice }

private def binarysortUnkeyedRegressionState : MergeState Nat Nat :=
  { binarysortRegressionState with
    listlen := 2
    data := binarysortUnkeyedRegressionSlice
    a := { cells := #[], backing := .inline, hasValues := false } }

private def binarysortTaggedEqualRegressionState : MergeState Nat Nat :=
  { binarysortRegressionState with
    listlen := 4
    data := binarysortTaggedEqualRegressionSlice }

/-- The source normalization `ok = 0 ↦ ok = 1` makes a singleton call a
zero-iteration outer loop with an empty trace. -/
theorem binarysort_singleton_ok_zero_regression :
    (binarysortTraced? binarysortSingletonRegressionState
      binarysortSingletonRegressionSlice 0 1 0).result.map
        (fun result => (result.fuelExhausted, result.slice.entries.toList)) =
      some (false, binarysortSingletonRegressionSlice.entries.toList) ∧
    (binarysortTraced? binarysortSingletonRegressionState
      binarysortSingletonRegressionSlice 0 1 0).trace = AccessTrace.empty := by
  decide

/-- The same `ok = 0` normalization on an unsorted pair executes one complete
insertion and returns the sorted key/value pair. -/
theorem binarysort_pair_ok_zero_regression :
    (binarysortTraced? binarysortPairRegressionState
      binarysortPairRegressionSlice 0 2 0).result.map
        (fun result => (result.fuelExhausted, result.slice.entries.toList)) =
      some
        (false,
          [{ key := 1, value := some 10 },
           { key := 2, value := some 20 }]) ∧
    (binarysortTraced? binarysortPairRegressionState
      binarysortPairRegressionSlice 0 2 0).trace.accesses =
      [{ kind := .read, region := .inputKeys, index := 1, extent := 2 },
       { kind := .read, region := .inputKeys, index := 0, extent := 2 },
       { kind := .read, region := .inputKeys, index := 0, extent := 2 },
       { kind := .write, region := .inputKeys, index := 1, extent := 2 },
       { kind := .write, region := .inputKeys, index := 0, extent := 2 },
       { kind := .read, region := .synchronizedValues, index := 1, extent := 2 },
       { kind := .read, region := .synchronizedValues, index := 0, extent := 2 },
       { kind := .write, region := .synchronizedValues, index := 1, extent := 2 },
       { kind := .write, region := .synchronizedValues, index := 0, extent := 2 }] := by
  decide

/-- A raw-domain call whose declared range exceeds the store retains the
failed pivot-read attempt, including its actual one-cell extent. -/
theorem binarysort_oob_attempted_read_regression :
    (binarysortTraced? binarysortSingletonRegressionState
      binarysortSingletonRegressionSlice 0 2 1).result = none ∧
    (binarysortTraced? binarysortSingletonRegressionState
      binarysortSingletonRegressionSlice 0 2 1).trace.accesses =
      [{ kind := .read, region := .inputKeys, index := 1, extent := 1 }] ∧
    ¬(binarysortTraced? binarysortSingletonRegressionState
      binarysortSingletonRegressionSlice 0 2 1).trace.allAccessesInBounds := by
  decide

/-- In the explicit no-values mode a valid full insertion emits only key-array
events; no synchronized-values event is reconstructed from entry payloads. -/
theorem binarysort_unkeyed_no_values_trace_regression :
    (binarysortTraced? binarysortUnkeyedRegressionState
      binarysortUnkeyedRegressionSlice 0 2 0).result.map
        (fun result => (result.fuelExhausted, result.slice.entries.toList)) =
      some
        (false,
          [{ key := 1, value := none },
           { key := 2, value := none }]) ∧
    (binarysortTraced? binarysortUnkeyedRegressionState
      binarysortUnkeyedRegressionSlice 0 2 0).trace.accesses =
      [{ kind := .read, region := .inputKeys, index := 1, extent := 2 },
       { kind := .read, region := .inputKeys, index := 0, extent := 2 },
       { kind := .read, region := .inputKeys, index := 0, extent := 2 },
       { kind := .write, region := .inputKeys, index := 1, extent := 2 },
       { kind := .write, region := .inputKeys, index := 0, extent := 2 }] := by
  decide

/-- A leftmost insertion executes the overlapping shift from the highest cell
to the lowest cell, then performs the pivot write; the complete key phase
precedes the identically ordered synchronized-values phase. -/
theorem binarysort_insert_front_regression :
    (binarysortShiftInsertTraced? true binarysortRegressionSlice 0 2 0
      { key := 1, value := some 10 }).result.map (·.entries.toList) =
        some
          [{ key := 1, value := some 10 },
           { key := 3, value := some 30 },
           { key := 4, value := some 40 }] ∧
      (binarysortShiftInsertTraced? true binarysortRegressionSlice 0 2 0
        { key := 1, value := some 10 }).trace.accesses =
        [{ kind := .read, region := .inputKeys, index := 1, extent := 3 },
         { kind := .write, region := .inputKeys, index := 2, extent := 3 },
         { kind := .read, region := .inputKeys, index := 0, extent := 3 },
         { kind := .write, region := .inputKeys, index := 1, extent := 3 },
         { kind := .write, region := .inputKeys, index := 0, extent := 3 },
         { kind := .read, region := .synchronizedValues, index := 2, extent := 3 },
         { kind := .read, region := .synchronizedValues, index := 1, extent := 3 },
         { kind := .write, region := .synchronizedValues, index := 2, extent := 3 },
         { kind := .read, region := .synchronizedValues, index := 0, extent := 3 },
         { kind := .write, region := .synchronizedValues, index := 1, extent := 3 },
         { kind := .write, region := .synchronizedValues, index := 0, extent := 3 }] := by
  decide

/-- A rightmost insertion has a zero-length shift but still performs the
source's key-pivot write, value-pivot read, and value-pivot write in order. -/
theorem binarysort_insert_end_no_shift_regression :
    (binarysortShiftInsertTraced? true binarysortEqualRegressionSlice 0 2 2
      { key := 2, value := some 21 }).result =
        some binarysortEqualRegressionSlice ∧
      (binarysortShiftInsertTraced? true binarysortEqualRegressionSlice 0 2 2
        { key := 2, value := some 21 }).trace.accesses =
        [{ kind := .write, region := .inputKeys, index := 2, extent := 3 },
         { kind := .read, region := .synchronizedValues, index := 2, extent := 3 },
         { kind := .write, region := .synchronizedValues, index := 2, extent := 3 }] := by
  decide

/-- With tagged equal keys, strict comparison is false and the search takes
the right branch past both older equal entries.  The full sort then shifts a
larger key and inserts the saved equal pivot after the older payloads. -/
theorem binarysort_equal_pivot_stability_regression :
    (binarysortSearchTraced? 4 binarysortTaggedEqualRegressionState.key_compare
      binarysortTaggedEqualRegressionSlice 0 { key := 1, value := some 12 }
      0 3).result.map (fun result =>
        (result.position, result.fuelExhausted)) = some (2, false) ∧
      (binarysortTraced? binarysortTaggedEqualRegressionState
        binarysortTaggedEqualRegressionSlice 0 4 3).result.map
          (fun result => (result.fuelExhausted, result.slice.entries.toList)) =
        some
          (false,
            [{ key := 1, value := some 10 },
             { key := 1, value := some 11 },
             { key := 1, value := some 12 },
             { key := 2, value := some 20 }]) := by
  decide

/-- A concrete assertion-domain rejection fails before any source access and
therefore has the empty trace. -/
theorem binarysort_invalid_guard_regression :
    (binarysortTraced? binarysortSingletonRegressionState
      binarysortSingletonRegressionSlice 0 0 0).result = none ∧
    (binarysortTraced? binarysortSingletonRegressionState
      binarysortSingletonRegressionSlice 0 0 0).trace = AccessTrace.empty := by
  decide

/-- Concrete active calls reach both otherwise synthetic zero-fuel arms and
make exhaustion observable in both the returned status and trace. -/
theorem binarysort_zero_fuel_regression :
    (binarysortSearchTraced? 0 binarysortRegressionState.key_compare
      binarysortEqualRegressionSlice 0 { key := 2, value := some 21 }
      0 1).result.map (·.fuelExhausted) = some true ∧
      (binarysortSearchTraced? 0 binarysortRegressionState.key_compare
        binarysortEqualRegressionSlice 0 { key := 2, value := some 21 }
        0 1).trace.fuelExhausted = true ∧
      (binarysortLoopTraced? 0 binarysortRegressionState
        binarysortEqualRegressionSlice 0 1 0).result.map
          (·.fuelExhausted) = some true ∧
      (binarysortLoopTraced? 0 binarysortRegressionState
        binarysortEqualRegressionSlice 0 1 0).trace.fuelExhausted = true := by
  decide

end CPythonListsort
