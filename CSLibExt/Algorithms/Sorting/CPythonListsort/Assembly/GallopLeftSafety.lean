/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.GallopSafety
import Code.Transcription.MergeHi

/-!
# `gallop_left` safety

This is the public node module for the left-biased gallop.  Its theorem has no
comparator-law premise.  It combines total execution, non-exhaustion, an empty
pending-push trace, signed trace bounds, temporary-payload liveness, the result
bound, and exact erasure to the reviewed `gallopLeft?` transcription.

The roadmap-facing theorem is source-generic.  Its agreement premise connects
the direct source used for tracing to the reviewed materialized `SortSlice`
call, including temporary-storage calls whose physical backing and index must
remain visible in the trace.
-/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- A successfully materialized `merge_hi` temporary prefix agrees with the
direct temporary source used by the traced left gallop. -/
theorem initializedTempPrefix_agreesWithSlice_of_eq_some
    (storage : TempStorage κ ν) (count : Nat) (slice : SortSlice κ ν)
    (hresult : initializedTempPrefix? storage count = some slice) :
    (GallopKeySource.temporary storage 0).AgreesWithSlice slice 0 count := by
  apply GallopKeySource.temporary_agreesWithSlice_of_entries
    storage 0 count slice
  simpa using
    (initializedTempPrefix_cells_of_eq_some storage count slice hresult).2

/-- Public source-generic `gallop_left` safety theorem.

No consistency, transitivity, totality, or stability law is assumed of
`state.key_compare`.  The traced evaluator succeeds without exhausting either
fuel counter, returns an index at most `n`, emits no pending-stack pushes,
records only signed in-bounds and live accesses, and erases exactly to the
agreeing reviewed `gallopLeft?` call. -/
theorem gallopLeft_safe (state : MergeState κ ν)
    (source : GallopKeySource κ ν) (slice : SortSlice κ ν)
    (sliceBase : Int) (key : κ) (n hint : Nat)
    (hvalid : source.ValidRange n) (hlive : source.Live)
    (hagrees : source.AgreesWithSlice slice sliceBase n)
    (hn : 0 < n) (hhint : hint < n) (hnmax : n ≤ PY_LIST_MAX) :
    ∃ result,
      (gallopLeftTraced? state source key n hint).result = some result ∧
      result.fuelExhausted = false ∧
      result.index ≤ n ∧
      (gallopLeftTraced? state source key n hint).trace.fuelExhausted = false ∧
      (gallopLeftTraced? state source key n hint).trace.pushDepths = [] ∧
      (gallopLeftTraced? state source key n hint).trace.allAccessesInBounds ∧
      (gallopLeftTraced? state source key n hint).trace.tempPayloadAccessesLive ∧
      (gallopLeftTraced? state source key n hint).erase =
        gallopLeft? state slice sliceBase key n hint := by
  rcases gallopLeftFromSource_safe state source key n hint hvalid hlive hn hhint
      hnmax with
    ⟨result, hresult, hnotExhausted, hbound,
      htraceFuel, htracePushes, htraceBounds, htraceLive⟩
  exact ⟨result, hresult, hnotExhausted, hbound, htraceFuel, htracePushes,
    htraceBounds, htraceLive, erase_gallopLeftTraced_eq_slice state source slice
      sliceBase key n hint hvalid hagrees hn hhint hnmax⟩

/-- Main-data convenience form of `gallopLeft_safe`. -/
theorem gallopLeft_main_safe (state : MergeState κ ν)
    (slice : SortSlice κ ν) (base : Int) (key : κ) (n hint : Nat)
    (hvalid : (GallopKeySource.main slice base).ValidRange n)
    (hn : 0 < n) (hhint : hint < n) (hnmax : n ≤ PY_LIST_MAX) :
    ∃ result,
      (gallopLeftTraced? state (.main slice base) key n hint).result =
        some result ∧
      result.fuelExhausted = false ∧
      result.index ≤ n ∧
      (gallopLeftTraced? state (.main slice base) key n hint).trace.fuelExhausted =
        false ∧
      (gallopLeftTraced? state (.main slice base) key n hint).trace.pushDepths = [] ∧
      (gallopLeftTraced? state (.main slice base) key n hint).trace.allAccessesInBounds ∧
      (gallopLeftTraced? state (.main slice base) key n hint).trace.tempPayloadAccessesLive ∧
      (gallopLeftTraced? state (.main slice base) key n hint).erase =
        gallopLeft? state slice base key n hint := by
  exact gallopLeft_safe state (.main slice base) slice base key n hint hvalid
    trivial (GallopKeySource.main_agreesWithSlice slice base n) hn hhint hnmax

/-- Temporary-storage convenience form.  `hlive` is a substantive premise:
the resulting trace contains real temporary-payload events and proves that
none use `.released` backing. -/
theorem gallopLeft_temporary_safe (state : MergeState κ ν)
    (storage : TempStorage κ ν) (sourceBase : Int)
    (slice : SortSlice κ ν) (sliceBase : Int) (key : κ) (n hint : Nat)
    (hvalid : (GallopKeySource.temporary storage sourceBase).ValidRange n)
    (hlive : storage.Live)
    (hagrees : (GallopKeySource.temporary storage sourceBase).AgreesWithSlice
      slice sliceBase n)
    (hn : 0 < n) (hhint : hint < n) (hnmax : n ≤ PY_LIST_MAX) :
    let execution :=
      gallopLeftTraced? state (.temporary storage sourceBase) key n hint
    ∃ result,
      execution.result = some result ∧
      result.fuelExhausted = false ∧
      result.index ≤ n ∧
      execution.trace.fuelExhausted = false ∧
      execution.trace.pushDepths = [] ∧
      execution.trace.allAccessesInBounds ∧
      execution.trace.tempPayloadAccessesLive ∧
      execution.erase =
        gallopLeft? state slice sliceBase key n hint := by
  exact gallopLeft_safe state (.temporary storage sourceBase) slice sliceBase
    key n hint hvalid hlive hagrees hn hhint hnmax

end CPythonListsort
