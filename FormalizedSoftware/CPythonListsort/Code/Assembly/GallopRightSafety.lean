/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.GallopSafety
import Code.Transcription.MergeLo

/-!
# `gallop_right` safety

This is the public node module for the right-biased gallop.  The proof uses an
explicit equality with the left evaluator under comparator duality; it does
not assume any comparator law, preserves the complete access trace, and
exports that galloping never records a pending-stack push.

The roadmap-facing theorem is source-generic.  Its agreement premise connects
the direct source used for tracing to the reviewed materialized `SortSlice`
call, while temporary reads retain their actual backing and physical index.
-/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- A successfully materialized `merge_lo` active temporary run agrees with
the direct temporary source used by the traced right gallop. -/
theorem tempRun_agreesWithSlice_of_eq_some (storage : TempStorage κ ν)
    (start count : Nat) (slice : SortSlice κ ν)
    (hresult : tempRun? storage start count = some slice) :
    (GallopKeySource.temporary storage (Int.ofNat start)).AgreesWithSlice
      slice 0 count :=
  GallopKeySource.temporary_agreesWithSlice_of_entries storage start count
    slice (tempRun_cells_of_eq_some storage start count slice hresult).2

/-- Public source-generic `gallop_right` safety theorem.

The traced evaluator succeeds without fuel exhaustion, returns an index at
most `n`, emits no pending-stack pushes, records only signed in-bounds and live
accesses, and erases exactly to the agreeing reviewed `gallopRight?`
transcription. -/
theorem gallopRight_safe (state : MergeState κ ν)
    (source : GallopKeySource κ ν) (slice : SortSlice κ ν)
    (sliceBase : Int) (key : κ) (n hint : Nat)
    (hvalid : source.ValidRange n) (hlive : source.Live)
    (hagrees : source.AgreesWithSlice slice sliceBase n)
    (hn : 0 < n) (hhint : hint < n) (hnmax : n ≤ PY_LIST_MAX) :
    ∃ result,
      (gallopRightTraced? state source key n hint).result = some result ∧
      result.fuelExhausted = false ∧
      result.index ≤ n ∧
      (gallopRightTraced? state source key n hint).trace.fuelExhausted = false ∧
      (gallopRightTraced? state source key n hint).trace.pushDepths = [] ∧
      (gallopRightTraced? state source key n hint).trace.allAccessesInBounds ∧
      (gallopRightTraced? state source key n hint).trace.tempPayloadAccessesLive ∧
      (gallopRightTraced? state source key n hint).erase =
        gallopRight? state slice sliceBase key n hint := by
  rcases gallopRightFromSource_safe state source key n hint hvalid hlive hn hhint
      hnmax with
    ⟨result, hresult, hnotExhausted, hbound,
      htraceFuel, htracePushes, htraceBounds, htraceLive⟩
  exact ⟨result, hresult, hnotExhausted, hbound, htraceFuel, htracePushes,
    htraceBounds, htraceLive, erase_gallopRightTraced_eq_slice state source slice
      sliceBase key n hint hvalid hagrees hn hhint hnmax⟩

/-- Main-data convenience form of `gallopRight_safe`. -/
theorem gallopRight_main_safe (state : MergeState κ ν)
    (slice : SortSlice κ ν) (base : Int) (key : κ) (n hint : Nat)
    (hvalid : (GallopKeySource.main slice base).ValidRange n)
    (hn : 0 < n) (hhint : hint < n) (hnmax : n ≤ PY_LIST_MAX) :
    ∃ result,
      (gallopRightTraced? state (.main slice base) key n hint).result =
        some result ∧
      result.fuelExhausted = false ∧
      result.index ≤ n ∧
      (gallopRightTraced? state (.main slice base) key n hint).trace.fuelExhausted =
        false ∧
      (gallopRightTraced? state (.main slice base) key n hint).trace.pushDepths = [] ∧
      (gallopRightTraced? state (.main slice base) key n hint).trace.allAccessesInBounds ∧
      (gallopRightTraced? state (.main slice base) key n hint).trace.tempPayloadAccessesLive ∧
      (gallopRightTraced? state (.main slice base) key n hint).erase =
        gallopRight? state slice base key n hint := by
  exact gallopRight_safe state (.main slice base) slice base key n hint hvalid
    trivial (GallopKeySource.main_agreesWithSlice slice base n) hn hhint hnmax

/-- Temporary-storage convenience form.  Its liveness premise and conclusion
are non-vacuous because the trace records real temporary-payload accesses. -/
theorem gallopRight_temporary_safe (state : MergeState κ ν)
    (storage : TempStorage κ ν) (sourceBase : Int)
    (slice : SortSlice κ ν) (sliceBase : Int) (key : κ) (n hint : Nat)
    (hvalid : (GallopKeySource.temporary storage sourceBase).ValidRange n)
    (hlive : storage.Live)
    (hagrees : (GallopKeySource.temporary storage sourceBase).AgreesWithSlice
      slice sliceBase n)
    (hn : 0 < n) (hhint : hint < n) (hnmax : n ≤ PY_LIST_MAX) :
    let execution :=
      gallopRightTraced? state (.temporary storage sourceBase) key n hint
    ∃ result,
      execution.result = some result ∧
      result.fuelExhausted = false ∧
      result.index ≤ n ∧
      execution.trace.fuelExhausted = false ∧
      execution.trace.pushDepths = [] ∧
      execution.trace.allAccessesInBounds ∧
      execution.trace.tempPayloadAccessesLive ∧
      execution.erase =
        gallopRight? state slice sliceBase key n hint := by
  exact gallopRight_safe state (.temporary storage sourceBase) slice sliceBase
    key n hint hvalid hlive hagrees hn hhint hnmax

end CPythonListsort
