/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.AccessTrace
import Code.Transcription.Gallop
import Code.Transcription.TempStorageInvariant
import Mathlib

/-!
# Shared traced gallop safety support

The C gallop routines search either the main key array or the temporary key
buffer.  Materializing temporary cells as a ghost `SortSlice` would erase the
backing identity and physical cell index from the access trace, so this module
uses a small source interface whose reads go directly to the represented
storage.

The left- and right-biased public safety theorems live in the adjacent
`GallopLeftSafety` and `GallopRightSafety` modules.  This file contains their
shared source model, traced evaluators, and proof-facing contracts.
-/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- Storage searched by a gallop.  `base` is the physical index corresponding
to logical index zero of the searched run. -/
inductive GallopKeySource (κ : Type u) (ν : Type v) where
  | main (slice : SortSlice κ ν) (base : Int)
  | temporary (storage : TempStorage κ ν) (base : Int)

namespace GallopKeySource

/-- Physical index corresponding to logical index zero. -/
def base : GallopKeySource κ ν → Int
  | .main _ base => base
  | .temporary _ base => base

/-- Number of physical logical cells in the represented storage. -/
def extent : GallopKeySource κ ν → Nat
  | .main slice _ => slice.entries.size
  | .temporary storage _ => storage.cells.size

/-- Untraced direct read at a logical index relative to `base`. -/
def read? (source : GallopKeySource κ ν) (index : Int) :
    Option (SortSliceEntry κ ν) :=
  let physical := source.base + index
  match source with
  | .main slice _ => slice.read? physical
  | .temporary storage _ =>
      if 0 ≤ physical then storage.cells[physical.toNat]?.bind id else none

/-- Traced direct read.  Temporary reads retain the actual backing and the
physical logical-cell index; no temporary slice is materialized. -/
def readTraced? (source : GallopKeySource κ ν) (index : Int) :
    TraceResult (SortSliceEntry κ ν) :=
  let physical := source.base + index
  match source with
  | .main slice _ => TraceResult.sortSliceKeysRead? slice physical
  | .temporary storage _ => TraceResult.tempPayloadRead? storage physical

/-- A searched prefix is physically in bounds and every cell in it is
initialized.  Initialization is automatic for main data and an explicit,
honest premise for temporary storage. -/
def ValidRange (source : GallopKeySource κ ν) (n : Nat) : Prop :=
  0 ≤ source.base ∧
    source.base + Int.ofNat n ≤ Int.ofNat source.extent ∧
    ∀ i < n, ∃ entry, source.read? (Int.ofNat i) = some entry

/-- Temporary backing is live; main data satisfies this vacuously. -/
def Live : GallopKeySource κ ν → Prop
  | .main _ _ => True
  | .temporary storage _ => storage.Live

/-- A direct source presents exactly the same logical keys as a reviewed
`SortSlice` call throughout the searched half-open range `[0, n)`.  The two
bases are intentionally independent: a temporary source can retain its real
physical offset while the materialized transcription slice starts at zero. -/
def AgreesWithSlice (source : GallopKeySource κ ν) (slice : SortSlice κ ν)
    (sliceBase : Int) (n : Nat) : Prop :=
  ∀ index : Int, 0 ≤ index → index < Int.ofNat n →
    source.read? index = slice.read? (sliceBase + index)

/-- Main storage agrees definitionally with the same slice and base. -/
@[simp]
theorem main_agreesWithSlice (slice : SortSlice κ ν) (base : Int) (n : Nat) :
    (GallopKeySource.main slice base).AgreesWithSlice slice base n := by
  intro index _hindexNonnegative _hindexUpper
  rfl

/-- Pointwise use of the reviewed-slice agreement contract. -/
theorem AgreesWithSlice.read_eq (source : GallopKeySource κ ν)
    (slice : SortSlice κ ν) (sliceBase : Int) (n : Nat)
    (hagrees : source.AgreesWithSlice slice sliceBase n) (index : Int)
    (hindexNonnegative : 0 ≤ index) (hindexUpper : index < Int.ofNat n) :
    source.read? index = slice.read? (sliceBase + index) :=
  hagrees index hindexNonnegative hindexUpper

/-- A directly usable constructor for the temporary slices materialized by
`merge_lo` and `merge_hi`: cell-for-cell agreement of the produced entries
discharges the semantic bridge while retaining the storage's real start
index. -/
theorem temporary_agreesWithSlice_of_entries (storage : TempStorage κ ν)
    (start n : Nat) (slice : SortSlice κ ν)
    (hentries : ∀ i < n,
      storage.cells[start + i]?.bind id = slice.entries[i]?) :
    (GallopKeySource.temporary storage (Int.ofNat start)).AgreesWithSlice
      slice 0 n := by
  intro index hindexNonnegative hindexUpper
  let i := index.toNat
  have hindexEq : Int.ofNat i = index := Int.toNat_of_nonneg hindexNonnegative
  have hi : i < n := (Int.toNat_lt hindexNonnegative).2 hindexUpper
  rw [← hindexEq]
  have hphysical : 0 ≤ Int.ofNat start + Int.ofNat i := by
    exact add_nonneg (Int.natCast_nonneg start) (Int.natCast_nonneg i)
  change (if 0 ≤ Int.ofNat start + Int.ofNat i then
      storage.cells[(Int.ofNat start + Int.ofNat i).toNat]?.bind id else none) =
    slice.read? (0 + Int.ofNat i)
  rw [if_pos hphysical]
  have hiNonnegative : 0 ≤ Int.ofNat i := Int.natCast_nonneg i
  simp only [zero_add, SortSlice.read?, if_pos hiNonnegative]
  have hsum : (Int.ofNat start + Int.ofNat i).toNat = start + i := by rfl
  have hitoNat : (Int.ofNat i).toNat = i := rfl
  rw [hsum, hitoNat, hentries i hi]

@[simp]
theorem erase_readTraced (source : GallopKeySource κ ν) (index : Int) :
    (source.readTraced? index).erase = source.read? index := by
  cases source with
  | main slice base => rfl
  | temporary storage base =>
      simp [readTraced?, read?, GallopKeySource.base,
        TraceResult.erase_tempPayloadRead]

@[simp]
theorem trace_readTraced (source : GallopKeySource κ ν) (index : Int) :
    (source.readTraced? index).trace =
      AccessTrace.singletonAccess .read
        (match source with
         | .main _ _ => .inputKeys
         | .temporary storage _ => .tempPayload storage.backing)
        (source.base + index) source.extent := by
  cases source with
  | main slice base => rfl
  | temporary storage base =>
      simp [readTraced?, GallopKeySource.base, GallopKeySource.extent]

/-- A valid logical index has a successful direct read. -/
theorem read_eq_some (source : GallopKeySource κ ν) {n i : Nat}
    (hvalid : source.ValidRange n) (hi : i < n) :
    ∃ entry, source.read? (Int.ofNat i) = some entry :=
  hvalid.2.2 i hi

/-- Every read at a valid logical index emits one in-bounds event. -/
theorem readTraced_inBounds (source : GallopKeySource κ ν) {n i : Nat}
    (hvalid : source.ValidRange n) (hi : i < n) :
    (source.readTraced? (Int.ofNat i)).trace.allAccessesInBounds := by
  rcases hvalid with ⟨hbase, hupper, hreadable⟩
  rw [trace_readTraced]
  simp only [AccessTrace.allAccessesInBounds, AccessTrace.singletonAccess,
    List.mem_singleton, forall_eq, AccessEvent.InBounds]
  constructor
  · have hiInt : Int.ofNat i < Int.ofNat n := Int.ofNat_lt.mpr hi
    have hiNonnegative : 0 ≤ Int.ofNat i := Int.natCast_nonneg i
    omega
  · have hiInt : Int.ofNat i < Int.ofNat n := Int.ofNat_lt.mpr hi
    omega

/-- A direct read from a live source emits no released-backing event. -/
theorem readTraced_live (source : GallopKeySource κ ν) (index : Int)
    (hlive : source.Live) :
    (source.readTraced? index).trace.tempPayloadAccessesLive := by
  rw [trace_readTraced]
  cases source with
  | main slice base => simp [AccessTrace.tempPayloadAccessesLive,
      AccessTrace.singletonAccess, AccessEvent.TempPayloadLive]
  | temporary storage base =>
      simpa [Live, TempStorage.Live, AccessTrace.tempPayloadAccessesLive,
        AccessTrace.singletonAccess, AccessEvent.TempPayloadLive] using hlive

end GallopKeySource

/-! ## Generic untraced evaluators -/

/-- Exponential search to the right for the left-biased gallop. -/
def gallopLeftRightExponentialFromSource? :
    Nat → BoolComparator κ → GallopKeySource κ ν → κ → Nat → Nat → Nat → Nat →
      Option ExponentialResult
  | 0, _, _, _, _, maxOffset, lastOffset, offset =>
      some {
        lastOffset := lastOffset
        offset := offset
        fuelExhausted := decide (offset < maxOffset) }
  | fuel + 1, lt, source, key, hint, maxOffset, lastOffset, offset =>
      if offset < maxOffset then
        gallopBindOptionAcross (source.read? (Int.ofNat (hint + offset))) fun entry =>
          if iflt lt entry.key key then
            if offset ≤ (PY_SSIZE_T_MAX - 1) / 2 then
              gallopLeftRightExponentialFromSource? fuel lt source key hint
                maxOffset offset (2 * offset + 1)
            else none
          else some {
            lastOffset := lastOffset
            offset := offset
            fuelExhausted := false }
      else some {
        lastOffset := lastOffset
        offset := offset
        fuelExhausted := false }

/-- Exponential search to the left for the left-biased gallop. -/
def gallopLeftLeftExponentialFromSource? :
    Nat → BoolComparator κ → GallopKeySource κ ν → κ → Nat → Nat → Nat → Nat →
      Option ExponentialResult
  | 0, _, _, _, _, maxOffset, lastOffset, offset =>
      some {
        lastOffset := lastOffset
        offset := offset
        fuelExhausted := decide (offset < maxOffset) }
  | fuel + 1, lt, source, key, hint, maxOffset, lastOffset, offset =>
      if offset < maxOffset then
        gallopBindOptionAcross (source.read? (Int.ofNat hint - Int.ofNat offset)) fun entry =>
          if iflt lt entry.key key then
            some {
              lastOffset := lastOffset
              offset := offset
              fuelExhausted := false }
          else if offset ≤ (PY_SSIZE_T_MAX - 1) / 2 then
            gallopLeftLeftExponentialFromSource? fuel lt source key hint
              maxOffset offset (2 * offset + 1)
          else none
      else some {
        lastOffset := lastOffset
        offset := offset
        fuelExhausted := false }

/-- Binary finishing phase for the left-biased gallop. -/
def gallopLeftBinaryFromSource? :
    Nat → BoolComparator κ → GallopKeySource κ ν → κ → Nat → Nat →
      Option GallopResult
  | 0, _, _, _, lower, upper =>
      some {
        index := lower
        fuelExhausted := decide (lower < upper) }
  | fuel + 1, lt, source, key, lower, upper =>
      if lower < upper then
        let middle := lower + (upper - lower) / 2
        gallopBindOptionAcross (source.read? (Int.ofNat middle)) fun entry =>
          if iflt lt entry.key key then
            gallopLeftBinaryFromSource? fuel lt source key (middle + 1) upper
          else gallopLeftBinaryFromSource? fuel lt source key lower middle
      else some {
        index := upper
        fuelExhausted := false }

/-- Exponential search to the left for the right-biased gallop. -/
def gallopRightLeftExponentialFromSource? :
    Nat → BoolComparator κ → GallopKeySource κ ν → κ → Nat → Nat → Nat → Nat →
      Option ExponentialResult
  | 0, _, _, _, _, maxOffset, lastOffset, offset =>
      some {
        lastOffset := lastOffset
        offset := offset
        fuelExhausted := decide (offset < maxOffset) }
  | fuel + 1, lt, source, key, hint, maxOffset, lastOffset, offset =>
      if offset < maxOffset then
        gallopBindOptionAcross (source.read? (Int.ofNat hint - Int.ofNat offset)) fun entry =>
          if iflt lt key entry.key then
            if offset ≤ (PY_SSIZE_T_MAX - 1) / 2 then
              gallopRightLeftExponentialFromSource? fuel lt source key hint
                maxOffset offset (2 * offset + 1)
            else none
          else some {
            lastOffset := lastOffset
            offset := offset
            fuelExhausted := false }
      else some {
        lastOffset := lastOffset
        offset := offset
        fuelExhausted := false }

/-- Exponential search to the right for the right-biased gallop. -/
def gallopRightRightExponentialFromSource? :
    Nat → BoolComparator κ → GallopKeySource κ ν → κ → Nat → Nat → Nat → Nat →
      Option ExponentialResult
  | 0, _, _, _, _, maxOffset, lastOffset, offset =>
      some {
        lastOffset := lastOffset
        offset := offset
        fuelExhausted := decide (offset < maxOffset) }
  | fuel + 1, lt, source, key, hint, maxOffset, lastOffset, offset =>
      if offset < maxOffset then
        gallopBindOptionAcross (source.read? (Int.ofNat (hint + offset))) fun entry =>
          if iflt lt key entry.key then
            some {
              lastOffset := lastOffset
              offset := offset
              fuelExhausted := false }
          else if offset ≤ (PY_SSIZE_T_MAX - 1) / 2 then
            gallopRightRightExponentialFromSource? fuel lt source key hint
              maxOffset offset (2 * offset + 1)
          else none
      else some {
        lastOffset := lastOffset
        offset := offset
        fuelExhausted := false }

/-- Binary finishing phase for the right-biased gallop. -/
def gallopRightBinaryFromSource? :
    Nat → BoolComparator κ → GallopKeySource κ ν → κ → Nat → Nat →
      Option GallopResult
  | 0, _, _, _, lower, upper =>
      some {
        index := lower
        fuelExhausted := decide (lower < upper) }
  | fuel + 1, lt, source, key, lower, upper =>
      if lower < upper then
        let middle := lower + (upper - lower) / 2
        gallopBindOptionAcross (source.read? (Int.ofNat middle)) fun entry =>
          if iflt lt key entry.key then
            gallopRightBinaryFromSource? fuel lt source key lower middle
          else gallopRightBinaryFromSource? fuel lt source key (middle + 1) upper
      else some {
        index := upper
        fuelExhausted := false }

/-- Finish the left-biased search after its exponential phase. -/
def finishGallopLeftFromSource? (fuel : Nat) (lt : BoolComparator κ)
    (source : GallopKeySource κ ν) (key : κ) (n : Nat)
    (lastOffset upperOffset : Int) (exponentialFuelExhausted : Bool) :
    Option GallopResult :=
  if -1 ≤ lastOffset ∧ lastOffset < upperOffset ∧ upperOffset ≤ Int.ofNat n then
    let lowerOffset := lastOffset + 1
    if 0 ≤ lowerOffset ∧ 0 ≤ upperOffset then
      let lower := lowerOffset.toNat
      let upper := upperOffset.toNat
      if exponentialFuelExhausted then
        some {
          index := lower
          fuelExhausted := true }
      else gallopLeftBinaryFromSource? fuel lt source key lower upper
    else none
  else none

/-- Finish the right-biased search after its exponential phase. -/
def finishGallopRightFromSource? (fuel : Nat) (lt : BoolComparator κ)
    (source : GallopKeySource κ ν) (key : κ) (n : Nat)
    (lastOffset upperOffset : Int) (exponentialFuelExhausted : Bool) :
    Option GallopResult :=
  if -1 ≤ lastOffset ∧ lastOffset < upperOffset ∧ upperOffset ≤ Int.ofNat n then
    let lowerOffset := lastOffset + 1
    if 0 ≤ lowerOffset ∧ 0 ≤ upperOffset then
      let lower := lowerOffset.toNat
      let upper := upperOffset.toNat
      if exponentialFuelExhausted then
        some {
          index := lower
          fuelExhausted := true }
      else gallopRightBinaryFromSource? fuel lt source key lower upper
    else none
  else none

/-- Left-biased gallop over a direct key source. -/
def gallopLeftFromSource? (state : MergeState κ ν)
    (source : GallopKeySource κ ν) (key : κ) (n hint : Nat) :
    Option GallopResult :=
  if 0 < n ∧ hint < n ∧ n ≤ PY_SSIZE_T_MAX then
    gallopBindOptionAcross (source.read? (Int.ofNat hint)) fun hinted =>
      if iflt state.key_compare hinted.key key then do
        let maxOffset := n - hint
        let exponential ← gallopLeftRightExponentialFromSource? (n + 1)
          state.key_compare source key hint maxOffset 0 1
        let offset := min exponential.offset maxOffset
        finishGallopLeftFromSource? (n + 1) state.key_compare source key n
          (Int.ofNat exponential.lastOffset + Int.ofNat hint)
          (Int.ofNat offset + Int.ofNat hint) exponential.fuelExhausted
      else do
        let maxOffset := hint + 1
        let exponential ← gallopLeftLeftExponentialFromSource? (n + 1)
          state.key_compare source key hint maxOffset 0 1
        let offset := min exponential.offset maxOffset
        finishGallopLeftFromSource? (n + 1) state.key_compare source key n
          (Int.ofNat hint - Int.ofNat offset)
          (Int.ofNat hint - Int.ofNat exponential.lastOffset)
          exponential.fuelExhausted
  else none

/-- Right-biased gallop over a direct key source. -/
def gallopRightFromSource? (state : MergeState κ ν)
    (source : GallopKeySource κ ν) (key : κ) (n hint : Nat) :
    Option GallopResult :=
  if 0 < n ∧ hint < n ∧ n ≤ PY_SSIZE_T_MAX then
    gallopBindOptionAcross (source.read? (Int.ofNat hint)) fun hinted =>
      if iflt state.key_compare key hinted.key then do
        let maxOffset := hint + 1
        let exponential ← gallopRightLeftExponentialFromSource? (n + 1)
          state.key_compare source key hint maxOffset 0 1
        let offset := min exponential.offset maxOffset
        finishGallopRightFromSource? (n + 1) state.key_compare source key n
          (Int.ofNat hint - Int.ofNat offset)
          (Int.ofNat hint - Int.ofNat exponential.lastOffset)
          exponential.fuelExhausted
      else do
        let maxOffset := n - hint
        let exponential ← gallopRightRightExponentialFromSource? (n + 1)
          state.key_compare source key hint maxOffset 0 1
        let offset := min exponential.offset maxOffset
        finishGallopRightFromSource? (n + 1) state.key_compare source key n
          (Int.ofNat exponential.lastOffset + Int.ofNat hint)
          (Int.ofNat offset + Int.ofNat hint) exponential.fuelExhausted
  else none

/-! ## Traced evaluators -/

private def tracedExponentialResult (result : ExponentialResult) :
    TraceResult ExponentialResult :=
  if result.fuelExhausted then
    (TraceResult.pure result).markFuelExhausted
  else TraceResult.pure result

private def tracedGallopResult (result : GallopResult) : TraceResult GallopResult :=
  if result.fuelExhausted then
    (TraceResult.pure result).markFuelExhausted
  else TraceResult.pure result

def gallopLeftRightExponentialTraced? :
    Nat → BoolComparator κ → GallopKeySource κ ν → κ → Nat → Nat → Nat → Nat →
      TraceResult ExponentialResult
  | 0, _, _, _, _, maxOffset, lastOffset, offset =>
      tracedExponentialResult {
        lastOffset := lastOffset
        offset := offset
        fuelExhausted := decide (offset < maxOffset) }
  | fuel + 1, lt, source, key, hint, maxOffset, lastOffset, offset =>
      if offset < maxOffset then
        (source.readTraced? (Int.ofNat (hint + offset))).bind fun entry =>
          if iflt lt entry.key key then
            if offset ≤ (PY_SSIZE_T_MAX - 1) / 2 then
              gallopLeftRightExponentialTraced? fuel lt source key hint
                maxOffset offset (2 * offset + 1)
            else TraceResult.failure
          else TraceResult.pure {
              lastOffset := lastOffset
              offset := offset
              fuelExhausted := false }
      else TraceResult.pure {
          lastOffset := lastOffset
          offset := offset
          fuelExhausted := false }

def gallopLeftLeftExponentialTraced? :
    Nat → BoolComparator κ → GallopKeySource κ ν → κ → Nat → Nat → Nat → Nat →
      TraceResult ExponentialResult
  | 0, _, _, _, _, maxOffset, lastOffset, offset =>
      tracedExponentialResult {
        lastOffset := lastOffset
        offset := offset
        fuelExhausted := decide (offset < maxOffset) }
  | fuel + 1, lt, source, key, hint, maxOffset, lastOffset, offset =>
      if offset < maxOffset then
        (source.readTraced? (Int.ofNat hint - Int.ofNat offset)).bind fun entry =>
          if iflt lt entry.key key then
            TraceResult.pure {
                lastOffset := lastOffset
                offset := offset
                fuelExhausted := false }
          else if offset ≤ (PY_SSIZE_T_MAX - 1) / 2 then
            gallopLeftLeftExponentialTraced? fuel lt source key hint
              maxOffset offset (2 * offset + 1)
          else TraceResult.failure
      else TraceResult.pure {
          lastOffset := lastOffset
          offset := offset
          fuelExhausted := false }

def gallopLeftBinaryTraced? :
    Nat → BoolComparator κ → GallopKeySource κ ν → κ → Nat → Nat →
      TraceResult GallopResult
  | 0, _, _, _, lower, upper =>
      tracedGallopResult {
        index := lower
        fuelExhausted := decide (lower < upper) }
  | fuel + 1, lt, source, key, lower, upper =>
      if lower < upper then
        let middle := lower + (upper - lower) / 2
        (source.readTraced? (Int.ofNat middle)).bind fun entry =>
          if iflt lt entry.key key then
            gallopLeftBinaryTraced? fuel lt source key (middle + 1) upper
          else gallopLeftBinaryTraced? fuel lt source key lower middle
      else TraceResult.pure {
        index := upper
        fuelExhausted := false }

def gallopRightLeftExponentialTraced? :
    Nat → BoolComparator κ → GallopKeySource κ ν → κ → Nat → Nat → Nat → Nat →
      TraceResult ExponentialResult
  | 0, _, _, _, _, maxOffset, lastOffset, offset =>
      tracedExponentialResult {
        lastOffset := lastOffset
        offset := offset
        fuelExhausted := decide (offset < maxOffset) }
  | fuel + 1, lt, source, key, hint, maxOffset, lastOffset, offset =>
      if offset < maxOffset then
        (source.readTraced? (Int.ofNat hint - Int.ofNat offset)).bind fun entry =>
          if iflt lt key entry.key then
            if offset ≤ (PY_SSIZE_T_MAX - 1) / 2 then
              gallopRightLeftExponentialTraced? fuel lt source key hint
                maxOffset offset (2 * offset + 1)
            else TraceResult.failure
          else TraceResult.pure {
              lastOffset := lastOffset
              offset := offset
              fuelExhausted := false }
      else TraceResult.pure {
          lastOffset := lastOffset
          offset := offset
          fuelExhausted := false }

def gallopRightRightExponentialTraced? :
    Nat → BoolComparator κ → GallopKeySource κ ν → κ → Nat → Nat → Nat → Nat →
      TraceResult ExponentialResult
  | 0, _, _, _, _, maxOffset, lastOffset, offset =>
      tracedExponentialResult {
        lastOffset := lastOffset
        offset := offset
        fuelExhausted := decide (offset < maxOffset) }
  | fuel + 1, lt, source, key, hint, maxOffset, lastOffset, offset =>
      if offset < maxOffset then
        (source.readTraced? (Int.ofNat (hint + offset))).bind fun entry =>
          if iflt lt key entry.key then
            TraceResult.pure {
                lastOffset := lastOffset
                offset := offset
                fuelExhausted := false }
          else if offset ≤ (PY_SSIZE_T_MAX - 1) / 2 then
            gallopRightRightExponentialTraced? fuel lt source key hint
              maxOffset offset (2 * offset + 1)
          else TraceResult.failure
      else TraceResult.pure {
          lastOffset := lastOffset
          offset := offset
          fuelExhausted := false }

def gallopRightBinaryTraced? :
    Nat → BoolComparator κ → GallopKeySource κ ν → κ → Nat → Nat →
      TraceResult GallopResult
  | 0, _, _, _, lower, upper =>
      tracedGallopResult {
        index := lower
        fuelExhausted := decide (lower < upper) }
  | fuel + 1, lt, source, key, lower, upper =>
      if lower < upper then
        let middle := lower + (upper - lower) / 2
        (source.readTraced? (Int.ofNat middle)).bind fun entry =>
          if iflt lt key entry.key then
            gallopRightBinaryTraced? fuel lt source key lower middle
          else gallopRightBinaryTraced? fuel lt source key (middle + 1) upper
      else TraceResult.pure {
        index := upper
        fuelExhausted := false }

def finishGallopLeftTraced? (fuel : Nat) (lt : BoolComparator κ)
    (source : GallopKeySource κ ν) (key : κ) (n : Nat)
    (lastOffset upperOffset : Int) (exponentialFuelExhausted : Bool) :
    TraceResult GallopResult :=
  if -1 ≤ lastOffset ∧ lastOffset < upperOffset ∧ upperOffset ≤ Int.ofNat n then
    let lowerOffset := lastOffset + 1
    if 0 ≤ lowerOffset ∧ 0 ≤ upperOffset then
      let lower := lowerOffset.toNat
      let upper := upperOffset.toNat
      if exponentialFuelExhausted then
        tracedGallopResult {
          index := lower
          fuelExhausted := true }
      else gallopLeftBinaryTraced? fuel lt source key lower upper
    else TraceResult.failure
  else TraceResult.failure

def finishGallopRightTraced? (fuel : Nat) (lt : BoolComparator κ)
    (source : GallopKeySource κ ν) (key : κ) (n : Nat)
    (lastOffset upperOffset : Int) (exponentialFuelExhausted : Bool) :
    TraceResult GallopResult :=
  if -1 ≤ lastOffset ∧ lastOffset < upperOffset ∧ upperOffset ≤ Int.ofNat n then
    let lowerOffset := lastOffset + 1
    if 0 ≤ lowerOffset ∧ 0 ≤ upperOffset then
      let lower := lowerOffset.toNat
      let upper := upperOffset.toNat
      if exponentialFuelExhausted then
        tracedGallopResult {
          index := lower
          fuelExhausted := true }
      else gallopRightBinaryTraced? fuel lt source key lower upper
    else TraceResult.failure
  else TraceResult.failure

/-- Traced left-biased gallop over either main or temporary storage. -/
def gallopLeftTraced? (state : MergeState κ ν)
    (source : GallopKeySource κ ν) (key : κ) (n hint : Nat) :
    TraceResult GallopResult :=
  if 0 < n ∧ hint < n ∧ n ≤ PY_SSIZE_T_MAX then
    (source.readTraced? (Int.ofNat hint)).bind fun hinted =>
      if iflt state.key_compare hinted.key key then
        (gallopLeftRightExponentialTraced? (n + 1) state.key_compare source key hint
          (n - hint) 0 1).bind fun exponential =>
            let offset := min exponential.offset (n - hint)
            finishGallopLeftTraced? (n + 1) state.key_compare source key n
              (Int.ofNat exponential.lastOffset + Int.ofNat hint)
              (Int.ofNat offset + Int.ofNat hint) exponential.fuelExhausted
      else
        (gallopLeftLeftExponentialTraced? (n + 1) state.key_compare source key hint
          (hint + 1) 0 1).bind fun exponential =>
            let offset := min exponential.offset (hint + 1)
            finishGallopLeftTraced? (n + 1) state.key_compare source key n
              (Int.ofNat hint - Int.ofNat offset)
              (Int.ofNat hint - Int.ofNat exponential.lastOffset)
              exponential.fuelExhausted
  else TraceResult.failure

/-- Traced right-biased gallop over either main or temporary storage. -/
def gallopRightTraced? (state : MergeState κ ν)
    (source : GallopKeySource κ ν) (key : κ) (n hint : Nat) :
    TraceResult GallopResult :=
  if 0 < n ∧ hint < n ∧ n ≤ PY_SSIZE_T_MAX then
    (source.readTraced? (Int.ofNat hint)).bind fun hinted =>
      if iflt state.key_compare key hinted.key then
        (gallopRightLeftExponentialTraced? (n + 1) state.key_compare source key hint
          (hint + 1) 0 1).bind fun exponential =>
            let offset := min exponential.offset (hint + 1)
            finishGallopRightTraced? (n + 1) state.key_compare source key n
              (Int.ofNat hint - Int.ofNat offset)
              (Int.ofNat hint - Int.ofNat exponential.lastOffset)
              exponential.fuelExhausted
      else
        (gallopRightRightExponentialTraced? (n + 1) state.key_compare source key hint
          (n - hint) 0 1).bind fun exponential =>
            let offset := min exponential.offset (n - hint)
            finishGallopRightTraced? (n + 1) state.key_compare source key n
              (Int.ofNat exponential.lastOffset + Int.ofNat hint)
              (Int.ofNat offset + Int.ofNat hint) exponential.fuelExhausted
  else TraceResult.failure

/-! ## Absence of merge-memory boundary and merge-policy events

Gallops read either the main keys or the live temporary payload, but they do
not cross a `merge_init`, `merge_getmem`, directional-merge, or
`merge_freemem` boundary.  The helper inductions below cover the complete
traced evaluators, including rejected reads, arithmetic-guard failures, and
fuel-exhausted results. -/

/-- Internal proof-facing shorthand for a trace fragment that emits no
merge-memory boundary or merge-policy event. -/
private def GallopMemoryEventFree (execution : TraceResult α) : Prop :=
  execution.trace.memoryEvents = [] ∧ execution.trace.policyEvents = []

private theorem gallopMemoryEventFree_pure (value : α) :
    GallopMemoryEventFree (TraceResult.pure value) := by
  exact ⟨rfl, rfl⟩

private theorem gallopMemoryEventFree_failure :
    GallopMemoryEventFree (TraceResult.failure : TraceResult α) := by
  exact ⟨rfl, rfl⟩

private theorem gallopMemoryEventFree_bind (current : TraceResult α)
    (next : α → TraceResult β) (hcurrent : GallopMemoryEventFree current)
    (hnext : ∀ value, GallopMemoryEventFree (next value)) :
    GallopMemoryEventFree (current.bind next) := by
  exact
    ⟨TraceResult.memoryEvents_bind_eq_nil current next hcurrent.1
        (fun value => (hnext value).1),
      TraceResult.policyEvents_bind_eq_nil current next hcurrent.2
        (fun value => (hnext value).2)⟩

private theorem gallopMemoryEventFree_sourceRead
    (source : GallopKeySource κ ν) (index : Int) :
    GallopMemoryEventFree (source.readTraced? index) := by
  simp [GallopMemoryEventFree, GallopKeySource.trace_readTraced,
    AccessTrace.singletonAccess]

set_option linter.flexible false in
private theorem gallopMemoryEventFree_leftRightExponential
    (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
    (key : κ) (hint maxOffset lastOffset offset : Nat) :
    GallopMemoryEventFree
      (gallopLeftRightExponentialTraced? fuel lt source key hint maxOffset
        lastOffset offset) := by
  induction fuel generalizing lastOffset offset with
  | zero =>
      by_cases hfuel : offset < maxOffset <;>
        simp [gallopLeftRightExponentialTraced?, GallopMemoryEventFree,
          hfuel] <;> (constructor <;> rfl)
  | succ fuel ih =>
      simp only [gallopLeftRightExponentialTraced?]
      split
      · apply gallopMemoryEventFree_bind
        · exact gallopMemoryEventFree_sourceRead _ _
        · intro entry
          split
          · split
            · exact ih _ _
            · exact gallopMemoryEventFree_failure
          · exact gallopMemoryEventFree_pure _
      · exact gallopMemoryEventFree_pure _

set_option linter.flexible false in
private theorem gallopMemoryEventFree_leftLeftExponential
    (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
    (key : κ) (hint maxOffset lastOffset offset : Nat) :
    GallopMemoryEventFree
      (gallopLeftLeftExponentialTraced? fuel lt source key hint maxOffset
        lastOffset offset) := by
  induction fuel generalizing lastOffset offset with
  | zero =>
      by_cases hfuel : offset < maxOffset <;>
        simp [gallopLeftLeftExponentialTraced?, GallopMemoryEventFree,
          hfuel] <;> (constructor <;> rfl)
  | succ fuel ih =>
      simp only [gallopLeftLeftExponentialTraced?]
      split
      · apply gallopMemoryEventFree_bind
        · exact gallopMemoryEventFree_sourceRead _ _
        · intro entry
          split
          · exact gallopMemoryEventFree_pure _
          · split
            · exact ih _ _
            · exact gallopMemoryEventFree_failure
      · exact gallopMemoryEventFree_pure _

set_option linter.flexible false in
private theorem gallopMemoryEventFree_rightLeftExponential
    (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
    (key : κ) (hint maxOffset lastOffset offset : Nat) :
    GallopMemoryEventFree
      (gallopRightLeftExponentialTraced? fuel lt source key hint maxOffset
        lastOffset offset) := by
  induction fuel generalizing lastOffset offset with
  | zero =>
      by_cases hfuel : offset < maxOffset <;>
        simp [gallopRightLeftExponentialTraced?, GallopMemoryEventFree,
          hfuel] <;> (constructor <;> rfl)
  | succ fuel ih =>
      simp only [gallopRightLeftExponentialTraced?]
      split
      · apply gallopMemoryEventFree_bind
        · exact gallopMemoryEventFree_sourceRead _ _
        · intro entry
          split
          · split
            · exact ih _ _
            · exact gallopMemoryEventFree_failure
          · exact gallopMemoryEventFree_pure _
      · exact gallopMemoryEventFree_pure _

set_option linter.flexible false in
private theorem gallopMemoryEventFree_rightRightExponential
    (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
    (key : κ) (hint maxOffset lastOffset offset : Nat) :
    GallopMemoryEventFree
      (gallopRightRightExponentialTraced? fuel lt source key hint maxOffset
        lastOffset offset) := by
  induction fuel generalizing lastOffset offset with
  | zero =>
      by_cases hfuel : offset < maxOffset <;>
        simp [gallopRightRightExponentialTraced?, GallopMemoryEventFree,
          hfuel] <;> (constructor <;> rfl)
  | succ fuel ih =>
      simp only [gallopRightRightExponentialTraced?]
      split
      · apply gallopMemoryEventFree_bind
        · exact gallopMemoryEventFree_sourceRead _ _
        · intro entry
          split
          · exact gallopMemoryEventFree_pure _
          · split
            · exact ih _ _
            · exact gallopMemoryEventFree_failure
      · exact gallopMemoryEventFree_pure _

set_option linter.flexible false in
private theorem gallopMemoryEventFree_leftBinary
    (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
    (key : κ) (lower upper : Nat) :
    GallopMemoryEventFree
      (gallopLeftBinaryTraced? fuel lt source key lower upper) := by
  induction fuel generalizing lower upper with
  | zero =>
      by_cases hfuel : lower < upper <;>
        simp [gallopLeftBinaryTraced?, GallopMemoryEventFree, hfuel] <;>
          (constructor <;> rfl)
  | succ fuel ih =>
      simp only [gallopLeftBinaryTraced?]
      split
      · apply gallopMemoryEventFree_bind
        · exact gallopMemoryEventFree_sourceRead _ _
        · intro entry
          split <;> exact ih _ _
      · exact gallopMemoryEventFree_pure _

set_option linter.flexible false in
private theorem gallopMemoryEventFree_rightBinary
    (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
    (key : κ) (lower upper : Nat) :
    GallopMemoryEventFree
      (gallopRightBinaryTraced? fuel lt source key lower upper) := by
  induction fuel generalizing lower upper with
  | zero =>
      by_cases hfuel : lower < upper <;>
        simp [gallopRightBinaryTraced?, GallopMemoryEventFree, hfuel] <;>
          (constructor <;> rfl)
  | succ fuel ih =>
      simp only [gallopRightBinaryTraced?]
      split
      · apply gallopMemoryEventFree_bind
        · exact gallopMemoryEventFree_sourceRead _ _
        · intro entry
          split <;> exact ih _ _
      · exact gallopMemoryEventFree_pure _

private theorem gallopMemoryEventFree_finishLeft
    (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
    (key : κ) (n : Nat) (lastOffset upperOffset : Int)
    (exponentialFuelExhausted : Bool) :
    GallopMemoryEventFree
      (finishGallopLeftTraced? fuel lt source key n lastOffset upperOffset
        exponentialFuelExhausted) := by
  unfold finishGallopLeftTraced?
  split
  · dsimp only
    split
    · split
      · constructor <;> rfl
      · exact gallopMemoryEventFree_leftBinary _ _ _ _ _ _
    · exact gallopMemoryEventFree_failure
  · exact gallopMemoryEventFree_failure

private theorem gallopMemoryEventFree_finishRight
    (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
    (key : κ) (n : Nat) (lastOffset upperOffset : Int)
    (exponentialFuelExhausted : Bool) :
    GallopMemoryEventFree
      (finishGallopRightTraced? fuel lt source key n lastOffset upperOffset
        exponentialFuelExhausted) := by
  unfold finishGallopRightTraced?
  split
  · dsimp only
    split
    · split
      · constructor <;> rfl
      · exact gallopMemoryEventFree_rightBinary _ _ _ _ _ _
    · exact gallopMemoryEventFree_failure
  · exact gallopMemoryEventFree_failure

private theorem gallopLeftTraced_topLevelEvents_eq_nil (state : MergeState κ ν)
    (source : GallopKeySource κ ν) (key : κ) (n hint : Nat) :
    GallopMemoryEventFree (gallopLeftTraced? state source key n hint) := by
  unfold gallopLeftTraced?
  split
  · apply gallopMemoryEventFree_bind
    · exact gallopMemoryEventFree_sourceRead _ _
    · intro hinted
      split
      · apply gallopMemoryEventFree_bind
        · exact gallopMemoryEventFree_leftRightExponential _ _ _ _ _ _ _ _
        · intro exponential
          exact gallopMemoryEventFree_finishLeft _ _ _ _ _ _ _ _
      · apply gallopMemoryEventFree_bind
        · exact gallopMemoryEventFree_leftLeftExponential _ _ _ _ _ _ _ _
        · intro exponential
          exact gallopMemoryEventFree_finishLeft _ _ _ _ _ _ _ _
  · exact gallopMemoryEventFree_failure

private theorem gallopRightTraced_topLevelEvents_eq_nil (state : MergeState κ ν)
    (source : GallopKeySource κ ν) (key : κ) (n hint : Nat) :
    GallopMemoryEventFree (gallopRightTraced? state source key n hint) := by
  unfold gallopRightTraced?
  split
  · apply gallopMemoryEventFree_bind
    · exact gallopMemoryEventFree_sourceRead _ _
    · intro hinted
      split
      · apply gallopMemoryEventFree_bind
        · exact gallopMemoryEventFree_rightLeftExponential _ _ _ _ _ _ _ _
        · intro exponential
          exact gallopMemoryEventFree_finishRight _ _ _ _ _ _ _ _
      · apply gallopMemoryEventFree_bind
        · exact gallopMemoryEventFree_rightRightExponential _ _ _ _ _ _ _ _
        · intro exponential
          exact gallopMemoryEventFree_finishRight _ _ _ _ _ _ _ _
  · exact gallopMemoryEventFree_failure

/-- Every left-biased gallop execution emits no merge-memory boundary events.
This is unconditional: it includes invalid-input failure, failed reads,
arithmetic-guard failure, and either exponential or binary fuel exhaustion. -/
theorem gallopLeftTraced_memoryEvents_eq_nil (state : MergeState κ ν)
    (source : GallopKeySource κ ν) (key : κ) (n hint : Nat) :
    (gallopLeftTraced? state source key n hint).trace.memoryEvents = [] :=
  (gallopLeftTraced_topLevelEvents_eq_nil state source key n hint).1

/-- Every left-biased gallop execution emits no merge-policy event. -/
theorem gallopLeftTraced_policyEvents_eq_nil (state : MergeState κ ν)
    (source : GallopKeySource κ ν) (key : κ) (n hint : Nat) :
    (gallopLeftTraced? state source key n hint).trace.policyEvents = [] :=
  (gallopLeftTraced_topLevelEvents_eq_nil state source key n hint).2

/-- Every right-biased gallop execution emits no merge-memory boundary events.
This is unconditional: it includes invalid-input failure, failed reads,
arithmetic-guard failure, and either exponential or binary fuel exhaustion. -/
theorem gallopRightTraced_memoryEvents_eq_nil (state : MergeState κ ν)
    (source : GallopKeySource κ ν) (key : κ) (n hint : Nat) :
    (gallopRightTraced? state source key n hint).trace.memoryEvents = [] :=
  (gallopRightTraced_topLevelEvents_eq_nil state source key n hint).1

/-- Every right-biased gallop execution emits no merge-policy event. -/
theorem gallopRightTraced_policyEvents_eq_nil (state : MergeState κ ν)
    (source : GallopKeySource κ ν) (key : κ) (n hint : Nat) :
    (gallopRightTraced? state source key n hint).trace.policyEvents = [] :=
  (gallopRightTraced_topLevelEvents_eq_nil state source key n hint).2

/-! ## Exact erasure -/

/-- `TraceResult.bind` erases to the same explicit `Option` sequencing used by
the reviewed gallop transcription. -/
@[simp]
theorem TraceResult.erase_bind_gallop (current : TraceResult α)
    (next : α → TraceResult β) :
    (current.bind next).erase =
      gallopBindOptionAcross current.erase (fun value => (next value).erase) := by
  cases current with
  | mk result trace => cases result <;> rfl

@[simp]
private theorem erase_tracedExponentialResult (result : ExponentialResult) :
    (tracedExponentialResult result).erase = some result := by
  cases h : result.fuelExhausted <;>
    simp [tracedExponentialResult, h]

@[simp]
private theorem erase_tracedGallopResult (result : GallopResult) :
    (tracedGallopResult result).erase = some result := by
  cases h : result.fuelExhausted <;>
    simp [tracedGallopResult, h]

@[simp]
theorem erase_gallopLeftRightExponentialTraced (fuel : Nat)
    (lt : BoolComparator κ) (source : GallopKeySource κ ν) (key : κ)
    (hint maxOffset lastOffset offset : Nat) :
    (gallopLeftRightExponentialTraced? fuel lt source key hint maxOffset
      lastOffset offset).erase =
      gallopLeftRightExponentialFromSource? fuel lt source key hint maxOffset
        lastOffset offset := by
  induction fuel generalizing lastOffset offset with
  | zero => simp [gallopLeftRightExponentialTraced?,
      gallopLeftRightExponentialFromSource?]
  | succ fuel ih =>
      simp only [gallopLeftRightExponentialTraced?,
        gallopLeftRightExponentialFromSource?]
      split
      · rw [TraceResult.erase_bind_gallop, GallopKeySource.erase_readTraced]
        apply congrArg
          (gallopBindOptionAcross
            (source.read? (Int.ofNat hint + Int.ofNat offset)))
        funext entry
        by_cases hcompare : lt entry.key key = true
        · by_cases hguard : offset ≤ (PY_SSIZE_T_MAX - 1) / 2 <;>
            simp [hcompare, hguard, ih]
        · simp [hcompare]
      · simp

@[simp]
theorem erase_gallopLeftLeftExponentialTraced (fuel : Nat)
    (lt : BoolComparator κ) (source : GallopKeySource κ ν) (key : κ)
    (hint maxOffset lastOffset offset : Nat) :
    (gallopLeftLeftExponentialTraced? fuel lt source key hint maxOffset
      lastOffset offset).erase =
      gallopLeftLeftExponentialFromSource? fuel lt source key hint maxOffset
        lastOffset offset := by
  induction fuel generalizing lastOffset offset with
  | zero => simp [gallopLeftLeftExponentialTraced?,
      gallopLeftLeftExponentialFromSource?]
  | succ fuel ih =>
      simp only [gallopLeftLeftExponentialTraced?,
        gallopLeftLeftExponentialFromSource?]
      split
      · rw [TraceResult.erase_bind_gallop, GallopKeySource.erase_readTraced]
        apply congrArg
          (gallopBindOptionAcross
            (source.read? (Int.ofNat hint - Int.ofNat offset)))
        funext entry
        by_cases hcompare : lt entry.key key = true
        · simp [hcompare]
        · by_cases hguard : offset ≤ (PY_SSIZE_T_MAX - 1) / 2 <;>
            simp [hcompare, hguard, ih]
      · simp

@[simp]
theorem erase_gallopLeftBinaryTraced (fuel : Nat)
    (lt : BoolComparator κ) (source : GallopKeySource κ ν) (key : κ)
    (lower upper : Nat) :
    (gallopLeftBinaryTraced? fuel lt source key lower upper).erase =
      gallopLeftBinaryFromSource? fuel lt source key lower upper := by
  induction fuel generalizing lower upper with
  | zero => simp [gallopLeftBinaryTraced?, gallopLeftBinaryFromSource?]
  | succ fuel ih =>
      simp only [gallopLeftBinaryTraced?, gallopLeftBinaryFromSource?]
      split
      · let middle := lower + (upper - lower) / 2
        rw [TraceResult.erase_bind_gallop, GallopKeySource.erase_readTraced]
        apply congrArg (gallopBindOptionAcross (source.read? (Int.ofNat middle)))
        funext entry
        by_cases hcompare : lt entry.key key = true <;> simp [hcompare, ih]
      · simp

@[simp]
theorem erase_gallopRightLeftExponentialTraced (fuel : Nat)
    (lt : BoolComparator κ) (source : GallopKeySource κ ν) (key : κ)
    (hint maxOffset lastOffset offset : Nat) :
    (gallopRightLeftExponentialTraced? fuel lt source key hint maxOffset
      lastOffset offset).erase =
      gallopRightLeftExponentialFromSource? fuel lt source key hint maxOffset
        lastOffset offset := by
  induction fuel generalizing lastOffset offset with
  | zero => simp [gallopRightLeftExponentialTraced?,
      gallopRightLeftExponentialFromSource?]
  | succ fuel ih =>
      simp only [gallopRightLeftExponentialTraced?,
        gallopRightLeftExponentialFromSource?]
      split
      · rw [TraceResult.erase_bind_gallop, GallopKeySource.erase_readTraced]
        apply congrArg
          (gallopBindOptionAcross
            (source.read? (Int.ofNat hint - Int.ofNat offset)))
        funext entry
        by_cases hcompare : lt key entry.key = true
        · by_cases hguard : offset ≤ (PY_SSIZE_T_MAX - 1) / 2 <;>
            simp [hcompare, hguard, ih]
        · simp [hcompare]
      · simp

@[simp]
theorem erase_gallopRightRightExponentialTraced (fuel : Nat)
    (lt : BoolComparator κ) (source : GallopKeySource κ ν) (key : κ)
    (hint maxOffset lastOffset offset : Nat) :
    (gallopRightRightExponentialTraced? fuel lt source key hint maxOffset
      lastOffset offset).erase =
      gallopRightRightExponentialFromSource? fuel lt source key hint maxOffset
        lastOffset offset := by
  induction fuel generalizing lastOffset offset with
  | zero => simp [gallopRightRightExponentialTraced?,
      gallopRightRightExponentialFromSource?]
  | succ fuel ih =>
      simp only [gallopRightRightExponentialTraced?,
        gallopRightRightExponentialFromSource?]
      split
      · rw [TraceResult.erase_bind_gallop, GallopKeySource.erase_readTraced]
        apply congrArg
          (gallopBindOptionAcross
            (source.read? (Int.ofNat hint + Int.ofNat offset)))
        funext entry
        by_cases hcompare : lt key entry.key = true
        · simp [hcompare]
        · by_cases hguard : offset ≤ (PY_SSIZE_T_MAX - 1) / 2 <;>
            simp [hcompare, hguard, ih]
      · simp

@[simp]
theorem erase_gallopRightBinaryTraced (fuel : Nat)
    (lt : BoolComparator κ) (source : GallopKeySource κ ν) (key : κ)
    (lower upper : Nat) :
    (gallopRightBinaryTraced? fuel lt source key lower upper).erase =
      gallopRightBinaryFromSource? fuel lt source key lower upper := by
  induction fuel generalizing lower upper with
  | zero => simp [gallopRightBinaryTraced?, gallopRightBinaryFromSource?]
  | succ fuel ih =>
      simp only [gallopRightBinaryTraced?, gallopRightBinaryFromSource?]
      split
      · let middle := lower + (upper - lower) / 2
        rw [TraceResult.erase_bind_gallop, GallopKeySource.erase_readTraced]
        apply congrArg (gallopBindOptionAcross (source.read? (Int.ofNat middle)))
        funext entry
        by_cases hcompare : lt key entry.key = true <;> simp [hcompare, ih]
      · simp

@[simp]
theorem erase_finishGallopLeftTraced (fuel : Nat) (lt : BoolComparator κ)
    (source : GallopKeySource κ ν) (key : κ) (n : Nat)
    (lastOffset upperOffset : Int) (exhausted : Bool) :
    (finishGallopLeftTraced? fuel lt source key n lastOffset upperOffset
      exhausted).erase =
      finishGallopLeftFromSource? fuel lt source key n lastOffset upperOffset
        exhausted := by
  by_cases houter :
      -1 ≤ lastOffset ∧ lastOffset < upperOffset ∧
        upperOffset ≤ Int.ofNat n
  · by_cases hinner : 0 ≤ lastOffset + 1 ∧ 0 ≤ upperOffset
    · unfold finishGallopLeftTraced? finishGallopLeftFromSource?
      rw [if_pos houter, if_pos houter]
      rw [if_pos hinner, if_pos hinner]
      cases exhausted <;> simp
    · unfold finishGallopLeftTraced? finishGallopLeftFromSource?
      rw [if_pos houter, if_pos houter]
      dsimp only
      rw [if_neg hinner, if_neg hinner]
      rfl
  · unfold finishGallopLeftTraced? finishGallopLeftFromSource?
    rw [if_neg houter, if_neg houter]
    rfl

@[simp]
theorem erase_finishGallopRightTraced (fuel : Nat) (lt : BoolComparator κ)
    (source : GallopKeySource κ ν) (key : κ) (n : Nat)
    (lastOffset upperOffset : Int) (exhausted : Bool) :
    (finishGallopRightTraced? fuel lt source key n lastOffset upperOffset
      exhausted).erase =
      finishGallopRightFromSource? fuel lt source key n lastOffset upperOffset
        exhausted := by
  by_cases houter :
      -1 ≤ lastOffset ∧ lastOffset < upperOffset ∧
        upperOffset ≤ Int.ofNat n
  · by_cases hinner : 0 ≤ lastOffset + 1 ∧ 0 ≤ upperOffset
    · unfold finishGallopRightTraced? finishGallopRightFromSource?
      rw [if_pos houter, if_pos houter]
      rw [if_pos hinner, if_pos hinner]
      cases exhausted <;> simp
    · unfold finishGallopRightTraced? finishGallopRightFromSource?
      rw [if_pos houter, if_pos houter]
      dsimp only
      rw [if_neg hinner, if_neg hinner]
      rfl
  · unfold finishGallopRightTraced? finishGallopRightFromSource?
    rw [if_neg houter, if_neg houter]
    rfl

/-- Erasing the generic traced left gallop gives the direct-source evaluator. -/
@[simp]
theorem erase_gallopLeftTraced (state : MergeState κ ν)
    (source : GallopKeySource κ ν) (key : κ) (n hint : Nat) :
    (gallopLeftTraced? state source key n hint).erase =
      gallopLeftFromSource? state source key n hint := by
  by_cases hinput : 0 < n ∧ hint < n ∧ n ≤ PY_SSIZE_T_MAX
  · unfold gallopLeftTraced? gallopLeftFromSource?
    rw [if_pos hinput, if_pos hinput]
    rw [TraceResult.erase_bind_gallop, GallopKeySource.erase_readTraced]
    apply congrArg
      (gallopBindOptionAcross (source.read? (Int.ofNat hint)))
    funext hinted
    by_cases hcompare : iflt state.key_compare hinted.key key = true
    · rw [if_pos hcompare, if_pos hcompare]
      rw [TraceResult.erase_bind_gallop,
        erase_gallopLeftRightExponentialTraced]
      cases hphase : gallopLeftRightExponentialFromSource? (n + 1)
          state.key_compare source key hint (n - hint) 0 1 <;>
        simp [gallopBindOptionAcross, hphase]
    · rw [if_neg hcompare, if_neg hcompare]
      rw [TraceResult.erase_bind_gallop,
        erase_gallopLeftLeftExponentialTraced]
      cases hphase : gallopLeftLeftExponentialFromSource? (n + 1)
          state.key_compare source key hint (hint + 1) 0 1 <;>
        simp [gallopBindOptionAcross, hphase]
  · simp [gallopLeftTraced?, gallopLeftFromSource?, hinput]

/-- Erasing the generic traced right gallop gives the direct-source evaluator. -/
@[simp]
theorem erase_gallopRightTraced (state : MergeState κ ν)
    (source : GallopKeySource κ ν) (key : κ) (n hint : Nat) :
    (gallopRightTraced? state source key n hint).erase =
      gallopRightFromSource? state source key n hint := by
  by_cases hinput : 0 < n ∧ hint < n ∧ n ≤ PY_SSIZE_T_MAX
  · unfold gallopRightTraced? gallopRightFromSource?
    rw [if_pos hinput, if_pos hinput]
    rw [TraceResult.erase_bind_gallop, GallopKeySource.erase_readTraced]
    apply congrArg
      (gallopBindOptionAcross (source.read? (Int.ofNat hint)))
    funext hinted
    by_cases hcompare : iflt state.key_compare key hinted.key = true
    · rw [if_pos hcompare, if_pos hcompare]
      rw [TraceResult.erase_bind_gallop,
        erase_gallopRightLeftExponentialTraced]
      cases hphase : gallopRightLeftExponentialFromSource? (n + 1)
          state.key_compare source key hint (hint + 1) 0 1 <;>
        simp [gallopBindOptionAcross, hphase]
    · rw [if_neg hcompare, if_neg hcompare]
      rw [TraceResult.erase_bind_gallop,
        erase_gallopRightRightExponentialTraced]
      cases hphase : gallopRightRightExponentialFromSource? (n + 1)
          state.key_compare source key hint (n - hint) 0 1 <;>
        simp [gallopBindOptionAcross, hphase]
  · simp [gallopRightTraced?, gallopRightFromSource?, hinput]

/-! Relating the direct-source evaluator to the reviewed public transcription. -/

private theorem gallopLeftRightExponentialFromSource_main
    (fuel : Nat) (lt : BoolComparator κ) (slice : SortSlice κ ν) (base : Int)
    (key : κ) (hint maxOffset lastOffset offset : Nat) :
    gallopLeftRightExponentialFromSource? fuel lt (.main slice base) key hint
      maxOffset lastOffset offset =
      gallopLeftRightExponential? fuel lt slice base key hint maxOffset
        lastOffset offset := by
  induction fuel generalizing lastOffset offset with
  | zero => rfl
  | succ fuel ih =>
      simp only [gallopLeftRightExponentialFromSource?,
        gallopLeftRightExponential?]
      split
      · simp [GallopKeySource.read?, GallopKeySource.base, ih, add_assoc]
        rfl
      · rfl

private theorem gallopLeftLeftExponentialFromSource_main
    (fuel : Nat) (lt : BoolComparator κ) (slice : SortSlice κ ν) (base : Int)
    (key : κ) (hint maxOffset lastOffset offset : Nat) :
    gallopLeftLeftExponentialFromSource? fuel lt (.main slice base) key hint
      maxOffset lastOffset offset =
      gallopLeftLeftExponential? fuel lt slice base key hint maxOffset
        lastOffset offset := by
  induction fuel generalizing lastOffset offset with
  | zero => rfl
  | succ fuel ih =>
      simp only [gallopLeftLeftExponentialFromSource?,
        gallopLeftLeftExponential?]
      split
      · simp [GallopKeySource.read?, GallopKeySource.base, ih, add_assoc,
          sub_eq_add_neg]
        rfl
      · rfl

private theorem gallopLeftBinaryFromSource_main
    (fuel : Nat) (lt : BoolComparator κ) (slice : SortSlice κ ν) (base : Int)
    (key : κ) (lower upper : Nat) :
    gallopLeftBinaryFromSource? fuel lt (.main slice base) key lower upper =
      gallopLeftBinary? fuel lt slice base key lower upper := by
  induction fuel generalizing lower upper with
  | zero => rfl
  | succ fuel ih =>
      simp only [gallopLeftBinaryFromSource?, gallopLeftBinary?]
      split
      · simp [GallopKeySource.read?, GallopKeySource.base, ih, add_assoc]
      · rfl

private theorem gallopRightLeftExponentialFromSource_main
    (fuel : Nat) (lt : BoolComparator κ) (slice : SortSlice κ ν) (base : Int)
    (key : κ) (hint maxOffset lastOffset offset : Nat) :
    gallopRightLeftExponentialFromSource? fuel lt (.main slice base) key hint
      maxOffset lastOffset offset =
      gallopRightLeftExponential? fuel lt slice base key hint maxOffset
        lastOffset offset := by
  induction fuel generalizing lastOffset offset with
  | zero => rfl
  | succ fuel ih =>
      simp only [gallopRightLeftExponentialFromSource?,
        gallopRightLeftExponential?]
      split
      · simp [GallopKeySource.read?, GallopKeySource.base, ih, add_assoc,
          sub_eq_add_neg]
        rfl
      · rfl

private theorem gallopRightRightExponentialFromSource_main
    (fuel : Nat) (lt : BoolComparator κ) (slice : SortSlice κ ν) (base : Int)
    (key : κ) (hint maxOffset lastOffset offset : Nat) :
    gallopRightRightExponentialFromSource? fuel lt (.main slice base) key hint
      maxOffset lastOffset offset =
      gallopRightRightExponential? fuel lt slice base key hint maxOffset
        lastOffset offset := by
  induction fuel generalizing lastOffset offset with
  | zero => rfl
  | succ fuel ih =>
      simp only [gallopRightRightExponentialFromSource?,
        gallopRightRightExponential?]
      split
      · simp [GallopKeySource.read?, GallopKeySource.base, ih, add_assoc]
        rfl
      · rfl

private theorem gallopRightBinaryFromSource_main
    (fuel : Nat) (lt : BoolComparator κ) (slice : SortSlice κ ν) (base : Int)
    (key : κ) (lower upper : Nat) :
    gallopRightBinaryFromSource? fuel lt (.main slice base) key lower upper =
      gallopRightBinary? fuel lt slice base key lower upper := by
  induction fuel generalizing lower upper with
  | zero => rfl
  | succ fuel ih =>
      simp only [gallopRightBinaryFromSource?, gallopRightBinary?]
      split
      · simp [GallopKeySource.read?, GallopKeySource.base, ih, add_assoc]
      · rfl

private theorem finishGallopLeftFromSource_main
    (fuel : Nat) (lt : BoolComparator κ) (slice : SortSlice κ ν) (base : Int)
    (key : κ) (n : Nat) (lastOffset upperOffset : Int) (exhausted : Bool) :
    finishGallopLeftFromSource? fuel lt (.main slice base) key n lastOffset
      upperOffset exhausted =
      finishGallopLeft? fuel lt slice base key n lastOffset upperOffset exhausted := by
  simp [finishGallopLeftFromSource?, finishGallopLeft?,
    gallopLeftBinaryFromSource_main]

private theorem finishGallopRightFromSource_main
    (fuel : Nat) (lt : BoolComparator κ) (slice : SortSlice κ ν) (base : Int)
    (key : κ) (n : Nat) (lastOffset upperOffset : Int) (exhausted : Bool) :
    finishGallopRightFromSource? fuel lt (.main slice base) key n lastOffset
      upperOffset exhausted =
      finishGallopRight? fuel lt slice base key n lastOffset upperOffset exhausted := by
  simp [finishGallopRightFromSource?, finishGallopRight?,
    gallopRightBinaryFromSource_main]

/-- On main data, the direct-source left evaluator is exactly `gallopLeft?`. -/
theorem gallopLeftFromSource_main (state : MergeState κ ν)
    (slice : SortSlice κ ν) (base : Int) (key : κ) (n hint : Nat) :
    gallopLeftFromSource? state (.main slice base) key n hint =
      gallopLeft? state slice base key n hint := by
  simp [gallopLeftFromSource?, gallopLeft?, GallopKeySource.read?,
    GallopKeySource.base, gallopLeftRightExponentialFromSource_main,
    gallopLeftLeftExponentialFromSource_main, finishGallopLeftFromSource_main]

/-- On main data, the direct-source right evaluator is exactly `gallopRight?`. -/
theorem gallopRightFromSource_main (state : MergeState κ ν)
    (slice : SortSlice κ ν) (base : Int) (key : κ) (n hint : Nat) :
    gallopRightFromSource? state (.main slice base) key n hint =
      gallopRight? state slice base key n hint := by
  simp [gallopRightFromSource?, gallopRight?, GallopKeySource.read?,
    GallopKeySource.base, gallopRightLeftExponentialFromSource_main,
    gallopRightRightExponentialFromSource_main, finishGallopRightFromSource_main]

/-! ### Congruence with a reviewed materialized slice -/

/-- The rightward exponential phase of `gallop_left` is unchanged when its
direct source agrees with the reviewed slice throughout the searched range. -/
theorem gallopLeftRightExponentialFromSource_eq_slice (fuel : Nat)
    (lt : BoolComparator κ) (source : GallopKeySource κ ν)
    (slice : SortSlice κ ν) (sliceBase : Int) (key : κ)
    (hint maxOffset lastOffset offset n : Nat)
    (hagrees : source.AgreesWithSlice slice sliceBase n)
    (hwindow : hint + maxOffset ≤ n) :
    gallopLeftRightExponentialFromSource? fuel lt source key hint maxOffset
        lastOffset offset =
      gallopLeftRightExponential? fuel lt slice sliceBase key hint maxOffset
        lastOffset offset := by
  induction fuel generalizing lastOffset offset with
  | zero => rfl
  | succ fuel ih =>
      simp only [gallopLeftRightExponentialFromSource?,
        gallopLeftRightExponential?]
      by_cases hprobe : offset < maxOffset
      · rw [if_pos hprobe, if_pos hprobe]
        have hindexNonnegative : 0 ≤ Int.ofNat (hint + offset) :=
          Int.natCast_nonneg _
        have hindexUpper : Int.ofNat (hint + offset) < Int.ofNat n := by
          exact Int.ofNat_lt.mpr (by omega)
        rw [hagrees _ hindexNonnegative hindexUpper]
        simp only [Int.ofNat_eq_natCast, Int.natCast_add, add_assoc]
        apply congrArg (gallopBindOptionAcross _)
        funext entry
        by_cases hcompare : lt entry.key key = true
        · by_cases hguard : offset ≤ (PY_SSIZE_T_MAX - 1) / 2 <;>
            simp [hcompare, hguard, ih]
        · simp [hcompare]
      · rw [if_neg hprobe, if_neg hprobe]

/-- The leftward exponential phase of `gallop_left` is unchanged under
reviewed-slice agreement. -/
theorem gallopLeftLeftExponentialFromSource_eq_slice (fuel : Nat)
    (lt : BoolComparator κ) (source : GallopKeySource κ ν)
    (slice : SortSlice κ ν) (sliceBase : Int) (key : κ)
    (hint maxOffset lastOffset offset n : Nat)
    (hagrees : source.AgreesWithSlice slice sliceBase n)
    (hhint : hint < n) (hwindow : maxOffset ≤ hint + 1) :
    gallopLeftLeftExponentialFromSource? fuel lt source key hint maxOffset
        lastOffset offset =
      gallopLeftLeftExponential? fuel lt slice sliceBase key hint maxOffset
        lastOffset offset := by
  induction fuel generalizing lastOffset offset with
  | zero => rfl
  | succ fuel ih =>
      simp only [gallopLeftLeftExponentialFromSource?,
        gallopLeftLeftExponential?]
      by_cases hprobe : offset < maxOffset
      · rw [if_pos hprobe, if_pos hprobe]
        have hoffsetHint : offset ≤ hint := by omega
        have hindexNonnegative :
            0 ≤ Int.ofNat hint - Int.ofNat offset := by
          simp only [Int.ofNat_eq_natCast]
          omega
        have hindexUpper :
            Int.ofNat hint - Int.ofNat offset < Int.ofNat n := by
          simp only [Int.ofNat_eq_natCast]
          omega
        rw [hagrees _ hindexNonnegative hindexUpper]
        simp only [sub_eq_add_neg, add_assoc]
        apply congrArg (gallopBindOptionAcross _)
        funext entry
        by_cases hcompare : lt entry.key key = true
        · simp [hcompare]
        · by_cases hguard : offset ≤ (PY_SSIZE_T_MAX - 1) / 2 <;>
            simp [hcompare, hguard, ih]
      · rw [if_neg hprobe, if_neg hprobe]

/-- The left-biased binary phase is unchanged under reviewed-slice
agreement. -/
theorem gallopLeftBinaryFromSource_eq_slice (fuel : Nat)
    (lt : BoolComparator κ) (source : GallopKeySource κ ν)
    (slice : SortSlice κ ν) (sliceBase : Int) (key : κ)
    (lower upper n : Nat)
    (hagrees : source.AgreesWithSlice slice sliceBase n)
    (hupper : upper ≤ n) :
    gallopLeftBinaryFromSource? fuel lt source key lower upper =
      gallopLeftBinary? fuel lt slice sliceBase key lower upper := by
  induction fuel generalizing lower upper with
  | zero => rfl
  | succ fuel ih =>
      simp only [gallopLeftBinaryFromSource?, gallopLeftBinary?]
      by_cases hsearch : lower < upper
      · rw [if_pos hsearch, if_pos hsearch]
        let middle := lower + (upper - lower) / 2
        have hmiddleUpper : middle < upper := by
          dsimp [middle]
          omega
        have hindexNonnegative : 0 ≤ Int.ofNat middle :=
          Int.natCast_nonneg _
        have hindexUpper : Int.ofNat middle < Int.ofNat n :=
          Int.ofNat_lt.mpr (by omega)
        rw [hagrees _ hindexNonnegative hindexUpper]
        apply congrArg
          (gallopBindOptionAcross
            (slice.read? (sliceBase + Int.ofNat middle)))
        funext entry
        by_cases hcompare : lt entry.key key = true
        · simp [hcompare, ih _ _ hupper]
        · have hmiddleBound : middle ≤ n := by omega
          simp only [iflt_eq, hcompare]
          exact ih lower middle hmiddleBound
      · rw [if_neg hsearch, if_neg hsearch]

/-- The leftward exponential phase of `gallop_right` is unchanged under
reviewed-slice agreement. -/
theorem gallopRightLeftExponentialFromSource_eq_slice (fuel : Nat)
    (lt : BoolComparator κ) (source : GallopKeySource κ ν)
    (slice : SortSlice κ ν) (sliceBase : Int) (key : κ)
    (hint maxOffset lastOffset offset n : Nat)
    (hagrees : source.AgreesWithSlice slice sliceBase n)
    (hhint : hint < n) (hwindow : maxOffset ≤ hint + 1) :
    gallopRightLeftExponentialFromSource? fuel lt source key hint maxOffset
        lastOffset offset =
      gallopRightLeftExponential? fuel lt slice sliceBase key hint maxOffset
        lastOffset offset := by
  induction fuel generalizing lastOffset offset with
  | zero => rfl
  | succ fuel ih =>
      simp only [gallopRightLeftExponentialFromSource?,
        gallopRightLeftExponential?]
      by_cases hprobe : offset < maxOffset
      · rw [if_pos hprobe, if_pos hprobe]
        have hoffsetHint : offset ≤ hint := by omega
        have hindexNonnegative :
            0 ≤ Int.ofNat hint - Int.ofNat offset := by
          simp only [Int.ofNat_eq_natCast]
          omega
        have hindexUpper :
            Int.ofNat hint - Int.ofNat offset < Int.ofNat n := by
          simp only [Int.ofNat_eq_natCast]
          omega
        rw [hagrees _ hindexNonnegative hindexUpper]
        simp only [sub_eq_add_neg, add_assoc]
        apply congrArg (gallopBindOptionAcross _)
        funext entry
        by_cases hcompare : lt key entry.key = true
        · by_cases hguard : offset ≤ (PY_SSIZE_T_MAX - 1) / 2 <;>
            simp [hcompare, hguard, ih]
        · simp [hcompare]
      · rw [if_neg hprobe, if_neg hprobe]

/-- The rightward exponential phase of `gallop_right` is unchanged under
reviewed-slice agreement. -/
theorem gallopRightRightExponentialFromSource_eq_slice (fuel : Nat)
    (lt : BoolComparator κ) (source : GallopKeySource κ ν)
    (slice : SortSlice κ ν) (sliceBase : Int) (key : κ)
    (hint maxOffset lastOffset offset n : Nat)
    (hagrees : source.AgreesWithSlice slice sliceBase n)
    (hwindow : hint + maxOffset ≤ n) :
    gallopRightRightExponentialFromSource? fuel lt source key hint maxOffset
        lastOffset offset =
      gallopRightRightExponential? fuel lt slice sliceBase key hint maxOffset
        lastOffset offset := by
  induction fuel generalizing lastOffset offset with
  | zero => rfl
  | succ fuel ih =>
      simp only [gallopRightRightExponentialFromSource?,
        gallopRightRightExponential?]
      by_cases hprobe : offset < maxOffset
      · rw [if_pos hprobe, if_pos hprobe]
        have hindexNonnegative : 0 ≤ Int.ofNat (hint + offset) :=
          Int.natCast_nonneg _
        have hindexUpper : Int.ofNat (hint + offset) < Int.ofNat n := by
          exact Int.ofNat_lt.mpr (by omega)
        rw [hagrees _ hindexNonnegative hindexUpper]
        simp only [Int.ofNat_eq_natCast, Int.natCast_add, add_assoc]
        apply congrArg (gallopBindOptionAcross _)
        funext entry
        by_cases hcompare : lt key entry.key = true
        · simp [hcompare]
        · by_cases hguard : offset ≤ (PY_SSIZE_T_MAX - 1) / 2 <;>
            simp [hcompare, hguard, ih]
      · rw [if_neg hprobe, if_neg hprobe]

/-- The right-biased binary phase is unchanged under reviewed-slice
agreement. -/
theorem gallopRightBinaryFromSource_eq_slice (fuel : Nat)
    (lt : BoolComparator κ) (source : GallopKeySource κ ν)
    (slice : SortSlice κ ν) (sliceBase : Int) (key : κ)
    (lower upper n : Nat)
    (hagrees : source.AgreesWithSlice slice sliceBase n)
    (hupper : upper ≤ n) :
    gallopRightBinaryFromSource? fuel lt source key lower upper =
      gallopRightBinary? fuel lt slice sliceBase key lower upper := by
  induction fuel generalizing lower upper with
  | zero => rfl
  | succ fuel ih =>
      simp only [gallopRightBinaryFromSource?, gallopRightBinary?]
      by_cases hsearch : lower < upper
      · rw [if_pos hsearch, if_pos hsearch]
        let middle := lower + (upper - lower) / 2
        have hmiddleUpper : middle < upper := by
          dsimp [middle]
          omega
        have hindexNonnegative : 0 ≤ Int.ofNat middle :=
          Int.natCast_nonneg _
        have hindexUpper : Int.ofNat middle < Int.ofNat n :=
          Int.ofNat_lt.mpr (by omega)
        rw [hagrees _ hindexNonnegative hindexUpper]
        apply congrArg
          (gallopBindOptionAcross
            (slice.read? (sliceBase + Int.ofNat middle)))
        funext entry
        by_cases hcompare : lt key entry.key = true
        · have hmiddleBound : middle ≤ n := by omega
          simp only [iflt_eq, hcompare, if_true]
          exact ih lower middle hmiddleBound
        · simp [hcompare, ih _ _ hupper]
      · rw [if_neg hsearch, if_neg hsearch]

/-- The left-biased finishing phase is unchanged under reviewed-slice
agreement.  Its own signed guard supplies the binary phase's upper bound. -/
theorem finishGallopLeftFromSource_eq_slice (fuel : Nat)
    (lt : BoolComparator κ) (source : GallopKeySource κ ν)
    (slice : SortSlice κ ν) (sliceBase : Int) (key : κ) (n : Nat)
    (lastOffset upperOffset : Int) (exhausted : Bool)
    (hagrees : source.AgreesWithSlice slice sliceBase n) :
    finishGallopLeftFromSource? fuel lt source key n lastOffset upperOffset
        exhausted =
      finishGallopLeft? fuel lt slice sliceBase key n lastOffset upperOffset
        exhausted := by
  by_cases houter :
      -1 ≤ lastOffset ∧ lastOffset < upperOffset ∧
        upperOffset ≤ Int.ofNat n
  · by_cases hinner : 0 ≤ lastOffset + 1 ∧ 0 ≤ upperOffset
    · unfold finishGallopLeftFromSource? finishGallopLeft?
      rw [if_pos houter, if_pos houter]
      dsimp only
      rw [if_pos hinner, if_pos hinner]
      cases exhausted with
      | false =>
          exact gallopLeftBinaryFromSource_eq_slice fuel lt source slice
            sliceBase key (lastOffset + 1).toNat upperOffset.toNat n hagrees
            (Int.toNat_le.mpr houter.2.2)
      | true => rfl
    · unfold finishGallopLeftFromSource? finishGallopLeft?
      rw [if_pos houter, if_pos houter]
      dsimp only
      rw [if_neg hinner, if_neg hinner]
  · unfold finishGallopLeftFromSource? finishGallopLeft?
    rw [if_neg houter, if_neg houter]

/-- The right-biased finishing phase is unchanged under reviewed-slice
agreement. -/
theorem finishGallopRightFromSource_eq_slice (fuel : Nat)
    (lt : BoolComparator κ) (source : GallopKeySource κ ν)
    (slice : SortSlice κ ν) (sliceBase : Int) (key : κ) (n : Nat)
    (lastOffset upperOffset : Int) (exhausted : Bool)
    (hagrees : source.AgreesWithSlice slice sliceBase n) :
    finishGallopRightFromSource? fuel lt source key n lastOffset upperOffset
        exhausted =
      finishGallopRight? fuel lt slice sliceBase key n lastOffset upperOffset
        exhausted := by
  by_cases houter :
      -1 ≤ lastOffset ∧ lastOffset < upperOffset ∧
        upperOffset ≤ Int.ofNat n
  · by_cases hinner : 0 ≤ lastOffset + 1 ∧ 0 ≤ upperOffset
    · unfold finishGallopRightFromSource? finishGallopRight?
      rw [if_pos houter, if_pos houter]
      dsimp only
      rw [if_pos hinner, if_pos hinner]
      cases exhausted with
      | false =>
          exact gallopRightBinaryFromSource_eq_slice fuel lt source slice
            sliceBase key (lastOffset + 1).toNat upperOffset.toNat n hagrees
            (Int.toNat_le.mpr houter.2.2)
      | true => rfl
    · unfold finishGallopRightFromSource? finishGallopRight?
      rw [if_pos houter, if_pos houter]
      dsimp only
      rw [if_neg hinner, if_neg hinner]
  · unfold finishGallopRightFromSource? finishGallopRight?
    rw [if_neg houter, if_neg houter]

/-- Under pointwise agreement with a reviewed materialized slice, the complete
direct-source `gallop_left` evaluator is exactly the original transcription.
The valid-range premise is the same premise consumed by the safety proof; no
evaluator equality is assumed. -/
theorem gallopLeftFromSource_eq_slice_of_ssize (state : MergeState κ ν)
    (source : GallopKeySource κ ν) (slice : SortSlice κ ν)
    (sliceBase : Int) (key : κ) (n hint : Nat)
    (hagrees : source.AgreesWithSlice slice sliceBase n)
    (hn : 0 < n) (hhint : hint < n) (hnSsize : n ≤ PY_SSIZE_T_MAX) :
    gallopLeftFromSource? state source key n hint =
      gallopLeft? state slice sliceBase key n hint := by
  have hinput : 0 < n ∧ hint < n ∧ n ≤ PY_SSIZE_T_MAX :=
    ⟨hn, hhint, hnSsize⟩
  unfold gallopLeftFromSource? gallopLeft?
  rw [if_pos hinput, if_pos hinput]
  have hindexNonnegative : 0 ≤ Int.ofNat hint := Int.natCast_nonneg _
  have hindexUpper : Int.ofNat hint < Int.ofNat n := Int.ofNat_lt.mpr hhint
  rw [hagrees _ hindexNonnegative hindexUpper]
  apply congrArg
    (gallopBindOptionAcross
      (slice.read? (sliceBase + Int.ofNat hint)))
  funext hinted
  by_cases hcompare : iflt state.key_compare hinted.key key = true
  · rw [if_pos hcompare, if_pos hcompare]
    dsimp only
    have hphaseEq := gallopLeftRightExponentialFromSource_eq_slice
      (n + 1) state.key_compare source slice sliceBase key hint (n - hint)
      0 1 n hagrees (by omega)
    rw [hphaseEq]
    cases hphase : gallopLeftRightExponential? (n + 1) state.key_compare
        slice sliceBase key hint (n - hint) 0 1 with
    | none => rfl
    | some exponential =>
        change
          finishGallopLeftFromSource? (n + 1) state.key_compare source key n
              (Int.ofNat exponential.lastOffset + Int.ofNat hint)
              (Int.ofNat (min exponential.offset (n - hint)) + Int.ofNat hint)
              exponential.fuelExhausted =
            finishGallopLeft? (n + 1) state.key_compare slice sliceBase key n
              (Int.ofNat exponential.lastOffset + Int.ofNat hint)
              (Int.ofNat (min exponential.offset (n - hint)) + Int.ofNat hint)
              exponential.fuelExhausted
        exact finishGallopLeftFromSource_eq_slice (n + 1) state.key_compare
          source slice sliceBase key n
          (Int.ofNat exponential.lastOffset + Int.ofNat hint)
          (Int.ofNat (min exponential.offset (n - hint)) + Int.ofNat hint)
          exponential.fuelExhausted hagrees
  · rw [if_neg hcompare, if_neg hcompare]
    dsimp only
    have hphaseEq := gallopLeftLeftExponentialFromSource_eq_slice
      (n + 1) state.key_compare source slice sliceBase key hint (hint + 1)
      0 1 n hagrees hhint (by omega)
    rw [hphaseEq]
    cases hphase : gallopLeftLeftExponential? (n + 1) state.key_compare
        slice sliceBase key hint (hint + 1) 0 1 with
    | none => rfl
    | some exponential =>
        change
          finishGallopLeftFromSource? (n + 1) state.key_compare source key n
              (Int.ofNat hint - Int.ofNat (min exponential.offset (hint + 1)))
              (Int.ofNat hint - Int.ofNat exponential.lastOffset)
              exponential.fuelExhausted =
            finishGallopLeft? (n + 1) state.key_compare slice sliceBase key n
              (Int.ofNat hint - Int.ofNat (min exponential.offset (hint + 1)))
              (Int.ofNat hint - Int.ofNat exponential.lastOffset)
              exponential.fuelExhausted
        exact finishGallopLeftFromSource_eq_slice (n + 1) state.key_compare
          source slice sliceBase key n
          (Int.ofNat hint - Int.ofNat (min exponential.offset (hint + 1)))
          (Int.ofNat hint - Int.ofNat exponential.lastOffset)
          exponential.fuelExhausted hagrees

/-- Right-biased counterpart of `gallopLeftFromSource_eq_slice`.  It remains
valid for an arbitrary Boolean comparator. -/
theorem gallopRightFromSource_eq_slice_of_ssize (state : MergeState κ ν)
    (source : GallopKeySource κ ν) (slice : SortSlice κ ν)
    (sliceBase : Int) (key : κ) (n hint : Nat)
    (hagrees : source.AgreesWithSlice slice sliceBase n)
    (hn : 0 < n) (hhint : hint < n) (hnSsize : n ≤ PY_SSIZE_T_MAX) :
    gallopRightFromSource? state source key n hint =
      gallopRight? state slice sliceBase key n hint := by
  have hinput : 0 < n ∧ hint < n ∧ n ≤ PY_SSIZE_T_MAX :=
    ⟨hn, hhint, hnSsize⟩
  unfold gallopRightFromSource? gallopRight?
  rw [if_pos hinput, if_pos hinput]
  have hindexNonnegative : 0 ≤ Int.ofNat hint := Int.natCast_nonneg _
  have hindexUpper : Int.ofNat hint < Int.ofNat n := Int.ofNat_lt.mpr hhint
  rw [hagrees _ hindexNonnegative hindexUpper]
  apply congrArg
    (gallopBindOptionAcross
      (slice.read? (sliceBase + Int.ofNat hint)))
  funext hinted
  by_cases hcompare : iflt state.key_compare key hinted.key = true
  · rw [if_pos hcompare, if_pos hcompare]
    dsimp only
    have hphaseEq := gallopRightLeftExponentialFromSource_eq_slice
      (n + 1) state.key_compare source slice sliceBase key hint (hint + 1)
      0 1 n hagrees hhint (by omega)
    rw [hphaseEq]
    cases hphase : gallopRightLeftExponential? (n + 1) state.key_compare
        slice sliceBase key hint (hint + 1) 0 1 with
    | none => rfl
    | some exponential =>
        change
          finishGallopRightFromSource? (n + 1) state.key_compare source key n
              (Int.ofNat hint - Int.ofNat (min exponential.offset (hint + 1)))
              (Int.ofNat hint - Int.ofNat exponential.lastOffset)
              exponential.fuelExhausted =
            finishGallopRight? (n + 1) state.key_compare slice sliceBase key n
              (Int.ofNat hint - Int.ofNat (min exponential.offset (hint + 1)))
              (Int.ofNat hint - Int.ofNat exponential.lastOffset)
              exponential.fuelExhausted
        exact finishGallopRightFromSource_eq_slice (n + 1) state.key_compare
          source slice sliceBase key n
          (Int.ofNat hint - Int.ofNat (min exponential.offset (hint + 1)))
          (Int.ofNat hint - Int.ofNat exponential.lastOffset)
          exponential.fuelExhausted hagrees
  · rw [if_neg hcompare, if_neg hcompare]
    dsimp only
    have hphaseEq := gallopRightRightExponentialFromSource_eq_slice
      (n + 1) state.key_compare source slice sliceBase key hint (n - hint)
      0 1 n hagrees (by omega)
    rw [hphaseEq]
    cases hphase : gallopRightRightExponential? (n + 1) state.key_compare
        slice sliceBase key hint (n - hint) 0 1 with
    | none => rfl
    | some exponential =>
        change
          finishGallopRightFromSource? (n + 1) state.key_compare source key n
              (Int.ofNat exponential.lastOffset + Int.ofNat hint)
              (Int.ofNat (min exponential.offset (n - hint)) + Int.ofNat hint)
              exponential.fuelExhausted =
            finishGallopRight? (n + 1) state.key_compare slice sliceBase key n
              (Int.ofNat exponential.lastOffset + Int.ofNat hint)
              (Int.ofNat (min exponential.offset (n - hint)) + Int.ofNat hint)
              exponential.fuelExhausted
        exact finishGallopRightFromSource_eq_slice (n + 1) state.key_compare
          source slice sliceBase key n
          (Int.ofNat exponential.lastOffset + Int.ofNat hint)
          (Int.ofNat (min exponential.offset (n - hint)) + Int.ofNat hint)
          exponential.fuelExhausted hagrees

/-- Compatibility wrapper for the safety-facing list-allocation bound. -/
theorem gallopLeftFromSource_eq_slice (state : MergeState κ ν)
    (source : GallopKeySource κ ν) (slice : SortSlice κ ν)
    (sliceBase : Int) (key : κ) (n hint : Nat)
    (_hvalid : source.ValidRange n)
    (hagrees : source.AgreesWithSlice slice sliceBase n)
    (hn : 0 < n) (hhint : hint < n) (hnmax : n ≤ PY_LIST_MAX) :
    gallopLeftFromSource? state source key n hint =
      gallopLeft? state slice sliceBase key n hint := by
  have hnSsize : n ≤ PY_SSIZE_T_MAX := by
    norm_num [PY_LIST_MAX, PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES] at hnmax ⊢
    omega
  exact gallopLeftFromSource_eq_slice_of_ssize state source slice sliceBase key
    n hint hagrees hn hhint hnSsize

/-- Compatibility wrapper for the safety-facing list-allocation bound. -/
theorem gallopRightFromSource_eq_slice (state : MergeState κ ν)
    (source : GallopKeySource κ ν) (slice : SortSlice κ ν)
    (sliceBase : Int) (key : κ) (n hint : Nat)
    (_hvalid : source.ValidRange n)
    (hagrees : source.AgreesWithSlice slice sliceBase n)
    (hn : 0 < n) (hhint : hint < n) (hnmax : n ≤ PY_LIST_MAX) :
    gallopRightFromSource? state source key n hint =
      gallopRight? state slice sliceBase key n hint := by
  have hnSsize : n ≤ PY_SSIZE_T_MAX := by
    norm_num [PY_LIST_MAX, PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES] at hnmax ⊢
    omega
  exact gallopRightFromSource_eq_slice_of_ssize state source slice sliceBase key
    n hint hagrees hn hhint hnSsize

/-- Exact erasure of a traced left gallop over any agreeing direct source to
the corresponding reviewed materialized-slice call. -/
theorem erase_gallopLeftTraced_eq_slice (state : MergeState κ ν)
    (source : GallopKeySource κ ν) (slice : SortSlice κ ν)
    (sliceBase : Int) (key : κ) (n hint : Nat)
    (hvalid : source.ValidRange n)
    (hagrees : source.AgreesWithSlice slice sliceBase n)
    (hn : 0 < n) (hhint : hint < n) (hnmax : n ≤ PY_LIST_MAX) :
    (gallopLeftTraced? state source key n hint).erase =
      gallopLeft? state slice sliceBase key n hint := by
  rw [erase_gallopLeftTraced]
  exact gallopLeftFromSource_eq_slice state source slice sliceBase key n hint
    hvalid hagrees hn hhint hnmax

/-- Exact erasure of a traced right gallop over any agreeing direct source to
the corresponding reviewed materialized-slice call. -/
theorem erase_gallopRightTraced_eq_slice (state : MergeState κ ν)
    (source : GallopKeySource κ ν) (slice : SortSlice κ ν)
    (sliceBase : Int) (key : κ) (n hint : Nat)
    (hvalid : source.ValidRange n)
    (hagrees : source.AgreesWithSlice slice sliceBase n)
    (hn : 0 < n) (hhint : hint < n) (hnmax : n ≤ PY_LIST_MAX) :
    (gallopRightTraced? state source key n hint).erase =
      gallopRight? state slice sliceBase key n hint := by
  rw [erase_gallopRightTraced]
  exact gallopRightFromSource_eq_slice state source slice sliceBase key n hint
    hvalid hagrees hn hhint hnmax

/-- Exact erasure of the traced left gallop on main data. -/
theorem erase_gallopLeftTraced_main (state : MergeState κ ν)
    (slice : SortSlice κ ν) (base : Int) (key : κ) (n hint : Nat) :
    (gallopLeftTraced? state (.main slice base) key n hint).erase =
      gallopLeft? state slice base key n hint := by
  rw [erase_gallopLeftTraced, gallopLeftFromSource_main]

/-- Exact erasure of the traced right gallop on main data. -/
theorem erase_gallopRightTraced_main (state : MergeState κ ν)
    (slice : SortSlice κ ν) (base : Int) (key : κ) (n hint : Nat) :
    (gallopRightTraced? state (.main slice base) key n hint).erase =
      gallopRight? state slice base key n hint := by
  rw [erase_gallopRightTraced, gallopRightFromSource_main]

/-! ## Shared safety contracts -/

/-- The trace-only obligations shared by every gallop phase. -/
def GallopTraceSafe (execution : TraceResult α) : Prop :=
  execution.trace.fuelExhausted = false ∧
    execution.trace.pushDepths = [] ∧
    execution.trace.allAccessesInBounds ∧
    execution.trace.tempPayloadAccessesLive

@[simp]
theorem gallopTraceSafe_pure (value : α) :
    GallopTraceSafe (TraceResult.pure value) := by
  refine ⟨rfl, rfl, AccessTrace.allAccessesInBounds_empty,
    AccessTrace.tempPayloadAccessesLive_empty⟩

/-- Sequentially composing two successful, safe traced computations preserves
all shared trace obligations, including the absence of pending-stack pushes. -/
theorem gallopTraceSafe_bind (current : TraceResult α)
    (next : α → TraceResult β) (value : α)
    (hresult : current.result = some value)
    (hcurrent : GallopTraceSafe current)
    (hnext : GallopTraceSafe (next value)) :
    GallopTraceSafe (current.bind next) := by
  rcases hcurrent with
    ⟨hcurrentFuel, hcurrentPushes, hcurrentBounds, hcurrentLive⟩
  rcases hnext with ⟨hnextFuel, hnextPushes, hnextBounds, hnextLive⟩
  rw [GallopTraceSafe, TraceResult.trace_bind, hresult]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [hcurrentFuel, hnextFuel]
  · simp [AccessTrace.compose, hcurrentPushes, hnextPushes]
  · exact (AccessTrace.allAccessesInBounds_compose _ _).2
      ⟨hcurrentBounds, hnextBounds⟩
  · exact (AccessTrace.tempPayloadAccessesLive_compose _ _).2
      ⟨hcurrentLive, hnextLive⟩

/-- A valid direct-source read is successful and satisfies the shared trace
obligations. -/
theorem GallopKeySource.readTraced_safe (source : GallopKeySource κ ν)
    {n i : Nat} (hvalid : source.ValidRange n) (hlive : source.Live)
    (hi : i < n) :
    ∃ entry,
      (source.readTraced? (Int.ofNat i)).result = some entry ∧
        GallopTraceSafe (source.readTraced? (Int.ofNat i)) := by
  rcases source.read_eq_some hvalid hi with ⟨entry, hentry⟩
  refine ⟨entry, ?_, ?_⟩
  · simpa [TraceResult.erase] using
      (source.erase_readTraced (Int.ofNat i)).trans hentry
  · refine ⟨?_, ?_, source.readTraced_inBounds hvalid hi,
      source.readTraced_live (Int.ofNat i) hlive⟩
    · rw [source.trace_readTraced]
      rfl
    · rw [source.trace_readTraced]
      rfl

/-- The selected-project list bound leaves ample headroom for the C doubling
guard in either exponential phase. -/
theorem gallop_doubling_guard {offset maxOffset n : Nat}
    (hoffset : offset < maxOffset) (hmax : maxOffset ≤ n)
    (hn : n ≤ PY_LIST_MAX) :
    offset ≤ (PY_SSIZE_T_MAX - 1) / 2 := by
  norm_num [PY_LIST_MAX, PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES] at hn ⊢
  omega

/-! ### Exponential phases -/

/-- Safety invariant for the rightward exponential phase of `gallop_left`. -/
theorem gallopLeftRightExponential_safe (fuel : Nat)
    (lt : BoolComparator κ) (source : GallopKeySource κ ν) (key : κ)
    (hint maxOffset lastOffset offset n : Nat)
    (hvalid : source.ValidRange n) (hlive : source.Live)
    (hwindow : hint + maxOffset ≤ n) (hnmax : n ≤ PY_LIST_MAX)
    (hoffsetPositive : 0 < offset) (hlastOffset : lastOffset < offset)
    (hlastMax : lastOffset < maxOffset)
    (hbudget : maxOffset ≤ fuel + offset) :
    ∃ result,
      (gallopLeftRightExponentialTraced? fuel lt source key hint maxOffset
        lastOffset offset).result = some result ∧
      result.fuelExhausted = false ∧
      result.lastOffset < result.offset ∧
      result.lastOffset < maxOffset ∧
      GallopTraceSafe
        (gallopLeftRightExponentialTraced? fuel lt source key hint maxOffset
          lastOffset offset) := by
  induction fuel generalizing lastOffset offset with
  | zero =>
      have hstop : ¬ offset < maxOffset := by omega
      let outcome : ExponentialResult := ⟨lastOffset, offset, false⟩
      refine ⟨outcome, ?_, rfl, hlastOffset, hlastMax, ?_⟩
      · simp [gallopLeftRightExponentialTraced?, hstop,
          tracedExponentialResult, TraceResult.pure, outcome]
      · simp [gallopLeftRightExponentialTraced?, hstop,
          tracedExponentialResult]
  | succ fuel ih =>
      by_cases hprobe : offset < maxOffset
      · have hindex : hint + offset < n := by omega
        rcases source.readTraced_safe hvalid hlive hindex with
          ⟨entry, hreadResult, hreadSafe⟩
        by_cases hcompare : iflt lt entry.key key = true
        · have hmax : maxOffset ≤ n := by omega
          have hguard := gallop_doubling_guard hprobe hmax hnmax
          have hnewPositive : 0 < 2 * offset + 1 := by omega
          have hnewLast : offset < 2 * offset + 1 := by omega
          have hnewBudget : maxOffset ≤ fuel + (2 * offset + 1) := by omega
          rcases ih offset (2 * offset + 1) hnewPositive hnewLast hprobe
              hnewBudget with
            ⟨result, hresult, hnotExhausted, hresultOrder, hresultMax,
              htrace⟩
          refine ⟨result, ?_, hnotExhausted, hresultOrder, hresultMax, ?_⟩
          · simp only [gallopLeftRightExponentialTraced?, if_pos hprobe,
              TraceResult.bind, hreadResult, if_pos hcompare,
              if_pos hguard, hresult]
          · have hbound := gallopTraceSafe_bind
              (source.readTraced? (Int.ofNat (hint + offset)))
              (fun readEntry =>
                if iflt lt readEntry.key key then
                  if offset ≤ (PY_SSIZE_T_MAX - 1) / 2 then
                    gallopLeftRightExponentialTraced? fuel lt source key hint
                      maxOffset offset (2 * offset + 1)
                  else TraceResult.failure
                else TraceResult.pure {
                  lastOffset := lastOffset
                  offset := offset
                  fuelExhausted := false })
              entry hreadResult hreadSafe
              (by simpa only [if_pos hcompare, if_pos hguard]
                using htrace)
            rw [gallopLeftRightExponentialTraced?, if_pos hprobe]
            exact hbound
        · let outcome : ExponentialResult := ⟨lastOffset, offset, false⟩
          refine ⟨outcome, ?_, rfl, hlastOffset, hlastMax, ?_⟩
          · simp only [gallopLeftRightExponentialTraced?, if_pos hprobe,
              TraceResult.bind, hreadResult, if_neg hcompare,
              TraceResult.pure, outcome]
          · have hbound := gallopTraceSafe_bind
              (source.readTraced? (Int.ofNat (hint + offset)))
              (fun readEntry =>
                if iflt lt readEntry.key key then
                  if offset ≤ (PY_SSIZE_T_MAX - 1) / 2 then
                    gallopLeftRightExponentialTraced? fuel lt source key hint
                      maxOffset offset (2 * offset + 1)
                  else TraceResult.failure
                else TraceResult.pure {
                  lastOffset := lastOffset
                  offset := offset
                  fuelExhausted := false })
              entry hreadResult hreadSafe
              (by simpa only [if_neg hcompare] using
                (gallopTraceSafe_pure outcome))
            rw [gallopLeftRightExponentialTraced?, if_pos hprobe]
            exact hbound
      · let outcome : ExponentialResult := ⟨lastOffset, offset, false⟩
        refine ⟨outcome, ?_, rfl, hlastOffset, hlastMax, ?_⟩
        · simp [gallopLeftRightExponentialTraced?, hprobe,
            TraceResult.pure, outcome]
        · simp [gallopLeftRightExponentialTraced?, hprobe]

/-- Safety invariant for the leftward exponential phase of `gallop_left`. -/
theorem gallopLeftLeftExponential_safe (fuel : Nat)
    (lt : BoolComparator κ) (source : GallopKeySource κ ν) (key : κ)
    (hint maxOffset lastOffset offset n : Nat)
    (hvalid : source.ValidRange n) (hlive : source.Live)
    (hhint : hint < n) (hwindow : maxOffset ≤ hint + 1)
    (hnmax : n ≤ PY_LIST_MAX)
    (hoffsetPositive : 0 < offset) (hlastOffset : lastOffset < offset)
    (hlastMax : lastOffset < maxOffset)
    (hbudget : maxOffset ≤ fuel + offset) :
    ∃ result,
      (gallopLeftLeftExponentialTraced? fuel lt source key hint maxOffset
        lastOffset offset).result = some result ∧
      result.fuelExhausted = false ∧
      result.lastOffset < result.offset ∧
      result.lastOffset < maxOffset ∧
      GallopTraceSafe
        (gallopLeftLeftExponentialTraced? fuel lt source key hint maxOffset
          lastOffset offset) := by
  induction fuel generalizing lastOffset offset with
  | zero =>
      have hstop : ¬ offset < maxOffset := by omega
      let outcome : ExponentialResult := ⟨lastOffset, offset, false⟩
      refine ⟨outcome, ?_, rfl, hlastOffset, hlastMax, ?_⟩
      · simp [gallopLeftLeftExponentialTraced?, hstop,
          tracedExponentialResult, TraceResult.pure, outcome]
      · simp [gallopLeftLeftExponentialTraced?, hstop,
          tracedExponentialResult]
  | succ fuel ih =>
      by_cases hprobe : offset < maxOffset
      · have hoffsetHint : offset ≤ hint := by omega
        have hindex : hint - offset < n := by omega
        rcases source.readTraced_safe hvalid hlive hindex with
          ⟨entry, hreadResultNat, hreadSafeNat⟩
        have hindexEq :
            Int.ofNat hint - Int.ofNat offset = Int.ofNat (hint - offset) := by
          exact (Int.ofNat_sub hoffsetHint).symm
        have hreadResult :
            (source.readTraced?
              (Int.ofNat hint - Int.ofNat offset)).result = some entry := by
          rw [hindexEq]
          exact hreadResultNat
        have hreadSafe : GallopTraceSafe
            (source.readTraced? (Int.ofNat hint - Int.ofNat offset)) := by
          rw [hindexEq]
          exact hreadSafeNat
        by_cases hcompare : iflt lt entry.key key = true
        · let outcome : ExponentialResult := ⟨lastOffset, offset, false⟩
          refine ⟨outcome, ?_, rfl, hlastOffset, hlastMax, ?_⟩
          · simp only [gallopLeftLeftExponentialTraced?, if_pos hprobe,
              TraceResult.bind, hreadResult, if_pos hcompare,
              TraceResult.pure, outcome]
          · have hbound := gallopTraceSafe_bind
              (source.readTraced? (Int.ofNat hint - Int.ofNat offset))
              (fun readEntry =>
                if iflt lt readEntry.key key then
                  TraceResult.pure {
                    lastOffset := lastOffset
                    offset := offset
                    fuelExhausted := false }
                else if offset ≤ (PY_SSIZE_T_MAX - 1) / 2 then
                  gallopLeftLeftExponentialTraced? fuel lt source key hint
                    maxOffset offset (2 * offset + 1)
                else TraceResult.failure)
              entry hreadResult hreadSafe
              (by simpa only [if_pos hcompare] using
                (gallopTraceSafe_pure outcome))
            rw [gallopLeftLeftExponentialTraced?, if_pos hprobe]
            exact hbound
        · have hmax : maxOffset ≤ n := by omega
          have hguard := gallop_doubling_guard hprobe hmax hnmax
          have hnewPositive : 0 < 2 * offset + 1 := by omega
          have hnewLast : offset < 2 * offset + 1 := by omega
          have hnewBudget : maxOffset ≤ fuel + (2 * offset + 1) := by omega
          rcases ih offset (2 * offset + 1) hnewPositive hnewLast hprobe
              hnewBudget with
            ⟨result, hresult, hnotExhausted, hresultOrder, hresultMax,
              htrace⟩
          refine ⟨result, ?_, hnotExhausted, hresultOrder, hresultMax, ?_⟩
          · simp only [gallopLeftLeftExponentialTraced?, if_pos hprobe,
              TraceResult.bind, hreadResult, if_neg hcompare,
              if_pos hguard, hresult]
          · have hbound := gallopTraceSafe_bind
              (source.readTraced? (Int.ofNat hint - Int.ofNat offset))
              (fun readEntry =>
                if iflt lt readEntry.key key then
                  TraceResult.pure {
                    lastOffset := lastOffset
                    offset := offset
                    fuelExhausted := false }
                else if offset ≤ (PY_SSIZE_T_MAX - 1) / 2 then
                  gallopLeftLeftExponentialTraced? fuel lt source key hint
                    maxOffset offset (2 * offset + 1)
                else TraceResult.failure)
              entry hreadResult hreadSafe
              (by simpa only [if_neg hcompare, if_pos hguard] using htrace)
            rw [gallopLeftLeftExponentialTraced?, if_pos hprobe]
            exact hbound
      · let outcome : ExponentialResult := ⟨lastOffset, offset, false⟩
        refine ⟨outcome, ?_, rfl, hlastOffset, hlastMax, ?_⟩
        · simp [gallopLeftLeftExponentialTraced?, hprobe,
            TraceResult.pure, outcome]
        · simp [gallopLeftLeftExponentialTraced?, hprobe]

/-! ### Binary phases -/

/-- Comparator-independent termination, bounds, and trace safety for the
left-biased binary finishing phase. -/
theorem gallopLeftBinary_safe (fuel : Nat) (lt : BoolComparator κ)
    (source : GallopKeySource κ ν) (key : κ) (lower upper n : Nat)
    (hvalid : source.ValidRange n) (hlive : source.Live)
    (hlowerUpper : lower ≤ upper) (hupper : upper ≤ n)
    (hbudget : upper - lower ≤ fuel) :
    ∃ result,
      (gallopLeftBinaryTraced? fuel lt source key lower upper).result =
        some result ∧
      result.fuelExhausted = false ∧
      lower ≤ result.index ∧
      result.index ≤ upper ∧
      GallopTraceSafe
        (gallopLeftBinaryTraced? fuel lt source key lower upper) := by
  induction fuel generalizing lower upper with
  | zero =>
      have hstop : ¬ lower < upper := by omega
      let outcome : GallopResult := ⟨lower, false⟩
      refine ⟨outcome, ?_, rfl, Nat.le_refl lower, ?_, ?_⟩
      · simp [gallopLeftBinaryTraced?, hstop, tracedGallopResult,
          TraceResult.pure, outcome]
      · omega
      · simp [gallopLeftBinaryTraced?, hstop, tracedGallopResult]
  | succ fuel ih =>
      by_cases hsearch : lower < upper
      · let middle := lower + (upper - lower) / 2
        have hlowerMiddle : lower ≤ middle := by
          simp [middle]
        have hmiddleUpper : middle < upper := by
          dsimp [middle]
          omega
        have hmiddleIndex : middle < n := by omega
        rcases source.readTraced_safe hvalid hlive hmiddleIndex with
          ⟨entry, hreadResult, hreadSafe⟩
        by_cases hcompare : iflt lt entry.key key = true
        · have hnextOrder : middle + 1 ≤ upper := by omega
          have hnextBudget : upper - (middle + 1) ≤ fuel := by
            dsimp [middle]
            omega
          rcases ih (middle + 1) upper hnextOrder hupper hnextBudget with
            ⟨result, hresult, hnotExhausted, hresultLower, hresultUpper,
              htrace⟩
          have hreadResult' :
              (source.readTraced?
                (Int.ofNat (lower + (upper - lower) / 2))).result =
                some entry := by
            simpa only [middle] using hreadResult
          have hresult' :
              (gallopLeftBinaryTraced? fuel lt source key
                (lower + (upper - lower) / 2 + 1) upper).result =
                some result := by
            simpa only [middle] using hresult
          refine ⟨result, ?_, hnotExhausted, ?_, hresultUpper, ?_⟩
          · simp only [gallopLeftBinaryTraced?, if_pos hsearch,
              TraceResult.bind, hreadResult', if_pos hcompare, hresult']
          · omega
          · have hbound := gallopTraceSafe_bind
              (source.readTraced? (Int.ofNat middle))
              (fun readEntry =>
                if iflt lt readEntry.key key then
                  gallopLeftBinaryTraced? fuel lt source key (middle + 1) upper
                else gallopLeftBinaryTraced? fuel lt source key lower middle)
              entry hreadResult hreadSafe
              (by simpa only [if_pos hcompare] using htrace)
            rw [gallopLeftBinaryTraced?, if_pos hsearch]
            exact hbound
        · have hnextUpper : middle ≤ n := by omega
          have hnextBudget : middle - lower ≤ fuel := by
            dsimp [middle]
            omega
          rcases ih lower middle hlowerMiddle hnextUpper hnextBudget with
            ⟨result, hresult, hnotExhausted, hresultLower, hresultUpper,
              htrace⟩
          have hreadResult' :
              (source.readTraced?
                (Int.ofNat (lower + (upper - lower) / 2))).result =
                some entry := by
            simpa only [middle] using hreadResult
          have hresult' :
              (gallopLeftBinaryTraced? fuel lt source key lower
                (lower + (upper - lower) / 2)).result = some result := by
            simpa only [middle] using hresult
          refine ⟨result, ?_, hnotExhausted, hresultLower, ?_, ?_⟩
          · simp only [gallopLeftBinaryTraced?, if_pos hsearch,
              TraceResult.bind, hreadResult', if_neg hcompare, hresult']
          · omega
          · have hbound := gallopTraceSafe_bind
              (source.readTraced? (Int.ofNat middle))
              (fun readEntry =>
                if iflt lt readEntry.key key then
                  gallopLeftBinaryTraced? fuel lt source key (middle + 1) upper
                else gallopLeftBinaryTraced? fuel lt source key lower middle)
              entry hreadResult hreadSafe
              (by simpa only [if_neg hcompare] using htrace)
            rw [gallopLeftBinaryTraced?, if_pos hsearch]
            exact hbound
      · have hequal : lower = upper := by omega
        let outcome : GallopResult := ⟨upper, false⟩
        refine ⟨outcome, ?_, rfl, ?_, Nat.le_refl upper, ?_⟩
        · simp [gallopLeftBinaryTraced?, hsearch, TraceResult.pure, outcome]
        · omega
        · simp [gallopLeftBinaryTraced?, hsearch]

/-! ### Auditable left/right comparator duality -/

/-- Swapping the arguments and negating the Boolean result turns the
left-biased branch test into the right-biased branch test.  No law of the
original comparator is used. -/
def gallopComparatorDual (lt : BoolComparator κ) : BoolComparator κ :=
  fun left right => !(lt right left)

@[simp]
theorem gallopComparatorDual_apply (lt : BoolComparator κ) (left right : κ) :
    gallopComparatorDual lt left right = !(lt right left) := rfl

/-- The rightward exponential phase of `gallop_right` is definitionally the
rightward `gallop_left` phase under comparator duality. -/
theorem gallopRightRight_eq_leftRight_dual (fuel : Nat)
    (lt : BoolComparator κ) (source : GallopKeySource κ ν) (key : κ)
    (hint maxOffset lastOffset offset : Nat) :
    gallopRightRightExponentialTraced? fuel lt source key hint maxOffset
        lastOffset offset =
      gallopLeftRightExponentialTraced? fuel (gallopComparatorDual lt) source
        key hint maxOffset lastOffset offset := by
  induction fuel generalizing lastOffset offset with
  | zero => rfl
  | succ fuel ih =>
      simp only [gallopRightRightExponentialTraced?,
        gallopLeftRightExponentialTraced?]
      by_cases hprobe : offset < maxOffset
      · rw [if_pos hprobe, if_pos hprobe]
        apply congrArg
          (TraceResult.bind
            (source.readTraced? (Int.ofNat (hint + offset))))
        funext entry
        by_cases hcompare : lt key entry.key = true
        · simp [gallopComparatorDual, hcompare]
        · have hfalse : lt key entry.key = false :=
            Bool.eq_false_of_not_eq_true hcompare
          simp [gallopComparatorDual, hfalse, ih]
      · simp [hprobe]

/-- The leftward exponential phase of `gallop_right` is the leftward
`gallop_left` phase under comparator duality. -/
theorem gallopRightLeft_eq_leftLeft_dual (fuel : Nat)
    (lt : BoolComparator κ) (source : GallopKeySource κ ν) (key : κ)
    (hint maxOffset lastOffset offset : Nat) :
    gallopRightLeftExponentialTraced? fuel lt source key hint maxOffset
        lastOffset offset =
      gallopLeftLeftExponentialTraced? fuel (gallopComparatorDual lt) source
        key hint maxOffset lastOffset offset := by
  induction fuel generalizing lastOffset offset with
  | zero => rfl
  | succ fuel ih =>
      simp only [gallopRightLeftExponentialTraced?,
        gallopLeftLeftExponentialTraced?]
      by_cases hprobe : offset < maxOffset
      · rw [if_pos hprobe, if_pos hprobe]
        apply congrArg
          (TraceResult.bind
            (source.readTraced? (Int.ofNat hint - Int.ofNat offset)))
        funext entry
        by_cases hcompare : lt key entry.key = true
        · simp [gallopComparatorDual, hcompare, ih]
        · have hfalse : lt key entry.key = false :=
            Bool.eq_false_of_not_eq_true hcompare
          simp [gallopComparatorDual, hfalse]
      · simp [hprobe]

/-- The right-biased binary phase is the left-biased binary phase under the
same explicit comparator duality. -/
theorem gallopRightBinary_eq_leftBinary_dual (fuel : Nat)
    (lt : BoolComparator κ) (source : GallopKeySource κ ν) (key : κ)
    (lower upper : Nat) :
    gallopRightBinaryTraced? fuel lt source key lower upper =
      gallopLeftBinaryTraced? fuel (gallopComparatorDual lt) source key
        lower upper := by
  induction fuel generalizing lower upper with
  | zero => rfl
  | succ fuel ih =>
      simp only [gallopRightBinaryTraced?, gallopLeftBinaryTraced?]
      by_cases hsearch : lower < upper
      · rw [if_pos hsearch, if_pos hsearch]
        let middle := lower + (upper - lower) / 2
        apply congrArg
          (TraceResult.bind (source.readTraced? (Int.ofNat middle)))
        funext entry
        by_cases hcompare : lt key entry.key = true
        · simp [gallopComparatorDual, hcompare, ih]
        · have hfalse : lt key entry.key = false :=
            Bool.eq_false_of_not_eq_true hcompare
          simp [gallopComparatorDual, hfalse, ih]
      · simp [hsearch]

/-- Safety of the rightward `gallop_right` exponential phase, transported
through the explicit comparator-duality equality above. -/
theorem gallopRightRightExponential_safe (fuel : Nat)
    (lt : BoolComparator κ) (source : GallopKeySource κ ν) (key : κ)
    (hint maxOffset lastOffset offset n : Nat)
    (hvalid : source.ValidRange n) (hlive : source.Live)
    (hwindow : hint + maxOffset ≤ n) (hnmax : n ≤ PY_LIST_MAX)
    (hoffsetPositive : 0 < offset) (hlastOffset : lastOffset < offset)
    (hlastMax : lastOffset < maxOffset)
    (hbudget : maxOffset ≤ fuel + offset) :
    ∃ result,
      (gallopRightRightExponentialTraced? fuel lt source key hint maxOffset
        lastOffset offset).result = some result ∧
      result.fuelExhausted = false ∧
      result.lastOffset < result.offset ∧
      result.lastOffset < maxOffset ∧
      GallopTraceSafe
        (gallopRightRightExponentialTraced? fuel lt source key hint maxOffset
          lastOffset offset) := by
  rw [gallopRightRight_eq_leftRight_dual]
  exact gallopLeftRightExponential_safe fuel (gallopComparatorDual lt) source
    key hint maxOffset lastOffset offset n hvalid hlive hwindow hnmax
    hoffsetPositive hlastOffset hlastMax hbudget

/-- Safety of the leftward `gallop_right` exponential phase, transported
through comparator duality. -/
theorem gallopRightLeftExponential_safe (fuel : Nat)
    (lt : BoolComparator κ) (source : GallopKeySource κ ν) (key : κ)
    (hint maxOffset lastOffset offset n : Nat)
    (hvalid : source.ValidRange n) (hlive : source.Live)
    (hhint : hint < n) (hwindow : maxOffset ≤ hint + 1)
    (hnmax : n ≤ PY_LIST_MAX)
    (hoffsetPositive : 0 < offset) (hlastOffset : lastOffset < offset)
    (hlastMax : lastOffset < maxOffset)
    (hbudget : maxOffset ≤ fuel + offset) :
    ∃ result,
      (gallopRightLeftExponentialTraced? fuel lt source key hint maxOffset
        lastOffset offset).result = some result ∧
      result.fuelExhausted = false ∧
      result.lastOffset < result.offset ∧
      result.lastOffset < maxOffset ∧
      GallopTraceSafe
        (gallopRightLeftExponentialTraced? fuel lt source key hint maxOffset
          lastOffset offset) := by
  rw [gallopRightLeft_eq_leftLeft_dual]
  exact gallopLeftLeftExponential_safe fuel (gallopComparatorDual lt) source
    key hint maxOffset lastOffset offset n hvalid hlive hhint hwindow hnmax
    hoffsetPositive hlastOffset hlastMax hbudget

/-- Safety of the right-biased binary finishing phase, transported through
comparator duality. -/
theorem gallopRightBinary_safe (fuel : Nat) (lt : BoolComparator κ)
    (source : GallopKeySource κ ν) (key : κ) (lower upper n : Nat)
    (hvalid : source.ValidRange n) (hlive : source.Live)
    (hlowerUpper : lower ≤ upper) (hupper : upper ≤ n)
    (hbudget : upper - lower ≤ fuel) :
    ∃ result,
      (gallopRightBinaryTraced? fuel lt source key lower upper).result =
        some result ∧
      result.fuelExhausted = false ∧
      lower ≤ result.index ∧
      result.index ≤ upper ∧
      GallopTraceSafe
        (gallopRightBinaryTraced? fuel lt source key lower upper) := by
  rw [gallopRightBinary_eq_leftBinary_dual]
  exact gallopLeftBinary_safe fuel (gallopComparatorDual lt) source key lower
    upper n hvalid hlive hlowerUpper hupper hbudget

/-! ### Finishing-phase assembly -/

/-- Once the exponential phase supplies a valid signed interval and reports
non-exhaustion, the left-biased binary finish is total and safe. -/
theorem finishGallopLeft_safe (fuel : Nat) (lt : BoolComparator κ)
    (source : GallopKeySource κ ν) (key : κ) (n : Nat)
    (lastOffset upperOffset : Int)
    (hvalid : source.ValidRange n) (hlive : source.Live)
    (hlast : -1 ≤ lastOffset) (horder : lastOffset < upperOffset)
    (hupper : upperOffset ≤ Int.ofNat n)
    (hlowerNonnegative : 0 ≤ lastOffset + 1)
    (hupperNonnegative : 0 ≤ upperOffset) (hfuel : n ≤ fuel) :
    ∃ result,
      (finishGallopLeftTraced? fuel lt source key n lastOffset upperOffset
        false).result = some result ∧
      result.fuelExhausted = false ∧
      result.index ≤ n ∧
      GallopTraceSafe
        (finishGallopLeftTraced? fuel lt source key n lastOffset upperOffset
          false) := by
  let lower := (lastOffset + 1).toNat
  let upper := upperOffset.toNat
  have hlowerUpper : lower ≤ upper := by
    apply Int.toNat_le_toNat
    omega
  have hupperNat : upper ≤ n := by
    exact Int.toNat_le.mpr hupper
  have hbudget : upper - lower ≤ fuel := by omega
  rcases gallopLeftBinary_safe fuel lt source key lower upper n hvalid hlive
      hlowerUpper hupperNat hbudget with
    ⟨result, hresult, hnotExhausted, _hresultLower, hresultUpper, htrace⟩
  have houter :
      -1 ≤ lastOffset ∧ lastOffset < upperOffset ∧
        upperOffset ≤ Int.ofNat n := ⟨hlast, horder, hupper⟩
  have hinner : 0 ≤ lastOffset + 1 ∧ 0 ≤ upperOffset :=
    ⟨hlowerNonnegative, hupperNonnegative⟩
  have hfinish :
      finishGallopLeftTraced? fuel lt source key n lastOffset upperOffset false =
        gallopLeftBinaryTraced? fuel lt source key lower upper := by
    unfold finishGallopLeftTraced?
    rw [if_pos houter]
    rw [if_pos hinner]
    rfl
  rw [hfinish]
  exact ⟨result, hresult, hnotExhausted, by omega, htrace⟩

/-- Right-biased counterpart of `finishGallopLeft_safe`. -/
theorem finishGallopRight_safe (fuel : Nat) (lt : BoolComparator κ)
    (source : GallopKeySource κ ν) (key : κ) (n : Nat)
    (lastOffset upperOffset : Int)
    (hvalid : source.ValidRange n) (hlive : source.Live)
    (hlast : -1 ≤ lastOffset) (horder : lastOffset < upperOffset)
    (hupper : upperOffset ≤ Int.ofNat n)
    (hlowerNonnegative : 0 ≤ lastOffset + 1)
    (hupperNonnegative : 0 ≤ upperOffset) (hfuel : n ≤ fuel) :
    ∃ result,
      (finishGallopRightTraced? fuel lt source key n lastOffset upperOffset
        false).result = some result ∧
      result.fuelExhausted = false ∧
      result.index ≤ n ∧
      GallopTraceSafe
        (finishGallopRightTraced? fuel lt source key n lastOffset upperOffset
          false) := by
  let lower := (lastOffset + 1).toNat
  let upper := upperOffset.toNat
  have hlowerUpper : lower ≤ upper := by
    apply Int.toNat_le_toNat
    omega
  have hupperNat : upper ≤ n := by
    exact Int.toNat_le.mpr hupper
  have hbudget : upper - lower ≤ fuel := by omega
  rcases gallopRightBinary_safe fuel lt source key lower upper n hvalid hlive
      hlowerUpper hupperNat hbudget with
    ⟨result, hresult, hnotExhausted, _hresultLower, hresultUpper, htrace⟩
  have houter :
      -1 ≤ lastOffset ∧ lastOffset < upperOffset ∧
        upperOffset ≤ Int.ofNat n := ⟨hlast, horder, hupper⟩
  have hinner : 0 ≤ lastOffset + 1 ∧ 0 ≤ upperOffset :=
    ⟨hlowerNonnegative, hupperNonnegative⟩
  have hfinish :
      finishGallopRightTraced? fuel lt source key n lastOffset upperOffset false =
        gallopRightBinaryTraced? fuel lt source key lower upper := by
    unfold finishGallopRightTraced?
    rw [if_pos houter]
    rw [if_pos hinner]
    rfl
  rw [hfinish]
  exact ⟨result, hresult, hnotExhausted, by omega, htrace⟩

/-! ### Whole direct-source gallops -/

/-- The complete left-biased gallop is total, non-fuel-exhausting, bounded,
and trace-safe on any valid live source.  The comparator is arbitrary. -/
theorem gallopLeftFromSource_safe (state : MergeState κ ν)
    (source : GallopKeySource κ ν) (key : κ) (n hint : Nat)
    (hvalid : source.ValidRange n) (hlive : source.Live)
    (hn : 0 < n) (hhint : hint < n) (hnmax : n ≤ PY_LIST_MAX) :
    ∃ result,
      (gallopLeftTraced? state source key n hint).result = some result ∧
      result.fuelExhausted = false ∧
      result.index ≤ n ∧
      GallopTraceSafe (gallopLeftTraced? state source key n hint) := by
  have hnSsize : n ≤ PY_SSIZE_T_MAX := by
    norm_num [PY_LIST_MAX, PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES] at hnmax ⊢
    omega
  have hinput : 0 < n ∧ hint < n ∧ n ≤ PY_SSIZE_T_MAX :=
    ⟨hn, hhint, hnSsize⟩
  rcases source.readTraced_safe hvalid hlive hhint with
    ⟨hinted, hhintedResult, hhintedSafe⟩
  by_cases hcompare : iflt state.key_compare hinted.key key = true
  · let maxOffset := n - hint
    have hmaxPositive : 0 < maxOffset := by
      dsimp [maxOffset]
      omega
    have hwindow : hint + maxOffset ≤ n := by
      dsimp [maxOffset]
      omega
    have hbudget : maxOffset ≤ (n + 1) + 1 := by omega
    rcases gallopLeftRightExponential_safe (n + 1) state.key_compare source
        key hint maxOffset 0 1 n hvalid hlive hwindow hnmax (by omega)
        (by omega) hmaxPositive hbudget with
      ⟨exponential, hexponentialResult, hexponentialFuel,
        hexponentialOrder, hexponentialMax, hexponentialTrace⟩
    let capped := min exponential.offset maxOffset
    have hexponentialCapped : exponential.lastOffset < capped := by
      dsimp [capped]
      omega
    have hcappedMax : capped ≤ maxOffset := by
      exact Nat.min_le_right _ _
    have hlast :
        (-1 : Int) ≤
          Int.ofNat exponential.lastOffset + Int.ofNat hint := by
      simp only [Int.ofNat_eq_natCast]
      omega
    have horder :
        Int.ofNat exponential.lastOffset + Int.ofNat hint <
          Int.ofNat capped + Int.ofNat hint := by
      simp only [Int.ofNat_eq_natCast]
      omega
    have hupper :
        Int.ofNat capped + Int.ofNat hint ≤ Int.ofNat n := by
      simp only [Int.ofNat_eq_natCast]
      dsimp [maxOffset] at hcappedMax
      omega
    have hlowerNonnegative :
        0 ≤ Int.ofNat exponential.lastOffset + Int.ofNat hint + 1 := by
      simp only [Int.ofNat_eq_natCast]
      omega
    have hupperNonnegative :
        0 ≤ Int.ofNat capped + Int.ofNat hint := by
      simp only [Int.ofNat_eq_natCast]
      omega
    rcases finishGallopLeft_safe (n + 1) state.key_compare source key n
        (Int.ofNat exponential.lastOffset + Int.ofNat hint)
        (Int.ofNat capped + Int.ofNat hint) hvalid hlive hlast horder hupper
        hlowerNonnegative hupperNonnegative (by omega) with
      ⟨result, hfinishResult, hresultFuel, hresultBound, hfinishTrace⟩
    have hexponentialResult' :
        (gallopLeftRightExponentialTraced? (n + 1) state.key_compare source
          key hint (n - hint) 0 1).result = some exponential := by
      simpa only [maxOffset] using hexponentialResult
    have hbranchResult :
        ((gallopLeftRightExponentialTraced? (n + 1) state.key_compare source
            key hint (n - hint) 0 1).bind fun current =>
          let currentCapped := min current.offset (n - hint)
          finishGallopLeftTraced? (n + 1) state.key_compare source key n
            (Int.ofNat current.lastOffset + Int.ofNat hint)
            (Int.ofNat currentCapped + Int.ofNat hint)
            current.fuelExhausted).result = some result := by
      simp only [TraceResult.bind, hexponentialResult']
      simpa only [maxOffset, capped, hexponentialFuel] using hfinishResult
    have hbranchTrace : GallopTraceSafe
        ((gallopLeftRightExponentialTraced? (n + 1) state.key_compare source
            key hint (n - hint) 0 1).bind fun current =>
          let currentCapped := min current.offset (n - hint)
          finishGallopLeftTraced? (n + 1) state.key_compare source key n
            (Int.ofNat current.lastOffset + Int.ofNat hint)
            (Int.ofNat currentCapped + Int.ofNat hint)
            current.fuelExhausted) := by
      apply gallopTraceSafe_bind _ _ exponential hexponentialResult
        hexponentialTrace
      simpa only [maxOffset, capped, hexponentialFuel] using hfinishTrace
    refine ⟨result, ?_, hresultFuel, hresultBound, ?_⟩
    · simp only [gallopLeftTraced?, if_pos hinput, TraceResult.bind,
        hhintedResult, if_pos hcompare]
      exact hbranchResult
    · have hwhole := gallopTraceSafe_bind
        (source.readTraced? (Int.ofNat hint))
        (fun current =>
          if iflt state.key_compare current.key key then
            (gallopLeftRightExponentialTraced? (n + 1) state.key_compare source
              key hint (n - hint) 0 1).bind fun exponentialCurrent =>
                let currentCapped := min exponentialCurrent.offset (n - hint)
                finishGallopLeftTraced? (n + 1) state.key_compare source key n
                  (Int.ofNat exponentialCurrent.lastOffset + Int.ofNat hint)
                  (Int.ofNat currentCapped + Int.ofNat hint)
                  exponentialCurrent.fuelExhausted
          else
            (gallopLeftLeftExponentialTraced? (n + 1) state.key_compare source
              key hint (hint + 1) 0 1).bind fun exponentialCurrent =>
                let currentCapped := min exponentialCurrent.offset (hint + 1)
                finishGallopLeftTraced? (n + 1) state.key_compare source key n
                  (Int.ofNat hint - Int.ofNat currentCapped)
                  (Int.ofNat hint - Int.ofNat exponentialCurrent.lastOffset)
                  exponentialCurrent.fuelExhausted)
        hinted hhintedResult hhintedSafe
        (by simpa only [if_pos hcompare] using hbranchTrace)
      rw [gallopLeftTraced?, if_pos hinput]
      exact hwhole
  · let maxOffset := hint + 1
    have hmaxPositive : 0 < maxOffset := by
      dsimp [maxOffset]
      omega
    have hwindow : maxOffset ≤ hint + 1 := by rfl
    have hbudget : maxOffset ≤ (n + 1) + 1 := by
      dsimp [maxOffset]
      omega
    rcases gallopLeftLeftExponential_safe (n + 1) state.key_compare source
        key hint maxOffset 0 1 n hvalid hlive hhint hwindow hnmax (by omega)
        (by omega) hmaxPositive hbudget with
      ⟨exponential, hexponentialResult, hexponentialFuel,
        hexponentialOrder, hexponentialMax, hexponentialTrace⟩
    let capped := min exponential.offset maxOffset
    have hexponentialCapped : exponential.lastOffset < capped := by
      dsimp [capped]
      omega
    have hcappedMax : capped ≤ maxOffset := Nat.min_le_right _ _
    have hlast :
        (-1 : Int) ≤ Int.ofNat hint - Int.ofNat capped := by
      simp only [Int.ofNat_eq_natCast]
      dsimp [maxOffset] at hcappedMax
      omega
    have horder :
        Int.ofNat hint - Int.ofNat capped <
          Int.ofNat hint - Int.ofNat exponential.lastOffset := by
      simp only [Int.ofNat_eq_natCast]
      omega
    have hupper :
        Int.ofNat hint - Int.ofNat exponential.lastOffset ≤
          Int.ofNat n := by
      simp only [Int.ofNat_eq_natCast]
      omega
    have hlowerNonnegative :
        0 ≤ Int.ofNat hint - Int.ofNat capped + 1 := by
      simp only [Int.ofNat_eq_natCast]
      dsimp [maxOffset] at hcappedMax
      omega
    have hupperNonnegative :
        0 ≤ Int.ofNat hint - Int.ofNat exponential.lastOffset := by
      simp only [Int.ofNat_eq_natCast]
      dsimp [maxOffset] at hexponentialMax
      omega
    rcases finishGallopLeft_safe (n + 1) state.key_compare source key n
        (Int.ofNat hint - Int.ofNat capped)
        (Int.ofNat hint - Int.ofNat exponential.lastOffset) hvalid hlive
        hlast horder hupper hlowerNonnegative hupperNonnegative (by omega) with
      ⟨result, hfinishResult, hresultFuel, hresultBound, hfinishTrace⟩
    have hexponentialResult' :
        (gallopLeftLeftExponentialTraced? (n + 1) state.key_compare source
          key hint (hint + 1) 0 1).result = some exponential := by
      simpa only [maxOffset] using hexponentialResult
    have hbranchResult :
        ((gallopLeftLeftExponentialTraced? (n + 1) state.key_compare source
            key hint (hint + 1) 0 1).bind fun current =>
          let currentCapped := min current.offset (hint + 1)
          finishGallopLeftTraced? (n + 1) state.key_compare source key n
            (Int.ofNat hint - Int.ofNat currentCapped)
            (Int.ofNat hint - Int.ofNat current.lastOffset)
            current.fuelExhausted).result = some result := by
      simp only [TraceResult.bind, hexponentialResult']
      simpa only [maxOffset, capped, hexponentialFuel] using hfinishResult
    have hbranchTrace : GallopTraceSafe
        ((gallopLeftLeftExponentialTraced? (n + 1) state.key_compare source
            key hint (hint + 1) 0 1).bind fun current =>
          let currentCapped := min current.offset (hint + 1)
          finishGallopLeftTraced? (n + 1) state.key_compare source key n
            (Int.ofNat hint - Int.ofNat currentCapped)
            (Int.ofNat hint - Int.ofNat current.lastOffset)
            current.fuelExhausted) := by
      apply gallopTraceSafe_bind _ _ exponential hexponentialResult
        hexponentialTrace
      simpa only [maxOffset, capped, hexponentialFuel] using hfinishTrace
    refine ⟨result, ?_, hresultFuel, hresultBound, ?_⟩
    · simp only [gallopLeftTraced?, if_pos hinput, TraceResult.bind,
        hhintedResult, if_neg hcompare]
      exact hbranchResult
    · have hwhole := gallopTraceSafe_bind
        (source.readTraced? (Int.ofNat hint))
        (fun current =>
          if iflt state.key_compare current.key key then
            (gallopLeftRightExponentialTraced? (n + 1) state.key_compare source
              key hint (n - hint) 0 1).bind fun exponentialCurrent =>
                let currentCapped := min exponentialCurrent.offset (n - hint)
                finishGallopLeftTraced? (n + 1) state.key_compare source key n
                  (Int.ofNat exponentialCurrent.lastOffset + Int.ofNat hint)
                  (Int.ofNat currentCapped + Int.ofNat hint)
                  exponentialCurrent.fuelExhausted
          else
            (gallopLeftLeftExponentialTraced? (n + 1) state.key_compare source
              key hint (hint + 1) 0 1).bind fun exponentialCurrent =>
                let currentCapped := min exponentialCurrent.offset (hint + 1)
                finishGallopLeftTraced? (n + 1) state.key_compare source key n
                  (Int.ofNat hint - Int.ofNat currentCapped)
                  (Int.ofNat hint - Int.ofNat exponentialCurrent.lastOffset)
                  exponentialCurrent.fuelExhausted)
        hinted hhintedResult hhintedSafe
        (by simpa only [if_neg hcompare] using hbranchTrace)
      rw [gallopLeftTraced?, if_pos hinput]
      exact hwhole

/-- State obtained by replacing only the comparator with the auditable dual.
All geometry and storage fields are unchanged. -/
def gallopDualState (state : MergeState κ ν) : MergeState κ ν :=
  { state with key_compare := gallopComparatorDual state.key_compare }

@[simp]
theorem gallopDualState_keyCompare (state : MergeState κ ν) :
    (gallopDualState state).key_compare =
      gallopComparatorDual state.key_compare := rfl

/-- Whole-evaluator equality exposing why right-gallop safety follows from
left-gallop safety without any comparator law.  The traces are equal, not just
their erased results. -/
theorem gallopRight_eq_left_dual (state : MergeState κ ν)
    (source : GallopKeySource κ ν) (key : κ) (n hint : Nat) :
    gallopRightTraced? state source key n hint =
      gallopLeftTraced? (gallopDualState state) source key n hint := by
  simp only [gallopRightTraced?, gallopLeftTraced?]
  by_cases hinput : 0 < n ∧ hint < n ∧ n ≤ PY_SSIZE_T_MAX
  · rw [if_pos hinput, if_pos hinput]
    apply congrArg (TraceResult.bind (source.readTraced? (Int.ofNat hint)))
    funext hinted
    by_cases hcompare : state.key_compare key hinted.key = true
    · simp [gallopDualState, gallopComparatorDual, hcompare,
        gallopRightLeft_eq_leftLeft_dual,
        finishGallopRightTraced?, finishGallopLeftTraced?,
        gallopRightBinary_eq_leftBinary_dual]
    · have hfalse : state.key_compare key hinted.key = false :=
        Bool.eq_false_of_not_eq_true hcompare
      simp [gallopDualState, gallopComparatorDual, hfalse,
        gallopRightRight_eq_leftRight_dual,
        finishGallopRightTraced?, finishGallopLeftTraced?,
        gallopRightBinary_eq_leftBinary_dual]
  · rw [if_neg hinput, if_neg hinput]

/-- Complete right-biased source safety, transported through exact traced
comparator duality. -/
theorem gallopRightFromSource_safe (state : MergeState κ ν)
    (source : GallopKeySource κ ν) (key : κ) (n hint : Nat)
    (hvalid : source.ValidRange n) (hlive : source.Live)
    (hn : 0 < n) (hhint : hint < n) (hnmax : n ≤ PY_LIST_MAX) :
    ∃ result,
      (gallopRightTraced? state source key n hint).result = some result ∧
      result.fuelExhausted = false ∧
      result.index ≤ n ∧
      GallopTraceSafe (gallopRightTraced? state source key n hint) := by
  rw [gallopRight_eq_left_dual]
  exact gallopLeftFromSource_safe (gallopDualState state) source key n hint
    hvalid hlive hn hhint hnmax

end CPythonListsort
