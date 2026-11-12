/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.AccessTrace
import Mathlib

/-!
# Safety of the `sortslice` movement primitives

The instrumentation in this file is assembled directly from the typed
`SortSlice` access wrappers.  The Boolean `valuesPresent` is the modeled C
pointer mode: synchronized-values events are controlled only by that flag and
never by an individual entry's optional payload.

Bulk operations follow the source's two phases exactly: every key movement is
observed before any synchronized-values movement.  Each phase independently
executes the paired-entry transcription.  This is intentional: one execution
models movement of the key array and the other movement of the values array;
both erase to the same atomic paired-entry operation.
-/

namespace CPythonListsort

universe u v

namespace SortSlice

/-- An entry agrees with the explicit C `values != NULL` mode.  In values
mode every payload exists; without a values array every payload is absent. -/
def EntryMatchesValuesMode (valuesPresent : Bool)
    (entry : SortSliceEntry κ ν) : Prop :=
  match valuesPresent with
  | false => entry.value = none
  | true => ∃ value, entry.value = some value

/-- Global representation invariant connecting the separate C-pointer mode to
the paired-entry model.  The trace mode is never inferred from an individual
entry: instead, every entry must agree with the supplied mode. -/
def ValuesModeInvariant (valuesPresent : Bool) (slice : SortSlice κ ν) : Prop :=
  ∀ (index : Nat) (hindex : index < slice.entries.size),
    EntryMatchesValuesMode valuesPresent slice.entries[index]

/-- A signed index denotes an existing cell of `slice`. -/
def IndexInBounds (slice : SortSlice κ ν) (index : Int) : Prop :=
  0 ≤ index ∧ index < Int.ofNat slice.entries.size

/-- A pointer-like cursor lies between the beginning of the slice and its
permitted one-past endpoint, inclusive.  Unlike `IndexInBounds`, the upper
endpoint is a valid cursor but cannot itself be dereferenced. -/
def CursorInRange (slice : SortSlice κ ν) (cursor : Int) : Prop :=
  0 ≤ cursor ∧ cursor ≤ Int.ofNat slice.entries.size

/-- An `advance` starts at a valid cursor and its signed displacement stays
between the distance back to zero and the distance forward to the permitted
one-past endpoint.  This states the arithmetic obligation independently of
the desired postcondition even though advancement emits no indexed access. -/
def CursorMovementInRange (slice : SortSlice κ ν)
    (index amount : Int) : Prop :=
  CursorInRange slice index ∧
    -index ≤ amount ∧
    amount ≤ Int.ofNat slice.entries.size - index

/-- The half-open range `[start, start + count)` lies in `slice`.  For
`count = 0`, a one-past-the-end cursor is admitted. -/
def RangeInBounds (slice : SortSlice κ ν) (start : Int)
    (count : Nat) : Prop :=
  0 ≤ start ∧ start + Int.ofNat count ≤ Int.ofNat slice.entries.size

/-- One key-array copy, using the typed key read and key write wrappers. -/
def copyKeysFromTraced? (destination source : SortSlice κ ν)
    (dst src : Int) : TraceResult (SortSlice κ ν) :=
  (TraceResult.sortSliceKeysRead? source src).bind fun entry =>
    TraceResult.sortSliceKeysWrite? destination dst entry

/-- One synchronized-values copy.  This primitive is called only when the
explicit C-pointer mode says that a values array is present. -/
def copyValuesFromTraced? (destination source : SortSlice κ ν)
    (dst src : Int) : TraceResult (SortSlice κ ν) :=
  (TraceResult.sortSliceValuesRead? source src).bind fun entry =>
    TraceResult.sortSliceValuesWrite? destination dst entry

/-- Traced `sortslice_copy`: key read/write first, followed by values
read/write exactly when `valuesPresent` is true. -/
def copyFromTraced? (valuesPresent : Bool)
    (destination source : SortSlice κ ν) (dst src : Int) :
    TraceResult (SortSlice κ ν) :=
  (copyKeysFromTraced? destination source dst src).bind fun keyResult =>
    if valuesPresent then
      copyValuesFromTraced? destination source dst src
    else
      TraceResult.pure keyResult

/-- Shared-store specialization of `copyFromTraced?`. -/
def copyTraced? (valuesPresent : Bool) (slice : SortSlice κ ν)
    (dst src : Int) : TraceResult (SortSlice κ ν) :=
  copyFromTraced? valuesPresent slice slice dst src

/-- Traced `sortslice_copy_incr` over its general two-slice C domain; cursor
movement occurs after the copy and only the destination store is updated. -/
def copyFromIncrTraced? (valuesPresent : Bool)
    (destination source : SortSlice κ ν)
    (dst src : Int) : TraceResult (CursorResult κ ν) :=
  (copyFromTraced? valuesPresent destination source dst src).map fun updated =>
    { slice := updated, dst := dst + 1, src := src + 1 }

/-- Traced `sortslice_copy_decr` over its general two-slice C domain; cursor
movement occurs after the copy and only the destination store is updated. -/
def copyFromDecrTraced? (valuesPresent : Bool)
    (destination source : SortSlice κ ν)
    (dst src : Int) : TraceResult (CursorResult κ ν) :=
  (copyFromTraced? valuesPresent destination source dst src).map fun updated =>
    { slice := updated, dst := dst - 1, src := src - 1 }

/-- Shared-store specialization of `copyFromIncrTraced?`. -/
def copyIncrTraced? (valuesPresent : Bool) (slice : SortSlice κ ν)
    (dst src : Int) : TraceResult (CursorResult κ ν) :=
  copyFromIncrTraced? valuesPresent slice slice dst src

/-- Shared-store specialization of `copyFromDecrTraced?`. -/
def copyDecrTraced? (valuesPresent : Bool) (slice : SortSlice κ ν)
    (dst src : Int) : TraceResult (CursorResult κ ν) :=
  copyFromDecrTraced? valuesPresent slice slice dst src

/-- Key-array phase of `sortslice_memcpy`, in increasing address order. -/
def memcpyKeysTraced? :
    Nat → SortSlice κ ν → SortSlice κ ν → Int → Int →
      TraceResult (SortSlice κ ν)
  | 0, destination, _, _, _ => TraceResult.pure destination
  | count + 1, destination, source, dst, src =>
      (copyKeysFromTraced? destination source dst src).bind fun updated =>
        memcpyKeysTraced? count updated source (dst + 1) (src + 1)

/-- Synchronized-values phase of `sortslice_memcpy`, also increasing. -/
def memcpyValuesTraced? :
    Nat → SortSlice κ ν → SortSlice κ ν → Int → Int →
      TraceResult (SortSlice κ ν)
  | 0, destination, _, _, _ => TraceResult.pure destination
  | count + 1, destination, source, dst, src =>
      (copyValuesFromTraced? destination source dst src).bind fun updated =>
        memcpyValuesTraced? count updated source (dst + 1) (src + 1)

/-- Traced `sortslice_memcpy`.  The backing-domain check occurs before either
physical phase.  On an admissible call the second phase starts from the
original paired store, reflecting that C's key and values arrays are distinct. -/
def memcpyTraced? (valuesPresent : Bool) (count : Nat)
    (destination : SortSlice κ ν) (source : MemcpySource destination)
    (dst src : Int) :
    TraceResult (SortSlice κ ν) :=
  if source.Admissible dst src count then
    (memcpyKeysTraced? count destination source.store dst src).bind fun keyResult =>
      if valuesPresent then
        memcpyValuesTraced? count destination source.store dst src
      else
        TraceResult.pure keyResult
  else
    TraceResult.failure

/-- Forward key phase of an overlap-safe move. -/
def memmoveForwardKeysTraced? :
    Nat → SortSlice κ ν → Int → Int → TraceResult (SortSlice κ ν)
  | 0, slice, _, _ => TraceResult.pure slice
  | count + 1, slice, dst, src =>
      (copyKeysFromTraced? slice slice dst src).bind fun updated =>
        memmoveForwardKeysTraced? count updated (dst + 1) (src + 1)

/-- Forward synchronized-values phase of an overlap-safe move. -/
def memmoveForwardValuesTraced? :
    Nat → SortSlice κ ν → Int → Int → TraceResult (SortSlice κ ν)
  | 0, slice, _, _ => TraceResult.pure slice
  | count + 1, slice, dst, src =>
      (copyValuesFromTraced? slice slice dst src).bind fun updated =>
        memmoveForwardValuesTraced? count updated (dst + 1) (src + 1)

/-- Backward key phase.  The first event is at offset `count`, matching the
source-safe right-to-left traversal in the transcription. -/
def memmoveBackwardKeysTraced? :
    Nat → SortSlice κ ν → Int → Int → TraceResult (SortSlice κ ν)
  | 0, slice, _, _ => TraceResult.pure slice
  | count + 1, slice, dst, src =>
      let offset := Int.ofNat count
      (copyKeysFromTraced? slice slice (dst + offset) (src + offset)).bind
        fun updated => memmoveBackwardKeysTraced? count updated dst src

/-- Backward synchronized-values phase, with the identical overlap order. -/
def memmoveBackwardValuesTraced? :
    Nat → SortSlice κ ν → Int → Int → TraceResult (SortSlice κ ν)
  | 0, slice, _, _ => TraceResult.pure slice
  | count + 1, slice, dst, src =>
      let offset := Int.ofNat count
      (copyValuesFromTraced? slice slice (dst + offset) (src + offset)).bind
        fun updated => memmoveBackwardValuesTraced? count updated dst src

/-- Traced overlap-safe movement.  Both key and values phases use the same
direction selected by `memmoveDirection`; all key events precede value events. -/
def memmoveTraced? (valuesPresent : Bool) (slice : SortSlice κ ν)
    (dst src : Int) (count : Nat) : TraceResult (SortSlice κ ν) :=
  match memmoveDirection dst src with
  | .forward =>
      (memmoveForwardKeysTraced? count slice dst src).bind fun keyResult =>
        if valuesPresent then
          memmoveForwardValuesTraced? count slice dst src
        else
          TraceResult.pure keyResult
  | .backward =>
      (memmoveBackwardKeysTraced? count slice dst src).bind fun keyResult =>
      if valuesPresent then
          memmoveBackwardValuesTraced? count slice dst src
        else
          TraceResult.pure keyResult

/-- Traced general two-store `sortslice_memmove`.  Explicit same-backing
provenance selects the overlap-safe directional trace, while explicit distinct
provenance selects increasing-address key and values phases over the unchanged
source store. -/
def memmoveFromTraced? (valuesPresent : Bool)
    (destination : SortSlice κ ν) (source : MemmoveSource destination)
    (dst src : Int) (count : Nat) : TraceResult (SortSlice κ ν) :=
  match source with
  | .sameBacking => memmoveTraced? valuesPresent destination dst src count
  | .distinctBacking source =>
      (memcpyKeysTraced? count destination source dst src).bind fun keyResult =>
        if valuesPresent then
          memcpyValuesTraced? count destination source dst src
        else
          TraceResult.pure keyResult

@[simp]
theorem memmoveFromTraced_sameBacking (valuesPresent : Bool)
    (destination : SortSlice κ ν) (dst src : Int) (count : Nat) :
    memmoveFromTraced? valuesPresent destination .sameBacking dst src count =
      memmoveTraced? valuesPresent destination dst src count := by
  rfl

/-- Pointer advancement emits no indexed access.  `valuesPresent` remains an
explicit input because C advances the optional values pointer in the same
mode, but both pointer adjustments erase to the model's single cursor. -/
def advanceTraced (_valuesPresent : Bool) (index amount : Int) :
    TraceResult Int :=
  TraceResult.pure (advance index amount)

/-! ## Exact erasure -/

@[simp]
theorem erase_copyKeysFromTraced (destination source : SortSlice κ ν)
    (dst src : Int) :
    (copyKeysFromTraced? destination source dst src).erase =
      destination.copyFrom? source dst src := by
  simp [copyKeysFromTraced?, copyFrom?, TraceResult.erase_bind]

@[simp]
theorem erase_copyValuesFromTraced (destination source : SortSlice κ ν)
    (dst src : Int) :
    (copyValuesFromTraced? destination source dst src).erase =
      destination.copyFrom? source dst src := by
  simp [copyValuesFromTraced?, copyFrom?, TraceResult.erase_bind]

@[simp]
theorem erase_copyFromTraced (valuesPresent : Bool)
    (destination source : SortSlice κ ν) (dst src : Int) :
    (copyFromTraced? valuesPresent destination source dst src).erase =
      destination.copyFrom? source dst src := by
  unfold copyFromTraced?
  rw [TraceResult.erase_bind, erase_copyKeysFromTraced]
  cases hcopy : destination.copyFrom? source dst src <;>
    cases valuesPresent <;> simp [hcopy]

@[simp]
theorem erase_copyTraced (valuesPresent : Bool) (slice : SortSlice κ ν)
    (dst src : Int) :
    (copyTraced? valuesPresent slice dst src).erase = slice.copy? dst src := by
  simp [copyTraced?, copy?]

@[simp]
theorem erase_copyFromIncrTraced (valuesPresent : Bool)
    (destination source : SortSlice κ ν)
    (dst src : Int) :
    (copyFromIncrTraced? valuesPresent destination source dst src).erase =
      destination.copyFromIncr? source dst src := by
  simp only [copyFromIncrTraced?, TraceResult.erase_map,
    erase_copyFromTraced]
  cases hcopy : destination.copyFrom? source dst src <;>
    simp [copyFromIncr?, hcopy]

@[simp]
theorem erase_copyFromDecrTraced (valuesPresent : Bool)
    (destination source : SortSlice κ ν)
    (dst src : Int) :
    (copyFromDecrTraced? valuesPresent destination source dst src).erase =
      destination.copyFromDecr? source dst src := by
  simp only [copyFromDecrTraced?, TraceResult.erase_map,
    erase_copyFromTraced]
  cases hcopy : destination.copyFrom? source dst src <;>
    simp [copyFromDecr?, hcopy]

@[simp]
theorem erase_copyIncrTraced (valuesPresent : Bool) (slice : SortSlice κ ν)
    (dst src : Int) :
    (copyIncrTraced? valuesPresent slice dst src).erase =
      slice.copyIncr? dst src := by
  simp [copyIncrTraced?, copyIncr?]

@[simp]
theorem erase_copyDecrTraced (valuesPresent : Bool) (slice : SortSlice κ ν)
    (dst src : Int) :
    (copyDecrTraced? valuesPresent slice dst src).erase =
      slice.copyDecr? dst src := by
  simp [copyDecrTraced?, copyDecr?]

@[simp]
theorem erase_memcpyKeysTraced (count : Nat)
    (destination source : SortSlice κ ν) (dst src : Int) :
    (memcpyKeysTraced? count destination source dst src).erase =
      memcpyCore? count destination source dst src := by
  induction count generalizing destination dst src with
  | zero => rfl
  | succ count ih =>
      simp [memcpyKeysTraced?, memcpyCore?, ih]

@[simp]
theorem erase_memcpyValuesTraced (count : Nat)
    (destination source : SortSlice κ ν) (dst src : Int) :
    (memcpyValuesTraced? count destination source dst src).erase =
      memcpyCore? count destination source dst src := by
  induction count generalizing destination dst src with
  | zero => rfl
  | succ count ih =>
      simp [memcpyValuesTraced?, memcpyCore?, ih]

@[simp]
theorem erase_memcpyTraced (valuesPresent : Bool) (count : Nat)
    (destination : SortSlice κ ν) (source : MemcpySource destination)
    (dst src : Int) :
    (memcpyTraced? valuesPresent count destination source dst src).erase =
      memcpy? count destination source dst src := by
  unfold memcpyTraced? memcpy?
  split
  · rw [TraceResult.erase_bind, erase_memcpyKeysTraced]
    cases hcopy : memcpyCore? count destination source.store dst src <;>
      cases valuesPresent <;> simp [hcopy]
  · rfl

/-- Rejected same-backing overlap produces neither a partial access trace nor
an observable traced result, and still obeys exact erasure. -/
theorem memcpyTraced_sameBacking_overlap_rejected (valuesPresent : Bool)
    (count : Nat) (destination : SortSlice κ ν) (dst src : Int)
    (hoverlap : ¬ MemcpyRangesDisjoint dst src count) :
    (memcpyTraced? valuesPresent count destination .sameBacking dst src).result = none ∧
      (memcpyTraced? valuesPresent count destination .sameBacking dst src).trace =
        AccessTrace.empty ∧
      (memcpyTraced? valuesPresent count destination .sameBacking dst src).erase =
        memcpy? count destination .sameBacking dst src := by
  simp [memcpyTraced?, memcpy?, MemcpySource.Admissible, hoverlap,
    TraceResult.failure, TraceResult.erase]

@[simp]
theorem erase_memmoveForwardKeysTraced (count : Nat)
    (slice : SortSlice κ ν) (dst src : Int) :
    (memmoveForwardKeysTraced? count slice dst src).erase =
      memmoveForward? count slice dst src := by
  induction count generalizing slice dst src with
  | zero => rfl
  | succ count ih =>
      simp [memmoveForwardKeysTraced?, memmoveForward?, ih, copy?]

@[simp]
theorem erase_memmoveForwardValuesTraced (count : Nat)
    (slice : SortSlice κ ν) (dst src : Int) :
    (memmoveForwardValuesTraced? count slice dst src).erase =
      memmoveForward? count slice dst src := by
  induction count generalizing slice dst src with
  | zero => rfl
  | succ count ih =>
      simp [memmoveForwardValuesTraced?, memmoveForward?, ih, copy?]

@[simp]
theorem erase_memmoveBackwardKeysTraced (count : Nat)
    (slice : SortSlice κ ν) (dst src : Int) :
    (memmoveBackwardKeysTraced? count slice dst src).erase =
      memmoveBackward? count slice dst src := by
  induction count generalizing slice dst src with
  | zero => rfl
  | succ count ih =>
      simp [memmoveBackwardKeysTraced?, memmoveBackward?, ih, copy?]

@[simp]
theorem erase_memmoveBackwardValuesTraced (count : Nat)
    (slice : SortSlice κ ν) (dst src : Int) :
    (memmoveBackwardValuesTraced? count slice dst src).erase =
      memmoveBackward? count slice dst src := by
  induction count generalizing slice dst src with
  | zero => rfl
  | succ count ih =>
      simp [memmoveBackwardValuesTraced?, memmoveBackward?, ih, copy?]

@[simp]
theorem erase_memmoveTraced (valuesPresent : Bool) (slice : SortSlice κ ν)
    (dst src : Int) (count : Nat) :
    (memmoveTraced? valuesPresent slice dst src count).erase =
      slice.memmove? dst src count := by
  cases hdir : memmoveDirection dst src with
  | forward =>
      simp only [memmoveTraced?, memmove?, hdir, TraceResult.erase_bind,
        erase_memmoveForwardKeysTraced]
      cases hmove : memmoveForward? count slice dst src <;>
        cases valuesPresent <;> simp [hmove]
  | backward =>
      simp only [memmoveTraced?, memmove?, hdir, TraceResult.erase_bind,
        erase_memmoveBackwardKeysTraced]
      cases hmove : memmoveBackward? count slice dst src <;>
        cases valuesPresent <;> simp [hmove]

@[simp]
theorem erase_memmoveFromTraced (valuesPresent : Bool)
    (destination : SortSlice κ ν) (source : MemmoveSource destination)
    (dst src : Int) (count : Nat) :
    (memmoveFromTraced? valuesPresent destination source dst src count).erase =
      memmoveFrom? destination source dst src count := by
  cases source with
  | sameBacking => simp [memmoveFromTraced?, memmoveFrom?]
  | distinctBacking source =>
      simp only [memmoveFromTraced?, memmoveFrom?, TraceResult.erase_bind,
        erase_memcpyKeysTraced]
      cases hmove : memcpyCore? count destination source dst src <;>
        cases valuesPresent <;> simp [hmove]

@[simp]
theorem erase_advanceTraced (valuesPresent : Bool) (index amount : Int) :
    (advanceTraced valuesPresent index amount).erase =
      some (advance index amount) := by
  rfl

/-! ## Valid ranges and exact local event order -/

theorem read_eq_some_of_indexInBounds (slice : SortSlice κ ν) (index : Int)
    (h : IndexInBounds slice index) :
    ∃ entry, slice.read? index = some entry := by
  rcases h with ⟨hnonnegative, hupper⟩
  have hnat : index.toNat < slice.entries.size :=
    (Int.toNat_lt hnonnegative).2 hupper
  refine ⟨slice.entries[index.toNat], ?_⟩
  simp [read?, hnonnegative, Array.getElem?_eq_getElem hnat]

theorem write_eq_some_of_indexInBounds (slice : SortSlice κ ν) (index : Int)
    (entry : SortSliceEntry κ ν) (h : IndexInBounds slice index) :
    ∃ updated, slice.write? index entry = some updated := by
  rcases h with ⟨hnonnegative, hupper⟩
  have hnat : index.toNat < slice.entries.size :=
    (Int.toNat_lt hnonnegative).2 hupper
  refine ⟨{ entries := slice.entries.set index.toNat entry }, ?_⟩
  simp [write?, hnonnegative, hnat]

/-- Regression for the representation gap this invariant closes: an entry
with a payload cannot inhabit a slice declared to have no values array. -/
theorem falseMode_somePayload_violates_invariant (key : κ) (value : ν) :
    ¬ ValuesModeInvariant false
      ({ entries := #[{ key := key, value := some value }] } : SortSlice κ ν) := by
  intro hinvariant
  have hentry := hinvariant 0 (by simp)
  simp [EntryMatchesValuesMode] at hentry

/-- Reading from a mode-valid slice can only return an entry matching that
same explicit values mode. -/
theorem ValuesModeInvariant.read_matches_of_eq_some
    {valuesPresent : Bool} {slice : SortSlice κ ν} {index : Int}
    {entry : SortSliceEntry κ ν}
    (hinvariant : ValuesModeInvariant valuesPresent slice)
    (hread : slice.read? index = some entry) :
    EntryMatchesValuesMode valuesPresent entry := by
  unfold read? at hread
  split at hread
  · rename_i hnonnegative
    have hindex : index.toNat < slice.entries.size := by
      by_contra hnot
      have hout : slice.entries[index.toNat]? = none :=
        Array.getElem?_eq_none (Nat.le_of_not_gt hnot)
      simp [hout] at hread
    rw [Array.getElem?_eq_getElem hindex] at hread
    simp only [Option.some.injEq] at hread
    subst entry
    exact hinvariant index.toNat hindex
  · simp at hread

/-- Replacing one cell with a mode-matching entry preserves the global
values-mode invariant. -/
theorem ValuesModeInvariant.write_preserved_of_eq_some
    {valuesPresent : Bool} {slice updated : SortSlice κ ν}
    {index : Int} {entry : SortSliceEntry κ ν}
    (hinvariant : ValuesModeInvariant valuesPresent slice)
    (hentry : EntryMatchesValuesMode valuesPresent entry)
    (hwrite : slice.write? index entry = some updated) :
    ValuesModeInvariant valuesPresent updated := by
  unfold write? at hwrite
  split at hwrite
  · dsimp only at hwrite
    split at hwrite
    · rename_i hnonnegative hinBounds
      simp only [Option.some.injEq] at hwrite
      subst updated
      intro other hother
      rw [Array.getElem_set]
      split
      · exact hentry
      · apply hinvariant
    · contradiction
  · contradiction

/-- A successful atomic copy preserves the destination mode when source and
destination share the same explicit mode. -/
theorem ValuesModeInvariant.copyFrom_preserved_of_eq_some
    {valuesPresent : Bool}
    {destination source updated : SortSlice κ ν} {dst src : Int}
    (hdestination : ValuesModeInvariant valuesPresent destination)
    (hsource : ValuesModeInvariant valuesPresent source)
    (hcopy : destination.copyFrom? source dst src = some updated) :
    ValuesModeInvariant valuesPresent updated := by
  simp only [copyFrom?, bind, Option.bind] at hcopy
  split at hcopy
  · simp at hcopy
  · rename_i entry hread
    exact hdestination.write_preserved_of_eq_some
      (hsource.read_matches_of_eq_some hread) hcopy

theorem ValuesModeInvariant.copy_preserved_of_eq_some
    {valuesPresent : Bool} {slice updated : SortSlice κ ν} {dst src : Int}
    (hinvariant : ValuesModeInvariant valuesPresent slice)
    (hcopy : slice.copy? dst src = some updated) :
    ValuesModeInvariant valuesPresent updated :=
  hinvariant.copyFrom_preserved_of_eq_some hinvariant hcopy

theorem ValuesModeInvariant.copyFromIncr_preserved_of_eq_some
    {valuesPresent : Bool} {destination source : SortSlice κ ν} {dst src : Int}
    {result : CursorResult κ ν}
    (hdestination : ValuesModeInvariant valuesPresent destination)
    (hsource : ValuesModeInvariant valuesPresent source)
    (hcopy : destination.copyFromIncr? source dst src = some result) :
    ValuesModeInvariant valuesPresent result.slice := by
  simp only [copyFromIncr?, bind, Option.bind] at hcopy
  split at hcopy
  · simp at hcopy
  · rename_i updated hstep
    have hresult :
        ({ slice := updated, dst := dst + 1, src := src + 1 } :
          CursorResult κ ν) = result := by
      simpa using hcopy
    rw [← hresult]
    exact hdestination.copyFrom_preserved_of_eq_some hsource hstep

theorem ValuesModeInvariant.copyFromDecr_preserved_of_eq_some
    {valuesPresent : Bool} {destination source : SortSlice κ ν} {dst src : Int}
    {result : CursorResult κ ν}
    (hdestination : ValuesModeInvariant valuesPresent destination)
    (hsource : ValuesModeInvariant valuesPresent source)
    (hcopy : destination.copyFromDecr? source dst src = some result) :
    ValuesModeInvariant valuesPresent result.slice := by
  simp only [copyFromDecr?, bind, Option.bind] at hcopy
  split at hcopy
  · simp at hcopy
  · rename_i updated hstep
    have hresult :
        ({ slice := updated, dst := dst - 1, src := src - 1 } :
          CursorResult κ ν) = result := by
      simpa using hcopy
    rw [← hresult]
    exact hdestination.copyFrom_preserved_of_eq_some hsource hstep

theorem ValuesModeInvariant.copyIncr_preserved_of_eq_some
    {valuesPresent : Bool} {slice : SortSlice κ ν} {dst src : Int}
    {result : CursorResult κ ν}
    (hinvariant : ValuesModeInvariant valuesPresent slice)
    (hcopy : slice.copyIncr? dst src = some result) :
    ValuesModeInvariant valuesPresent result.slice :=
  hinvariant.copyFromIncr_preserved_of_eq_some hinvariant hcopy

theorem ValuesModeInvariant.copyDecr_preserved_of_eq_some
    {valuesPresent : Bool} {slice : SortSlice κ ν} {dst src : Int}
    {result : CursorResult κ ν}
    (hinvariant : ValuesModeInvariant valuesPresent slice)
    (hcopy : slice.copyDecr? dst src = some result) :
    ValuesModeInvariant valuesPresent result.slice :=
  hinvariant.copyFromDecr_preserved_of_eq_some hinvariant hcopy

theorem ValuesModeInvariant.memcpyCore_preserved_of_eq_some
    {valuesPresent : Bool} (count : Nat)
    {destination source updated : SortSlice κ ν} {dst src : Int}
    (hdestination : ValuesModeInvariant valuesPresent destination)
    (hsource : ValuesModeInvariant valuesPresent source)
    (hcopy : memcpyCore? count destination source dst src = some updated) :
    ValuesModeInvariant valuesPresent updated := by
  induction count generalizing destination dst src with
  | zero =>
      simp only [memcpyCore?, Option.some.injEq] at hcopy
      subst updated
      exact hdestination
  | succ count ih =>
      simp only [memcpyCore?, bind, Option.bind] at hcopy
      split at hcopy
      · simp at hcopy
      · rename_i first hfirst
        exact ih
          (hdestination.copyFrom_preserved_of_eq_some hsource hfirst)
          hcopy

theorem ValuesModeInvariant.memcpy_preserved_of_eq_some
    {valuesPresent : Bool} (count : Nat)
    {destination updated : SortSlice κ ν}
    (source : MemcpySource destination) {dst src : Int}
    (hdestination : ValuesModeInvariant valuesPresent destination)
    (hsource : ValuesModeInvariant valuesPresent source.store)
    (hcopy : memcpy? count destination source dst src = some updated) :
    ValuesModeInvariant valuesPresent updated := by
  unfold memcpy? at hcopy
  split at hcopy
  · exact hdestination.memcpyCore_preserved_of_eq_some count hsource hcopy
  · simp at hcopy

theorem ValuesModeInvariant.memmoveForward_preserved_of_eq_some
    {valuesPresent : Bool} (count : Nat)
    {slice updated : SortSlice κ ν} {dst src : Int}
    (hinvariant : ValuesModeInvariant valuesPresent slice)
    (hmove : memmoveForward? count slice dst src = some updated) :
    ValuesModeInvariant valuesPresent updated := by
  induction count generalizing slice dst src with
  | zero =>
      simp only [memmoveForward?, Option.some.injEq] at hmove
      subst updated
      exact hinvariant
  | succ count ih =>
      simp only [memmoveForward?, bind, Option.bind] at hmove
      split at hmove
      · simp at hmove
      · rename_i first hfirst
        exact ih (hinvariant.copy_preserved_of_eq_some hfirst) hmove

theorem ValuesModeInvariant.memmoveBackward_preserved_of_eq_some
    {valuesPresent : Bool} (count : Nat)
    {slice updated : SortSlice κ ν} {dst src : Int}
    (hinvariant : ValuesModeInvariant valuesPresent slice)
    (hmove : memmoveBackward? count slice dst src = some updated) :
    ValuesModeInvariant valuesPresent updated := by
  induction count generalizing slice dst src with
  | zero =>
      simp only [memmoveBackward?, Option.some.injEq] at hmove
      subst updated
      exact hinvariant
  | succ count ih =>
      simp only [memmoveBackward?, bind, Option.bind] at hmove
      split at hmove
      · simp at hmove
      · rename_i first hfirst
        exact ih (hinvariant.copy_preserved_of_eq_some hfirst) hmove

theorem ValuesModeInvariant.memmove_preserved_of_eq_some
    {valuesPresent : Bool} {slice updated : SortSlice κ ν}
    {dst src : Int} {count : Nat}
    (hinvariant : ValuesModeInvariant valuesPresent slice)
    (hmove : slice.memmove? dst src count = some updated) :
    ValuesModeInvariant valuesPresent updated := by
  unfold memmove? at hmove
  split at hmove
  · exact hinvariant.memmoveForward_preserved_of_eq_some count hmove
  · exact hinvariant.memmoveBackward_preserved_of_eq_some count hmove

theorem ValuesModeInvariant.memmoveFrom_preserved_of_eq_some
    {valuesPresent : Bool} {destination updated : SortSlice κ ν}
    (source : MemmoveSource destination) {dst src : Int} {count : Nat}
    (hdestination : ValuesModeInvariant valuesPresent destination)
    (hsource : ValuesModeInvariant valuesPresent source.store)
    (hmove : memmoveFrom? destination source dst src count = some updated) :
    ValuesModeInvariant valuesPresent updated := by
  cases source with
  | sameBacking =>
      exact hdestination.memmove_preserved_of_eq_some hmove
  | distinctBacking source =>
      exact hdestination.memcpyCore_preserved_of_eq_some count hsource hmove

/-! ## Values-mode preservation for the traced primitives -/

theorem copyFromTraced_valuesModeInvariant
    (valuesPresent : Bool) (destination source updated : SortSlice κ ν)
    (dst src : Int)
    (hdestination : ValuesModeInvariant valuesPresent destination)
    (hsource : ValuesModeInvariant valuesPresent source)
    (hresult :
      (copyFromTraced? valuesPresent destination source dst src).result =
        some updated) :
    ValuesModeInvariant valuesPresent updated := by
  apply hdestination.copyFrom_preserved_of_eq_some hsource
  rw [← erase_copyFromTraced valuesPresent destination source dst src]
  exact hresult

theorem copyTraced_valuesModeInvariant
    (valuesPresent : Bool) (slice updated : SortSlice κ ν) (dst src : Int)
    (hinvariant : ValuesModeInvariant valuesPresent slice)
    (hresult : (copyTraced? valuesPresent slice dst src).result = some updated) :
    ValuesModeInvariant valuesPresent updated := by
  apply hinvariant.copy_preserved_of_eq_some
  rw [← erase_copyTraced valuesPresent slice dst src]
  exact hresult

theorem copyFromIncrTraced_valuesModeInvariant
    (valuesPresent : Bool) (destination source : SortSlice κ ν)
    (dst src : Int)
    (result : CursorResult κ ν)
    (hdestination : ValuesModeInvariant valuesPresent destination)
    (hsource : ValuesModeInvariant valuesPresent source)
    (hresult :
      (copyFromIncrTraced? valuesPresent destination source dst src).result =
        some result) :
    ValuesModeInvariant valuesPresent result.slice := by
  apply hdestination.copyFromIncr_preserved_of_eq_some hsource
  rw [← erase_copyFromIncrTraced valuesPresent destination source dst src]
  exact hresult

theorem copyFromDecrTraced_valuesModeInvariant
    (valuesPresent : Bool) (destination source : SortSlice κ ν)
    (dst src : Int)
    (result : CursorResult κ ν)
    (hdestination : ValuesModeInvariant valuesPresent destination)
    (hsource : ValuesModeInvariant valuesPresent source)
    (hresult :
      (copyFromDecrTraced? valuesPresent destination source dst src).result =
        some result) :
    ValuesModeInvariant valuesPresent result.slice := by
  apply hdestination.copyFromDecr_preserved_of_eq_some hsource
  rw [← erase_copyFromDecrTraced valuesPresent destination source dst src]
  exact hresult

theorem copyIncrTraced_valuesModeInvariant
    (valuesPresent : Bool) (slice : SortSlice κ ν) (dst src : Int)
    (result : CursorResult κ ν)
    (hinvariant : ValuesModeInvariant valuesPresent slice)
    (hresult :
      (copyIncrTraced? valuesPresent slice dst src).result = some result) :
    ValuesModeInvariant valuesPresent result.slice := by
  exact copyFromIncrTraced_valuesModeInvariant valuesPresent slice slice dst src
    result hinvariant hinvariant hresult

theorem copyDecrTraced_valuesModeInvariant
    (valuesPresent : Bool) (slice : SortSlice κ ν) (dst src : Int)
    (result : CursorResult κ ν)
    (hinvariant : ValuesModeInvariant valuesPresent slice)
    (hresult :
      (copyDecrTraced? valuesPresent slice dst src).result = some result) :
    ValuesModeInvariant valuesPresent result.slice := by
  exact copyFromDecrTraced_valuesModeInvariant valuesPresent slice slice dst src
    result hinvariant hinvariant hresult

theorem memcpyTraced_valuesModeInvariant
    (valuesPresent : Bool) (count : Nat)
    (destination : SortSlice κ ν) (source : MemcpySource destination)
    (updated : SortSlice κ ν) (dst src : Int)
    (hdestination : ValuesModeInvariant valuesPresent destination)
    (hsource : ValuesModeInvariant valuesPresent source.store)
    (hresult :
      (memcpyTraced? valuesPresent count destination source dst src).result =
        some updated) :
    ValuesModeInvariant valuesPresent updated := by
  apply hdestination.memcpy_preserved_of_eq_some count source hsource
  rw [← erase_memcpyTraced valuesPresent count destination source dst src]
  exact hresult

theorem memmoveTraced_valuesModeInvariant
    (valuesPresent : Bool) (slice updated : SortSlice κ ν)
    (dst src : Int) (count : Nat)
    (hinvariant : ValuesModeInvariant valuesPresent slice)
    (hresult :
      (memmoveTraced? valuesPresent slice dst src count).result = some updated) :
    ValuesModeInvariant valuesPresent updated := by
  apply hinvariant.memmove_preserved_of_eq_some
  rw [← erase_memmoveTraced valuesPresent slice dst src count]
  exact hresult

theorem memmoveFromTraced_valuesModeInvariant
    (valuesPresent : Bool) (destination : SortSlice κ ν)
    (source : MemmoveSource destination) (updated : SortSlice κ ν)
    (dst src : Int) (count : Nat)
    (hdestination : ValuesModeInvariant valuesPresent destination)
    (hsource : ValuesModeInvariant valuesPresent source.store)
    (hresult :
      (memmoveFromTraced? valuesPresent destination source dst src count).result =
        some updated) :
    ValuesModeInvariant valuesPresent updated := by
  apply hdestination.memmoveFrom_preserved_of_eq_some source hsource
  rw [← erase_memmoveFromTraced valuesPresent destination source dst src count]
  exact hresult

/-- The exact key-array event pair for one source-language assignment. -/
def keyCopyAccesses (destinationExtent sourceExtent : Nat)
    (dst src : Int) : List AccessEvent :=
  [{ kind := .read, region := .inputKeys,
     index := src, extent := sourceExtent },
   { kind := .write, region := .inputKeys,
     index := dst, extent := destinationExtent }]

/-- The exact optional-values event pair for one source-language assignment. -/
def valuesCopyAccesses (destinationExtent sourceExtent : Nat)
    (dst src : Int) : List AccessEvent :=
  [{ kind := .read, region := .synchronizedValues,
     index := src, extent := sourceExtent },
   { kind := .write, region := .synchronizedValues,
     index := dst, extent := destinationExtent }]

theorem copyKeysFromTraced_accesses
    (destination source : SortSlice κ ν) (dst src : Int)
    (_hdst : IndexInBounds destination dst)
    (hsrc : IndexInBounds source src) :
    (copyKeysFromTraced? destination source dst src).trace.accesses =
      keyCopyAccesses destination.entries.size source.entries.size dst src := by
  rcases read_eq_some_of_indexInBounds source src hsrc with ⟨entry, hread⟩
  simp [copyKeysFromTraced?, TraceResult.trace_bind,
    TraceResult.sortSliceKeysRead?, TraceResult.sortSliceKeysWrite?,
    hread, TraceResult.captureAccess, AccessTrace.singletonAccess,
    AccessTrace.compose, keyCopyAccesses]

theorem copyValuesFromTraced_accesses
    (destination source : SortSlice κ ν) (dst src : Int)
    (_hdst : IndexInBounds destination dst)
    (hsrc : IndexInBounds source src) :
    (copyValuesFromTraced? destination source dst src).trace.accesses =
      valuesCopyAccesses destination.entries.size source.entries.size dst src := by
  rcases read_eq_some_of_indexInBounds source src hsrc with ⟨entry, hread⟩
  simp [copyValuesFromTraced?, TraceResult.trace_bind,
    TraceResult.sortSliceValuesRead?, TraceResult.sortSliceValuesWrite?,
    hread, TraceResult.captureAccess, AccessTrace.singletonAccess,
    AccessTrace.compose, valuesCopyAccesses]

/-- Exact C order for `sortslice_copy`: the optional values pair occurs after
the key pair iff the explicit pointer mode is true. -/
theorem copyFromTraced_accesses
    (valuesPresent : Bool) (destination source : SortSlice κ ν)
    (dst src : Int) (hdst : IndexInBounds destination dst)
    (hsrc : IndexInBounds source src) :
    (copyFromTraced? valuesPresent destination source dst src).trace.accesses =
      keyCopyAccesses destination.entries.size source.entries.size dst src ++
        if valuesPresent then
          valuesCopyAccesses destination.entries.size source.entries.size dst src
        else [] := by
  rcases read_eq_some_of_indexInBounds source src hsrc with ⟨entry, hread⟩
  rcases write_eq_some_of_indexInBounds destination dst entry hdst with
    ⟨updated, hwrite⟩
  have hcopy : destination.copyFrom? source dst src = some updated := by
    simp [copyFrom?, hread, hwrite]
  have hkeyResult :
      (copyKeysFromTraced? destination source dst src).result = some updated := by
    change (copyKeysFromTraced? destination source dst src).erase = some updated
    rw [erase_copyKeysFromTraced]
    exact hcopy
  unfold copyFromTraced?
  rw [TraceResult.trace_bind, hkeyResult]
  cases valuesPresent <;>
    simp [copyKeysFromTraced_accesses destination source dst src hdst hsrc,
      copyValuesFromTraced_accesses destination source dst src hdst hsrc,
      TraceResult.pure, AccessTrace.compose, AccessTrace.empty]

/-- Advancing the two cursors adds no event: the general incrementing copy has
exactly the key-before-values event order of its underlying two-slice copy. -/
theorem copyFromIncrTraced_accesses
    (valuesPresent : Bool) (destination source : SortSlice κ ν)
    (dst src : Int) (hdst : IndexInBounds destination dst)
    (hsrc : IndexInBounds source src) :
    (copyFromIncrTraced? valuesPresent destination source dst src).trace.accesses =
      keyCopyAccesses destination.entries.size source.entries.size dst src ++
        if valuesPresent then
          valuesCopyAccesses destination.entries.size source.entries.size dst src
        else [] := by
  simpa [copyFromIncrTraced?, TraceResult.map] using
    copyFromTraced_accesses valuesPresent destination source dst src hdst hsrc

/-- Retreating the two cursors adds no event: the general decrementing copy
has exactly the key-before-values event order of its underlying two-slice copy. -/
theorem copyFromDecrTraced_accesses
    (valuesPresent : Bool) (destination source : SortSlice κ ν)
    (dst src : Int) (hdst : IndexInBounds destination dst)
    (hsrc : IndexInBounds source src) :
    (copyFromDecrTraced? valuesPresent destination source dst src).trace.accesses =
      keyCopyAccesses destination.entries.size source.entries.size dst src ++
        if valuesPresent then
          valuesCopyAccesses destination.entries.size source.entries.size dst src
        else [] := by
  simpa [copyFromDecrTraced?, TraceResult.map] using
    copyFromTraced_accesses valuesPresent destination source dst src hdst hsrc

theorem copyFromTraced_allAccessesInBounds
    (valuesPresent : Bool) (destination source : SortSlice κ ν)
    (dst src : Int) (hdst : IndexInBounds destination dst)
    (hsrc : IndexInBounds source src) :
    (copyFromTraced? valuesPresent destination source dst src).trace
      |>.allAccessesInBounds := by
  rw [AccessTrace.allAccessesInBounds]
  rw [copyFromTraced_accesses valuesPresent destination source dst src hdst hsrc]
  rcases hdst with ⟨hdst0, hdstN⟩
  rcases hsrc with ⟨hsrc0, hsrcN⟩
  cases valuesPresent
  · simp only [Bool.false_eq_true, if_false, List.append_nil]
    intro event hevent
    simp only [keyCopyAccesses, List.mem_cons, List.not_mem_nil, or_false]
      at hevent
    rcases hevent with rfl | rfl
    · exact ⟨hsrc0, hsrcN⟩
    · exact ⟨hdst0, hdstN⟩
  · simp only [if_true]
    intro event hevent
    simp only [keyCopyAccesses, valuesCopyAccesses, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hevent
    rcases hevent with (rfl | rfl) | (rfl | rfl)
    · exact ⟨hsrc0, hsrcN⟩
    · exact ⟨hdst0, hdstN⟩
    · exact ⟨hsrc0, hsrcN⟩
    · exact ⟨hdst0, hdstN⟩

theorem copyTraced_allAccessesInBounds
    (valuesPresent : Bool) (slice : SortSlice κ ν) (dst src : Int)
    (hdst : IndexInBounds slice dst) (hsrc : IndexInBounds slice src) :
    (copyTraced? valuesPresent slice dst src).trace.allAccessesInBounds := by
  exact copyFromTraced_allAccessesInBounds valuesPresent slice slice dst src
    hdst hsrc

theorem copyFromIncrTraced_allAccessesInBounds
    (valuesPresent : Bool) (destination source : SortSlice κ ν)
    (dst src : Int) (hdst : IndexInBounds destination dst)
    (hsrc : IndexInBounds source src) :
    (copyFromIncrTraced? valuesPresent destination source dst src).trace
      |>.allAccessesInBounds := by
  simpa [copyFromIncrTraced?, TraceResult.map] using
    copyFromTraced_allAccessesInBounds valuesPresent destination source dst src
      hdst hsrc

theorem copyFromDecrTraced_allAccessesInBounds
    (valuesPresent : Bool) (destination source : SortSlice κ ν)
    (dst src : Int) (hdst : IndexInBounds destination dst)
    (hsrc : IndexInBounds source src) :
    (copyFromDecrTraced? valuesPresent destination source dst src).trace
      |>.allAccessesInBounds := by
  simpa [copyFromDecrTraced?, TraceResult.map] using
    copyFromTraced_allAccessesInBounds valuesPresent destination source dst src
      hdst hsrc

theorem copyIncrTraced_allAccessesInBounds
    (valuesPresent : Bool) (slice : SortSlice κ ν) (dst src : Int)
    (hdst : IndexInBounds slice dst) (hsrc : IndexInBounds slice src) :
    (copyIncrTraced? valuesPresent slice dst src).trace.allAccessesInBounds := by
  exact copyFromIncrTraced_allAccessesInBounds valuesPresent slice slice dst src
    hdst hsrc

theorem copyDecrTraced_allAccessesInBounds
    (valuesPresent : Bool) (slice : SortSlice κ ν) (dst src : Int)
    (hdst : IndexInBounds slice dst) (hsrc : IndexInBounds slice src) :
    (copyDecrTraced? valuesPresent slice dst src).trace.allAccessesInBounds := by
  exact copyFromDecrTraced_allAccessesInBounds valuesPresent slice slice dst src
    hdst hsrc

theorem copyKeysFromTraced_allAccessesInBounds
    (destination source : SortSlice κ ν) (dst src : Int)
    (hdst : IndexInBounds destination dst)
    (hsrc : IndexInBounds source src) :
    (copyKeysFromTraced? destination source dst src).trace
      |>.allAccessesInBounds := by
  rw [AccessTrace.allAccessesInBounds,
    copyKeysFromTraced_accesses destination source dst src hdst hsrc]
  intro event hevent
  simp only [keyCopyAccesses, List.mem_cons, List.not_mem_nil, or_false]
    at hevent
  rcases hevent with rfl | rfl
  · simpa [IndexInBounds, AccessEvent.InBounds] using hsrc
  · simpa [IndexInBounds, AccessEvent.InBounds] using hdst

theorem copyValuesFromTraced_allAccessesInBounds
    (destination source : SortSlice κ ν) (dst src : Int)
    (hdst : IndexInBounds destination dst)
    (hsrc : IndexInBounds source src) :
    (copyValuesFromTraced? destination source dst src).trace
      |>.allAccessesInBounds := by
  rw [AccessTrace.allAccessesInBounds,
    copyValuesFromTraced_accesses destination source dst src hdst hsrc]
  intro event hevent
  simp only [valuesCopyAccesses, List.mem_cons, List.not_mem_nil, or_false]
    at hevent
  rcases hevent with rfl | rfl
  · simpa [IndexInBounds, AccessEvent.InBounds] using hsrc
  · simpa [IndexInBounds, AccessEvent.InBounds] using hdst

/-- Valid source and destination cells make the atomic paired copy succeed. -/
theorem copyFrom_eq_some_of_bounds
    (destination source : SortSlice κ ν) (dst src : Int)
    (hdst : IndexInBounds destination dst)
    (hsrc : IndexInBounds source src) :
    ∃ updated, destination.copyFrom? source dst src = some updated := by
  rcases read_eq_some_of_indexInBounds source src hsrc with ⟨entry, hread⟩
  rcases write_eq_some_of_indexInBounds destination dst entry hdst with
    ⟨updated, hwrite⟩
  exact ⟨updated, by simp [copyFrom?, hread, hwrite]⟩

theorem RangeInBounds.head {slice : SortSlice κ ν} {start : Int}
    {count : Nat} (h : RangeInBounds slice start (count + 1)) :
    IndexInBounds slice start := by
  rcases h with ⟨hstart, hend⟩
  constructor
  · exact hstart
  · simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] at hend ⊢
    omega

theorem RangeInBounds.tail {slice : SortSlice κ ν} {start : Int}
    {count : Nat} (h : RangeInBounds slice start (count + 1)) :
    RangeInBounds slice (start + 1) count := by
  rcases h with ⟨hstart, hend⟩
  constructor
  · omega
  · simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] at hend ⊢
    omega

theorem RangeInBounds.prefix {slice : SortSlice κ ν} {start : Int}
    {count : Nat} (h : RangeInBounds slice start (count + 1)) :
    RangeInBounds slice start count := by
  rcases h with ⟨hstart, hend⟩
  constructor
  · exact hstart
  · simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] at hend ⊢
    omega

theorem RangeInBounds.last {slice : SortSlice κ ν} {start : Int}
    {count : Nat} (h : RangeInBounds slice start (count + 1)) :
    IndexInBounds slice (start + Int.ofNat count) := by
  rcases h with ⟨hstart, hend⟩
  constructor
  · exact add_nonneg hstart (Int.natCast_nonneg count)
  · simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] at hend ⊢
    omega

/-- Extent equality transports a valid range between paired-store snapshots. -/
theorem RangeInBounds.of_size_eq {first second : SortSlice κ ν}
    {start : Int} {count : Nat} (h : RangeInBounds first start count)
    (hsize : second.entries.size = first.entries.size) :
    RangeInBounds second start count := by
  simpa [RangeInBounds, hsize] using h

/-- Extent equality transports a valid single index between snapshots. -/
theorem IndexInBounds.of_size_eq {first second : SortSlice κ ν}
    {index : Int} (h : IndexInBounds first index)
    (hsize : second.entries.size = first.entries.size) :
    IndexInBounds second index := by
  simpa [IndexInBounds, hsize] using h

/-- An in-bounds cell index is also a valid cursor. -/
theorem IndexInBounds.cursorInRange {slice : SortSlice κ ν} {index : Int}
    (h : IndexInBounds slice index) : CursorInRange slice index := by
  exact ⟨h.1, h.2.le⟩

/-- Advancing once from an existing cell can land on the permitted one-past
endpoint, but never beyond it. -/
theorem IndexInBounds.increment_cursorInRange
    {slice : SortSlice κ ν} {index : Int}
    (h : IndexInBounds slice index) : CursorInRange slice (index + 1) := by
  rcases h with ⟨hlower, hupper⟩
  constructor <;> omega

/-- Decrementing an existing positive cell index remains a valid cursor.  The
strictly-positive premise is essential: decrementing cell zero would create a
one-before-beginning pointer, which this model does not call valid. -/
theorem IndexInBounds.decrement_cursorInRange
    {slice : SortSlice κ ν} {index : Int}
    (h : IndexInBounds slice index) (hpositive : 0 < index) :
    CursorInRange slice (index - 1) := by
  rcases h with ⟨_, hupper⟩
  constructor <;> omega

/-- Extent equality transports cursor validity, including the one-past
endpoint, between storage snapshots. -/
theorem CursorInRange.of_size_eq {first second : SortSlice κ ν}
    {cursor : Int} (h : CursorInRange first cursor)
    (hsize : second.entries.size = first.entries.size) :
    CursorInRange second cursor := by
  simpa [CursorInRange, hsize] using h

/-- The explicit displacement bounds imply validity of the advanced cursor. -/
theorem CursorMovementInRange.result
    {slice : SortSlice κ ν} {index amount : Int}
    (h : CursorMovementInRange slice index amount) :
    CursorInRange slice (advance index amount) := by
  rcases h with ⟨hcursor, hlower, hupper⟩
  rcases hcursor with ⟨hindex, _⟩
  simp only [CursorInRange, advance]
  constructor <;> omega

/-- The key phase of `memcpy` succeeds on exact valid ranges, records only
in-bounds accesses, and preserves the destination extent. -/
theorem memcpyKeysTraced_safe (count : Nat)
    (destination source : SortSlice κ ν) (dst src : Int)
    (hdst : RangeInBounds destination dst count)
    (hsrc : RangeInBounds source src count) :
    ∃ updated,
      (memcpyKeysTraced? count destination source dst src).result = some updated ∧
        (memcpyKeysTraced? count destination source dst src).trace.allAccessesInBounds ∧
        updated.entries.size = destination.entries.size := by
  induction count generalizing destination dst src with
  | zero =>
      exact ⟨destination, rfl, by simp [memcpyKeysTraced?, TraceResult.pure], rfl⟩
  | succ count ih =>
      have hdstHead := hdst.head
      have hsrcHead := hsrc.head
      rcases copyFrom_eq_some_of_bounds destination source dst src hdstHead
          hsrcHead with ⟨first, hcopy⟩
      have hfirst :
          (copyKeysFromTraced? destination source dst src).result = some first := by
        change (copyKeysFromTraced? destination source dst src).erase = some first
        rw [erase_copyKeysFromTraced]
        exact hcopy
      have hfirstSize : first.entries.size = destination.entries.size :=
        copyFrom_entries_size_of_eq_some destination source first dst src hcopy
      have hdstTail : RangeInBounds first (dst + 1) count :=
        hdst.tail.of_size_eq hfirstSize
      have hsrcTail : RangeInBounds source (src + 1) count := hsrc.tail
      rcases ih first (dst + 1) (src + 1) hdstTail hsrcTail with
        ⟨updated, hrest, hrestBounds, hrestSize⟩
      refine ⟨updated, ?_, ?_, hrestSize.trans hfirstSize⟩
      · simpa [memcpyKeysTraced?, TraceResult.bind, hfirst] using hrest
      · have htrace :
            (memcpyKeysTraced? (count + 1) destination source dst src).trace =
              (copyKeysFromTraced? destination source dst src).trace.compose
                (memcpyKeysTraced? count first source (dst + 1) (src + 1)).trace := by
          simp [memcpyKeysTraced?, TraceResult.trace_bind, hfirst]
        rw [htrace, AccessTrace.allAccessesInBounds_compose]
        exact ⟨copyKeysFromTraced_allAccessesInBounds destination source dst src
          hdstHead hsrcHead, hrestBounds⟩

/-- The optional-values phase of `memcpy` has the same success, bounds, and
extent facts as the key phase. -/
theorem memcpyValuesTraced_safe (count : Nat)
    (destination source : SortSlice κ ν) (dst src : Int)
    (hdst : RangeInBounds destination dst count)
    (hsrc : RangeInBounds source src count) :
    ∃ updated,
      (memcpyValuesTraced? count destination source dst src).result = some updated ∧
        (memcpyValuesTraced? count destination source dst src).trace.allAccessesInBounds ∧
        updated.entries.size = destination.entries.size := by
  induction count generalizing destination dst src with
  | zero =>
      exact ⟨destination, rfl, by simp [memcpyValuesTraced?, TraceResult.pure], rfl⟩
  | succ count ih =>
      have hdstHead := hdst.head
      have hsrcHead := hsrc.head
      rcases copyFrom_eq_some_of_bounds destination source dst src hdstHead
          hsrcHead with ⟨first, hcopy⟩
      have hfirst :
          (copyValuesFromTraced? destination source dst src).result = some first := by
        change (copyValuesFromTraced? destination source dst src).erase = some first
        rw [erase_copyValuesFromTraced]
        exact hcopy
      have hfirstSize : first.entries.size = destination.entries.size :=
        copyFrom_entries_size_of_eq_some destination source first dst src hcopy
      have hdstTail : RangeInBounds first (dst + 1) count :=
        hdst.tail.of_size_eq hfirstSize
      have hsrcTail : RangeInBounds source (src + 1) count := hsrc.tail
      rcases ih first (dst + 1) (src + 1) hdstTail hsrcTail with
        ⟨updated, hrest, hrestBounds, hrestSize⟩
      refine ⟨updated, ?_, ?_, hrestSize.trans hfirstSize⟩
      · simpa [memcpyValuesTraced?, TraceResult.bind, hfirst] using hrest
      · have htrace :
            (memcpyValuesTraced? (count + 1) destination source dst src).trace =
              (copyValuesFromTraced? destination source dst src).trace.compose
                (memcpyValuesTraced? count first source (dst + 1) (src + 1)).trace := by
          simp [memcpyValuesTraced?, TraceResult.trace_bind, hfirst]
        rw [htrace, AccessTrace.allAccessesInBounds_compose]
        exact ⟨copyValuesFromTraced_allAccessesInBounds destination source dst src
          hdstHead hsrcHead, hrestBounds⟩

/-- Complete `memcpy` safety under its backing-domain condition and exact
source and destination ranges. -/
theorem memcpyTraced_safe
    (valuesPresent : Bool) (count : Nat)
    (destination : SortSlice κ ν) (source : MemcpySource destination)
    (dst src : Int)
    (hadmissible : source.Admissible dst src count)
    (hdst : RangeInBounds destination dst count)
    (hsrc : RangeInBounds source.store src count) :
    ∃ updated,
      (memcpyTraced? valuesPresent count destination source dst src).result =
          some updated ∧
        (memcpyTraced? valuesPresent count destination source dst src).trace.allAccessesInBounds ∧
        updated.entries.size = destination.entries.size := by
  rcases memcpyKeysTraced_safe count destination source.store dst src hdst hsrc with
    ⟨keyResult, hkeys, hkeysBounds, hkeysSize⟩
  cases valuesPresent with
  | false =>
      refine ⟨keyResult, ?_, ?_, hkeysSize⟩
      · simp [memcpyTraced?, hadmissible, TraceResult.bind, TraceResult.pure,
          hkeys]
      · simpa [memcpyTraced?, hadmissible, TraceResult.trace_bind, hkeys,
          TraceResult.pure] using hkeysBounds
  | true =>
      rcases memcpyValuesTraced_safe count destination source.store dst src hdst hsrc with
        ⟨valuesResult, hvalues, hvaluesBounds, hvaluesSize⟩
      refine ⟨valuesResult, ?_, ?_, hvaluesSize⟩
      · simpa [memcpyTraced?, hadmissible, TraceResult.bind, hkeys] using hvalues
      · have htrace :
            (memcpyTraced? true count destination source dst src).trace =
              (memcpyKeysTraced? count destination source.store dst src).trace.compose
                (memcpyValuesTraced? count destination source.store dst src).trace := by
          simp [memcpyTraced?, hadmissible, TraceResult.trace_bind, hkeys]
        rw [htrace, AccessTrace.allAccessesInBounds_compose]
        exact ⟨hkeysBounds, hvaluesBounds⟩

/-- Source-level bulk ordering: all key-array events precede the optional
values-array phase, and that second phase is selected solely by the explicit
mode bit. -/
theorem memcpyTraced_phase_order
    (valuesPresent : Bool) (count : Nat)
    (destination : SortSlice κ ν) (source : MemcpySource destination)
    (dst src : Int)
    (hadmissible : source.Admissible dst src count)
    (hdst : RangeInBounds destination dst count)
    (hsrc : RangeInBounds source.store src count) :
    (memcpyTraced? valuesPresent count destination source dst src).trace.accesses =
      (memcpyKeysTraced? count destination source.store dst src).trace.accesses ++
        if valuesPresent then
          (memcpyValuesTraced? count destination source.store dst src).trace.accesses
        else [] := by
  rcases memcpyKeysTraced_safe count destination source.store dst src hdst hsrc with
    ⟨keyResult, hkeys, _, _⟩
  cases valuesPresent <;>
    simp [memcpyTraced?, hadmissible, TraceResult.trace_bind, hkeys,
      TraceResult.pure, AccessTrace.compose, AccessTrace.empty]

/-- Regression: distinct provenance remains admissible independently of
contents, and values mode retains the complete key phase before the values
phase. -/
theorem memcpyTraced_distinctBacking_values_phase_order
    (count : Nat) (destination source : SortSlice κ ν) (dst src : Int)
    (hdst : RangeInBounds destination dst count)
    (hsrc : RangeInBounds source src count) :
    (memcpyTraced? true count destination (.distinctBacking source) dst src).trace.accesses =
      (memcpyKeysTraced? count destination source dst src).trace.accesses ++
        (memcpyValuesTraced? count destination source dst src).trace.accesses := by
  simpa [MemcpySource.store] using
    memcpyTraced_phase_order true count destination (.distinctBacking source)
      dst src (by simp [MemcpySource.Admissible]) hdst hsrc

/-- Forward key traversal is safe on exact source and destination ranges. -/
theorem memmoveForwardKeysTraced_safe (count : Nat)
    (slice : SortSlice κ ν) (dst src : Int)
    (hdst : RangeInBounds slice dst count)
    (hsrc : RangeInBounds slice src count) :
    ∃ updated,
      (memmoveForwardKeysTraced? count slice dst src).result = some updated ∧
        (memmoveForwardKeysTraced? count slice dst src).trace.allAccessesInBounds ∧
        updated.entries.size = slice.entries.size := by
  induction count generalizing slice dst src with
  | zero =>
      exact ⟨slice, rfl, by simp [memmoveForwardKeysTraced?, TraceResult.pure], rfl⟩
  | succ count ih =>
      have hdstHead := hdst.head
      have hsrcHead := hsrc.head
      rcases copyFrom_eq_some_of_bounds slice slice dst src hdstHead hsrcHead with
        ⟨first, hcopy⟩
      have hfirst :
          (copyKeysFromTraced? slice slice dst src).result = some first := by
        change (copyKeysFromTraced? slice slice dst src).erase = some first
        rw [erase_copyKeysFromTraced]
        exact hcopy
      have hfirstSize : first.entries.size = slice.entries.size :=
        copyFrom_entries_size_of_eq_some slice slice first dst src hcopy
      have hdstTail : RangeInBounds first (dst + 1) count :=
        hdst.tail.of_size_eq hfirstSize
      have hsrcTail : RangeInBounds first (src + 1) count :=
        hsrc.tail.of_size_eq hfirstSize
      rcases ih first (dst + 1) (src + 1) hdstTail hsrcTail with
        ⟨updated, hrest, hrestBounds, hrestSize⟩
      refine ⟨updated, ?_, ?_, hrestSize.trans hfirstSize⟩
      · simpa [memmoveForwardKeysTraced?, TraceResult.bind, hfirst] using hrest
      · have htrace :
            (memmoveForwardKeysTraced? (count + 1) slice dst src).trace =
              (copyKeysFromTraced? slice slice dst src).trace.compose
                (memmoveForwardKeysTraced? count first (dst + 1) (src + 1)).trace := by
          simp [memmoveForwardKeysTraced?, TraceResult.trace_bind, hfirst]
        rw [htrace, AccessTrace.allAccessesInBounds_compose]
        exact ⟨copyKeysFromTraced_allAccessesInBounds slice slice dst src
          hdstHead hsrcHead, hrestBounds⟩

/-- Forward synchronized-values traversal is safe on the same ranges. -/
theorem memmoveForwardValuesTraced_safe (count : Nat)
    (slice : SortSlice κ ν) (dst src : Int)
    (hdst : RangeInBounds slice dst count)
    (hsrc : RangeInBounds slice src count) :
    ∃ updated,
      (memmoveForwardValuesTraced? count slice dst src).result = some updated ∧
        (memmoveForwardValuesTraced? count slice dst src).trace.allAccessesInBounds ∧
        updated.entries.size = slice.entries.size := by
  induction count generalizing slice dst src with
  | zero =>
      exact ⟨slice, rfl, by simp [memmoveForwardValuesTraced?, TraceResult.pure], rfl⟩
  | succ count ih =>
      have hdstHead := hdst.head
      have hsrcHead := hsrc.head
      rcases copyFrom_eq_some_of_bounds slice slice dst src hdstHead hsrcHead with
        ⟨first, hcopy⟩
      have hfirst :
          (copyValuesFromTraced? slice slice dst src).result = some first := by
        change (copyValuesFromTraced? slice slice dst src).erase = some first
        rw [erase_copyValuesFromTraced]
        exact hcopy
      have hfirstSize : first.entries.size = slice.entries.size :=
        copyFrom_entries_size_of_eq_some slice slice first dst src hcopy
      have hdstTail : RangeInBounds first (dst + 1) count :=
        hdst.tail.of_size_eq hfirstSize
      have hsrcTail : RangeInBounds first (src + 1) count :=
        hsrc.tail.of_size_eq hfirstSize
      rcases ih first (dst + 1) (src + 1) hdstTail hsrcTail with
        ⟨updated, hrest, hrestBounds, hrestSize⟩
      refine ⟨updated, ?_, ?_, hrestSize.trans hfirstSize⟩
      · simpa [memmoveForwardValuesTraced?, TraceResult.bind, hfirst] using hrest
      · have htrace :
            (memmoveForwardValuesTraced? (count + 1) slice dst src).trace =
              (copyValuesFromTraced? slice slice dst src).trace.compose
                (memmoveForwardValuesTraced? count first (dst + 1) (src + 1)).trace := by
          simp [memmoveForwardValuesTraced?, TraceResult.trace_bind, hfirst]
        rw [htrace, AccessTrace.allAccessesInBounds_compose]
        exact ⟨copyValuesFromTraced_allAccessesInBounds slice slice dst src
          hdstHead hsrcHead, hrestBounds⟩

/-- Backward key traversal starts at the last cell of each range and remains
safe while recursing toward the first. -/
theorem memmoveBackwardKeysTraced_safe (count : Nat)
    (slice : SortSlice κ ν) (dst src : Int)
    (hdst : RangeInBounds slice dst count)
    (hsrc : RangeInBounds slice src count) :
    ∃ updated,
      (memmoveBackwardKeysTraced? count slice dst src).result = some updated ∧
        (memmoveBackwardKeysTraced? count slice dst src).trace.allAccessesInBounds ∧
        updated.entries.size = slice.entries.size := by
  induction count generalizing slice dst src with
  | zero =>
      exact ⟨slice, rfl, by simp [memmoveBackwardKeysTraced?, TraceResult.pure], rfl⟩
  | succ count ih =>
      have hdstLast := hdst.last
      have hsrcLast := hsrc.last
      rcases copyFrom_eq_some_of_bounds slice slice
          (dst + Int.ofNat count) (src + Int.ofNat count) hdstLast hsrcLast with
        ⟨first, hcopy⟩
      have hfirst :
          (copyKeysFromTraced? slice slice (dst + Int.ofNat count)
            (src + Int.ofNat count)).result = some first := by
        change (copyKeysFromTraced? slice slice (dst + Int.ofNat count)
          (src + Int.ofNat count)).erase = some first
        rw [erase_copyKeysFromTraced]
        exact hcopy
      have hfirst' :
          (copyKeysFromTraced? slice slice (dst + (count : Int))
            (src + (count : Int))).result = some first := by
        simpa using hfirst
      have hfirstSize : first.entries.size = slice.entries.size :=
        copyFrom_entries_size_of_eq_some slice slice first
          (dst + Int.ofNat count) (src + Int.ofNat count) hcopy
      have hdstPrefix : RangeInBounds first dst count :=
        hdst.prefix.of_size_eq hfirstSize
      have hsrcPrefix : RangeInBounds first src count :=
        hsrc.prefix.of_size_eq hfirstSize
      rcases ih first dst src hdstPrefix hsrcPrefix with
        ⟨updated, hrest, hrestBounds, hrestSize⟩
      refine ⟨updated, ?_, ?_, hrestSize.trans hfirstSize⟩
      · simpa [memmoveBackwardKeysTraced?, TraceResult.bind, hfirst'] using hrest
      · have htrace :
            (memmoveBackwardKeysTraced? (count + 1) slice dst src).trace =
              (copyKeysFromTraced? slice slice (dst + Int.ofNat count)
                (src + Int.ofNat count)).trace.compose
                (memmoveBackwardKeysTraced? count first dst src).trace := by
          simp [memmoveBackwardKeysTraced?, TraceResult.trace_bind, hfirst']
        rw [htrace, AccessTrace.allAccessesInBounds_compose]
        exact ⟨copyKeysFromTraced_allAccessesInBounds slice slice
          (dst + Int.ofNat count) (src + Int.ofNat count) hdstLast hsrcLast,
          hrestBounds⟩

/-- Backward synchronized-values traversal uses the identical last-to-first
event order. -/
theorem memmoveBackwardValuesTraced_safe (count : Nat)
    (slice : SortSlice κ ν) (dst src : Int)
    (hdst : RangeInBounds slice dst count)
    (hsrc : RangeInBounds slice src count) :
    ∃ updated,
      (memmoveBackwardValuesTraced? count slice dst src).result = some updated ∧
        (memmoveBackwardValuesTraced? count slice dst src).trace.allAccessesInBounds ∧
        updated.entries.size = slice.entries.size := by
  induction count generalizing slice dst src with
  | zero =>
      exact ⟨slice, rfl, by simp [memmoveBackwardValuesTraced?, TraceResult.pure], rfl⟩
  | succ count ih =>
      have hdstLast := hdst.last
      have hsrcLast := hsrc.last
      rcases copyFrom_eq_some_of_bounds slice slice
          (dst + Int.ofNat count) (src + Int.ofNat count) hdstLast hsrcLast with
        ⟨first, hcopy⟩
      have hfirst :
          (copyValuesFromTraced? slice slice (dst + Int.ofNat count)
            (src + Int.ofNat count)).result = some first := by
        change (copyValuesFromTraced? slice slice (dst + Int.ofNat count)
          (src + Int.ofNat count)).erase = some first
        rw [erase_copyValuesFromTraced]
        exact hcopy
      have hfirst' :
          (copyValuesFromTraced? slice slice (dst + (count : Int))
            (src + (count : Int))).result = some first := by
        simpa using hfirst
      have hfirstSize : first.entries.size = slice.entries.size :=
        copyFrom_entries_size_of_eq_some slice slice first
          (dst + Int.ofNat count) (src + Int.ofNat count) hcopy
      have hdstPrefix : RangeInBounds first dst count :=
        hdst.prefix.of_size_eq hfirstSize
      have hsrcPrefix : RangeInBounds first src count :=
        hsrc.prefix.of_size_eq hfirstSize
      rcases ih first dst src hdstPrefix hsrcPrefix with
        ⟨updated, hrest, hrestBounds, hrestSize⟩
      refine ⟨updated, ?_, ?_, hrestSize.trans hfirstSize⟩
      · simpa [memmoveBackwardValuesTraced?, TraceResult.bind, hfirst'] using hrest
      · have htrace :
            (memmoveBackwardValuesTraced? (count + 1) slice dst src).trace =
              (copyValuesFromTraced? slice slice (dst + Int.ofNat count)
                (src + Int.ofNat count)).trace.compose
                (memmoveBackwardValuesTraced? count first dst src).trace := by
          simp [memmoveBackwardValuesTraced?, TraceResult.trace_bind, hfirst']
        rw [htrace, AccessTrace.allAccessesInBounds_compose]
        exact ⟨copyValuesFromTraced_allAccessesInBounds slice slice
          (dst + Int.ofNat count) (src + Int.ofNat count) hdstLast hsrcLast,
          hrestBounds⟩

/-- Complete overlap-safe movement theorem.  The actual direction branch is
retained, and the optional values phase follows that same branch. -/
theorem memmoveTraced_safe
    (valuesPresent : Bool) (slice : SortSlice κ ν)
    (dst src : Int) (count : Nat)
    (hdst : RangeInBounds slice dst count)
    (hsrc : RangeInBounds slice src count) :
    ∃ updated,
      (memmoveTraced? valuesPresent slice dst src count).result = some updated ∧
        (memmoveTraced? valuesPresent slice dst src count).trace.allAccessesInBounds ∧
        updated.entries.size = slice.entries.size := by
  cases hdir : memmoveDirection dst src with
  | forward =>
      rcases memmoveForwardKeysTraced_safe count slice dst src hdst hsrc with
        ⟨keyResult, hkeys, hkeysBounds, hkeysSize⟩
      cases valuesPresent with
      | false =>
          refine ⟨keyResult, ?_, ?_, hkeysSize⟩
          · simp [memmoveTraced?, hdir, TraceResult.bind, TraceResult.pure, hkeys]
          · simpa [memmoveTraced?, hdir, TraceResult.trace_bind, TraceResult.pure,
              hkeys] using hkeysBounds
      | true =>
          rcases memmoveForwardValuesTraced_safe count slice dst src hdst hsrc with
            ⟨valuesResult, hvalues, hvaluesBounds, hvaluesSize⟩
          refine ⟨valuesResult, ?_, ?_, hvaluesSize⟩
          · simpa [memmoveTraced?, hdir, TraceResult.bind, hkeys] using hvalues
          · have htrace :
                (memmoveTraced? true slice dst src count).trace =
                  (memmoveForwardKeysTraced? count slice dst src).trace.compose
                    (memmoveForwardValuesTraced? count slice dst src).trace := by
              simp [memmoveTraced?, hdir, TraceResult.trace_bind, hkeys]
            rw [htrace, AccessTrace.allAccessesInBounds_compose]
            exact ⟨hkeysBounds, hvaluesBounds⟩
  | backward =>
      rcases memmoveBackwardKeysTraced_safe count slice dst src hdst hsrc with
        ⟨keyResult, hkeys, hkeysBounds, hkeysSize⟩
      cases valuesPresent with
      | false =>
          refine ⟨keyResult, ?_, ?_, hkeysSize⟩
          · simp [memmoveTraced?, hdir, TraceResult.bind, TraceResult.pure, hkeys]
          · simpa [memmoveTraced?, hdir, TraceResult.trace_bind, TraceResult.pure,
              hkeys] using hkeysBounds
      | true =>
          rcases memmoveBackwardValuesTraced_safe count slice dst src hdst hsrc with
            ⟨valuesResult, hvalues, hvaluesBounds, hvaluesSize⟩
          refine ⟨valuesResult, ?_, ?_, hvaluesSize⟩
          · simpa [memmoveTraced?, hdir, TraceResult.bind, hkeys] using hvalues
          · have htrace :
                (memmoveTraced? true slice dst src count).trace =
                  (memmoveBackwardKeysTraced? count slice dst src).trace.compose
                    (memmoveBackwardValuesTraced? count slice dst src).trace := by
              simp [memmoveTraced?, hdir, TraceResult.trace_bind, hkeys]
            rw [htrace, AccessTrace.allAccessesInBounds_compose]
            exact ⟨hkeysBounds, hvaluesBounds⟩

/-- Exact key-before-values phase order for `memmove`, with both phases using
the source-selected traversal direction. -/
theorem memmoveTraced_phase_order
    (valuesPresent : Bool) (slice : SortSlice κ ν)
    (dst src : Int) (count : Nat)
    (hdst : RangeInBounds slice dst count)
    (hsrc : RangeInBounds slice src count) :
    (memmoveTraced? valuesPresent slice dst src count).trace.accesses =
      match memmoveDirection dst src with
      | .forward =>
          (memmoveForwardKeysTraced? count slice dst src).trace.accesses ++
            if valuesPresent then
              (memmoveForwardValuesTraced? count slice dst src).trace.accesses
            else []
      | .backward =>
          (memmoveBackwardKeysTraced? count slice dst src).trace.accesses ++
            if valuesPresent then
              (memmoveBackwardValuesTraced? count slice dst src).trace.accesses
            else [] := by
  cases hdir : memmoveDirection dst src with
  | forward =>
      rcases memmoveForwardKeysTraced_safe count slice dst src hdst hsrc with
        ⟨keyResult, hkeys, _, _⟩
      cases valuesPresent <;>
        simp [memmoveTraced?, hdir, TraceResult.trace_bind, hkeys,
          TraceResult.pure, AccessTrace.compose, AccessTrace.empty]
  | backward =>
      rcases memmoveBackwardKeysTraced_safe count slice dst src hdst hsrc with
        ⟨keyResult, hkeys, _, _⟩
      cases valuesPresent <;>
        simp [memmoveTraced?, hdir, TraceResult.trace_bind, hkeys,
          TraceResult.pure, AccessTrace.compose, AccessTrace.empty]

/-- Complete safety for the provenance-aware two-store movement.  The source
range is measured in the explicitly selected backing; only the destination is
updated, and its extent is preserved. -/
theorem memmoveFromTraced_safe
    (valuesPresent : Bool) (destination : SortSlice κ ν)
    (source : MemmoveSource destination) (dst src : Int) (count : Nat)
    (hdst : RangeInBounds destination dst count)
    (hsrc : RangeInBounds source.store src count) :
    ∃ updated,
      (memmoveFromTraced? valuesPresent destination source dst src count).result =
          some updated ∧
        ((memmoveFromTraced? valuesPresent destination source dst src count).trace
          |>.allAccessesInBounds) ∧
        updated.entries.size = destination.entries.size := by
  cases source with
  | sameBacking =>
      simpa [memmoveFromTraced?, MemcpySource.store] using
        memmoveTraced_safe valuesPresent destination dst src count hdst hsrc
  | distinctBacking source =>
      simpa [memmoveFromTraced?, memcpyTraced?, MemcpySource.Admissible,
        MemcpySource.store] using
        (memcpyTraced_safe valuesPresent count destination
          (.distinctBacking source) dst src
          (by simp [MemcpySource.Admissible]) hdst hsrc)

/-- Provenance-sensitive source and phase order.  Shared storage uses the
overlap geometry's direction in both physical phases; distinct storage uses
the forward `memcpyCore?` source order in both phases.  In either branch all
key events precede all optional-values events. -/
theorem memmoveFromTraced_phase_order
    (valuesPresent : Bool) (destination : SortSlice κ ν)
    (source : MemmoveSource destination) (dst src : Int) (count : Nat)
    (hdst : RangeInBounds destination dst count)
    (hsrc : RangeInBounds source.store src count) :
    (memmoveFromTraced? valuesPresent destination source dst src count).trace.accesses =
      match source with
      | .sameBacking =>
          match memmoveDirection dst src with
          | .forward =>
              (memmoveForwardKeysTraced? count destination dst src).trace.accesses ++
                if valuesPresent then
                  (memmoveForwardValuesTraced? count destination dst src).trace.accesses
                else []
          | .backward =>
              (memmoveBackwardKeysTraced? count destination dst src).trace.accesses ++
                if valuesPresent then
                  (memmoveBackwardValuesTraced? count destination dst src).trace.accesses
                else []
      | .distinctBacking source =>
          (memcpyKeysTraced? count destination source dst src).trace.accesses ++
            if valuesPresent then
              (memcpyValuesTraced? count destination source dst src).trace.accesses
            else [] := by
  cases source with
  | sameBacking =>
      simpa [memmoveFromTraced?, MemcpySource.store] using
        memmoveTraced_phase_order valuesPresent destination dst src count hdst hsrc
  | distinctBacking source =>
      simpa [memmoveFromTraced?, memcpyTraced?, MemcpySource.Admissible,
        MemcpySource.store] using
        (memcpyTraced_phase_order valuesPresent count destination
          (.distinctBacking source) dst src
          (by simp [MemcpySource.Admissible]) hdst hsrc)

/-- Shared provenance specializes the general order theorem to directional
overlap-safe traversal. -/
theorem memmoveFromTraced_sameBacking_phase_order
    (valuesPresent : Bool) (destination : SortSlice κ ν)
    (dst src : Int) (count : Nat)
    (hdst : RangeInBounds destination dst count)
    (hsrc : RangeInBounds destination src count) :
    (memmoveFromTraced? valuesPresent destination .sameBacking dst src count).trace.accesses =
      match memmoveDirection dst src with
      | .forward =>
          (memmoveForwardKeysTraced? count destination dst src).trace.accesses ++
            if valuesPresent then
              (memmoveForwardValuesTraced? count destination dst src).trace.accesses
            else []
      | .backward =>
          (memmoveBackwardKeysTraced? count destination dst src).trace.accesses ++
            if valuesPresent then
              (memmoveBackwardValuesTraced? count destination dst src).trace.accesses
            else [] := by
  simpa [MemcpySource.store] using
    memmoveFromTraced_phase_order valuesPresent destination .sameBacking dst src
      count hdst hsrc

/-- Distinct provenance specializes the general order theorem to forward
two-store traversal, independently of extensional equality of the stores. -/
theorem memmoveFromTraced_distinctBacking_phase_order
    (valuesPresent : Bool) (count : Nat)
    (destination source : SortSlice κ ν) (dst src : Int)
    (hdst : RangeInBounds destination dst count)
    (hsrc : RangeInBounds source src count) :
    (memmoveFromTraced? valuesPresent destination (.distinctBacking source)
      dst src count).trace.accesses =
        (memcpyKeysTraced? count destination source dst src).trace.accesses ++
          if valuesPresent then
            (memcpyValuesTraced? count destination source dst src).trace.accesses
          else [] := by
  simpa [MemcpySource.store] using
    memmoveFromTraced_phase_order valuesPresent destination
      (.distinctBacking source) dst src count hdst hsrc

/-- Full one-cell copy safety, including success and common-extent
preservation. -/
theorem copyFromTraced_safe
    (valuesPresent : Bool) (destination source : SortSlice κ ν)
    (dst src : Int) (hdst : IndexInBounds destination dst)
    (hsrc : IndexInBounds source src) :
    ∃ updated,
      (copyFromTraced? valuesPresent destination source dst src).result =
          some updated ∧
        (copyFromTraced? valuesPresent destination source dst src).trace.allAccessesInBounds ∧
        updated.entries.size = destination.entries.size := by
  rcases copyFrom_eq_some_of_bounds destination source dst src hdst hsrc with
    ⟨updated, hcopy⟩
  have hresult :
      (copyFromTraced? valuesPresent destination source dst src).result =
        some updated := by
    change (copyFromTraced? valuesPresent destination source dst src).erase =
      some updated
    rw [erase_copyFromTraced]
    exact hcopy
  exact ⟨updated, hresult,
    copyFromTraced_allAccessesInBounds valuesPresent destination source dst src
      hdst hsrc,
    copyFrom_entries_size_of_eq_some destination source updated dst src hcopy⟩

theorem copyTraced_safe
    (valuesPresent : Bool) (slice : SortSlice κ ν) (dst src : Int)
    (hdst : IndexInBounds slice dst) (hsrc : IndexInBounds slice src) :
    ∃ updated,
      (copyTraced? valuesPresent slice dst src).result = some updated ∧
        (copyTraced? valuesPresent slice dst src).trace.allAccessesInBounds ∧
        updated.entries.size = slice.entries.size := by
  simpa [copyTraced?] using
    copyFromTraced_safe valuesPresent slice slice dst src hdst hsrc

/-- Full incrementing two-slice copy safety.  The returned destination cursor
is measured against the updated destination, while the returned source cursor
is measured against the unchanged source. -/
theorem copyFromIncrTraced_safe
    (valuesPresent : Bool) (destination source : SortSlice κ ν)
    (dst src : Int)
    (hdestination : ValuesModeInvariant valuesPresent destination)
    (hsource : ValuesModeInvariant valuesPresent source)
    (hdst : IndexInBounds destination dst) (hsrc : IndexInBounds source src) :
    ∃ result,
      (copyFromIncrTraced? valuesPresent destination source dst src).result =
          some result ∧
        ((copyFromIncrTraced? valuesPresent destination source dst src).trace
          |>.allAccessesInBounds) ∧
        result.slice.entries.size = destination.entries.size ∧
        ValuesModeInvariant valuesPresent result.slice ∧
        ValuesModeInvariant valuesPresent source ∧
        CursorInRange result.slice result.dst ∧
        CursorInRange source result.src := by
  rcases copyFromTraced_safe valuesPresent destination source dst src hdst hsrc with
    ⟨updated, hcopy, hbounds, hsize⟩
  let result : CursorResult κ ν :=
    { slice := updated, dst := dst + 1, src := src + 1 }
  have hresult :
      (copyFromIncrTraced? valuesPresent destination source dst src).result =
        some result := by
    simp [copyFromIncrTraced?, TraceResult.map, hcopy, result]
  refine ⟨result, hresult, ?_, hsize, ?_, hsource, ?_, ?_⟩
  · simpa [copyFromIncrTraced?, TraceResult.map] using hbounds
  · exact copyFromIncrTraced_valuesModeInvariant valuesPresent destination
      source dst src result hdestination hsource hresult
  · change CursorInRange updated (dst + 1)
    exact hdst.increment_cursorInRange.of_size_eq hsize
  · change CursorInRange source (src + 1)
    exact hsrc.increment_cursorInRange

/-- Full decrementing two-slice copy safety.  Strict positivity of both input
cursors is essential: without it a returned cursor could be one-before-beginning. -/
theorem copyFromDecrTraced_safe
    (valuesPresent : Bool) (destination source : SortSlice κ ν)
    (dst src : Int)
    (hdestination : ValuesModeInvariant valuesPresent destination)
    (hsource : ValuesModeInvariant valuesPresent source)
    (hdst : IndexInBounds destination dst) (hsrc : IndexInBounds source src)
    (hdstPositive : 0 < dst) (hsrcPositive : 0 < src) :
    ∃ result,
      (copyFromDecrTraced? valuesPresent destination source dst src).result =
          some result ∧
        ((copyFromDecrTraced? valuesPresent destination source dst src).trace
          |>.allAccessesInBounds) ∧
        result.slice.entries.size = destination.entries.size ∧
        ValuesModeInvariant valuesPresent result.slice ∧
        ValuesModeInvariant valuesPresent source ∧
        CursorInRange result.slice result.dst ∧
        CursorInRange source result.src := by
  rcases copyFromTraced_safe valuesPresent destination source dst src hdst hsrc with
    ⟨updated, hcopy, hbounds, hsize⟩
  let result : CursorResult κ ν :=
    { slice := updated, dst := dst - 1, src := src - 1 }
  have hresult :
      (copyFromDecrTraced? valuesPresent destination source dst src).result =
        some result := by
    simp [copyFromDecrTraced?, TraceResult.map, hcopy, result]
  refine ⟨result, hresult, ?_, hsize, ?_, hsource, ?_, ?_⟩
  · simpa [copyFromDecrTraced?, TraceResult.map] using hbounds
  · exact copyFromDecrTraced_valuesModeInvariant valuesPresent destination
      source dst src result hdestination hsource hresult
  · change CursorInRange updated (dst - 1)
    exact (hdst.decrement_cursorInRange hdstPositive).of_size_eq hsize
  · change CursorInRange source (src - 1)
    exact hsrc.decrement_cursorInRange hsrcPositive

/-- Shared-store specialization of `copyFromIncrTraced_safe`. -/
theorem copyIncrTraced_safe
    (valuesPresent : Bool) (slice : SortSlice κ ν) (dst src : Int)
    (hdst : IndexInBounds slice dst) (hsrc : IndexInBounds slice src)
    (hinvariant : ValuesModeInvariant valuesPresent slice) :
    ∃ result,
      (copyIncrTraced? valuesPresent slice dst src).result = some result ∧
        (copyIncrTraced? valuesPresent slice dst src).trace.allAccessesInBounds ∧
        result.slice.entries.size = slice.entries.size ∧
        ValuesModeInvariant valuesPresent result.slice ∧
        CursorInRange result.slice result.dst ∧
        CursorInRange result.slice result.src := by
  rcases copyFromIncrTraced_safe valuesPresent slice slice dst src
      hinvariant hinvariant hdst hsrc with
    ⟨result, hresult, hbounds, hsize, hmode, _, hdstCursor, hsrcCursor⟩
  exact ⟨result, hresult, hbounds, hsize, hmode, hdstCursor,
    hsrcCursor.of_size_eq hsize⟩

/-- Shared-store specialization of `copyFromDecrTraced_safe`. -/
theorem copyDecrTraced_safe
    (valuesPresent : Bool) (slice : SortSlice κ ν) (dst src : Int)
    (hdst : IndexInBounds slice dst) (hsrc : IndexInBounds slice src)
    (hdstPositive : 0 < dst) (hsrcPositive : 0 < src)
    (hinvariant : ValuesModeInvariant valuesPresent slice) :
    ∃ result,
      (copyDecrTraced? valuesPresent slice dst src).result = some result ∧
        (copyDecrTraced? valuesPresent slice dst src).trace.allAccessesInBounds ∧
        result.slice.entries.size = slice.entries.size ∧
        ValuesModeInvariant valuesPresent result.slice ∧
        CursorInRange result.slice result.dst ∧
        CursorInRange result.slice result.src := by
  rcases copyFromDecrTraced_safe valuesPresent slice slice dst src
      hinvariant hinvariant hdst hsrc hdstPositive hsrcPositive with
    ⟨result, hresult, hbounds, hsize, hmode, _, hdstCursor, hsrcCursor⟩
  exact ⟨result, hresult, hbounds, hsize, hmode, hdstCursor,
    hsrcCursor.of_size_eq hsize⟩

/-- Advancement is pure signed cursor arithmetic and emits no access event.
Its explicit movement-range premise rules out invalid arithmetic despite that
empty trace; the actual slice supplies the extent and the values-mode witness. -/
theorem advanceTraced_safe (valuesPresent : Bool) (slice : SortSlice κ ν)
    (index amount : Int)
    (hinvariant : ValuesModeInvariant valuesPresent slice)
    (hmovement : CursorMovementInRange slice index amount) :
    (advanceTraced valuesPresent index amount).result =
        some (advance index amount) ∧
      (advanceTraced valuesPresent index amount).trace = AccessTrace.empty ∧
      (advanceTraced valuesPresent index amount).trace.allAccessesInBounds ∧
      CursorInRange slice (advance index amount) ∧
      ValuesModeInvariant valuesPresent slice := by
  exact ⟨rfl, rfl, AccessTrace.allAccessesInBounds_empty,
    hmovement.result, hinvariant⟩

/-- One-cell copy safety with the matching source/destination values mode
made explicit and preserved in the result. -/
theorem copyFromTraced_mode_safe
    (valuesPresent : Bool) (destination source : SortSlice κ ν)
    (dst src : Int)
    (hdestination : ValuesModeInvariant valuesPresent destination)
    (hsource : ValuesModeInvariant valuesPresent source)
    (hdst : IndexInBounds destination dst) (hsrc : IndexInBounds source src) :
    ∃ updated,
      (copyFromTraced? valuesPresent destination source dst src).result =
          some updated ∧
        (copyFromTraced? valuesPresent destination source dst src).trace.allAccessesInBounds ∧
        updated.entries.size = destination.entries.size ∧
        ValuesModeInvariant valuesPresent updated := by
  rcases copyFromTraced_safe valuesPresent destination source dst src hdst hsrc with
    ⟨updated, hresult, hbounds, hsize⟩
  exact ⟨updated, hresult, hbounds, hsize,
    copyFromTraced_valuesModeInvariant valuesPresent destination source updated
      dst src hdestination hsource hresult⟩

/-- Shared-store copy safety with values-mode preservation. -/
theorem copyTraced_mode_safe
    (valuesPresent : Bool) (slice : SortSlice κ ν) (dst src : Int)
    (hinvariant : ValuesModeInvariant valuesPresent slice)
    (hdst : IndexInBounds slice dst) (hsrc : IndexInBounds slice src) :
    ∃ updated,
      (copyTraced? valuesPresent slice dst src).result = some updated ∧
        (copyTraced? valuesPresent slice dst src).trace.allAccessesInBounds ∧
        updated.entries.size = slice.entries.size ∧
        ValuesModeInvariant valuesPresent updated := by
  rcases copyTraced_safe valuesPresent slice dst src hdst hsrc with
    ⟨updated, hresult, hbounds, hsize⟩
  exact ⟨updated, hresult, hbounds, hsize,
    copyTraced_valuesModeInvariant valuesPresent slice updated dst src
      hinvariant hresult⟩

/-- Nonoverlapping bulk-copy safety with matching modes on both stores and a
mode-valid destination result. -/
theorem memcpyTraced_mode_safe
    (valuesPresent : Bool) (count : Nat)
    (destination : SortSlice κ ν) (source : MemcpySource destination)
    (dst src : Int)
    (hadmissible : source.Admissible dst src count)
    (hdestination : ValuesModeInvariant valuesPresent destination)
    (hsource : ValuesModeInvariant valuesPresent source.store)
    (hdst : RangeInBounds destination dst count)
    (hsrc : RangeInBounds source.store src count) :
    ∃ updated,
      (memcpyTraced? valuesPresent count destination source dst src).result =
          some updated ∧
        (memcpyTraced? valuesPresent count destination source dst src).trace.allAccessesInBounds ∧
        updated.entries.size = destination.entries.size ∧
        ValuesModeInvariant valuesPresent updated := by
  rcases memcpyTraced_safe valuesPresent count destination source dst src
      hadmissible hdst hsrc with
    ⟨updated, hresult, hbounds, hsize⟩
  exact ⟨updated, hresult, hbounds, hsize,
    memcpyTraced_valuesModeInvariant valuesPresent count destination source
      updated dst src hdestination hsource hresult⟩

/-- Overlap-safe bulk movement preserves the single store's values mode. -/
theorem memmoveTraced_mode_safe
    (valuesPresent : Bool) (slice : SortSlice κ ν)
    (dst src : Int) (count : Nat)
    (hinvariant : ValuesModeInvariant valuesPresent slice)
    (hdst : RangeInBounds slice dst count)
    (hsrc : RangeInBounds slice src count) :
    ∃ updated,
      (memmoveTraced? valuesPresent slice dst src count).result = some updated ∧
        (memmoveTraced? valuesPresent slice dst src count).trace.allAccessesInBounds ∧
        updated.entries.size = slice.entries.size ∧
        ValuesModeInvariant valuesPresent updated := by
  rcases memmoveTraced_safe valuesPresent slice dst src count hdst hsrc with
    ⟨updated, hresult, hbounds, hsize⟩
  exact ⟨updated, hresult, hbounds, hsize,
    memmoveTraced_valuesModeInvariant valuesPresent slice updated dst src count
      hinvariant hresult⟩

/-- General two-store movement preserves the destination mode and leaves the
explicitly selected source store mode-valid.  For same-backing provenance the
source witness is the original destination invariant; for distinct provenance
it records that the separate source store is unchanged. -/
theorem memmoveFromTraced_mode_safe
    (valuesPresent : Bool) (destination : SortSlice κ ν)
    (source : MemmoveSource destination) (dst src : Int) (count : Nat)
    (hdestination : ValuesModeInvariant valuesPresent destination)
    (hsource : ValuesModeInvariant valuesPresent source.store)
    (hdst : RangeInBounds destination dst count)
    (hsrc : RangeInBounds source.store src count) :
    ∃ updated,
      (memmoveFromTraced? valuesPresent destination source dst src count).result =
          some updated ∧
        ((memmoveFromTraced? valuesPresent destination source dst src count).trace
          |>.allAccessesInBounds) ∧
        updated.entries.size = destination.entries.size ∧
        ValuesModeInvariant valuesPresent updated ∧
        ValuesModeInvariant valuesPresent source.store := by
  rcases memmoveFromTraced_safe valuesPresent destination source dst src count
      hdst hsrc with ⟨updated, hresult, hbounds, hsize⟩
  exact ⟨updated, hresult, hbounds, hsize,
    memmoveFromTraced_valuesModeInvariant valuesPresent destination source
      updated dst src count hdestination hsource hresult,
    hsource⟩

/-! ## Entry-array extent preservation -/

theorem copyFromTraced_entries_size_of_eq_some
    (valuesPresent : Bool) (destination source updated : SortSlice κ ν)
    (dst src : Int)
    (h : (copyFromTraced? valuesPresent destination source dst src).result =
      some updated) :
    updated.entries.size = destination.entries.size := by
  apply copyFrom_entries_size_of_eq_some destination source updated dst src
  rw [← erase_copyFromTraced valuesPresent destination source dst src]
  exact h

theorem copyTraced_entries_size_of_eq_some
    (valuesPresent : Bool) (slice updated : SortSlice κ ν) (dst src : Int)
    (h : (copyTraced? valuesPresent slice dst src).result = some updated) :
    updated.entries.size = slice.entries.size := by
  apply copy_entries_size_of_eq_some slice updated dst src
  rw [← erase_copyTraced valuesPresent slice dst src]
  exact h

theorem copyFromIncrTraced_entries_size_of_eq_some
    (valuesPresent : Bool) (destination source : SortSlice κ ν)
    (dst src : Int) (result : CursorResult κ ν)
    (h :
      (copyFromIncrTraced? valuesPresent destination source dst src).result =
        some result) :
    result.slice.entries.size = destination.entries.size := by
  apply copyFromIncr_entries_size_of_eq_some destination source dst src result
  rw [← erase_copyFromIncrTraced valuesPresent destination source dst src]
  exact h

theorem copyFromDecrTraced_entries_size_of_eq_some
    (valuesPresent : Bool) (destination source : SortSlice κ ν)
    (dst src : Int) (result : CursorResult κ ν)
    (h :
      (copyFromDecrTraced? valuesPresent destination source dst src).result =
        some result) :
    result.slice.entries.size = destination.entries.size := by
  apply copyFromDecr_entries_size_of_eq_some destination source dst src result
  rw [← erase_copyFromDecrTraced valuesPresent destination source dst src]
  exact h

theorem copyIncrTraced_entries_size_of_eq_some
    (valuesPresent : Bool) (slice : SortSlice κ ν) (dst src : Int)
    (result : CursorResult κ ν)
    (h : (copyIncrTraced? valuesPresent slice dst src).result = some result) :
    result.slice.entries.size = slice.entries.size := by
  exact copyFromIncrTraced_entries_size_of_eq_some valuesPresent slice slice
    dst src result h

theorem copyDecrTraced_entries_size_of_eq_some
    (valuesPresent : Bool) (slice : SortSlice κ ν) (dst src : Int)
    (result : CursorResult κ ν)
    (h : (copyDecrTraced? valuesPresent slice dst src).result = some result) :
    result.slice.entries.size = slice.entries.size := by
  exact copyFromDecrTraced_entries_size_of_eq_some valuesPresent slice slice
    dst src result h

theorem memcpyTraced_entries_size_of_eq_some
    (valuesPresent : Bool) (count : Nat)
    (destination : SortSlice κ ν) (source : MemcpySource destination)
    (updated : SortSlice κ ν) (dst src : Int)
    (h : (memcpyTraced? valuesPresent count destination source dst src).result =
      some updated) :
    updated.entries.size = destination.entries.size := by
  apply memcpy_entries_size_of_eq_some count destination source updated dst src
  rw [← erase_memcpyTraced valuesPresent count destination source dst src]
  exact h

theorem memmoveTraced_entries_size_of_eq_some
    (valuesPresent : Bool) (slice updated : SortSlice κ ν)
    (dst src : Int) (count : Nat)
    (h : (memmoveTraced? valuesPresent slice dst src count).result =
      some updated) :
    updated.entries.size = slice.entries.size := by
  apply memmove_entries_size_of_eq_some slice updated dst src count
  rw [← erase_memmoveTraced valuesPresent slice dst src count]
  exact h

theorem memmoveFromTraced_entries_size_of_eq_some
    (valuesPresent : Bool) (destination : SortSlice κ ν)
    (source : MemmoveSource destination) (updated : SortSlice κ ν)
    (dst src : Int) (count : Nat)
    (h :
      (memmoveFromTraced? valuesPresent destination source dst src count).result =
        some updated) :
    updated.entries.size = destination.entries.size := by
  apply memmoveFrom_entries_size_of_eq_some destination source updated dst src count
  rw [← erase_memmoveFromTraced valuesPresent destination source dst src count]
  exact h

/-! ## Umbrella contract -/

/-- The complete public contract represented by the roadmap's
`sortslice-safe` node.  It bundles erasure for every movement primitive,
source-order facts under a global explicit-values-mode invariant, in-bounds
execution under exact cell/range premises, cursor validity (including only the
documented one-past endpoint), mode preservation, and common-extent
preservation on every successful array-mutating result. -/
structure SortSlicePrimitiveSafety (key : Type u) (value : Type v) : Prop where
  eraseCopyFrom : ∀ (valuesPresent : Bool)
      (destination source : SortSlice key value) (dst src : Int),
    (copyFromTraced? valuesPresent destination source dst src).erase =
      destination.copyFrom? source dst src
  eraseCopy : ∀ (valuesPresent : Bool) (slice : SortSlice key value)
      (dst src : Int),
    (copyTraced? valuesPresent slice dst src).erase = slice.copy? dst src
  eraseCopyFromIncr : ∀ (valuesPresent : Bool)
      (destination source : SortSlice key value) (dst src : Int),
    (copyFromIncrTraced? valuesPresent destination source dst src).erase =
      destination.copyFromIncr? source dst src
  eraseCopyFromDecr : ∀ (valuesPresent : Bool)
      (destination source : SortSlice key value) (dst src : Int),
    (copyFromDecrTraced? valuesPresent destination source dst src).erase =
      destination.copyFromDecr? source dst src
  eraseCopyIncr : ∀ (valuesPresent : Bool) (slice : SortSlice key value)
      (dst src : Int),
    (copyIncrTraced? valuesPresent slice dst src).erase =
      slice.copyIncr? dst src
  eraseCopyDecr : ∀ (valuesPresent : Bool) (slice : SortSlice key value)
      (dst src : Int),
    (copyDecrTraced? valuesPresent slice dst src).erase =
      slice.copyDecr? dst src
  eraseMemcpy : ∀ (valuesPresent : Bool) (count : Nat)
      (destination : SortSlice key value)
      (source : MemcpySource destination) (dst src : Int),
    (memcpyTraced? valuesPresent count destination source dst src).erase =
      memcpy? count destination source dst src
  sameBackingMemcpyRejectsOverlap : ∀ (valuesPresent : Bool) (count : Nat)
      (destination : SortSlice key value) (dst src : Int),
    ¬ MemcpyRangesDisjoint dst src count →
      (memcpyTraced? valuesPresent count destination .sameBacking dst src).result =
          none ∧
        (memcpyTraced? valuesPresent count destination .sameBacking dst src).trace =
          AccessTrace.empty ∧
        (memcpyTraced? valuesPresent count destination .sameBacking dst src).erase =
          memcpy? count destination .sameBacking dst src
  eraseMemmoveFrom : ∀ (valuesPresent : Bool)
      (destination : SortSlice key value)
      (source : MemmoveSource destination) (dst src : Int) (count : Nat),
    (memmoveFromTraced? valuesPresent destination source dst src count).erase =
      memmoveFrom? destination source dst src count
  eraseMemmove : ∀ (valuesPresent : Bool) (slice : SortSlice key value)
      (dst src : Int) (count : Nat),
    (memmoveTraced? valuesPresent slice dst src count).erase =
      slice.memmove? dst src count
  eraseAdvance : ∀ (valuesPresent : Bool) (index amount : Int),
    (advanceTraced valuesPresent index amount).erase =
      some (advance index amount)
  falseModeRejectsPayload : ∀ (entryKey : key) (entryValue : value),
    ¬ ValuesModeInvariant false
      ({ entries := #[{ key := entryKey, value := some entryValue }] } :
        SortSlice key value)
  copyEventOrder : ∀ (valuesPresent : Bool)
      (destination source : SortSlice key value) (dst src : Int),
    ValuesModeInvariant valuesPresent destination →
      ValuesModeInvariant valuesPresent source →
      IndexInBounds destination dst → IndexInBounds source src →
      (copyFromTraced? valuesPresent destination source dst src).trace.accesses =
        keyCopyAccesses destination.entries.size source.entries.size dst src ++
          if valuesPresent then
            valuesCopyAccesses destination.entries.size source.entries.size dst src
          else []
  copyFromIncrEventOrder : ∀ (valuesPresent : Bool)
      (destination source : SortSlice key value) (dst src : Int),
    ValuesModeInvariant valuesPresent destination →
      ValuesModeInvariant valuesPresent source →
      IndexInBounds destination dst → IndexInBounds source src →
      (copyFromIncrTraced? valuesPresent destination source dst src).trace.accesses =
        keyCopyAccesses destination.entries.size source.entries.size dst src ++
          if valuesPresent then
            valuesCopyAccesses destination.entries.size source.entries.size dst src
          else []
  copyFromDecrEventOrder : ∀ (valuesPresent : Bool)
      (destination source : SortSlice key value) (dst src : Int),
    ValuesModeInvariant valuesPresent destination →
      ValuesModeInvariant valuesPresent source →
      IndexInBounds destination dst → IndexInBounds source src →
      (copyFromDecrTraced? valuesPresent destination source dst src).trace.accesses =
        keyCopyAccesses destination.entries.size source.entries.size dst src ++
          if valuesPresent then
            valuesCopyAccesses destination.entries.size source.entries.size dst src
          else []
  memcpyPhaseOrder : ∀ (valuesPresent : Bool) (count : Nat)
      (destination : SortSlice key value)
      (source : MemcpySource destination) (dst src : Int),
    ValuesModeInvariant valuesPresent destination →
      ValuesModeInvariant valuesPresent source.store →
      source.Admissible dst src count →
      RangeInBounds destination dst count →
      RangeInBounds source.store src count →
      (memcpyTraced? valuesPresent count destination source dst src).trace.accesses =
        (memcpyKeysTraced? count destination source.store dst src).trace.accesses ++
          if valuesPresent then
            (memcpyValuesTraced? count destination source.store dst src).trace.accesses
          else []
  memmoveFromPhaseOrder : ∀ (valuesPresent : Bool)
      (destination : SortSlice key value)
      (source : MemmoveSource destination) (dst src : Int) (count : Nat),
    ValuesModeInvariant valuesPresent destination →
      ValuesModeInvariant valuesPresent source.store →
      RangeInBounds destination dst count →
      RangeInBounds source.store src count →
      (memmoveFromTraced? valuesPresent destination source dst src count).trace.accesses =
        match source with
        | .sameBacking =>
            match memmoveDirection dst src with
            | .forward =>
                (memmoveForwardKeysTraced? count destination dst src).trace.accesses ++
                  if valuesPresent then
                    (memmoveForwardValuesTraced? count destination dst src).trace.accesses
                  else []
            | .backward =>
                (memmoveBackwardKeysTraced? count destination dst src).trace.accesses ++
                  if valuesPresent then
                    (memmoveBackwardValuesTraced? count destination dst src).trace.accesses
                  else []
        | .distinctBacking source =>
            (memcpyKeysTraced? count destination source dst src).trace.accesses ++
              if valuesPresent then
                (memcpyValuesTraced? count destination source dst src).trace.accesses
              else []
  memmovePhaseOrder : ∀ (valuesPresent : Bool)
      (slice : SortSlice key value) (dst src : Int) (count : Nat),
    ValuesModeInvariant valuesPresent slice →
      RangeInBounds slice dst count → RangeInBounds slice src count →
      (memmoveTraced? valuesPresent slice dst src count).trace.accesses =
        match memmoveDirection dst src with
        | .forward =>
            (memmoveForwardKeysTraced? count slice dst src).trace.accesses ++
              if valuesPresent then
                (memmoveForwardValuesTraced? count slice dst src).trace.accesses
              else []
        | .backward =>
            (memmoveBackwardKeysTraced? count slice dst src).trace.accesses ++
              if valuesPresent then
                (memmoveBackwardValuesTraced? count slice dst src).trace.accesses
              else []
  copyFromSafety : ∀ (valuesPresent : Bool)
      (destination source : SortSlice key value) (dst src : Int),
    ValuesModeInvariant valuesPresent destination →
      ValuesModeInvariant valuesPresent source →
      IndexInBounds destination dst → IndexInBounds source src →
      ∃ updated,
          (copyFromTraced? valuesPresent destination source dst src).result =
            some updated ∧
          (copyFromTraced? valuesPresent destination source dst src).trace.allAccessesInBounds ∧
          updated.entries.size = destination.entries.size ∧
          ValuesModeInvariant valuesPresent updated
  copySafety : ∀ (valuesPresent : Bool) (slice : SortSlice key value)
      (dst src : Int),
    ValuesModeInvariant valuesPresent slice →
      IndexInBounds slice dst → IndexInBounds slice src →
      ∃ updated,
        (copyTraced? valuesPresent slice dst src).result = some updated ∧
          (copyTraced? valuesPresent slice dst src).trace.allAccessesInBounds ∧
          updated.entries.size = slice.entries.size ∧
          ValuesModeInvariant valuesPresent updated
  copyFromIncrSafety : ∀ (valuesPresent : Bool)
      (destination source : SortSlice key value) (dst src : Int),
    ValuesModeInvariant valuesPresent destination →
      ValuesModeInvariant valuesPresent source →
      IndexInBounds destination dst → IndexInBounds source src →
      ∃ result,
        (copyFromIncrTraced? valuesPresent destination source dst src).result =
            some result ∧
          ((copyFromIncrTraced? valuesPresent destination source dst src).trace
            |>.allAccessesInBounds) ∧
          result.slice.entries.size = destination.entries.size ∧
          ValuesModeInvariant valuesPresent result.slice ∧
          ValuesModeInvariant valuesPresent source ∧
          CursorInRange result.slice result.dst ∧
          CursorInRange source result.src
  copyFromDecrSafety : ∀ (valuesPresent : Bool)
      (destination source : SortSlice key value) (dst src : Int),
    ValuesModeInvariant valuesPresent destination →
      ValuesModeInvariant valuesPresent source →
      IndexInBounds destination dst → IndexInBounds source src →
      0 < dst → 0 < src →
      ∃ result,
        (copyFromDecrTraced? valuesPresent destination source dst src).result =
            some result ∧
          ((copyFromDecrTraced? valuesPresent destination source dst src).trace
            |>.allAccessesInBounds) ∧
          result.slice.entries.size = destination.entries.size ∧
          ValuesModeInvariant valuesPresent result.slice ∧
          ValuesModeInvariant valuesPresent source ∧
          CursorInRange result.slice result.dst ∧
          CursorInRange source result.src
  copyIncrSafety : ∀ (valuesPresent : Bool) (slice : SortSlice key value)
      (dst src : Int),
    ValuesModeInvariant valuesPresent slice →
      IndexInBounds slice dst → IndexInBounds slice src →
      ∃ result,
        (copyIncrTraced? valuesPresent slice dst src).result = some result ∧
          (copyIncrTraced? valuesPresent slice dst src).trace.allAccessesInBounds ∧
          result.slice.entries.size = slice.entries.size ∧
          ValuesModeInvariant valuesPresent result.slice ∧
          CursorInRange result.slice result.dst ∧
          CursorInRange result.slice result.src
  copyDecrSafety : ∀ (valuesPresent : Bool) (slice : SortSlice key value)
      (dst src : Int),
    ValuesModeInvariant valuesPresent slice →
      IndexInBounds slice dst → IndexInBounds slice src →
      0 < dst → 0 < src →
      ∃ result,
        (copyDecrTraced? valuesPresent slice dst src).result = some result ∧
          (copyDecrTraced? valuesPresent slice dst src).trace.allAccessesInBounds ∧
          result.slice.entries.size = slice.entries.size ∧
          ValuesModeInvariant valuesPresent result.slice ∧
          CursorInRange result.slice result.dst ∧
          CursorInRange result.slice result.src
  memcpySafety : ∀ (valuesPresent : Bool) (count : Nat)
      (destination : SortSlice key value)
      (source : MemcpySource destination) (dst src : Int),
    ValuesModeInvariant valuesPresent destination →
      ValuesModeInvariant valuesPresent source.store →
      source.Admissible dst src count →
      RangeInBounds destination dst count →
      RangeInBounds source.store src count →
      ∃ updated,
          (memcpyTraced? valuesPresent count destination source dst src).result =
            some updated ∧
          (memcpyTraced? valuesPresent count destination source dst src).trace.allAccessesInBounds ∧
          updated.entries.size = destination.entries.size ∧
          ValuesModeInvariant valuesPresent updated
  memmoveFromSafety : ∀ (valuesPresent : Bool)
      (destination : SortSlice key value)
      (source : MemmoveSource destination) (dst src : Int) (count : Nat),
    ValuesModeInvariant valuesPresent destination →
      ValuesModeInvariant valuesPresent source.store →
      RangeInBounds destination dst count →
      RangeInBounds source.store src count →
      ∃ updated,
        (memmoveFromTraced? valuesPresent destination source dst src count).result =
            some updated ∧
          ((memmoveFromTraced? valuesPresent destination source dst src count).trace
            |>.allAccessesInBounds) ∧
          updated.entries.size = destination.entries.size ∧
          ValuesModeInvariant valuesPresent updated ∧
          ValuesModeInvariant valuesPresent source.store
  memmoveSafety : ∀ (valuesPresent : Bool) (slice : SortSlice key value)
      (dst src : Int) (count : Nat),
    ValuesModeInvariant valuesPresent slice →
      RangeInBounds slice dst count → RangeInBounds slice src count →
      ∃ updated,
        (memmoveTraced? valuesPresent slice dst src count).result = some updated ∧
          (memmoveTraced? valuesPresent slice dst src count).trace.allAccessesInBounds ∧
          updated.entries.size = slice.entries.size ∧
          ValuesModeInvariant valuesPresent updated
  advanceSafety : ∀ (valuesPresent : Bool) (slice : SortSlice key value)
      (index amount : Int),
    ValuesModeInvariant valuesPresent slice →
      CursorMovementInRange slice index amount →
      (advanceTraced valuesPresent index amount).result =
          some (advance index amount) ∧
        (advanceTraced valuesPresent index amount).trace = AccessTrace.empty ∧
        (advanceTraced valuesPresent index amount).trace.allAccessesInBounds ∧
        CursorInRange slice (advance index amount) ∧
        ValuesModeInvariant valuesPresent slice
  copyFromExtent : ∀ (valuesPresent : Bool)
      (destination source updated : SortSlice key value) (dst src : Int),
    (copyFromTraced? valuesPresent destination source dst src).result =
        some updated →
      updated.entries.size = destination.entries.size
  copyExtent : ∀ (valuesPresent : Bool)
      (slice updated : SortSlice key value) (dst src : Int),
    (copyTraced? valuesPresent slice dst src).result = some updated →
      updated.entries.size = slice.entries.size
  copyFromIncrExtent : ∀ (valuesPresent : Bool)
      (destination source : SortSlice key value) (dst src : Int)
      (result : CursorResult key value),
    (copyFromIncrTraced? valuesPresent destination source dst src).result =
        some result →
      result.slice.entries.size = destination.entries.size
  copyFromDecrExtent : ∀ (valuesPresent : Bool)
      (destination source : SortSlice key value) (dst src : Int)
      (result : CursorResult key value),
    (copyFromDecrTraced? valuesPresent destination source dst src).result =
        some result →
      result.slice.entries.size = destination.entries.size
  copyIncrExtent : ∀ (valuesPresent : Bool) (slice : SortSlice key value)
      (dst src : Int) (result : CursorResult key value),
    (copyIncrTraced? valuesPresent slice dst src).result = some result →
      result.slice.entries.size = slice.entries.size
  copyDecrExtent : ∀ (valuesPresent : Bool) (slice : SortSlice key value)
      (dst src : Int) (result : CursorResult key value),
    (copyDecrTraced? valuesPresent slice dst src).result = some result →
      result.slice.entries.size = slice.entries.size
  memcpyExtent : ∀ (valuesPresent : Bool) (count : Nat)
      (destination : SortSlice key value)
      (source : MemcpySource destination) (updated : SortSlice key value)
      (dst src : Int),
    (memcpyTraced? valuesPresent count destination source dst src).result =
        some updated →
      updated.entries.size = destination.entries.size
  memmoveFromExtent : ∀ (valuesPresent : Bool)
      (destination : SortSlice key value)
      (source : MemmoveSource destination) (updated : SortSlice key value)
      (dst src : Int) (count : Nat),
    (memmoveFromTraced? valuesPresent destination source dst src count).result =
        some updated →
      updated.entries.size = destination.entries.size
  memmoveExtent : ∀ (valuesPresent : Bool)
      (slice updated : SortSlice key value) (dst src : Int) (count : Nat),
    (memmoveTraced? valuesPresent slice dst src count).result = some updated →
      updated.entries.size = slice.entries.size

/-- Every `sortslice` primitive satisfies the complete traced safety contract.
This is the declaration intended for the roadmap node's `lean:` field. -/
theorem sortslice_primitives_safe : SortSlicePrimitiveSafety κ ν := by
  refine
    { eraseCopyFrom := erase_copyFromTraced
      eraseCopy := erase_copyTraced
      eraseCopyFromIncr := erase_copyFromIncrTraced
      eraseCopyFromDecr := erase_copyFromDecrTraced
      eraseCopyIncr := erase_copyIncrTraced
      eraseCopyDecr := erase_copyDecrTraced
      eraseMemcpy := erase_memcpyTraced
      sameBackingMemcpyRejectsOverlap :=
        memcpyTraced_sameBacking_overlap_rejected
      eraseMemmoveFrom := erase_memmoveFromTraced
      eraseMemmove := erase_memmoveTraced
      eraseAdvance := erase_advanceTraced
      falseModeRejectsPayload := falseMode_somePayload_violates_invariant
      copyEventOrder := ?_
      copyFromIncrEventOrder := ?_
      copyFromDecrEventOrder := ?_
      memcpyPhaseOrder := ?_
      memmoveFromPhaseOrder := ?_
      memmovePhaseOrder := ?_
      copyFromSafety := ?_
      copySafety := ?_
      copyFromIncrSafety := copyFromIncrTraced_safe
      copyFromDecrSafety := copyFromDecrTraced_safe
      copyIncrSafety := ?_
      copyDecrSafety := ?_
      memcpySafety := ?_
      memmoveFromSafety := memmoveFromTraced_mode_safe
      memmoveSafety := ?_
      advanceSafety := advanceTraced_safe
      copyFromExtent := copyFromTraced_entries_size_of_eq_some
      copyExtent := copyTraced_entries_size_of_eq_some
      copyFromIncrExtent := copyFromIncrTraced_entries_size_of_eq_some
      copyFromDecrExtent := copyFromDecrTraced_entries_size_of_eq_some
      copyIncrExtent := copyIncrTraced_entries_size_of_eq_some
      copyDecrExtent := copyDecrTraced_entries_size_of_eq_some
      memcpyExtent := memcpyTraced_entries_size_of_eq_some
      memmoveFromExtent := memmoveFromTraced_entries_size_of_eq_some
      memmoveExtent := memmoveTraced_entries_size_of_eq_some }
  · intro valuesPresent destination source dst src _ _ hdst hsrc
    exact copyFromTraced_accesses valuesPresent destination source dst src hdst hsrc
  · intro valuesPresent destination source dst src _ _ hdst hsrc
    exact copyFromIncrTraced_accesses valuesPresent destination source dst src
      hdst hsrc
  · intro valuesPresent destination source dst src _ _ hdst hsrc
    exact copyFromDecrTraced_accesses valuesPresent destination source dst src
      hdst hsrc
  · intro valuesPresent count destination source dst src _ _ hadmissible hdst hsrc
    exact memcpyTraced_phase_order valuesPresent count destination source dst src
      hadmissible hdst hsrc
  · intro valuesPresent destination source dst src count _ _ hdst hsrc
    cases source with
    | sameBacking =>
        exact memmoveFromTraced_sameBacking_phase_order valuesPresent destination
          dst src count hdst hsrc
    | distinctBacking source =>
        exact memmoveFromTraced_distinctBacking_phase_order valuesPresent count
          destination source dst src hdst hsrc
  · intro valuesPresent slice dst src count _ hdst hsrc
    exact memmoveTraced_phase_order valuesPresent slice dst src count hdst hsrc
  · intro valuesPresent destination source dst src hdestination hsource hdst hsrc
    exact copyFromTraced_mode_safe valuesPresent destination source dst src
      hdestination hsource hdst hsrc
  · intro valuesPresent slice dst src hinvariant hdst hsrc
    exact copyTraced_mode_safe valuesPresent slice dst src hinvariant hdst hsrc
  · intro valuesPresent slice dst src hinvariant hdst hsrc
    exact copyIncrTraced_safe valuesPresent slice dst src hdst hsrc hinvariant
  · intro valuesPresent slice dst src hinvariant hdst hsrc hdstPositive
      hsrcPositive
    exact copyDecrTraced_safe valuesPresent slice dst src hdst hsrc hdstPositive
      hsrcPositive hinvariant
  · intro valuesPresent count destination source dst src hdestination hsource
      hadmissible hdst hsrc
    exact memcpyTraced_mode_safe valuesPresent count destination source dst src
      hadmissible hdestination hsource hdst hsrc
  · intro valuesPresent slice dst src count hinvariant hdst hsrc
    exact memmoveTraced_mode_safe valuesPresent slice dst src count hinvariant
      hdst hsrc

end SortSlice

end CPythonListsort
