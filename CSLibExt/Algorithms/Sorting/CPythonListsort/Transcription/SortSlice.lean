/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

/-!
# `sortslice` model and movement primitives

CPython stores keys and optional payload values in parallel pointer arrays.
The Lean model stores their observable pairing as one entry, so every movement
primitive moves a key and its payload atomically.  Integer indices replace raw
pointers.  Failed bounds checks are explicit through `Option`; later safety
proofs establish that transcribed calls return `some`.

`memmove` carries explicit backing provenance.  On one shared store it chooses
its traversal direction from the overlap geometry: a rightward overlapping
move copies from the end, while a leftward move copies from the beginning, so
unread source entries are never overwritten.  A distinct backing instead uses
the source-language's forward two-store copy order, even when its contents
happen to equal the destination.  `memcpy` uses the same provenance distinction
but rejects overlapping same-backing ranges.
-/

namespace CPythonListsort

universe u v

/-- One observable key/payload pair.  `none` models `values == NULL`. -/
structure SortSliceEntry (κ : Type u) (ν : Type v) where
  key : κ
  value : Option ν
  deriving DecidableEq, Repr

/-- Array-backed storage used in place of CPython's synchronized pointer arrays. -/
structure SortSlice (κ : Type u) (ν : Type v) where
  entries : Array (SortSliceEntry κ ν)
  deriving DecidableEq, Repr

namespace SortSlice

/-- Read an entry through a signed pointer-like index. -/
def read? (slice : SortSlice κ ν) (index : Int) : Option (SortSliceEntry κ ν) :=
  if 0 ≤ index then
    slice.entries[index.toNat]?
  else
    none

/-- Replace an entry through a signed pointer-like index. -/
def write? (slice : SortSlice κ ν) (index : Int) (entry : SortSliceEntry κ ν) :
    Option (SortSlice κ ν) :=
  if hnonnegative : 0 ≤ index then
    let i := index.toNat
    if hinBounds : i < slice.entries.size then
      some { entries := slice.entries.set i entry }
    else
      none
  else
    none

/-- Copy one synchronized entry from `source` into `destination`. -/
def copyFrom? (destination source : SortSlice κ ν) (dst src : Int) :
    Option (SortSlice κ ν) := do
  let entry ← source.read? src
  destination.write? dst entry

/-- Copy one synchronized entry within a shared store. -/
def copy? (slice : SortSlice κ ν) (dst src : Int) : Option (SortSlice κ ν) :=
  copyFrom? slice slice dst src

/-- Result of a single copying step together with the advanced cursors. -/
structure CursorResult (κ : Type u) (ν : Type v) where
  slice : SortSlice κ ν
  dst : Int
  src : Int
  deriving DecidableEq, Repr

/-- Copy between the current cursors of two slices, then increment both as
`sortslice_copy_incr` does.  Only the destination store is updated; the source
cursor is nevertheless returned alongside the destination cursor. -/
def copyFromIncr? (destination source : SortSlice κ ν)
    (dst src : Int) : Option (CursorResult κ ν) := do
  let updated ← destination.copyFrom? source dst src
  pure { slice := updated, dst := dst + 1, src := src + 1 }

/-- Copy between the current cursors of two slices, then decrement both as
`sortslice_copy_decr` does.  Only the destination store is updated; the source
cursor is nevertheless returned alongside the destination cursor. -/
def copyFromDecr? (destination source : SortSlice κ ν)
    (dst src : Int) : Option (CursorResult κ ν) := do
  let updated ← destination.copyFrom? source dst src
  pure { slice := updated, dst := dst - 1, src := src - 1 }

/-- Shared-store specialization of `copyFromIncr?`. -/
def copyIncr? (slice : SortSlice κ ν) (dst src : Int) : Option (CursorResult κ ν) :=
  copyFromIncr? slice slice dst src

/-- Shared-store specialization of `copyFromDecr?`. -/
def copyDecr? (slice : SortSlice κ ν) (dst src : Int) : Option (CursorResult κ ν) :=
  copyFromDecr? slice slice dst src

/-- Two equal-length half-open ranges do not overlap.  The formulation admits
empty ranges and ranges that meet exactly at an endpoint. -/
def MemcpyRangesDisjoint (dst src : Int) (count : Nat) : Prop :=
  dst + Int.ofNat count ≤ src ∨ src + Int.ofNat count ≤ dst

instance (dst src : Int) (count : Nat) :
    Decidable (MemcpyRangesDisjoint dst src count) :=
  inferInstanceAs
    (Decidable
      (dst + Int.ofNat count ≤ src ∨ src + Int.ofNat count ≤ dst))

/-- Provenance of the source operand of `memcpy` relative to its destination.

The same-backing constructor carries no second `SortSlice`: its source is the
destination itself by construction.  The distinct-backing constructor is an
explicit provenance assertion and therefore remains distinct even when its
stored contents are extensionally equal to the destination. -/
inductive MemcpySource (destination : SortSlice κ ν) where
  | sameBacking
  | distinctBacking (source : SortSlice κ ν)
  deriving Repr

namespace MemcpySource

/-- Recover the source store selected by its backing provenance. -/
def store {destination : SortSlice κ ν} :
    MemcpySource destination → SortSlice κ ν
  | .sameBacking => destination
  | .distinctBacking source => source

/-- C `memcpy` admits different backings unconditionally with respect to
aliasing.  A shared backing instead requires disjoint logical entry ranges. -/
def Admissible {destination : SortSlice κ ν}
    (source : MemcpySource destination) (dst src : Int) (count : Nat) : Prop :=
  match source with
  | .sameBacking => MemcpyRangesDisjoint dst src count
  | .distinctBacking _ => True

instance {destination : SortSlice κ ν} (source : MemcpySource destination)
    (dst src : Int) (count : Nat) : Decidable (source.Admissible dst src count) :=
  match source with
  | .sameBacking => inferInstanceAs (Decidable (MemcpyRangesDisjoint dst src count))
  | .distinctBacking _ => isTrue trivial

end MemcpySource

/-- Unchecked forward-copy loop.  Its public wrapper supplies the C `memcpy`
backing-domain check once, before any access occurs. -/
def memcpyCore? :
    Nat → SortSlice κ ν → SortSlice κ ν → Int → Int → Option (SortSlice κ ν)
  | 0, destination, _, _, _ => some destination
  | count + 1, destination, source, dst, src => do
      let updated ← copyFrom? destination source dst src
      memcpyCore? count updated source (dst + 1) (src + 1)

/-- Copy `count` entries using C `memcpy`'s backing discipline.  Overlapping
same-backing ranges are outside the modeled domain and return `none` before any
copy step; distinct backings are not inferred from their contents. -/
def memcpy? (count : Nat) (destination : SortSlice κ ν)
    (source : MemcpySource destination) (dst src : Int) : Option (SortSlice κ ν) :=
  if source.Admissible dst src count then
    memcpyCore? count destination source.store dst src
  else
    none

/-- A positive or otherwise overlapping same-backing `memcpy` request is
rejected at the public boundary. -/
theorem memcpy_sameBacking_overlap_rejected (count : Nat)
    (destination : SortSlice κ ν) (dst src : Int)
    (hoverlap : ¬ MemcpyRangesDisjoint dst src count) :
    memcpy? count destination .sameBacking dst src = none := by
  simp [memcpy?, MemcpySource.Admissible, hoverlap]

/-- The traversal direction required for an overlap-safe movement. -/
inductive MovementDirection where
  | forward
  | backward
  deriving DecidableEq, Repr

/-- A leftward move is forward; a genuinely rightward move is backward. -/
def memmoveDirection (dst src : Int) : MovementDirection :=
  if dst ≤ src then .forward else .backward

/-- Forward traversal used by `memmove?` when the destination does not begin
to the right of the source.  Exported for direct trace instrumentation. -/
def memmoveForward? :
    Nat → SortSlice κ ν → Int → Int → Option (SortSlice κ ν)
  | 0, slice, _, _ => some slice
  | count + 1, slice, dst, src => do
      let updated ← slice.copy? dst src
      memmoveForward? count updated (dst + 1) (src + 1)

/-- Backward traversal used by `memmove?` for a rightward move, preventing an
overlapping write from destroying an unread source entry.  Exported for direct
trace instrumentation. -/
def memmoveBackward? :
    Nat → SortSlice κ ν → Int → Int → Option (SortSlice κ ν)
  | 0, slice, _, _ => some slice
  | count + 1, slice, dst, src => do
      let offset := Int.ofNat count
      let updated ← slice.copy? (dst + offset) (src + offset)
      memmoveBackward? count updated dst src

/-- Overlap-safe movement within one store, matching C `memmove` direction. -/
def memmove? (slice : SortSlice κ ν) (dst src : Int) (count : Nat) :
    Option (SortSlice κ ν) :=
  match memmoveDirection dst src with
  | .forward => memmoveForward? count slice dst src
  | .backward => memmoveBackward? count slice dst src

/-- Provenance of the source operand of `sortslice_memmove`.  Movement uses the
same dependent backing witness as `memcpy`, but imposes no disjointness
condition: shared storage is handled by overlap-safe traversal instead. -/
abbrev MemmoveSource (destination : SortSlice κ ν) :=
  MemcpySource destination

/-- General two-store `sortslice_memmove`.  Same-backing movement delegates to
the overlap-safe shared-store implementation, while a distinct backing follows
the C helper's increasing-address source order.  The branch is selected only by
the explicit provenance constructor, never by comparing stored contents. -/
def memmoveFrom? (destination : SortSlice κ ν)
    (source : MemmoveSource destination) (dst src : Int) (count : Nat) :
    Option (SortSlice κ ν) :=
  match source with
  | .sameBacking => destination.memmove? dst src count
  | .distinctBacking source => memcpyCore? count destination source dst src

@[simp]
theorem memmoveFrom_sameBacking (destination : SortSlice κ ν)
    (dst src : Int) (count : Nat) :
    memmoveFrom? destination .sameBacking dst src count =
      destination.memmove? dst src count := by
  rfl

@[simp]
theorem memmoveFrom_distinctBacking (destination source : SortSlice κ ν)
    (dst src : Int) (count : Nat) :
    memmoveFrom? destination (.distinctBacking source) dst src count =
      memcpyCore? count destination source dst src := by
  rfl

/-! The merge-policy layer only needs the storage-shape fact that successful
movement primitives replace entries in place and therefore preserve length. -/

theorem write_entries_size_of_eq_some (slice updated : SortSlice κ ν)
    (index : Int) (entry : SortSliceEntry κ ν)
    (h : slice.write? index entry = some updated) :
    updated.entries.size = slice.entries.size := by
  unfold write? at h
  split at h
  · dsimp only at h
    split at h
    · simp only [Option.some.injEq] at h
      subst updated
      simp
    · contradiction
  · contradiction

theorem copyFrom_entries_size_of_eq_some (destination source updated : SortSlice κ ν)
  (dst src : Int) (h : destination.copyFrom? source dst src = some updated) :
    updated.entries.size = destination.entries.size := by
  simp only [copyFrom?, bind, Option.bind] at h
  split at h
  · simp at h
  · exact write_entries_size_of_eq_some _ _ _ _ h

theorem copy_entries_size_of_eq_some (slice updated : SortSlice κ ν)
    (dst src : Int) (h : slice.copy? dst src = some updated) :
    updated.entries.size = slice.entries.size :=
  copyFrom_entries_size_of_eq_some _ _ _ _ _ h

theorem copyFromIncr_entries_size_of_eq_some
    (destination source : SortSlice κ ν) (dst src : Int)
    (result : CursorResult κ ν)
    (h : destination.copyFromIncr? source dst src = some result) :
    result.slice.entries.size = destination.entries.size := by
  simp only [copyFromIncr?, bind, Option.bind] at h
  split at h
  · simp at h
  · rename_i updated hcopy
    have hresult :
        { slice := updated, dst := dst + 1, src := src + 1 } = result := by
      simpa using h
    rw [← hresult]
    exact copyFrom_entries_size_of_eq_some _ _ _ _ _ hcopy

theorem copyFromDecr_entries_size_of_eq_some
    (destination source : SortSlice κ ν) (dst src : Int)
    (result : CursorResult κ ν)
    (h : destination.copyFromDecr? source dst src = some result) :
    result.slice.entries.size = destination.entries.size := by
  simp only [copyFromDecr?, bind, Option.bind] at h
  split at h
  · simp at h
  · rename_i updated hcopy
    have hresult :
        { slice := updated, dst := dst - 1, src := src - 1 } = result := by
      simpa using h
    rw [← hresult]
    exact copyFrom_entries_size_of_eq_some _ _ _ _ _ hcopy

theorem copyIncr_entries_size_of_eq_some (slice : SortSlice κ ν) (dst src : Int)
    (result : CursorResult κ ν) (h : slice.copyIncr? dst src = some result) :
    result.slice.entries.size = slice.entries.size := by
  exact copyFromIncr_entries_size_of_eq_some slice slice dst src result h

theorem copyDecr_entries_size_of_eq_some (slice : SortSlice κ ν) (dst src : Int)
    (result : CursorResult κ ν) (h : slice.copyDecr? dst src = some result) :
    result.slice.entries.size = slice.entries.size := by
  exact copyFromDecr_entries_size_of_eq_some slice slice dst src result h

private theorem memcpyCore_entries_size_of_eq_some (count : Nat)
    (destination source updated : SortSlice κ ν) (dst src : Int)
    (h : memcpyCore? count destination source dst src = some updated) :
    updated.entries.size = destination.entries.size := by
  induction count generalizing destination dst src with
  | zero =>
      simpa [memcpyCore?] using
        (congrArg (fun value => value.map (·.entries.size)) h).symm
  | succ count ih =>
      simp only [memcpyCore?, bind, Option.bind] at h
      split at h
      · simp at h
      · exact (ih _ _ _ h).trans (copyFrom_entries_size_of_eq_some _ _ _ _ _ ‹_›)

theorem memcpy_entries_size_of_eq_some (count : Nat)
    (destination : SortSlice κ ν) (source : MemcpySource destination)
    (updated : SortSlice κ ν) (dst src : Int)
    (h : memcpy? count destination source dst src = some updated) :
    updated.entries.size = destination.entries.size := by
  unfold memcpy? at h
  split at h
  · exact memcpyCore_entries_size_of_eq_some _ _ _ _ _ _ h
  · simp at h

private theorem memmoveForward_entries_size_of_eq_some (count : Nat)
    (slice updated : SortSlice κ ν) (dst src : Int)
    (h : memmoveForward? count slice dst src = some updated) :
    updated.entries.size = slice.entries.size := by
  induction count generalizing slice dst src with
  | zero =>
      simpa [memmoveForward?] using
        (congrArg (fun value => value.map (·.entries.size)) h).symm
  | succ count ih =>
      simp only [memmoveForward?, bind, Option.bind] at h
      split at h
      · simp at h
      · exact (ih _ _ _ h).trans (copy_entries_size_of_eq_some _ _ _ _ ‹_›)

private theorem memmoveBackward_entries_size_of_eq_some (count : Nat)
    (slice updated : SortSlice κ ν) (dst src : Int)
    (h : memmoveBackward? count slice dst src = some updated) :
    updated.entries.size = slice.entries.size := by
  induction count generalizing slice dst src with
  | zero =>
      simpa [memmoveBackward?] using
        (congrArg (fun value => value.map (·.entries.size)) h).symm
  | succ count ih =>
      simp only [memmoveBackward?, bind, Option.bind] at h
      split at h
      · simp at h
      · exact (ih _ _ _ h).trans (copy_entries_size_of_eq_some _ _ _ _ ‹_›)

theorem memmove_entries_size_of_eq_some (slice updated : SortSlice κ ν)
    (dst src : Int) (count : Nat) (h : slice.memmove? dst src count = some updated) :
    updated.entries.size = slice.entries.size := by
  simp only [memmove?] at h
  split at h
  · exact memmoveForward_entries_size_of_eq_some _ _ _ _ _ h
  · exact memmoveBackward_entries_size_of_eq_some _ _ _ _ _ h

theorem memmoveFrom_entries_size_of_eq_some
    (destination : SortSlice κ ν) (source : MemmoveSource destination)
    (updated : SortSlice κ ν) (dst src : Int) (count : Nat)
    (h : memmoveFrom? destination source dst src count = some updated) :
    updated.entries.size = destination.entries.size := by
  cases source with
  | sameBacking =>
      exact memmove_entries_size_of_eq_some destination updated dst src count h
  | distinctBacking source =>
      exact memcpyCore_entries_size_of_eq_some count destination source updated
        dst src h

/-- Pointer advancement becomes signed index arithmetic. -/
def advance (index amount : Int) : Int :=
  index + amount

private def overlapExample : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 1, value := some 10 },
        { key := 2, value := some 20 },
        { key := 3, value := some 30 },
        { key := 4, value := some 40 }] }

/-- Equal contents do not collapse explicit distinct-backing provenance. -/
example :
    memcpy? 4 overlapExample (.distinctBacking overlapExample) 0 0 =
      some overlapExample := by
  decide

/-- A positive exact self-copy overlaps and is therefore not a `memcpy`. -/
example : memcpy? 1 overlapExample .sameBacking 0 0 = none := by
  decide

/-- The rejection is range-based, not limited to the one-cell boundary. -/
example : memcpy? 2 overlapExample .sameBacking 1 1 = none := by
  decide

/-- Same-backing ranges may meet at the source-to-destination endpoint. -/
example :
    memcpy? 2 overlapExample .sameBacking 2 0 =
      some
        { entries :=
            #[{ key := 1, value := some 10 },
              { key := 2, value := some 20 },
              { key := 1, value := some 10 },
              { key := 2, value := some 20 }] } := by
  decide

/-- Same-backing ranges may also meet in the opposite order. -/
example :
    memcpy? 2 overlapExample .sameBacking 0 2 =
      some
        { entries :=
            #[{ key := 3, value := some 30 },
              { key := 4, value := some 40 },
              { key := 3, value := some 30 },
              { key := 4, value := some 40 }] } := by
  decide

/-- An empty copy admits equal one-past cursors on a shared backing. -/
example : memcpy? 0 overlapExample .sameBacking 4 4 = some overlapExample := by
  decide

/-- A rightward overlapping move retains the unread entries and their payloads. -/
example :
    overlapExample.memmove? 1 0 3 =
      some
        { entries :=
            #[{ key := 1, value := some 10 },
              { key := 1, value := some 10 },
              { key := 2, value := some 20 },
              { key := 3, value := some 30 }] } := by
  decide

/-- Equal contents do not turn explicit distinct provenance into aliasing. -/
example :
    memmoveFrom? overlapExample (.distinctBacking overlapExample) 0 0 4 =
      some overlapExample := by
  decide

/-- The general same-backing API retains backward-safe rightward overlap. -/
example :
    memmoveFrom? overlapExample .sameBacking 1 0 3 =
      some
        { entries :=
            #[{ key := 1, value := some 10 },
              { key := 1, value := some 10 },
              { key := 2, value := some 20 },
              { key := 3, value := some 30 }] } := by
  decide

end SortSlice

end CPythonListsort
