/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.SortSliceSafety
import Code.Transcription.ListSortImpl

/-!
# Valid top-level listsort inputs

The raw transcription keeps `hasKeyfunc` separate from its paired-entry input,
just as the C function keeps a nullable values pointer separate from the keys
pointer.  This module provides the public proof-carrying boundary: callers can
construct only inputs whose entries agree with that mode, while execution
still delegates unchanged to `listSortImpl?`.
-/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- A top-level input whose paired entries agree with the explicit key-function
mode passed to `listSortImpl?`. -/
structure ListSortInput (κ : Type u) (ν : Type v) where
  slice : SortSlice κ ν
  hasKeyfunc : Bool
  valuesMode : SortSlice.ValuesModeInvariant hasKeyfunc slice

namespace ListSortInput

/-- Build an unkeyed input with an explicitly selected (phantom) payload type.
Every entry has no separate payload, matching `values == NULL` in the C
representation. -/
def unkeyedAs (keys : Array κ) : ListSortInput κ ν where
  slice :=
    { entries := keys.map fun key =>
        { key := key
          value := none } }
  hasKeyfunc := false
  valuesMode := by
    intro index hindex
    simp [SortSlice.EntryMatchesValuesMode]

/-- Ergonomic unkeyed input constructor using `PUnit` for the payload type
that cannot occur when the values array is absent. -/
def unkeyed (keys : Array κ) : ListSortInput κ PUnit :=
  unkeyedAs keys

/-- Build a keyed input from `(key, value)` pairs.  Every entry receives a
payload, matching a non-null values pointer in the C representation. -/
def keyed (entries : Array (κ × ν)) : ListSortInput κ ν where
  slice :=
    { entries := entries.map fun entry =>
        { key := entry.1
          value := some entry.2 } }
  hasKeyfunc := true
  valuesMode := by
    intro index hindex
    simp [SortSlice.EntryMatchesValuesMode]

end ListSortInput

/-- Execute a validated top-level input through the unchanged raw
`listSortImpl?` transcription. -/
def listSort? (lt : BoolComparator κ) (reverse : Bool)
    (input : ListSortInput κ ν) : Option (ListSortImplResult κ ν) :=
  listSortImpl? lt reverse input.hasKeyfunc input.slice

@[simp]
theorem listSort_eq_listSortImpl (lt : BoolComparator κ)
    (reverse : Bool) (input : ListSortInput κ ν) :
    listSort? lt reverse input =
      listSortImpl? lt reverse input.hasKeyfunc input.slice := rfl

/-- `initialMergeState` transfers the validated input mode directly to the
main slice and the temporary-storage `hasValues` field. -/
theorem initialMergeState_valuesMode (lt : BoolComparator κ)
    (input : ListSortInput κ ν) :
    SortSlice.ValuesModeInvariant
      (initialMergeState lt input.hasKeyfunc input.slice).1.a.hasValues
      (initialMergeState lt input.hasKeyfunc input.slice).1.data := by
  simpa using input.valuesMode

end CPythonListsort
