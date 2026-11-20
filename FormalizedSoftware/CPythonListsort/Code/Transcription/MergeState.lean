/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Transcription.Comparator
import Code.Transcription.Minrun
import Code.Transcription.SortSlice

/-!
# `MergeState` and pending runs

The C structure mixes pointers, signed machine words, an active prefix of a
fixed-size stack, and temporary storage whose slots may be uninitialized. The
model keeps those observable distinctions while replacing pointers by indices
into one shared `SortSlice` store.
-/

namespace CPythonListsort

universe u v

/-- CPython's initial threshold for entering galloping mode. -/
def MIN_GALLOP : PySSize := 7

/-- Number of pointer slots in CPython's inline merge-state buffer. -/
def MERGESTATE_TEMP_SIZE : Nat := 256

/-- One active pending run. `base` is an index into `MergeState.data`.
The newest run has no initialized power until `found_new_run` processes its
successor, which is represented by `none`. -/
structure PendingRun where
  base : Nat
  len : PySSize
  power : Option Nat
  deriving DecidableEq, Repr

/-- Whether the temporary key pointer denotes the inline array, heap storage,
or storage that has already been released. -/
inductive TempBacking where
  | inline
  | heap
  | released
  deriving DecidableEq, Repr

/-- The two logically distinct payload regions participating in merge bulk
copies.  `main` is `MergeState.data`; `temporary` is `MergeState.a`. -/
inductive MergeStorageRegion where
  | main
  | temporary
  deriving DecidableEq, Repr

/-- Source and destination backing regions for one memcpy-class merge move. -/
structure MergeMemcpyBackings where
  destination : MergeStorageRegion
  source : MergeStorageRegion
  deriving DecidableEq, Repr

/-- A memcpy-class merge move crosses backing regions rather than aliasing one
region at two potentially overlapping ranges. -/
def MergeMemcpyBackings.Distinct (backings : MergeMemcpyBackings) : Prop :=
  backings.destination ≠ backings.source

/-- Temporary merge storage. The outer `Option` represents an allocated slot
whose C contents have not yet been initialized; an entry's own optional value
represents the independent `a.values == NULL` choice. The raw structure admits
arbitrary field combinations; `TempStorageInv` in the adjacent support module
characterizes the representation states reachable from `merge_init`. -/
structure TempStorage (κ : Type u) (ν : Type v) where
  cells : Array (Option (SortSliceEntry κ ν))
  backing : TempBacking
  hasValues : Bool
  deriving DecidableEq, Repr

/-- Version-one transcription of the observable `MergeState` fields.
Comparator-specialization function pointers collapse to `key_compare`. -/
structure MergeState (κ : Type u) (ν : Type v) where
  min_gallop : PySSize
  listlen : PySSize
  basekeys : Nat
  data : SortSlice κ ν
  a : TempStorage κ ν
  alloced : PySSize
  pending : Array PendingRun
  key_compare : BoolComparator κ
  mr_current : PySSize
  mr_e : PySSize
  mr_mask : PySSize

/-- CPython's mutable `n` is represented by the length of the active pending
array, so it cannot disagree with the modeled stack. -/
def MergeState.n (state : MergeState κ ν) : Nat :=
  state.pending.size

/-- Project the adaptive-minrun fields to the dedicated transcription state. -/
def MergeState.minrunState (state : MergeState κ ν) : MinrunState :=
  { listlen := state.listlen
    mr_current := state.mr_current
    mr_e := state.mr_e
    mr_mask := state.mr_mask }

end CPythonListsort
