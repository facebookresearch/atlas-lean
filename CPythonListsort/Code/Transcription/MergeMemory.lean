/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Transcription.TempStorageInvariant

/-!
# Observable temporary-storage transitions

Allocator failure after a valid request is outside version one. `mergeFreemem`
records the pointer and ownership transition performed by CPython while leaving
the recorded capacity and all unrelated state untouched. `mergeGetmem` retains
the signed capacity-reuse comparison, the unsigned allocation-size guard, and
the fact that the old heap block is freed before that guard is checked.
-/

namespace CPythonListsort

/-! ## Same-store merge movement provenance -/

/-- The four block-movement sites whose source and destination are both in
`MergeState.data`.  They are deliberately separate from the six tagged
temp/main `memcpy` sites: these calls require overlap-safe `memmove` semantics. -/
inductive MergeMemmoveCallsite where
  | loGallopB
  | loCopyBTail
  | hiGallopA
  | hiCopyATail
  deriving DecidableEq, Repr

/-- Site-tagged same-store movement.  The tag carries review provenance only;
the evaluator is definitionally the existing overlap-safe primitive. -/
def mergeDataMemmove? (_site : MergeMemmoveCallsite)
    (data : SortSlice κ ν) (dst src : Int) (count : Nat) :
    Option (SortSlice κ ν) :=
  data.memmove? dst src count

/-- Every tagged same-store merge move is exactly `SortSlice.memmove?`; no
`memcpy`-class primitive or distinct-backing assumption is substituted. -/
@[simp]
theorem mergeDataMemmove_eq (site : MergeMemmoveCallsite)
    (data : SortSlice κ ν) (dst src : Int) (count : Nat) :
    mergeDataMemmove? site data dst src count = data.memmove? dst src count :=
  rfl

/-- The provenance tag does not change the main backing's extent. -/
@[aesop safe forward]
theorem mergeDataMemmove_entries_size_of_eq_some
    (site : MergeMemmoveCallsite) (data updated : SortSlice κ ν)
    (dst src : Int) (count : Nat)
    (h : mergeDataMemmove? site data dst src count = some updated) :
    updated.entries.size = data.entries.size :=
  SortSlice.memmove_entries_size_of_eq_some data updated dst src count h

/-- Transcription of `merge_freemem`. Inline storage is retained. Any
non-inline key storage is released and its allocated cells cease to be
accessible; `alloced` and `hasValues` are intentionally unchanged. -/
def mergeFreemem (state : MergeState κ ν) : MergeState κ ν :=
  if state.a.backing = .inline then
    state
  else
    { state with
      a := { state.a with cells := #[], backing := .released } }

@[simp]
theorem mergeFreemem_inline (state : MergeState κ ν)
    (h : state.a.backing = .inline) : mergeFreemem state = state := by
  simp [mergeFreemem, h]

@[simp]
theorem mergeFreemem_noninline (state : MergeState κ ν)
    (h : state.a.backing ≠ .inline) :
    (mergeFreemem state).a =
      { state.a with cells := #[], backing := .released } := by
  simp [mergeFreemem, h]

/-- Freeing temporary memory preserves the representation invariant. Inline
storage is unchanged; any non-inline storage enters the released clause, which
requires empty cells but deliberately permits stale `alloced`. -/
@[simp]
theorem mergeFreemem_tempStorageInv (state : MergeState κ ν)
    (hInv : TempStorageInv state.a state.alloced) :
    TempStorageInv (mergeFreemem state).a (mergeFreemem state).alloced := by
  unfold mergeFreemem
  split
  · simpa using hInv
  · simp [TempStorageInv]

/-! ## `merge_getmem` -/

/-- Observable control-flow outcome of `merge_getmem`. The `.grown` case is the
version-one successful-allocation abstraction. `.guardRejected` is not an
allocator failure: it is the deterministic `size_t` overflow guard from the C
source, which runs after `merge_freemem`. -/
inductive MergeGetmemOutcome where
  | reused
  | grown
  | guardRejected
  deriving DecidableEq, Repr

/-- C integer returned on each modeled path. Both successful paths return zero;
the deterministic allocation-size rejection returns minus one. -/
def MergeGetmemOutcome.returnCode : MergeGetmemOutcome → Int
  | .reused | .grown => 0
  | .guardRejected => -1

/-- State and return-path information produced by `merge_getmem`. -/
structure MergeGetmemResult (κ : Type u) (ν : Type v) where
  state : MergeState κ ν
  outcome : MergeGetmemOutcome

/-- Largest logical request whose one-or-two-slot heap allocation fits the
selected 64-bit `Py_ssize_t` allocation bound. -/
def mergeGetmemAllocationLimit (storage : TempStorage κ ν) : Nat :=
  PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES / storage.multiplier

/-- Transcription of `merge_getmem` under the version-one convention that a
guard-admitted `PyMem_Malloc` call succeeds. The reuse test is signed, as in C.
The allocation guard views `need` through the same-width unsigned `size_t`
cast, represented by `need.toNat`. Fresh heap cells are uninitialized and old
payload contents are deliberately discarded rather than copied. -/
def mergeGetmem (state : MergeState κ ν) (need : PySSize) :
    MergeGetmemResult κ ν :=
  if need.sle state.alloced then
    { state := state, outcome := .reused }
  else
    let allocationLimit := mergeGetmemAllocationLimit state.a
    let freed := mergeFreemem state
    if allocationLimit < need.toNat then
      { state := freed, outcome := .guardRejected }
    else
      { state :=
          { freed with
            a :=
              { cells := Array.replicate need.toNat none
                backing := .heap
                hasValues := freed.a.hasValues }
            alloced := need }
        outcome := .grown }

/-- Capacity reuse is exactly the C signed comparison and leaves every field
unchanged. In particular, this equation also applies to an artificially
released input with stale `alloced`; liveness is intentionally supplied by a
separate safety theorem rather than enforced by this transcription. -/
@[simp]
theorem mergeGetmem_reused (state : MergeState κ ν) (need : PySSize)
    (hReuse : need.sle state.alloced = true) :
    mergeGetmem state need = { state := state, outcome := .reused } := by
  simp [mergeGetmem, hReuse]

/-- An oversized request observes the post-`merge_freemem` state because the C
source frees old heap storage before checking the unsigned allocation bound. -/
@[simp]
theorem mergeGetmem_guardRejected (state : MergeState κ ν) (need : PySSize)
    (hReuse : need.sle state.alloced = false)
    (hGuard : mergeGetmemAllocationLimit state.a < need.toNat) :
    mergeGetmem state need =
      { state := mergeFreemem state, outcome := .guardRejected } := by
  simp [mergeGetmem, hReuse, hGuard]

/-- A guard-admitted growth request installs fresh live heap backing of exactly
`need.toNat` logical cells, keeps keyed/unkeyed mode, and records `need` as the
new capacity. -/
theorem mergeGetmem_grown (state : MergeState κ ν) (need : PySSize)
    (hReuse : need.sle state.alloced = false)
    (hGuard : need.toNat ≤ mergeGetmemAllocationLimit state.a) :
    let result := mergeGetmem state need
    result.outcome = .grown ∧
      result.state.alloced = need ∧
      result.state.a.backing = .heap ∧
      result.state.a.hasValues = state.a.hasValues ∧
      result.state.a.cells = Array.replicate need.toNat none := by
  by_cases hInline : state.a.backing = .inline <;>
    simp [mergeGetmem, hReuse, Nat.not_lt.mpr hGuard, mergeFreemem, hInline]

/-- Successful growth accounts for exactly one physical pointer slot per
unkeyed logical cell and two per keyed logical cell. -/
theorem mergeGetmem_grown_physicalSlots (state : MergeState κ ν)
    (need : PySSize) (hReuse : need.sle state.alloced = false)
    (hGuard : need.toNat ≤ mergeGetmemAllocationLimit state.a) :
    (mergeGetmem state need).state.a.physicalSlots =
      state.a.multiplier * need.toNat := by
  by_cases hInline : state.a.backing = .inline <;>
    by_cases hValues : state.a.hasValues = true <;>
      simp [mergeGetmem, hReuse, Nat.not_lt.mpr hGuard, mergeFreemem, hInline,
        TempStorage.physicalSlots, TempStorage.multiplier, hValues]

/-- Equality at the allocation limit is admitted, matching the strict `>` C
guard. -/
theorem mergeGetmem_atAllocationLimit (state : MergeState κ ν)
    (need : PySSize) (hReuse : need.sle state.alloced = false)
    (hLimit : need.toNat = mergeGetmemAllocationLimit state.a) :
    (mergeGetmem state need).outcome = .grown := by
  exact (mergeGetmem_grown state need hReuse (by omega)).1

/-- One logical cell beyond the allocation limit takes the rejecting path. -/
theorem mergeGetmem_onePastAllocationLimit (state : MergeState κ ν)
    (need : PySSize) (hReuse : need.sle state.alloced = false)
    (hLimit : need.toNat = mergeGetmemAllocationLimit state.a + 1) :
    (mergeGetmem state need).outcome = .guardRejected := by
  rw [mergeGetmem_guardRejected state need hReuse (by omega)]

/-- Keyed storage has the exact worst-case allocation limit `2^59 - 1` on the
selected 64-bit platform. If the boundary request reaches the allocation path,
it grows, while the next request also reaches that path and is rejected. -/
theorem mergeGetmem_keyed_boundary_regression (state : MergeState κ ν)
    (hValues : state.a.hasValues = true)
    (hGrowth : (((2 ^ 59 - 1 : Nat) : PySSize).sle state.alloced) = false) :
    mergeGetmemAllocationLimit state.a = 2 ^ 59 - 1 ∧
      (mergeGetmem state ((2 ^ 59 - 1 : Nat) : PySSize)).outcome = .grown ∧
      (mergeGetmem state ((2 ^ 59 : Nat) : PySSize)).outcome = .guardRejected := by
  have hRejectGrowth : (((2 ^ 59 : Nat) : PySSize).sle state.alloced) = false := by
    simp [BitVec.sle] at hGrowth ⊢
    omega
  have hLimit : mergeGetmemAllocationLimit state.a = 2 ^ 59 - 1 := by
    simp [mergeGetmemAllocationLimit, TempStorage.multiplier, hValues,
      PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES]
  refine ⟨hLimit, ?_, ?_⟩
  · apply mergeGetmem_atAllocationLimit state _ hGrowth
    simp [hLimit]
  · apply mergeGetmem_onePastAllocationLimit state _ hRejectGrowth
    simp [hLimit]

end CPythonListsort
