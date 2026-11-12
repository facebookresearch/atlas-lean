/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Transcription.MergeMemory
import Mathlib

/-!
# `merge_getmem` storage validity

This module assembles the representation and liveness facts for the two
successful `merge_getmem` paths.  Reuse is safe only from live input storage:
the raw transcription intentionally admits a fabricated released state with a
stale `alloced`, but none of the theorems here do.  Growth uses the exact
allocation-limit premise supplied by the call-site request-bound theorem.
-/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- A live temporary-storage invariant accounts for every represented raw
pointer slot, regardless of whether the backing is inline or heap allocated. -/
theorem TempStorageInv.physicalSlots_eq
    {storage : TempStorage κ ν} {alloced : PySSize}
    (hInv : TempStorageInv storage alloced) (hLive : storage.Live) :
    storage.physicalSlots = storage.multiplier * alloced.toNat := by
  rw [TempStorage.physicalSlots, TempStorageInv.cells_size_eq hInv hLive]

/-- A nonnegative signed reuse request is no larger than the reused logical
capacity when viewed as a natural number.  The signed comparison itself forces
the larger word to be nonnegative as well. -/
private theorem toNat_le_of_sle_of_nonnegative
    {need capacity : PySSize} (hNeed : need.Nonnegative)
    (hReuse : need.sle capacity = true) :
    need.toNat ≤ capacity.toNat := by
  have hSigned : need.toInt ≤ capacity.toInt := by
    simpa [BitVec.sle] using hReuse
  have hCapacity : capacity.msb = false := by
    by_contra hNegative
    have hCapacityTrue : capacity.msb = true :=
      Bool.eq_true_of_not_eq_false hNegative
    have hNeedNonnegative := BitVec.toInt_nonneg_of_msb_false hNeed
    have hCapacityNegative := BitVec.toInt_neg_of_msb_true hCapacityTrue
    omega
  rw [BitVec.toInt_eq_toNat_of_msb hNeed,
    BitVec.toInt_eq_toNat_of_msb hCapacity] at hSigned
  exact_mod_cast hSigned

/-- The exact quotient guard bounds the number of physical pointer slots in a
fresh allocation.  `multiplier` is definitionally one or two. -/
private theorem physicalSlots_le_of_allocationLimit
    (storage : TempStorage κ ν) (need : PySSize)
    (hLimit : need.toNat ≤ mergeGetmemAllocationLimit storage) :
    storage.multiplier * need.toNat ≤
      PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES := by
  cases hValues : storage.hasValues <;>
    simp only [mergeGetmemAllocationLimit, TempStorage.multiplier, hValues,
      Bool.false_eq_true, ↓reduceIte] at hLimit ⊢
  · simpa using hLimit
  · have hMul :=
      (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mp hLimit
    simpa [Nat.mul_comm] using hMul

/-- Certificate for the state between `merge_freemem` and successful heap
allocation on the growth path.  Inline backing is retained unchanged; live
heap backing becomes released with no accessible payload.  In both cases the
representation invariant remains true even though the heap case is
temporarily not live. -/
structure MergeGetmemIntermediateFree
    (before freed : MergeState κ ν) : Prop where
  exactState : freed = mergeFreemem before
  invariant : TempStorageInv freed.a freed.alloced
  allocedPreserved : freed.alloced = before.alloced
  valuesModePreserved : freed.a.hasValues = before.a.hasValues
  backingTransition :
    (before.a.backing = .inline ∧
        freed = before ∧
        freed.a.backing = .inline) ∨
      (before.a.backing = .heap ∧
        freed.a.backing = .released ∧
        freed.a.cells = #[])

/-- `merge_freemem`'s preservation theorem supplies the representation fact
for the exact intermediate state used by the growth branch.  Liveness rules
out a fabricated already-released input, leaving precisely the inline-retain
and heap-release source cases. -/
theorem mergeGetmem_growth_intermediate_free
    (state : MergeState κ ν)
    (hInv : TempStorageInv state.a state.alloced)
    (hLive : state.a.Live) :
    MergeGetmemIntermediateFree state (mergeFreemem state) := by
  refine
    { exactState := rfl
      invariant := mergeFreemem_tempStorageInv state hInv
      allocedPreserved := ?_
      valuesModePreserved := ?_
      backingTransition := ?_ }
  · simp [mergeFreemem]
    split <;> rfl
  · simp only [mergeFreemem]
    split <;> rfl
  · cases hBacking : state.a.backing with
    | inline =>
        left
        simp [hBacking]
    | heap =>
        right
        simp [mergeFreemem, hBacking]
    | released =>
        exact (hLive hBacking).elim

/-- Every `MergeState` field that `merge_getmem` must frame.  Temporary
storage and its capacity are intentionally absent because growth replaces
exactly those two fields. -/
structure MergeGetmemNonStorageFrame (κ : Type u) (ν : Type v) where
  min_gallop : PySSize
  listlen : PySSize
  basekeys : Nat
  data : SortSlice κ ν
  pending : Array PendingRun
  key_compare : BoolComparator κ
  mr_current : PySSize
  mr_e : PySSize
  mr_mask : PySSize

/-- Project the non-storage frame preserved by `merge_getmem`. -/
def MergeState.mergeGetmemNonStorageFrame (state : MergeState κ ν) :
    MergeGetmemNonStorageFrame κ ν :=
  { min_gallop := state.min_gallop
    listlen := state.listlen
    basekeys := state.basekeys
    data := state.data
    pending := state.pending
    key_compare := state.key_compare
    mr_current := state.mr_current
    mr_e := state.mr_e
    mr_mask := state.mr_mask }

/-- Freeing storage changes no field in the exported non-storage frame. -/
@[simp]
theorem mergeFreemem_nonStorageFrame (state : MergeState κ ν) :
    (mergeFreemem state).mergeGetmemNonStorageFrame =
      state.mergeGetmemNonStorageFrame := by
  unfold mergeFreemem
  split <;> rfl

/-- Every `merge_getmem` outcome, including deterministic guard rejection,
preserves the complete non-storage frame. -/
@[simp]
theorem mergeGetmem_nonStorageFrame (state : MergeState κ ν)
    (need : PySSize) :
    (mergeGetmem state need).state.mergeGetmemNonStorageFrame =
      state.mergeGetmemNonStorageFrame := by
  unfold mergeGetmem
  split
  · rfl
  · dsimp only
    split
    · exact mergeFreemem_nonStorageFrame state
    · simpa only [MergeState.mergeGetmemNonStorageFrame] using
        mergeFreemem_nonStorageFrame state

/-- Facts shared by both successful `merge_getmem` paths.  In particular,
`requestFits` is a natural-number capacity fact suitable for array bounds; it
is not merely a repetition of the signed branch condition. -/
structure MergeGetmemStoragePost
    (before : MergeState κ ν) (need : PySSize)
    (result : MergeGetmemResult κ ν) : Prop where
  outcome : result.outcome = .reused ∨ result.outcome = .grown
  live : result.state.a.Live
  invariant : TempStorageInv result.state.a result.state.alloced
  valuesMode : result.state.a.hasValues = before.a.hasValues
  nonStorageFrame : result.state.mergeGetmemNonStorageFrame =
    before.mergeGetmemNonStorageFrame
  logicalCapacity : result.state.a.cells.size = result.state.alloced.toNat
  requestFits : need.toNat ≤ result.state.alloced.toNat
  physicalSlots : result.state.a.physicalSlots =
    result.state.a.multiplier * result.state.alloced.toNat
  /-- Reuse is exact state preservation, not merely preservation of selected
  storage facts. -/
  reuseAccounting : result.outcome = .reused → result.state = before
  /-- A growth result exports the exact, invariant-valid intermediate state
  after freeing and before installing its fresh heap allocation. -/
  growthIntermediateFree : result.outcome = .grown →
    MergeGetmemIntermediateFree before (mergeFreemem before)
  /-- On growth, the output uses exactly the old mode's multiplier times the
  requested logical capacity, and that raw slot count passes the byte guard. -/
  growthAccounting : result.outcome = .grown →
    result.state.alloced = need ∧
      result.state.a.backing = .heap ∧
      result.state.a.multiplier = before.a.multiplier ∧
      result.state.a.physicalSlots = before.a.multiplier * need.toNat ∧
      result.state.a.physicalSlots ≤
        PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES

namespace MergeGetmemStoragePost

variable {before : MergeState κ ν} {need : PySSize}
  {result : MergeGetmemResult κ ν}

/-- Direct downstream projection of the framed list length. -/
theorem listlen_eq (h : MergeGetmemStoragePost before need result) :
    result.state.listlen = before.listlen :=
  congrArg MergeGetmemNonStorageFrame.listlen h.nonStorageFrame

/-- Direct downstream projection of the framed main-list base. -/
theorem basekeys_eq (h : MergeGetmemStoragePost before need result) :
    result.state.basekeys = before.basekeys :=
  congrArg MergeGetmemNonStorageFrame.basekeys h.nonStorageFrame

/-- Direct downstream projection of the framed main data store. -/
theorem data_eq (h : MergeGetmemStoragePost before need result) :
    result.state.data = before.data :=
  congrArg MergeGetmemNonStorageFrame.data h.nonStorageFrame

/-- Direct downstream projection of the framed pending stack. -/
theorem pending_eq (h : MergeGetmemStoragePost before need result) :
    result.state.pending = before.pending :=
  congrArg MergeGetmemNonStorageFrame.pending h.nonStorageFrame

/-- Direct downstream projection of the framed galloping threshold. -/
theorem minGallop_eq (h : MergeGetmemStoragePost before need result) :
    result.state.min_gallop = before.min_gallop :=
  congrArg MergeGetmemNonStorageFrame.min_gallop h.nonStorageFrame

/-- Direct downstream projection of the framed comparator. -/
theorem keyCompare_eq (h : MergeGetmemStoragePost before need result) :
    result.state.key_compare = before.key_compare :=
  congrArg MergeGetmemNonStorageFrame.key_compare h.nonStorageFrame

/-- Direct downstream projection of all three framed adaptive-minrun fields. -/
theorem minrun_eq (h : MergeGetmemStoragePost before need result) :
    result.state.mr_current = before.mr_current ∧
      result.state.mr_e = before.mr_e ∧
      result.state.mr_mask = before.mr_mask :=
  ⟨congrArg MergeGetmemNonStorageFrame.mr_current h.nonStorageFrame,
    congrArg MergeGetmemNonStorageFrame.mr_e h.nonStorageFrame,
    congrArg MergeGetmemNonStorageFrame.mr_mask h.nonStorageFrame⟩

end MergeGetmemStoragePost

/-- The reuse branch leaves the entire state unchanged while preserving live,
invariant-valid storage with enough logical capacity for the request.  The
`Live` premise deliberately rules out stale-capacity reuse after release. -/
theorem mergeGetmem_reused_storage_valid
    (state : MergeState κ ν) (need : PySSize)
    (hInv : TempStorageInv state.a state.alloced)
    (hLive : state.a.Live) (hNeed : need.Nonnegative)
    (hReuse : need.sle state.alloced = true) :
    let result := mergeGetmem state need
    result.state = state ∧
      result.outcome = .reused ∧
      MergeGetmemStoragePost state need result := by
  rw [mergeGetmem_reused state need hReuse]
  refine ⟨rfl, rfl, ?_⟩
  refine
    { outcome := Or.inl rfl
      live := hLive
      invariant := hInv
      valuesMode := rfl
      nonStorageFrame := rfl
      logicalCapacity := TempStorageInv.cells_size_eq hInv hLive
      requestFits := toNat_le_of_sle_of_nonnegative hNeed hReuse
      physicalSlots := hInv.physicalSlots_eq hLive
      reuseAccounting := fun _ => rfl
      growthIntermediateFree := ?_
      growthAccounting := ?_ }
  · simp
  simp

/-- The growth branch installs fresh live heap backing of exactly
`need.toNat` logical cells.  Its physical allocation is exactly the old
keyed/unkeyed multiplier times that request and remains within the precise
pointer-count allocation limit. -/
theorem mergeGetmem_grown_storage_valid
    (state : MergeState κ ν) (need : PySSize)
    (hInv : TempStorageInv state.a state.alloced)
    (hLive : state.a.Live) (hNeed : need.Nonnegative)
    (hGrowth : need.sle state.alloced = false)
    (hLimit : need.toNat ≤ mergeGetmemAllocationLimit state.a) :
    let result := mergeGetmem state need
    result.outcome = .grown ∧
      result.state.alloced = need ∧
      result.state.a.backing = .heap ∧
      result.state.a.cells.size = need.toNat ∧
      result.state.a.physicalSlots = state.a.multiplier * need.toNat ∧
      result.state.a.physicalSlots ≤
        PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES ∧
      result.state.alloced.Nonnegative ∧
      MergeGetmemIntermediateFree state (mergeFreemem state) ∧
      MergeGetmemStoragePost state need result := by
  have hIntermediate := mergeGetmem_growth_intermediate_free state hInv hLive
  have hGrown := mergeGetmem_grown state need hGrowth hLimit
  have hPhysical := mergeGetmem_grown_physicalSlots state need hGrowth hLimit
  have hPhysicalBound := physicalSlots_le_of_allocationLimit state.a need hLimit
  rcases hGrown with
    ⟨hOutcome, hAlloced, hBacking, hValues, hCells⟩
  have hLiveResult : (mergeGetmem state need).state.a.Live := by
    simp [TempStorage.Live, hBacking]
  have hInvResult :
      TempStorageInv (mergeGetmem state need).state.a
        (mergeGetmem state need).state.alloced := by
    rw [hAlloced]
    simp [TempStorageInv, hBacking, hCells, hValues,
      TempStorage.physicalSlots, TempStorage.multiplier]
  have hLogical :
      (mergeGetmem state need).state.a.cells.size =
        (mergeGetmem state need).state.alloced.toNat := by
    rw [hCells, hAlloced]
    simp
  have hMultiplier :
      (mergeGetmem state need).state.a.multiplier = state.a.multiplier := by
    simp [TempStorage.multiplier, hValues]
  have hBound :
      (mergeGetmem state need).state.a.physicalSlots ≤
        PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES := by
    rw [hPhysical]
    exact hPhysicalBound
  refine
    ⟨hOutcome, hAlloced, hBacking, ?_, hPhysical, hBound, ?_, hIntermediate, ?_⟩
  · rw [hCells]
    simp
  · simpa only [hAlloced] using hNeed
  · refine
      { outcome := Or.inr hOutcome
        live := hLiveResult
        invariant := hInvResult
        valuesMode := hValues
        nonStorageFrame := mergeGetmem_nonStorageFrame state need
        logicalCapacity := hLogical
        requestFits := ?_
        physicalSlots := hInvResult.physicalSlots_eq hLiveResult
        reuseAccounting := ?_
        growthIntermediateFree := ?_
        growthAccounting := ?_ }
    · rw [hAlloced]
    · intro hReused
      simp [hOutcome] at hReused
    · intro _
      exact hIntermediate
    · intro _
      exact ⟨hAlloced, hBacking, hMultiplier, hPhysical, hBound⟩

/-- Public roadmap theorem: an admitted nonnegative request from live,
invariant-valid storage cannot take the guard-rejection path and returns live,
invariant-valid storage with enough logical capacity.  The growth certificate
also exposes exact multiplier and physical-allocation accounting. -/
theorem mergeGetmem_storage_valid
    (state : MergeState κ ν) (need : PySSize)
    (hInv : TempStorageInv state.a state.alloced)
    (hLive : state.a.Live) (hNeed : need.Nonnegative)
    (hLimit : need.sle state.alloced = false →
      need.toNat ≤ mergeGetmemAllocationLimit state.a) :
    MergeGetmemStoragePost state need (mergeGetmem state need) := by
  by_cases hReuse : need.sle state.alloced = true
  · exact (mergeGetmem_reused_storage_valid state need hInv hLive hNeed hReuse).2.2
  · have hGrowth : need.sle state.alloced = false := by
      cases hComparison : need.sle state.alloced
      · rfl
      · exact (hReuse hComparison).elim
    exact
      (mergeGetmem_grown_storage_valid state need hInv hLive hNeed hGrowth
        (hLimit hGrowth)).2.2.2.2.2.2.2.2

/-- Regression pinning the liveness boundary: storage explicitly marked
released cannot satisfy the public theorem's live-input premise, irrespective
of any stale `alloced` value that might make the raw reuse comparison true. -/
theorem releasedTempStorage_not_live (storage : TempStorage κ ν)
    (hReleased : storage.backing = .released) : ¬ storage.Live := by
  simp [TempStorage.Live, hReleased]

/-! ## Regression: why live input is essential -/

/-- A concrete impossible-at-a-merge-boundary state: `alloced` remains eight,
as it can after `merge_freemem`, while the payload is empty and released. -/
def fabricatedStaleReleasedMergeState : MergeState Unit Unit :=
  { min_gallop := MIN_GALLOP
    listlen := 0
    basekeys := 0
    data := { entries := #[] }
    a :=
      { cells := #[]
        backing := .released
        hasValues := false }
    alloced := 8
    pending := #[]
    key_compare := fun _ _ => false
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

/-- The raw transcription will reuse the stale capacity in the fabricated
released state: the representation invariant holds, the signed reuse test for
four cells succeeds, and the result remains released.  Only `TempStorage.Live`
separates this invalid merge-boundary state from the public safety theorem. -/
theorem fabricatedStaleReleasedMergeState_reuses :
    let state := fabricatedStaleReleasedMergeState
    let need : PySSize := 4
    TempStorageInv state.a state.alloced ∧
      ¬ state.a.Live ∧
      need.sle state.alloced = true ∧
      (mergeGetmem state need).outcome = .reused ∧
      (mergeGetmem state need).state = state ∧
      (mergeGetmem state need).state.a.backing = .released := by
  simp [fabricatedStaleReleasedMergeState, TempStorageInv, TempStorage.Live,
    mergeGetmem]

end CPythonListsort
