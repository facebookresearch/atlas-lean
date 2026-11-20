/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.MergeMemcpyProvenance

/-!
# Typed trace support for merge movement

The merge transcriptions keep the main list in `MergeState.data` and the
shorter run in `MergeState.a`.  `SortSlice`'s two-store movement API cannot be
used directly for that pair because temporary storage has a distinct carrier,
an explicit live/released backing state, and possibly-uninitialized cells.

This module supplies the common traced movement layer used by both merge
directions.  Every access goes through a state-derived wrapper from
`AccessTrace`; in particular, callers cannot manufacture the temporary backing
or either extent.  Bulk `memcpy` executors retain a classified call-site tag,
its exact direction, and its distinct-backing certificate at every recursive
call.  Key accesses for the complete range precede the optional synchronized-
values phase, which is selected solely by `state.a.hasValues`.
-/

namespace CPythonListsort

universe u v

open SortSlice

/-! ## Call-site provenance -/

/-- The closed union of the six classified merge `memcpy` sites. -/
inductive MergeMemcpySite where
  | lo (site : MergeLoMemcpyCallsite)
  | hi (site : MergeHiMemcpyCallsite)
  deriving DecidableEq, Repr

namespace MergeMemcpySite

/-- Physical source and destination regions of a classified site. -/
def backings : MergeMemcpySite → MergeMemcpyBackings
  | .lo site => site.backings
  | .hi site => site.backings

/-- The exported provenance theorem covers every site in the closed union. -/
theorem distinct (site : MergeMemcpySite) : site.backings.Distinct := by
  cases site with
  | lo site =>
      exact
        (mergeMemcpyCallsiteProvenance (κ := Unit) (ν := Unit))
          |>.mergeLoCallsitesDistinct site
  | hi site =>
      exact
        (mergeMemcpyCallsiteProvenance (κ := Unit) (ν := Unit))
          |>.mergeHiCallsitesDistinct site

/-- A classified main-to-temporary site, with provenance kept explicit. -/
structure MainToTempPermit (site : MergeMemcpySite) : Prop where
  direction : site.backings =
    { destination := .temporary, source := .main }
  distinctBacking : site.backings.Distinct

/-- A classified temporary-to-main site, with provenance kept explicit. -/
structure TempToMainPermit (site : MergeMemcpySite) : Prop where
  direction : site.backings =
    { destination := .main, source := .temporary }
  distinctBacking : site.backings.Distinct

end MergeMemcpySite

/-! ## Signed temporary ranges and backward cursors -/

/-- A signed index denotes an allocated logical temporary cell. -/
def TempIndexInBounds (storage : TempStorage κ ν) (index : Int) : Prop :=
  0 ≤ index ∧ index < Int.ofNat storage.cells.size

/-- The half-open signed range `[start, start + count)` lies in temporary
storage.  The empty range admits the one-past endpoint. -/
def TempRangeInBounds (storage : TempStorage κ ν) (start : Int)
    (count : Nat) : Prop :=
  0 ≤ start ∧ start + Int.ofNat count ≤ Int.ofNat storage.cells.size

/-- Backward merge cursors may be at a live cell or at the one-before-beginning
sentinel produced after copying cell zero.  A dereference still requires the
stronger `0 ≤ cursor` fact. -/
def BackwardCursorInRange (extent : Nat) (cursor : Int) : Prop :=
  -1 ≤ cursor ∧ cursor < Int.ofNat extent

namespace TempRangeInBounds

theorem head {storage : TempStorage κ ν} {start : Int} {count : Nat}
    (h : TempRangeInBounds storage start (count + 1)) :
    TempIndexInBounds storage start := by
  rcases h with ⟨hstart, hend⟩
  constructor
  · exact hstart
  · simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] at hend ⊢
    omega

theorem tail {storage : TempStorage κ ν} {start : Int} {count : Nat}
    (h : TempRangeInBounds storage start (count + 1)) :
    TempRangeInBounds storage (start + 1) count := by
  rcases h with ⟨hstart, hend⟩
  constructor
  · omega
  · simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] at hend ⊢
    omega

theorem of_size_eq {first second : TempStorage κ ν} {start : Int} {count : Nat}
    (h : TempRangeInBounds first start count)
    (hsize : second.cells.size = first.cells.size) :
    TempRangeInBounds second start count := by
  simpa [TempRangeInBounds, hsize] using h

end TempRangeInBounds

/-- Every cell in a temporary range is initialized. -/
def TempRangeInitialized (storage : TempStorage κ ν) (start : Int)
    (count : Nat) : Prop :=
  ∀ offset : Nat, offset < count →
    ∃ entry, (TraceResult.tempPayloadRead? storage
      (start + Int.ofNat offset)).erase = some entry

/-- Every initialized entry in a temporary range agrees with the explicit
values-pointer mode. -/
def TempRangeValuesMode (storage : TempStorage κ ν) (start : Int)
    (count : Nat) : Prop :=
  ∀ offset : Nat, offset < count →
    ∃ entry,
      (TraceResult.tempPayloadRead? storage
        (start + Int.ofNat offset)).erase = some entry ∧
      SortSlice.EntryMatchesValuesMode storage.hasValues entry

/-! ## Explicit untraced cores -/

/-- Untraced temporary read corresponding exactly to the typed wrapper. -/
def mergeTempRead? (storage : TempStorage κ ν) (index : Int) :
    Option (SortSliceEntry κ ν) :=
  if 0 ≤ index then storage.cells[index.toNat]?.bind id else none

/-- Untraced temporary write corresponding exactly to the typed wrapper. -/
def mergeTempWrite? (storage : TempStorage κ ν) (index : Int)
    (entry : SortSliceEntry κ ν) : Option (TempStorage κ ν) :=
  if 0 ≤ index ∧ index.toNat < storage.cells.size then
    some { storage with
      cells := storage.cells.setIfInBounds index.toNat (some entry) }
  else
    none

/-- One atomic main-to-temporary logical-cell copy. -/
def mainToTempCell? (state : MergeState κ ν) (tempDst mainSrc : Int) :
    Option (MergeState κ ν) := do
  let entry ← state.data.read? mainSrc
  let storage ← mergeTempWrite? state.a tempDst entry
  pure { state with a := storage }

/-- One atomic temporary-to-main logical-cell copy. -/
def tempToMainCell? (state : MergeState κ ν) (mainDst tempSrc : Int) :
    Option (MergeState κ ν) := do
  let entry ← mergeTempRead? state.a tempSrc
  let data ← state.data.write? mainDst entry
  pure { state with data := data }

/-- Forward distinct-backing main-to-temporary copy. -/
def mainToTempMemcpy? :
    Nat → MergeState κ ν → Int → Int → Option (MergeState κ ν)
  | 0, state, _, _ => some state
  | count + 1, state, tempDst, mainSrc => do
      let state ← mainToTempCell? state tempDst mainSrc
      mainToTempMemcpy? count state (tempDst + 1) (mainSrc + 1)

/-- Forward distinct-backing temporary-to-main copy. -/
def tempToMainMemcpy? :
    Nat → MergeState κ ν → Int → Int → Option (MergeState κ ν)
  | 0, state, _, _ => some state
  | count + 1, state, mainDst, tempSrc => do
      let state ← tempToMainCell? state mainDst tempSrc
      tempToMainMemcpy? count state (mainDst + 1) (tempSrc + 1)

/-- Main-data overlap-safe movement lifted back into `MergeState`. -/
def mainDataMemmove? (state : MergeState κ ν) (dst src : Int) (count : Nat) :
    Option (MergeState κ ν) := do
  let data ← state.data.memmove? dst src count
  pure { state with data := data }

/-! ## Typed one-cell phases -/

/-- Key phase of one main-to-temporary copy. -/
def mainToTempKeyTraced? (state : MergeState κ ν) (tempDst mainSrc : Int) :
    TraceResult (MergeState κ ν) :=
  (TraceResult.sortSliceKeysRead? state.data mainSrc).bind fun entry =>
    (TraceResult.tempPayloadWrite? state.a tempDst entry).map fun storage =>
      { state with a := storage }

/-- Optional synchronized-values phase of one main-to-temporary copy. -/
def mainToTempValuesTraced? (state : MergeState κ ν)
    (tempDst mainSrc : Int) : TraceResult (MergeState κ ν) :=
  (TraceResult.sortSliceValuesRead? state.data mainSrc).bind fun entry =>
    (TraceResult.tempPayloadWrite? state.a tempDst entry).map fun storage =>
      { state with a := storage }

/-- One source-language main-to-temporary copy.  The values phase starts from
the original paired state, as in `SortSlice.copyFromTraced?`, because either
physical phase represents the same atomic paired-entry update. -/
def mainToTempCellTraced? (state : MergeState κ ν) (tempDst mainSrc : Int) :
    TraceResult (MergeState κ ν) :=
  (mainToTempKeyTraced? state tempDst mainSrc).bind fun keyResult =>
    if state.a.hasValues then
      mainToTempValuesTraced? state tempDst mainSrc
    else
      TraceResult.pure keyResult

/-- Key phase of one temporary-to-main copy. -/
def tempToMainKeyTraced? (state : MergeState κ ν) (mainDst tempSrc : Int) :
    TraceResult (MergeState κ ν) :=
  (TraceResult.tempPayloadRead? state.a tempSrc).bind fun entry =>
    (TraceResult.sortSliceKeysWrite? state.data mainDst entry).map fun data =>
      { state with data := data }

/-- Optional synchronized-values phase of one temporary-to-main copy. -/
def tempToMainValuesTraced? (state : MergeState κ ν)
    (mainDst tempSrc : Int) : TraceResult (MergeState κ ν) :=
  (TraceResult.tempPayloadRead? state.a tempSrc).bind fun entry =>
    (TraceResult.sortSliceValuesWrite? state.data mainDst entry).map fun data =>
      { state with data := data }

/-- One source-language temporary-to-main copy. -/
def tempToMainCellTraced? (state : MergeState κ ν) (mainDst tempSrc : Int) :
    TraceResult (MergeState κ ν) :=
  (tempToMainKeyTraced? state mainDst tempSrc).bind fun keyResult =>
    if state.a.hasValues then
      tempToMainValuesTraced? state mainDst tempSrc
    else
      TraceResult.pure keyResult

/-! ## Recursively tagged bulk phases -/

/-- Complete key phase of main-to-temporary `memcpy`.  The site and both
proofs remain arguments of the recursive call. -/
def mainToTempKeysTraced? (site : MergeMemcpySite)
    (permit : site.MainToTempPermit) :
    Nat → MergeState κ ν → Int → Int → TraceResult (MergeState κ ν)
  | 0, state, _, _ => TraceResult.pure state
  | count + 1, state, tempDst, mainSrc =>
      (mainToTempKeyTraced? state tempDst mainSrc).bind fun state =>
        mainToTempKeysTraced? site permit count state
          (tempDst + 1) (mainSrc + 1)

/-- Complete optional-values phase of main-to-temporary `memcpy`. -/
def mainToTempValuesPhaseTraced? (site : MergeMemcpySite)
    (permit : site.MainToTempPermit) :
    Nat → MergeState κ ν → Int → Int → TraceResult (MergeState κ ν)
  | 0, state, _, _ => TraceResult.pure state
  | count + 1, state, tempDst, mainSrc =>
      (mainToTempValuesTraced? state tempDst mainSrc).bind fun state =>
        mainToTempValuesPhaseTraced? site permit count state
          (tempDst + 1) (mainSrc + 1)

/-- Tagged main-to-temporary `memcpy`, with all key events before all optional
values events. -/
def mainToTempMemcpyTraced? (site : MergeMemcpySite)
    (permit : site.MainToTempPermit) (count : Nat)
    (state : MergeState κ ν) (tempDst mainSrc : Int) :
    TraceResult (MergeState κ ν) :=
  (mainToTempKeysTraced? site permit count state tempDst mainSrc).bind
    fun keyResult =>
      if state.a.hasValues then
        mainToTempValuesPhaseTraced? site permit count state tempDst mainSrc
      else
        TraceResult.pure keyResult

/-- Complete key phase of temporary-to-main `memcpy`. -/
def tempToMainKeysTraced? (site : MergeMemcpySite)
    (permit : site.TempToMainPermit) :
    Nat → MergeState κ ν → Int → Int → TraceResult (MergeState κ ν)
  | 0, state, _, _ => TraceResult.pure state
  | count + 1, state, mainDst, tempSrc =>
      (tempToMainKeyTraced? state mainDst tempSrc).bind fun state =>
        tempToMainKeysTraced? site permit count state
          (mainDst + 1) (tempSrc + 1)

/-- Complete optional-values phase of temporary-to-main `memcpy`. -/
def tempToMainValuesPhaseTraced? (site : MergeMemcpySite)
    (permit : site.TempToMainPermit) :
    Nat → MergeState κ ν → Int → Int → TraceResult (MergeState κ ν)
  | 0, state, _, _ => TraceResult.pure state
  | count + 1, state, mainDst, tempSrc =>
      (tempToMainValuesTraced? state mainDst tempSrc).bind fun state =>
        tempToMainValuesPhaseTraced? site permit count state
          (mainDst + 1) (tempSrc + 1)

/-- Tagged temporary-to-main `memcpy`, with all key events before all optional
values events. -/
def tempToMainMemcpyTraced? (site : MergeMemcpySite)
    (permit : site.TempToMainPermit) (count : Nat)
    (state : MergeState κ ν) (mainDst tempSrc : Int) :
    TraceResult (MergeState κ ν) :=
  (tempToMainKeysTraced? site permit count state mainDst tempSrc).bind
    fun keyResult =>
      if state.a.hasValues then
        tempToMainValuesPhaseTraced? site permit count state mainDst tempSrc
      else
        TraceResult.pure keyResult

/-- Existing overlap-safe main-data movement, lifted through the state-derived
values mode. -/
def mainDataMemmoveTraced? (state : MergeState κ ν)
    (dst src : Int) (count : Nat) : TraceResult (MergeState κ ν) :=
  (SortSlice.memmoveTraced? state.a.hasValues state.data dst src count).map
    fun data => { state with data := data }

/-! ## Exact erasure -/

@[simp]
theorem erase_mergeTempRead (storage : TempStorage κ ν) (index : Int) :
    (TraceResult.tempPayloadRead? storage index).erase =
      mergeTempRead? storage index := by
  simp [mergeTempRead?]

@[simp]
theorem erase_mergeTempWrite (storage : TempStorage κ ν) (index : Int)
    (entry : SortSliceEntry κ ν) :
    (TraceResult.tempPayloadWrite? storage index entry).erase =
      mergeTempWrite? storage index entry := by
  simp [mergeTempWrite?]

@[simp]
theorem erase_mainToTempKeyTraced (state : MergeState κ ν)
    (tempDst mainSrc : Int) :
    (mainToTempKeyTraced? state tempDst mainSrc).erase =
      mainToTempCell? state tempDst mainSrc := by
  cases hread : state.data.read? mainSrc with
  | none => simp [mainToTempKeyTraced?, mainToTempCell?, hread]
  | some entry =>
      by_cases hbounds : 0 ≤ tempDst ∧ tempDst.toNat < state.a.cells.size <;>
        simp [mainToTempKeyTraced?, mainToTempCell?, mergeTempWrite?, hread,
          hbounds]

@[simp]
theorem erase_mainToTempValuesTraced (state : MergeState κ ν)
    (tempDst mainSrc : Int) :
    (mainToTempValuesTraced? state tempDst mainSrc).erase =
      mainToTempCell? state tempDst mainSrc := by
  cases hread : state.data.read? mainSrc with
  | none => simp [mainToTempValuesTraced?, mainToTempCell?, hread]
  | some entry =>
      by_cases hbounds : 0 ≤ tempDst ∧ tempDst.toNat < state.a.cells.size <;>
        simp [mainToTempValuesTraced?, mainToTempCell?, mergeTempWrite?, hread,
          hbounds]

@[simp]
theorem erase_mainToTempCellTraced (state : MergeState κ ν)
    (tempDst mainSrc : Int) :
    (mainToTempCellTraced? state tempDst mainSrc).erase =
      mainToTempCell? state tempDst mainSrc := by
  unfold mainToTempCellTraced?
  rw [TraceResult.erase_bind, erase_mainToTempKeyTraced]
  cases hcopy : mainToTempCell? state tempDst mainSrc <;>
    cases hmode : state.a.hasValues <;>
    simp [hcopy]

@[simp]
theorem erase_tempToMainKeyTraced (state : MergeState κ ν)
    (mainDst tempSrc : Int) :
    (tempToMainKeyTraced? state mainDst tempSrc).erase =
      tempToMainCell? state mainDst tempSrc := by
  unfold tempToMainKeyTraced? tempToMainCell?
  rw [TraceResult.erase_bind, erase_mergeTempRead]
  cases hread : mergeTempRead? state.a tempSrc with
  | none => simp
  | some entry =>
      cases hwrite : state.data.write? mainDst entry <;> simp [hwrite]

@[simp]
theorem erase_tempToMainValuesTraced (state : MergeState κ ν)
    (mainDst tempSrc : Int) :
    (tempToMainValuesTraced? state mainDst tempSrc).erase =
      tempToMainCell? state mainDst tempSrc := by
  unfold tempToMainValuesTraced? tempToMainCell?
  rw [TraceResult.erase_bind, erase_mergeTempRead]
  cases hread : mergeTempRead? state.a tempSrc with
  | none => simp
  | some entry =>
      cases hwrite : state.data.write? mainDst entry <;> simp [hwrite]

@[simp]
theorem erase_tempToMainCellTraced (state : MergeState κ ν)
    (mainDst tempSrc : Int) :
    (tempToMainCellTraced? state mainDst tempSrc).erase =
      tempToMainCell? state mainDst tempSrc := by
  unfold tempToMainCellTraced?
  rw [TraceResult.erase_bind, erase_tempToMainKeyTraced]
  cases hcopy : tempToMainCell? state mainDst tempSrc <;>
    cases hmode : state.a.hasValues <;>
    simp [hcopy]

@[simp]
theorem erase_mainToTempKeysTraced (site : MergeMemcpySite)
    (permit : site.MainToTempPermit) (count : Nat)
    (state : MergeState κ ν) (tempDst mainSrc : Int) :
    (mainToTempKeysTraced? site permit count state tempDst mainSrc).erase =
      mainToTempMemcpy? count state tempDst mainSrc := by
  induction count generalizing state tempDst mainSrc with
  | zero => rfl
  | succ count ih =>
      simp [mainToTempKeysTraced?, mainToTempMemcpy?, ih]

@[simp]
theorem erase_mainToTempValuesPhaseTraced (site : MergeMemcpySite)
    (permit : site.MainToTempPermit) (count : Nat)
    (state : MergeState κ ν) (tempDst mainSrc : Int) :
    (mainToTempValuesPhaseTraced? site permit count state tempDst mainSrc).erase =
      mainToTempMemcpy? count state tempDst mainSrc := by
  induction count generalizing state tempDst mainSrc with
  | zero => rfl
  | succ count ih =>
      simp [mainToTempValuesPhaseTraced?, mainToTempMemcpy?, ih]

@[simp]
theorem erase_mainToTempMemcpyTraced (site : MergeMemcpySite)
    (permit : site.MainToTempPermit) (count : Nat)
    (state : MergeState κ ν) (tempDst mainSrc : Int) :
    (mainToTempMemcpyTraced? site permit count state tempDst mainSrc).erase =
      mainToTempMemcpy? count state tempDst mainSrc := by
  unfold mainToTempMemcpyTraced?
  rw [TraceResult.erase_bind, erase_mainToTempKeysTraced]
  cases hcopy : mainToTempMemcpy? count state tempDst mainSrc <;>
    cases hmode : state.a.hasValues <;>
    simp [hcopy]

@[simp]
theorem erase_tempToMainKeysTraced (site : MergeMemcpySite)
    (permit : site.TempToMainPermit) (count : Nat)
    (state : MergeState κ ν) (mainDst tempSrc : Int) :
    (tempToMainKeysTraced? site permit count state mainDst tempSrc).erase =
      tempToMainMemcpy? count state mainDst tempSrc := by
  induction count generalizing state mainDst tempSrc with
  | zero => rfl
  | succ count ih =>
      simp [tempToMainKeysTraced?, tempToMainMemcpy?, ih]

@[simp]
theorem erase_tempToMainValuesPhaseTraced (site : MergeMemcpySite)
    (permit : site.TempToMainPermit) (count : Nat)
    (state : MergeState κ ν) (mainDst tempSrc : Int) :
    (tempToMainValuesPhaseTraced? site permit count state mainDst tempSrc).erase =
      tempToMainMemcpy? count state mainDst tempSrc := by
  induction count generalizing state mainDst tempSrc with
  | zero => rfl
  | succ count ih =>
      simp [tempToMainValuesPhaseTraced?, tempToMainMemcpy?, ih]

@[simp]
theorem erase_tempToMainMemcpyTraced (site : MergeMemcpySite)
    (permit : site.TempToMainPermit) (count : Nat)
    (state : MergeState κ ν) (mainDst tempSrc : Int) :
    (tempToMainMemcpyTraced? site permit count state mainDst tempSrc).erase =
      tempToMainMemcpy? count state mainDst tempSrc := by
  unfold tempToMainMemcpyTraced?
  rw [TraceResult.erase_bind, erase_tempToMainKeysTraced]
  cases hcopy : tempToMainMemcpy? count state mainDst tempSrc <;>
    cases hmode : state.a.hasValues <;>
    simp [hcopy]

@[simp]
theorem erase_mainDataMemmoveTraced (state : MergeState κ ν)
    (dst src : Int) (count : Nat) :
    (mainDataMemmoveTraced? state dst src count).erase =
      mainDataMemmove? state dst src count := by
  cases hmove : state.data.memmove? dst src count <;>
    simp [mainDataMemmoveTraced?, mainDataMemmove?, hmove]

/-! ## Structural frame -/

/-- Fields and extents unchanged by every movement primitive in this module.
The main contents and temporary contents are intentionally absent. -/
structure MergeMovementFrame (before after : MergeState κ ν) : Prop where
  minGallop : after.min_gallop = before.min_gallop
  listlen : after.listlen = before.listlen
  basekeys : after.basekeys = before.basekeys
  dataSize : after.data.entries.size = before.data.entries.size
  tempSize : after.a.cells.size = before.a.cells.size
  tempBacking : after.a.backing = before.a.backing
  tempValuesMode : after.a.hasValues = before.a.hasValues
  alloced : after.alloced = before.alloced
  pending : after.pending = before.pending
  comparator : after.key_compare = before.key_compare
  mrCurrent : after.mr_current = before.mr_current
  mrE : after.mr_e = before.mr_e
  mrMask : after.mr_mask = before.mr_mask

namespace MergeMovementFrame

theorem refl (state : MergeState κ ν) : MergeMovementFrame state state := by
  constructor <;> rfl

theorem trans {first second third : MergeState κ ν}
    (h₁ : MergeMovementFrame first second)
    (h₂ : MergeMovementFrame second third) :
    MergeMovementFrame first third := by
  constructor
  · exact h₂.minGallop.trans h₁.minGallop
  · exact h₂.listlen.trans h₁.listlen
  · exact h₂.basekeys.trans h₁.basekeys
  · exact h₂.dataSize.trans h₁.dataSize
  · exact h₂.tempSize.trans h₁.tempSize
  · exact h₂.tempBacking.trans h₁.tempBacking
  · exact h₂.tempValuesMode.trans h₁.tempValuesMode
  · exact h₂.alloced.trans h₁.alloced
  · exact h₂.pending.trans h₁.pending
  · exact h₂.comparator.trans h₁.comparator
  · exact h₂.mrCurrent.trans h₁.mrCurrent
  · exact h₂.mrE.trans h₁.mrE
  · exact h₂.mrMask.trans h₁.mrMask

/-- Shape-only temporary storage validity transports across movement. -/
theorem tempStorageInv {before after : MergeState κ ν}
    (hframe : MergeMovementFrame before after)
    (hinvariant : TempStorageInv before.a before.alloced) :
    TempStorageInv after.a after.alloced := by
  cases hbefore : before.a.backing with
  | inline =>
      have hafter : after.a.backing = .inline :=
        hframe.tempBacking.trans hbefore
      simp only [TempStorageInv, hbefore] at hinvariant
      simp only [TempStorageInv, hafter]
      simpa [TempStorage.multiplier, hframe.tempSize,
        hframe.tempValuesMode, hframe.alloced] using hinvariant
  | heap =>
      have hafter : after.a.backing = .heap :=
        hframe.tempBacking.trans hbefore
      simp only [TempStorageInv, hbefore] at hinvariant
      simp only [TempStorageInv, hafter]
      simpa [TempStorage.physicalSlots, TempStorage.multiplier,
        hframe.tempSize, hframe.tempValuesMode, hframe.alloced] using hinvariant
  | released =>
      have hafter : after.a.backing = .released :=
        hframe.tempBacking.trans hbefore
      simp only [TempStorageInv, hbefore, Array.isEmpty_iff] at hinvariant
      simp only [TempStorageInv, hafter, Array.isEmpty_iff]
      apply Array.size_eq_zero_iff.mp
      calc
        after.a.cells.size = before.a.cells.size := hframe.tempSize
        _ = 0 := by simpa using congrArg Array.size hinvariant

/-- Live backing transports because movement never changes the backing tag. -/
theorem live {before after : MergeState κ ν}
    (hframe : MergeMovementFrame before after) (hlive : before.a.Live) :
    after.a.Live := by
  simpa [TempStorage.Live, hframe.tempBacking] using hlive

end MergeMovementFrame

private theorem mainToTempCell_frame
    (state result : MergeState κ ν) (tempDst mainSrc : Int)
    (hresult : mainToTempCell? state tempDst mainSrc = some result) :
    MergeMovementFrame state result := by
  rcases Option.bind_eq_some_iff.mp hresult with ⟨entry, hread, htail⟩
  rcases Option.bind_eq_some_iff.mp htail with ⟨storage, hwrite, hfinal⟩
  change some { state with a := storage } = some result at hfinal
  injection hfinal with hfinal
  subst result
  have hsize : storage.cells.size = state.a.cells.size := by
    unfold mergeTempWrite? at hwrite
    split at hwrite <;> try contradiction
    injection hwrite with hwrite
    subst storage
    simp
  have hbacking : storage.backing = state.a.backing := by
    unfold mergeTempWrite? at hwrite
    split at hwrite <;> try contradiction
    injection hwrite with hwrite
    subst storage
    rfl
  have hvalues : storage.hasValues = state.a.hasValues := by
    unfold mergeTempWrite? at hwrite
    split at hwrite <;> try contradiction
    injection hwrite with hwrite
    subst storage
    rfl
  constructor <;> simp [hsize, hbacking, hvalues]

private theorem tempToMainCell_frame
    (state result : MergeState κ ν) (mainDst tempSrc : Int)
    (hresult : tempToMainCell? state mainDst tempSrc = some result) :
    MergeMovementFrame state result := by
  rcases Option.bind_eq_some_iff.mp hresult with ⟨entry, hread, htail⟩
  rcases Option.bind_eq_some_iff.mp htail with ⟨data, hwrite, hfinal⟩
  change some { state with data := data } = some result at hfinal
  injection hfinal with hfinal
  subst result
  constructor <;> try rfl
  exact SortSlice.write_entries_size_of_eq_some _ _ _ _ hwrite

theorem mainToTempMemcpy_frame (count : Nat) (state result : MergeState κ ν)
    (tempDst mainSrc : Int)
    (hresult : mainToTempMemcpy? count state tempDst mainSrc = some result) :
    MergeMovementFrame state result := by
  induction count generalizing state tempDst mainSrc with
  | zero =>
      simp only [mainToTempMemcpy?, Option.some.injEq] at hresult
      subst result
      exact .refl state
  | succ count ih =>
      simp only [mainToTempMemcpy?, bind, Option.bind] at hresult
      split at hresult <;> try contradiction
      rename_i next hcell
      exact (mainToTempCell_frame state next tempDst mainSrc hcell).trans
        (ih next (tempDst + 1) (mainSrc + 1) hresult)

theorem tempToMainMemcpy_frame (count : Nat) (state result : MergeState κ ν)
    (mainDst tempSrc : Int)
    (hresult : tempToMainMemcpy? count state mainDst tempSrc = some result) :
    MergeMovementFrame state result := by
  induction count generalizing state mainDst tempSrc with
  | zero =>
      simp only [tempToMainMemcpy?, Option.some.injEq] at hresult
      subst result
      exact .refl state
  | succ count ih =>
      simp only [tempToMainMemcpy?, bind, Option.bind] at hresult
      split at hresult <;> try contradiction
      rename_i next hcell
      exact (tempToMainCell_frame state next mainDst tempSrc hcell).trans
        (ih next (mainDst + 1) (tempSrc + 1) hresult)

theorem mainDataMemmove_frame (state result : MergeState κ ν)
    (dst src : Int) (count : Nat)
    (hresult : mainDataMemmove? state dst src count = some result) :
    MergeMovementFrame state result := by
  rcases Option.bind_eq_some_iff.mp hresult with ⟨data, hmove, hfinal⟩
  change some { state with data := data } = some result at hfinal
  injection hfinal with hfinal
  subst result
  constructor <;> try rfl
  exact SortSlice.memmove_entries_size_of_eq_some _ _ _ _ _ hmove

theorem mainToTempMemcpyTraced_frame (site : MergeMemcpySite)
    (permit : site.MainToTempPermit) (count : Nat)
    (state result : MergeState κ ν) (tempDst mainSrc : Int)
    (hresult :
      (mainToTempMemcpyTraced? site permit count state tempDst mainSrc).result =
        some result) :
    MergeMovementFrame state result := by
  apply mainToTempMemcpy_frame count state result tempDst mainSrc
  rw [← erase_mainToTempMemcpyTraced site permit count state tempDst mainSrc]
  exact hresult

theorem tempToMainMemcpyTraced_frame (site : MergeMemcpySite)
    (permit : site.TempToMainPermit) (count : Nat)
    (state result : MergeState κ ν) (mainDst tempSrc : Int)
    (hresult :
      (tempToMainMemcpyTraced? site permit count state mainDst tempSrc).result =
        some result) :
    MergeMovementFrame state result := by
  apply tempToMainMemcpy_frame count state result mainDst tempSrc
  rw [← erase_tempToMainMemcpyTraced site permit count state mainDst tempSrc]
  exact hresult

theorem mainDataMemmoveTraced_frame (state result : MergeState κ ν)
    (dst src : Int) (count : Nat)
    (hresult : (mainDataMemmoveTraced? state dst src count).result = some result) :
    MergeMovementFrame state result := by
  apply mainDataMemmove_frame state result dst src count
  rw [← erase_mainDataMemmoveTraced state dst src count]
  exact hresult

/-! ## Absence of control-flow events -/

/-- A local movement trace contains neither a fuel marker nor pending pushes. -/
def MovementAccessOnly (execution : TraceResult α) : Prop :=
  execution.trace.fuelExhausted = false ∧ execution.trace.pushDepths = []

namespace MovementAccessOnly

theorem pure (value : α) : MovementAccessOnly (TraceResult.pure value) := by
  simp [MovementAccessOnly, TraceResult.pure, AccessTrace.empty]

theorem map (current : TraceResult α) (transform : α → β)
    (h : MovementAccessOnly current) :
    MovementAccessOnly (current.map transform) := by
  exact h

theorem bind (current : TraceResult α) (next : α → TraceResult β)
    (hcurrent : MovementAccessOnly current)
    (hnext : ∀ value, MovementAccessOnly (next value)) :
    MovementAccessOnly (current.bind next) := by
  rcases hcurrent with ⟨hcurrentFuel, hcurrentPush⟩
  cases hresult : current.result with
  | none =>
      simpa [MovementAccessOnly, TraceResult.trace_bind, hresult] using
        And.intro hcurrentFuel hcurrentPush
  | some value =>
      rcases hnext value with ⟨hnextFuel, hnextPush⟩
      simp [MovementAccessOnly, TraceResult.trace_bind, hresult,
        AccessTrace.compose, hcurrentFuel, hcurrentPush, hnextFuel, hnextPush]

end MovementAccessOnly

private theorem tempRead_accessOnly (storage : TempStorage κ ν) (index : Int) :
    MovementAccessOnly (TraceResult.tempPayloadRead? storage index) := by
  simp [MovementAccessOnly, TraceResult.trace_tempPayloadRead,
    AccessTrace.singletonAccess]

private theorem tempWrite_accessOnly (storage : TempStorage κ ν) (index : Int)
    (entry : SortSliceEntry κ ν) :
    MovementAccessOnly (TraceResult.tempPayloadWrite? storage index entry) := by
  simp [MovementAccessOnly, TraceResult.trace_tempPayloadWrite,
    AccessTrace.singletonAccess]

private theorem keyRead_accessOnly (slice : SortSlice κ ν) (index : Int) :
    MovementAccessOnly (TraceResult.sortSliceKeysRead? slice index) := by
  simp [MovementAccessOnly, TraceResult.trace_sortSliceKeysRead,
    AccessTrace.singletonAccess]

private theorem valuesRead_accessOnly (slice : SortSlice κ ν) (index : Int) :
    MovementAccessOnly (TraceResult.sortSliceValuesRead? slice index) := by
  simp [MovementAccessOnly, TraceResult.trace_sortSliceValuesRead,
    AccessTrace.singletonAccess]

private theorem keyWrite_accessOnly (slice : SortSlice κ ν) (index : Int)
    (entry : SortSliceEntry κ ν) :
    MovementAccessOnly (TraceResult.sortSliceKeysWrite? slice index entry) := by
  simp [MovementAccessOnly, TraceResult.trace_sortSliceKeysWrite,
    AccessTrace.singletonAccess]

private theorem valuesWrite_accessOnly (slice : SortSlice κ ν) (index : Int)
    (entry : SortSliceEntry κ ν) :
    MovementAccessOnly (TraceResult.sortSliceValuesWrite? slice index entry) := by
  simp [MovementAccessOnly, TraceResult.trace_sortSliceValuesWrite,
    AccessTrace.singletonAccess]

theorem mainToTempCellTraced_accessOnly (state : MergeState κ ν)
    (tempDst mainSrc : Int) :
    MovementAccessOnly (mainToTempCellTraced? state tempDst mainSrc) := by
  apply MovementAccessOnly.bind
  · apply MovementAccessOnly.bind
    · exact keyRead_accessOnly state.data mainSrc
    · intro entry
      exact MovementAccessOnly.map _ _ (tempWrite_accessOnly state.a tempDst entry)
  · intro keyResult
    cases hmode : state.a.hasValues with
    | false => simp [MovementAccessOnly.pure]
    | true =>
        simp only [↓reduceIte]
        apply MovementAccessOnly.bind
        · exact valuesRead_accessOnly state.data mainSrc
        · intro entry
          exact MovementAccessOnly.map _ _
            (tempWrite_accessOnly state.a tempDst entry)

theorem tempToMainCellTraced_accessOnly (state : MergeState κ ν)
    (mainDst tempSrc : Int) :
    MovementAccessOnly (tempToMainCellTraced? state mainDst tempSrc) := by
  apply MovementAccessOnly.bind
  · apply MovementAccessOnly.bind
    · exact tempRead_accessOnly state.a tempSrc
    · intro entry
      exact MovementAccessOnly.map _ _
        (keyWrite_accessOnly state.data mainDst entry)
  · intro keyResult
    cases hmode : state.a.hasValues with
    | false => simp [MovementAccessOnly.pure]
    | true =>
        simp only [↓reduceIte]
        apply MovementAccessOnly.bind
        · exact tempRead_accessOnly state.a tempSrc
        · intro entry
          exact MovementAccessOnly.map _ _
            (valuesWrite_accessOnly state.data mainDst entry)

private theorem mainToTempKeysTraced_accessOnly (site : MergeMemcpySite)
    (permit : site.MainToTempPermit) (count : Nat)
    (state : MergeState κ ν) (tempDst mainSrc : Int) :
    MovementAccessOnly
      (mainToTempKeysTraced? site permit count state tempDst mainSrc) := by
  induction count generalizing state tempDst mainSrc with
  | zero => exact MovementAccessOnly.pure state
  | succ count ih =>
      apply MovementAccessOnly.bind
      · apply MovementAccessOnly.bind
        · exact keyRead_accessOnly state.data mainSrc
        · intro entry
          exact MovementAccessOnly.map _ _
            (tempWrite_accessOnly state.a tempDst entry)
      · intro next
        exact ih next (tempDst + 1) (mainSrc + 1)

private theorem mainToTempValuesPhaseTraced_accessOnly (site : MergeMemcpySite)
    (permit : site.MainToTempPermit) (count : Nat)
    (state : MergeState κ ν) (tempDst mainSrc : Int) :
    MovementAccessOnly
      (mainToTempValuesPhaseTraced? site permit count state tempDst mainSrc) := by
  induction count generalizing state tempDst mainSrc with
  | zero => exact MovementAccessOnly.pure state
  | succ count ih =>
      apply MovementAccessOnly.bind
      · apply MovementAccessOnly.bind
        · exact valuesRead_accessOnly state.data mainSrc
        · intro entry
          exact MovementAccessOnly.map _ _
            (tempWrite_accessOnly state.a tempDst entry)
      · intro next
        exact ih next (tempDst + 1) (mainSrc + 1)

theorem mainToTempMemcpyTraced_accessOnly (site : MergeMemcpySite)
    (permit : site.MainToTempPermit) (count : Nat)
    (state : MergeState κ ν) (tempDst mainSrc : Int) :
    MovementAccessOnly
      (mainToTempMemcpyTraced? site permit count state tempDst mainSrc) := by
  apply MovementAccessOnly.bind
  · exact mainToTempKeysTraced_accessOnly site permit count state tempDst mainSrc
  · intro keyResult
    cases hmode : state.a.hasValues with
    | false => simp [MovementAccessOnly.pure]
    | true =>
        simpa [hmode] using
          mainToTempValuesPhaseTraced_accessOnly site permit count state
            tempDst mainSrc

private theorem tempToMainKeysTraced_accessOnly (site : MergeMemcpySite)
    (permit : site.TempToMainPermit) (count : Nat)
    (state : MergeState κ ν) (mainDst tempSrc : Int) :
    MovementAccessOnly
      (tempToMainKeysTraced? site permit count state mainDst tempSrc) := by
  induction count generalizing state mainDst tempSrc with
  | zero => exact MovementAccessOnly.pure state
  | succ count ih =>
      apply MovementAccessOnly.bind
      · apply MovementAccessOnly.bind
        · exact tempRead_accessOnly state.a tempSrc
        · intro entry
          exact MovementAccessOnly.map _ _
            (keyWrite_accessOnly state.data mainDst entry)
      · intro next
        exact ih next (mainDst + 1) (tempSrc + 1)

private theorem tempToMainValuesPhaseTraced_accessOnly (site : MergeMemcpySite)
    (permit : site.TempToMainPermit) (count : Nat)
    (state : MergeState κ ν) (mainDst tempSrc : Int) :
    MovementAccessOnly
      (tempToMainValuesPhaseTraced? site permit count state mainDst tempSrc) := by
  induction count generalizing state mainDst tempSrc with
  | zero => exact MovementAccessOnly.pure state
  | succ count ih =>
      apply MovementAccessOnly.bind
      · apply MovementAccessOnly.bind
        · exact tempRead_accessOnly state.a tempSrc
        · intro entry
          exact MovementAccessOnly.map _ _
            (valuesWrite_accessOnly state.data mainDst entry)
      · intro next
        exact ih next (mainDst + 1) (tempSrc + 1)

theorem tempToMainMemcpyTraced_accessOnly (site : MergeMemcpySite)
    (permit : site.TempToMainPermit) (count : Nat)
    (state : MergeState κ ν) (mainDst tempSrc : Int) :
    MovementAccessOnly
      (tempToMainMemcpyTraced? site permit count state mainDst tempSrc) := by
  apply MovementAccessOnly.bind
  · exact tempToMainKeysTraced_accessOnly site permit count state mainDst tempSrc
  · intro keyResult
    cases hmode : state.a.hasValues with
    | false => simp [MovementAccessOnly.pure]
    | true =>
        simpa [hmode] using
          tempToMainValuesPhaseTraced_accessOnly site permit count state
            mainDst tempSrc

private theorem copyKeysFrom_accessOnly (destination source : SortSlice κ ν)
    (dst src : Int) :
    MovementAccessOnly
      (SortSlice.copyKeysFromTraced? destination source dst src) := by
  apply MovementAccessOnly.bind
  · exact keyRead_accessOnly source src
  · intro entry
    exact keyWrite_accessOnly destination dst entry

private theorem copyValuesFrom_accessOnly (destination source : SortSlice κ ν)
    (dst src : Int) :
    MovementAccessOnly
      (SortSlice.copyValuesFromTraced? destination source dst src) := by
  apply MovementAccessOnly.bind
  · exact valuesRead_accessOnly source src
  · intro entry
    exact valuesWrite_accessOnly destination dst entry

private theorem memmoveForwardKeys_accessOnly (count : Nat)
    (slice : SortSlice κ ν) (dst src : Int) :
    MovementAccessOnly
      (SortSlice.memmoveForwardKeysTraced? count slice dst src) := by
  induction count generalizing slice dst src with
  | zero => exact MovementAccessOnly.pure slice
  | succ count ih =>
      apply MovementAccessOnly.bind
      · exact copyKeysFrom_accessOnly slice slice dst src
      · intro updated
        exact ih updated (dst + 1) (src + 1)

private theorem memmoveForwardValues_accessOnly (count : Nat)
    (slice : SortSlice κ ν) (dst src : Int) :
    MovementAccessOnly
      (SortSlice.memmoveForwardValuesTraced? count slice dst src) := by
  induction count generalizing slice dst src with
  | zero => exact MovementAccessOnly.pure slice
  | succ count ih =>
      apply MovementAccessOnly.bind
      · exact copyValuesFrom_accessOnly slice slice dst src
      · intro updated
        exact ih updated (dst + 1) (src + 1)

private theorem memmoveBackwardKeys_accessOnly (count : Nat)
    (slice : SortSlice κ ν) (dst src : Int) :
    MovementAccessOnly
      (SortSlice.memmoveBackwardKeysTraced? count slice dst src) := by
  induction count generalizing slice dst src with
  | zero => exact MovementAccessOnly.pure slice
  | succ count ih =>
      apply MovementAccessOnly.bind
      · exact copyKeysFrom_accessOnly slice slice
          (dst + Int.ofNat count) (src + Int.ofNat count)
      · intro updated
        exact ih updated dst src

private theorem memmoveBackwardValues_accessOnly (count : Nat)
    (slice : SortSlice κ ν) (dst src : Int) :
    MovementAccessOnly
      (SortSlice.memmoveBackwardValuesTraced? count slice dst src) := by
  induction count generalizing slice dst src with
  | zero => exact MovementAccessOnly.pure slice
  | succ count ih =>
      apply MovementAccessOnly.bind
      · exact copyValuesFrom_accessOnly slice slice
          (dst + Int.ofNat count) (src + Int.ofNat count)
      · intro updated
        exact ih updated dst src

private theorem sortSliceMemmove_accessOnly (valuesPresent : Bool)
    (slice : SortSlice κ ν) (dst src : Int) (count : Nat) :
    MovementAccessOnly
      (SortSlice.memmoveTraced? valuesPresent slice dst src count) := by
  cases hdirection : SortSlice.memmoveDirection dst src with
  | forward =>
      simp only [SortSlice.memmoveTraced?, hdirection]
      apply MovementAccessOnly.bind
      · exact memmoveForwardKeys_accessOnly count slice dst src
      · intro keyResult
        cases hvalues : valuesPresent with
        | false => simp [MovementAccessOnly.pure]
        | true =>
            simpa [hvalues] using
              memmoveForwardValues_accessOnly count slice dst src
  | backward =>
      simp only [SortSlice.memmoveTraced?, hdirection]
      apply MovementAccessOnly.bind
      · exact memmoveBackwardKeys_accessOnly count slice dst src
      · intro keyResult
        cases hvalues : valuesPresent with
        | false => simp [MovementAccessOnly.pure]
        | true =>
            simpa [hvalues] using
              memmoveBackwardValues_accessOnly count slice dst src

theorem mainDataMemmoveTraced_accessOnly (state : MergeState κ ν)
    (dst src : Int) (count : Nat) :
    MovementAccessOnly (mainDataMemmoveTraced? state dst src count) := by
  exact MovementAccessOnly.map _ _
    (sortSliceMemmove_accessOnly state.a.hasValues state.data dst src count)

/-! ## Temporary initialization and write frames -/

theorem mergeTempWrite_eq_some_of_bounds (storage : TempStorage κ ν)
    (index : Int) (entry : SortSliceEntry κ ν)
    (hindex : TempIndexInBounds storage index) :
    ∃ updated, mergeTempWrite? storage index entry = some updated := by
  have hnat : index.toNat < storage.cells.size :=
    (Int.toNat_lt hindex.1).2 hindex.2
  refine ⟨{ storage with
    cells := storage.cells.setIfInBounds index.toNat (some entry) }, ?_⟩
  simp [mergeTempWrite?, hindex.1, hnat]

theorem mergeTempWrite_size_of_eq_some (storage updated : TempStorage κ ν)
    (index : Int) (entry : SortSliceEntry κ ν)
    (hwrite : mergeTempWrite? storage index entry = some updated) :
    updated.cells.size = storage.cells.size := by
  unfold mergeTempWrite? at hwrite
  split at hwrite <;> try contradiction
  injection hwrite with hwrite
  subst updated
  simp

theorem mergeTempWrite_backing_of_eq_some (storage updated : TempStorage κ ν)
    (index : Int) (entry : SortSliceEntry κ ν)
    (hwrite : mergeTempWrite? storage index entry = some updated) :
    updated.backing = storage.backing := by
  unfold mergeTempWrite? at hwrite
  split at hwrite <;> try contradiction
  injection hwrite with hwrite
  subst updated
  rfl

theorem mergeTempWrite_valuesMode_of_eq_some
    (storage updated : TempStorage κ ν) (index : Int)
    (entry : SortSliceEntry κ ν)
    (hwrite : mergeTempWrite? storage index entry = some updated) :
    updated.hasValues = storage.hasValues := by
  unfold mergeTempWrite? at hwrite
  split at hwrite <;> try contradiction
  injection hwrite with hwrite
  subst updated
  rfl

theorem mergeTempWrite_read_self_of_eq_some
    (storage updated : TempStorage κ ν) (index : Int)
    (entry : SortSliceEntry κ ν)
    (hwrite : mergeTempWrite? storage index entry = some updated) :
    mergeTempRead? updated index = some entry := by
  unfold mergeTempWrite? at hwrite
  split at hwrite
  · rename_i hbounds
    injection hwrite with hwrite
    subst updated
    have hnonnegative := hbounds.1
    have hnat := hbounds.2
    simp [mergeTempRead?, hnonnegative, hnat]
  · contradiction

theorem mergeTempWrite_read_ne_of_eq_some
    (storage updated : TempStorage κ ν) (written other : Int)
    (entry : SortSliceEntry κ ν)
    (hwrite : mergeTempWrite? storage written entry = some updated)
    (hne : other ≠ written) :
    mergeTempRead? updated other = mergeTempRead? storage other := by
  unfold mergeTempWrite? at hwrite
  split at hwrite
  · rename_i hbounds
    injection hwrite with hwrite
    subst updated
    by_cases hother : 0 ≤ other
    · have hnatne : written.toNat ≠ other.toNat := by
        intro heq
        apply hne
        have hwrittenCast := Int.toNat_of_nonneg hbounds.1
        have hotherCast := Int.toNat_of_nonneg hother
        omega
      simp [mergeTempRead?, hother, hnatne]
    · simp [mergeTempRead?, hother]
  · contradiction

namespace TempRangeInitialized

theorem head {storage : TempStorage κ ν} {start : Int} {count : Nat}
    (h : TempRangeInitialized storage start (count + 1)) :
    ∃ entry, mergeTempRead? storage start = some entry := by
  rcases h 0 (Nat.zero_lt_succ count) with ⟨entry, hentry⟩
  rw [erase_mergeTempRead] at hentry
  have hzero : start + Int.ofNat 0 = start := by
    simp [Int.ofNat_eq_natCast]
  rw [hzero] at hentry
  exact ⟨entry, hentry⟩

theorem tail {storage : TempStorage κ ν} {start : Int} {count : Nat}
    (h : TempRangeInitialized storage start (count + 1)) :
    TempRangeInitialized storage (start + 1) count := by
  intro offset hoffset
  rcases h (offset + 1) (by omega) with ⟨entry, hentry⟩
  refine ⟨entry, ?_⟩
  have hindex : start + Int.ofNat (offset + 1) =
      start + 1 + Int.ofNat offset := by
    simp [Int.ofNat_eq_natCast, add_left_comm, add_comm]
  simpa only [hindex] using hentry

end TempRangeInitialized

namespace TempRangeValuesMode

theorem initialized {storage : TempStorage κ ν} {start : Int} {count : Nat}
    (h : TempRangeValuesMode storage start count) :
    TempRangeInitialized storage start count := by
  intro offset hoffset
  rcases h offset hoffset with ⟨entry, hread, _⟩
  exact ⟨entry, hread⟩

theorem head {storage : TempStorage κ ν} {start : Int} {count : Nat}
    (h : TempRangeValuesMode storage start (count + 1)) :
    ∃ entry, mergeTempRead? storage start = some entry ∧
      SortSlice.EntryMatchesValuesMode storage.hasValues entry := by
  rcases h 0 (Nat.zero_lt_succ count) with ⟨entry, hread, hmode⟩
  rw [erase_mergeTempRead] at hread
  have hzero : start + Int.ofNat 0 = start := by
    simp [Int.ofNat_eq_natCast]
  rw [hzero] at hread
  exact ⟨entry, hread, hmode⟩

theorem tail {storage : TempStorage κ ν} {start : Int} {count : Nat}
    (h : TempRangeValuesMode storage start (count + 1)) :
    TempRangeValuesMode storage (start + 1) count := by
  intro offset hoffset
  rcases h (offset + 1) (by omega) with ⟨entry, hread, hmode⟩
  refine ⟨entry, ?_, hmode⟩
  have hindex : start + Int.ofNat (offset + 1) =
      start + 1 + Int.ofNat offset := by
    simp [Int.ofNat_eq_natCast, add_left_comm, add_comm]
  simpa only [hindex] using hread

end TempRangeValuesMode

/-! ## Common trace safety -/

/-- A trace contains an access of the requested kind to the requested region. -/
def AccessTrace.HasAccess (trace : AccessTrace) (kind : AccessKind)
    (region : AccessRegion) : Prop :=
  ∃ event ∈ trace.accesses, event.kind = kind ∧ event.region = region

/-- A trace contains a temporary-payload access of the requested kind.  The
backing observed by the event remains existentially visible. -/
def AccessTrace.HasTempAccess (trace : AccessTrace) (kind : AccessKind) : Prop :=
  ∃ backing, trace.HasAccess kind (.tempPayload backing)

namespace AccessTrace.HasAccess

theorem compose_left {earlier later : AccessTrace} {kind : AccessKind}
    {region : AccessRegion} (h : earlier.HasAccess kind region) :
    (earlier.compose later).HasAccess kind region := by
  rcases h with ⟨event, hevent, hkind, hregion⟩
  exact ⟨event, by simp [AccessTrace.compose, hevent], hkind, hregion⟩

theorem compose_right {earlier later : AccessTrace} {kind : AccessKind}
    {region : AccessRegion} (h : later.HasAccess kind region) :
    (earlier.compose later).HasAccess kind region := by
  rcases h with ⟨event, hevent, hkind, hregion⟩
  exact ⟨event, by simp [AccessTrace.compose, hevent], hkind, hregion⟩

theorem accesses_ne_nil {trace : AccessTrace} {kind : AccessKind}
    {region : AccessRegion} (h : trace.HasAccess kind region) :
    trace.accesses ≠ [] := by
  intro hempty
  rcases h with ⟨event, hevent, _, _⟩
  simp [hempty] at hevent

end AccessTrace.HasAccess

namespace AccessTrace.HasTempAccess

theorem compose_left {earlier later : AccessTrace} {kind : AccessKind}
    (h : earlier.HasTempAccess kind) :
    (earlier.compose later).HasTempAccess kind := by
  rcases h with ⟨backing, haccess⟩
  exact ⟨backing, haccess.compose_left⟩

theorem compose_right {earlier later : AccessTrace} {kind : AccessKind}
    (h : later.HasTempAccess kind) :
    (earlier.compose later).HasTempAccess kind := by
  rcases h with ⟨backing, haccess⟩
  exact ⟨backing, haccess.compose_right⟩

end AccessTrace.HasTempAccess

/-- Complete local trace obligations shared by all merge movements. -/
structure MovementTraceSafe (execution : TraceResult α) : Prop where
  fuel : execution.trace.fuelExhausted = false
  noPushes : execution.trace.pushDepths = []
  bounds : execution.trace.allAccessesInBounds
  tempLive : execution.trace.tempPayloadAccessesLive

namespace MovementTraceSafe

theorem pure (value : α) : MovementTraceSafe (TraceResult.pure value) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact AccessTrace.allAccessesInBounds_empty
  · exact AccessTrace.tempPayloadAccessesLive_empty

theorem map (current : TraceResult α) (transform : α → β)
    (h : MovementTraceSafe current) :
    MovementTraceSafe (current.map transform) := by
  exact ⟨h.fuel, h.noPushes, h.bounds, h.tempLive⟩

/-- Adding a raw merge-memory observation changes none of the access, push,
fuel, or released-payload obligations tracked by this structure. -/
theorem recordSuccessMemoryEvent (current : TraceResult α)
    (event : α → MergeMemoryEvent) (h : MovementTraceSafe current) :
    MovementTraceSafe (current.recordSuccessMemoryEvent event) := by
  exact
    { fuel := by simpa using h.fuel
      noPushes := by simpa using h.noPushes
      bounds := (TraceResult.allAccessesInBounds_recordSuccessMemoryEvent
        current event).2 h.bounds
      tempLive :=
        (TraceResult.tempPayloadAccessesLive_recordSuccessMemoryEvent
          current event).2 h.tempLive }

theorem bind (current : TraceResult α) (next : α → TraceResult β)
    (value : α) (hresult : current.result = some value)
    (hcurrent : MovementTraceSafe current)
    (hnext : MovementTraceSafe (next value)) :
    MovementTraceSafe (current.bind next) := by
  rcases hcurrent with ⟨hcurrentFuel, hcurrentPush, hcurrentBounds, hcurrentLive⟩
  rcases hnext with ⟨hnextFuel, hnextPush, hnextBounds, hnextLive⟩
  constructor
  · simp [TraceResult.trace_bind, hresult, hcurrentFuel, hnextFuel]
  · simp [TraceResult.trace_bind, hresult, AccessTrace.compose,
      hcurrentPush, hnextPush]
  · rw [TraceResult.trace_bind, hresult,
      AccessTrace.allAccessesInBounds_compose]
    exact ⟨hcurrentBounds, hnextBounds⟩
  · rw [TraceResult.trace_bind, hresult,
      AccessTrace.tempPayloadAccessesLive_compose]
    exact ⟨hcurrentLive, hnextLive⟩

end MovementTraceSafe

private theorem keyRead_safe (slice : SortSlice κ ν) (index : Int)
    (hindex : SortSlice.IndexInBounds slice index) :
    MovementTraceSafe (TraceResult.sortSliceKeysRead? slice index) := by
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
    MovementTraceSafe (TraceResult.sortSliceValuesRead? slice index) := by
  constructor
  · simp [TraceResult.trace_sortSliceValuesRead, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_sortSliceValuesRead, AccessTrace.singletonAccess]
  · rw [TraceResult.trace_sortSliceValuesRead]
    simpa [AccessTrace.allAccessesInBounds, AccessTrace.singletonAccess,
      AccessEvent.InBounds, SortSlice.IndexInBounds] using hindex
  · simp [TraceResult.trace_sortSliceValuesRead,
      AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
      AccessEvent.TempPayloadLive]

private theorem keyWrite_safe (slice : SortSlice κ ν) (index : Int)
    (entry : SortSliceEntry κ ν) (hindex : SortSlice.IndexInBounds slice index) :
    MovementTraceSafe (TraceResult.sortSliceKeysWrite? slice index entry) := by
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
    (entry : SortSliceEntry κ ν) (hindex : SortSlice.IndexInBounds slice index) :
    MovementTraceSafe (TraceResult.sortSliceValuesWrite? slice index entry) := by
  constructor
  · simp [TraceResult.trace_sortSliceValuesWrite, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_sortSliceValuesWrite, AccessTrace.singletonAccess]
  · rw [TraceResult.trace_sortSliceValuesWrite]
    simpa [AccessTrace.allAccessesInBounds, AccessTrace.singletonAccess,
      AccessEvent.InBounds, SortSlice.IndexInBounds] using hindex
  · simp [TraceResult.trace_sortSliceValuesWrite,
      AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
      AccessEvent.TempPayloadLive]

private theorem tempRead_safe (storage : TempStorage κ ν) (index : Int)
    (hindex : TempIndexInBounds storage index) (hlive : storage.Live) :
    MovementTraceSafe (TraceResult.tempPayloadRead? storage index) := by
  constructor
  · simp [TraceResult.trace_tempPayloadRead, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_tempPayloadRead, AccessTrace.singletonAccess]
  · rw [TraceResult.trace_tempPayloadRead]
    simpa [AccessTrace.allAccessesInBounds, AccessTrace.singletonAccess,
      AccessEvent.InBounds, TempIndexInBounds] using hindex
  · rw [TraceResult.trace_tempPayloadRead]
    simpa [AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
      AccessEvent.TempPayloadLive, TempStorage.Live] using hlive

private theorem tempWrite_safe (storage : TempStorage κ ν) (index : Int)
    (entry : SortSliceEntry κ ν) (hindex : TempIndexInBounds storage index)
    (hlive : storage.Live) :
    MovementTraceSafe (TraceResult.tempPayloadWrite? storage index entry) := by
  constructor
  · simp [TraceResult.trace_tempPayloadWrite, AccessTrace.singletonAccess]
  · simp [TraceResult.trace_tempPayloadWrite, AccessTrace.singletonAccess]
  · rw [TraceResult.trace_tempPayloadWrite]
    simpa [AccessTrace.allAccessesInBounds, AccessTrace.singletonAccess,
      AccessEvent.InBounds, TempIndexInBounds] using hindex
  · rw [TraceResult.trace_tempPayloadWrite]
    simpa [AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
      AccessEvent.TempPayloadLive, TempStorage.Live] using hlive

/-! ## One-cell totality and complete trace safety -/

/-- A valid main source and temporary destination make the untraced atomic
main-to-temporary movement total. -/
theorem mainToTempCell_eq_some_of_bounds (state : MergeState κ ν)
    (tempDst mainSrc : Int)
    (htemp : TempIndexInBounds state.a tempDst)
    (hmain : SortSlice.IndexInBounds state.data mainSrc) :
    ∃ result, mainToTempCell? state tempDst mainSrc = some result := by
  rcases SortSlice.read_eq_some_of_indexInBounds state.data mainSrc hmain with
    ⟨entry, hread⟩
  rcases mergeTempWrite_eq_some_of_bounds state.a tempDst entry htemp with
    ⟨storage, hwrite⟩
  refine ⟨{ state with a := storage }, ?_⟩
  simp [mainToTempCell?, hread, hwrite]

/-- An initialized temporary source and valid main destination make the
untraced atomic temporary-to-main movement total. -/
theorem tempToMainCell_eq_some_of_bounds (state : MergeState κ ν)
    (mainDst tempSrc : Int)
    (hmain : SortSlice.IndexInBounds state.data mainDst)
    (hreadable : ∃ entry, mergeTempRead? state.a tempSrc = some entry) :
    ∃ result, tempToMainCell? state mainDst tempSrc = some result := by
  rcases hreadable with ⟨entry, hread⟩
  rcases SortSlice.write_eq_some_of_indexInBounds state.data mainDst entry hmain with
    ⟨data, hwrite⟩
  refine ⟨{ state with data := data }, ?_⟩
  simp [tempToMainCell?, hread, hwrite]

theorem mainToTempCell_data_eq_of_eq_some (state result : MergeState κ ν)
    (tempDst mainSrc : Int)
    (hresult : mainToTempCell? state tempDst mainSrc = some result) :
    result.data = state.data := by
  rcases Option.bind_eq_some_iff.mp hresult with ⟨entry, hread, htail⟩
  rcases Option.bind_eq_some_iff.mp htail with ⟨storage, hwrite, hfinal⟩
  change some { state with a := storage } = some result at hfinal
  injection hfinal with hfinal
  subst result
  rfl

theorem tempToMainCell_temp_eq_of_eq_some (state result : MergeState κ ν)
    (mainDst tempSrc : Int)
    (hresult : tempToMainCell? state mainDst tempSrc = some result) :
    result.a = state.a := by
  rcases Option.bind_eq_some_iff.mp hresult with ⟨entry, hread, htail⟩
  rcases Option.bind_eq_some_iff.mp htail with ⟨data, hwrite, hfinal⟩
  change some { state with data := data } = some result at hfinal
  injection hfinal with hfinal
  subst result
  rfl

private theorem mainToTempKeyTraced_safe_of_bounds
    (state : MergeState κ ν) (tempDst mainSrc : Int)
    (htemp : TempIndexInBounds state.a tempDst)
    (hmain : SortSlice.IndexInBounds state.data mainSrc)
    (hlive : state.a.Live) :
    MovementTraceSafe (mainToTempKeyTraced? state tempDst mainSrc) := by
  rcases SortSlice.read_eq_some_of_indexInBounds state.data mainSrc hmain with
    ⟨entry, hread⟩
  have hreadTraced :
      (TraceResult.sortSliceKeysRead? state.data mainSrc).result = some entry := by
    change (TraceResult.sortSliceKeysRead? state.data mainSrc).erase = some entry
    simpa using hread
  unfold mainToTempKeyTraced?
  apply MovementTraceSafe.bind _ _ entry hreadTraced
  · exact keyRead_safe state.data mainSrc hmain
  · exact MovementTraceSafe.map _ _
      (tempWrite_safe state.a tempDst entry htemp hlive)

private theorem mainToTempValuesTraced_safe_of_bounds
    (state : MergeState κ ν) (tempDst mainSrc : Int)
    (htemp : TempIndexInBounds state.a tempDst)
    (hmain : SortSlice.IndexInBounds state.data mainSrc)
    (hlive : state.a.Live) :
    MovementTraceSafe (mainToTempValuesTraced? state tempDst mainSrc) := by
  rcases SortSlice.read_eq_some_of_indexInBounds state.data mainSrc hmain with
    ⟨entry, hread⟩
  have hreadTraced :
      (TraceResult.sortSliceValuesRead? state.data mainSrc).result = some entry := by
    change (TraceResult.sortSliceValuesRead? state.data mainSrc).erase = some entry
    simpa using hread
  unfold mainToTempValuesTraced?
  apply MovementTraceSafe.bind _ _ entry hreadTraced
  · exact valuesRead_safe state.data mainSrc hmain
  · exact MovementTraceSafe.map _ _
      (tempWrite_safe state.a tempDst entry htemp hlive)

/-- Complete one-cell main-to-temporary contract.  In addition to totality it
proves bounds, temporary liveness, absence of pushes, and non-exhaustion for
the exact traced execution. -/
theorem mainToTempCellTraced_safe (state : MergeState κ ν)
    (tempDst mainSrc : Int)
    (htemp : TempIndexInBounds state.a tempDst)
    (hmain : SortSlice.IndexInBounds state.data mainSrc)
    (hlive : state.a.Live) :
    ∃ result,
      (mainToTempCellTraced? state tempDst mainSrc).result = some result ∧
      MovementTraceSafe (mainToTempCellTraced? state tempDst mainSrc) ∧
      MergeMovementFrame state result := by
  rcases mainToTempCell_eq_some_of_bounds state tempDst mainSrc htemp hmain with
    ⟨result, hcore⟩
  have hkey : (mainToTempKeyTraced? state tempDst mainSrc).result = some result := by
    change (mainToTempKeyTraced? state tempDst mainSrc).erase = some result
    rw [erase_mainToTempKeyTraced]
    exact hcore
  have hexecution :
      (mainToTempCellTraced? state tempDst mainSrc).result = some result := by
    change (mainToTempCellTraced? state tempDst mainSrc).erase = some result
    rw [erase_mainToTempCellTraced]
    exact hcore
  refine ⟨result, hexecution, ?_, mainToTempCell_frame state result tempDst mainSrc hcore⟩
  unfold mainToTempCellTraced?
  apply MovementTraceSafe.bind _ _ result hkey
  · exact mainToTempKeyTraced_safe_of_bounds state tempDst mainSrc htemp hmain hlive
  · cases hmode : state.a.hasValues with
    | false => simp only [Bool.false_eq]
               exact MovementTraceSafe.pure result
    | true => simp only [↓reduceIte]
              exact mainToTempValuesTraced_safe_of_bounds state tempDst mainSrc
                htemp hmain hlive

private theorem tempToMainKeyTraced_safe_of_bounds
    (state : MergeState κ ν) (mainDst tempSrc : Int)
    (hmain : SortSlice.IndexInBounds state.data mainDst)
    (htemp : TempIndexInBounds state.a tempSrc)
    (hlive : state.a.Live)
    (hreadable : ∃ entry, mergeTempRead? state.a tempSrc = some entry) :
    MovementTraceSafe (tempToMainKeyTraced? state mainDst tempSrc) := by
  rcases hreadable with ⟨entry, hread⟩
  have hreadTraced :
      (TraceResult.tempPayloadRead? state.a tempSrc).result = some entry := by
    change (TraceResult.tempPayloadRead? state.a tempSrc).erase = some entry
    rw [erase_mergeTempRead]
    exact hread
  unfold tempToMainKeyTraced?
  apply MovementTraceSafe.bind _ _ entry hreadTraced
  · exact tempRead_safe state.a tempSrc htemp hlive
  · exact MovementTraceSafe.map _ _
      (keyWrite_safe state.data mainDst entry hmain)

private theorem tempToMainValuesTraced_safe_of_bounds
    (state : MergeState κ ν) (mainDst tempSrc : Int)
    (hmain : SortSlice.IndexInBounds state.data mainDst)
    (htemp : TempIndexInBounds state.a tempSrc)
    (hlive : state.a.Live)
    (hreadable : ∃ entry, mergeTempRead? state.a tempSrc = some entry) :
    MovementTraceSafe (tempToMainValuesTraced? state mainDst tempSrc) := by
  rcases hreadable with ⟨entry, hread⟩
  have hreadTraced :
      (TraceResult.tempPayloadRead? state.a tempSrc).result = some entry := by
    change (TraceResult.tempPayloadRead? state.a tempSrc).erase = some entry
    rw [erase_mergeTempRead]
    exact hread
  unfold tempToMainValuesTraced?
  apply MovementTraceSafe.bind _ _ entry hreadTraced
  · exact tempRead_safe state.a tempSrc htemp hlive
  · exact MovementTraceSafe.map _ _
      (valuesWrite_safe state.data mainDst entry hmain)

/-- Complete one-cell temporary-to-main trace contract. -/
theorem tempToMainCellTraced_safe (state : MergeState κ ν)
    (mainDst tempSrc : Int)
    (hmain : SortSlice.IndexInBounds state.data mainDst)
    (htemp : TempIndexInBounds state.a tempSrc)
    (hlive : state.a.Live)
    (hreadable : ∃ entry, mergeTempRead? state.a tempSrc = some entry) :
    ∃ result,
      (tempToMainCellTraced? state mainDst tempSrc).result = some result ∧
      MovementTraceSafe (tempToMainCellTraced? state mainDst tempSrc) ∧
      MergeMovementFrame state result := by
  rcases tempToMainCell_eq_some_of_bounds state mainDst tempSrc hmain hreadable with
    ⟨result, hcore⟩
  have hkey : (tempToMainKeyTraced? state mainDst tempSrc).result = some result := by
    change (tempToMainKeyTraced? state mainDst tempSrc).erase = some result
    rw [erase_tempToMainKeyTraced]
    exact hcore
  have hexecution :
      (tempToMainCellTraced? state mainDst tempSrc).result = some result := by
    change (tempToMainCellTraced? state mainDst tempSrc).erase = some result
    rw [erase_tempToMainCellTraced]
    exact hcore
  refine ⟨result, hexecution, ?_, tempToMainCell_frame state result mainDst tempSrc hcore⟩
  unfold tempToMainCellTraced?
  apply MovementTraceSafe.bind _ _ result hkey
  · exact tempToMainKeyTraced_safe_of_bounds state mainDst tempSrc hmain htemp
      hlive hreadable
  · cases hmode : state.a.hasValues with
    | false => simp only [Bool.false_eq]
               exact MovementTraceSafe.pure result
    | true => simp only [↓reduceIte]
              exact tempToMainValuesTraced_safe_of_bounds state mainDst tempSrc
                hmain htemp hlive hreadable

/-! ## Bulk phase totality and trace safety -/

private theorem mainToTempKeysTraced_safe_of_ranges (site : MergeMemcpySite)
    (permit : site.MainToTempPermit) (count : Nat)
    (state : MergeState κ ν) (tempDst mainSrc : Int)
    (htemp : TempRangeInBounds state.a tempDst count)
    (hmain : SortSlice.RangeInBounds state.data mainSrc count)
    (hlive : state.a.Live) :
    ∃ result,
      (mainToTempKeysTraced? site permit count state tempDst mainSrc).result =
        some result ∧
      MovementTraceSafe
        (mainToTempKeysTraced? site permit count state tempDst mainSrc) ∧
      MergeMovementFrame state result := by
  induction count generalizing state tempDst mainSrc with
  | zero =>
      refine ⟨state, rfl, MovementTraceSafe.pure state, .refl state⟩
  | succ count ih =>
      have htempHead := htemp.head
      have hmainHead := hmain.head
      rcases mainToTempCell_eq_some_of_bounds state tempDst mainSrc htempHead
          hmainHead with ⟨next, hcell⟩
      have hcellFrame := mainToTempCell_frame state next tempDst mainSrc hcell
      have hcellResult :
          (mainToTempKeyTraced? state tempDst mainSrc).result = some next := by
        change (mainToTempKeyTraced? state tempDst mainSrc).erase = some next
        rw [erase_mainToTempKeyTraced]
        exact hcell
      have htempTail : TempRangeInBounds next.a (tempDst + 1) count :=
        TempRangeInBounds.of_size_eq htemp.tail hcellFrame.tempSize
      have hmainTail : SortSlice.RangeInBounds next.data (mainSrc + 1) count :=
        SortSlice.RangeInBounds.of_size_eq hmain.tail hcellFrame.dataSize
      have hliveNext : next.a.Live := hcellFrame.live hlive
      rcases ih next (tempDst + 1) (mainSrc + 1) htempTail hmainTail hliveNext with
        ⟨result, hrest, hrestSafe, hrestFrame⟩
      refine ⟨result, ?_, ?_, hcellFrame.trans hrestFrame⟩
      · simp [mainToTempKeysTraced?, TraceResult.bind, hcellResult, hrest]
      · simp only [mainToTempKeysTraced?]
        exact MovementTraceSafe.bind _ _ next hcellResult
          (mainToTempKeyTraced_safe_of_bounds state tempDst mainSrc htempHead
            hmainHead hlive) hrestSafe

private theorem mainToTempValuesPhaseTraced_safe_of_ranges
    (site : MergeMemcpySite) (permit : site.MainToTempPermit) (count : Nat)
    (state : MergeState κ ν) (tempDst mainSrc : Int)
    (htemp : TempRangeInBounds state.a tempDst count)
    (hmain : SortSlice.RangeInBounds state.data mainSrc count)
    (hlive : state.a.Live) :
    ∃ result,
      (mainToTempValuesPhaseTraced? site permit count state tempDst mainSrc).result =
        some result ∧
      MovementTraceSafe
        (mainToTempValuesPhaseTraced? site permit count state tempDst mainSrc) ∧
      MergeMovementFrame state result := by
  induction count generalizing state tempDst mainSrc with
  | zero =>
      refine ⟨state, rfl, MovementTraceSafe.pure state, .refl state⟩
  | succ count ih =>
      have htempHead := htemp.head
      have hmainHead := hmain.head
      rcases mainToTempCell_eq_some_of_bounds state tempDst mainSrc htempHead
          hmainHead with ⟨next, hcell⟩
      have hcellFrame := mainToTempCell_frame state next tempDst mainSrc hcell
      have hcellResult :
          (mainToTempValuesTraced? state tempDst mainSrc).result = some next := by
        change (mainToTempValuesTraced? state tempDst mainSrc).erase = some next
        rw [erase_mainToTempValuesTraced]
        exact hcell
      have htempTail : TempRangeInBounds next.a (tempDst + 1) count :=
        TempRangeInBounds.of_size_eq htemp.tail hcellFrame.tempSize
      have hmainTail : SortSlice.RangeInBounds next.data (mainSrc + 1) count :=
        SortSlice.RangeInBounds.of_size_eq hmain.tail hcellFrame.dataSize
      have hliveNext : next.a.Live := hcellFrame.live hlive
      rcases ih next (tempDst + 1) (mainSrc + 1) htempTail hmainTail hliveNext with
        ⟨result, hrest, hrestSafe, hrestFrame⟩
      refine ⟨result, ?_, ?_, hcellFrame.trans hrestFrame⟩
      · simp [mainToTempValuesPhaseTraced?, TraceResult.bind, hcellResult, hrest]
      · simp only [mainToTempValuesPhaseTraced?]
        exact MovementTraceSafe.bind _ _ next hcellResult
          (mainToTempValuesTraced_safe_of_bounds state tempDst mainSrc htempHead
            hmainHead hlive) hrestSafe

private theorem mainToTempMemcpyTraced_traceSafe_of_ranges
    (site : MergeMemcpySite) (permit : site.MainToTempPermit) (count : Nat)
    (state : MergeState κ ν) (tempDst mainSrc : Int)
    (htemp : TempRangeInBounds state.a tempDst count)
    (hmain : SortSlice.RangeInBounds state.data mainSrc count)
    (hlive : state.a.Live) :
    ∃ result,
      (mainToTempMemcpyTraced? site permit count state tempDst mainSrc).result =
        some result ∧
      MovementTraceSafe
        (mainToTempMemcpyTraced? site permit count state tempDst mainSrc) ∧
      MergeMovementFrame state result := by
  rcases mainToTempKeysTraced_safe_of_ranges site permit count state tempDst
      mainSrc htemp hmain hlive with ⟨keyResult, hkeys, hkeysSafe, hkeysFrame⟩
  cases hmode : state.a.hasValues with
  | false =>
      refine ⟨keyResult, ?_, ?_, hkeysFrame⟩
      · simp [mainToTempMemcpyTraced?, TraceResult.bind, TraceResult.pure,
          hkeys, hmode]
      · unfold mainToTempMemcpyTraced?
        apply MovementTraceSafe.bind _ _ keyResult hkeys hkeysSafe
        simp only [hmode, Bool.false_eq]
        exact MovementTraceSafe.pure keyResult
  | true =>
      rcases mainToTempValuesPhaseTraced_safe_of_ranges site permit count state
          tempDst mainSrc htemp hmain hlive with
        ⟨valuesResult, hvalues, hvaluesSafe, hvaluesFrame⟩
      refine ⟨valuesResult, ?_, ?_, hvaluesFrame⟩
      · simp [mainToTempMemcpyTraced?, TraceResult.bind, hkeys, hmode, hvalues]
      · unfold mainToTempMemcpyTraced?
        apply MovementTraceSafe.bind _ _ keyResult hkeys hkeysSafe
        simpa only [hmode, Bool.true_eq, ↓reduceIte] using hvaluesSafe

private theorem tempToMainKeysTraced_safe_of_ranges (site : MergeMemcpySite)
    (permit : site.TempToMainPermit) (count : Nat)
    (state : MergeState κ ν) (mainDst tempSrc : Int)
    (hmain : SortSlice.RangeInBounds state.data mainDst count)
    (htemp : TempRangeInBounds state.a tempSrc count)
    (hinitialized : TempRangeInitialized state.a tempSrc count)
    (hlive : state.a.Live) :
    ∃ result,
      (tempToMainKeysTraced? site permit count state mainDst tempSrc).result =
        some result ∧
      MovementTraceSafe
        (tempToMainKeysTraced? site permit count state mainDst tempSrc) ∧
      MergeMovementFrame state result := by
  induction count generalizing state mainDst tempSrc with
  | zero =>
      refine ⟨state, rfl, MovementTraceSafe.pure state, .refl state⟩
  | succ count ih =>
      have hmainHead := hmain.head
      have htempHead := htemp.head
      have hreadable := hinitialized.head
      rcases tempToMainCell_eq_some_of_bounds state mainDst tempSrc hmainHead
          hreadable with ⟨next, hcell⟩
      have hcellFrame := tempToMainCell_frame state next mainDst tempSrc hcell
      have htempEq := tempToMainCell_temp_eq_of_eq_some state next mainDst tempSrc hcell
      have hcellResult :
          (tempToMainKeyTraced? state mainDst tempSrc).result = some next := by
        change (tempToMainKeyTraced? state mainDst tempSrc).erase = some next
        rw [erase_tempToMainKeyTraced]
        exact hcell
      have hmainTail : SortSlice.RangeInBounds next.data (mainDst + 1) count :=
        SortSlice.RangeInBounds.of_size_eq hmain.tail hcellFrame.dataSize
      have htempTail : TempRangeInBounds next.a (tempSrc + 1) count := by
        simpa only [htempEq] using htemp.tail
      have hinitializedTail : TempRangeInitialized next.a (tempSrc + 1) count := by
        simpa only [htempEq] using hinitialized.tail
      have hliveNext : next.a.Live := hcellFrame.live hlive
      rcases ih next (mainDst + 1) (tempSrc + 1) hmainTail htempTail
          hinitializedTail hliveNext with
        ⟨result, hrest, hrestSafe, hrestFrame⟩
      refine ⟨result, ?_, ?_, hcellFrame.trans hrestFrame⟩
      · simp [tempToMainKeysTraced?, TraceResult.bind, hcellResult, hrest]
      · simp only [tempToMainKeysTraced?]
        exact MovementTraceSafe.bind _ _ next hcellResult
          (tempToMainKeyTraced_safe_of_bounds state mainDst tempSrc hmainHead
            htempHead hlive hreadable) hrestSafe

private theorem tempToMainValuesPhaseTraced_safe_of_ranges
    (site : MergeMemcpySite) (permit : site.TempToMainPermit) (count : Nat)
    (state : MergeState κ ν) (mainDst tempSrc : Int)
    (hmain : SortSlice.RangeInBounds state.data mainDst count)
    (htemp : TempRangeInBounds state.a tempSrc count)
    (hinitialized : TempRangeInitialized state.a tempSrc count)
    (hlive : state.a.Live) :
    ∃ result,
      (tempToMainValuesPhaseTraced? site permit count state mainDst tempSrc).result =
        some result ∧
      MovementTraceSafe
        (tempToMainValuesPhaseTraced? site permit count state mainDst tempSrc) ∧
      MergeMovementFrame state result := by
  induction count generalizing state mainDst tempSrc with
  | zero =>
      refine ⟨state, rfl, MovementTraceSafe.pure state, .refl state⟩
  | succ count ih =>
      have hmainHead := hmain.head
      have htempHead := htemp.head
      have hreadable := hinitialized.head
      rcases tempToMainCell_eq_some_of_bounds state mainDst tempSrc hmainHead
          hreadable with ⟨next, hcell⟩
      have hcellFrame := tempToMainCell_frame state next mainDst tempSrc hcell
      have htempEq := tempToMainCell_temp_eq_of_eq_some state next mainDst tempSrc hcell
      have hcellResult :
          (tempToMainValuesTraced? state mainDst tempSrc).result = some next := by
        change (tempToMainValuesTraced? state mainDst tempSrc).erase = some next
        rw [erase_tempToMainValuesTraced]
        exact hcell
      have hmainTail : SortSlice.RangeInBounds next.data (mainDst + 1) count :=
        SortSlice.RangeInBounds.of_size_eq hmain.tail hcellFrame.dataSize
      have htempTail : TempRangeInBounds next.a (tempSrc + 1) count := by
        simpa only [htempEq] using htemp.tail
      have hinitializedTail : TempRangeInitialized next.a (tempSrc + 1) count := by
        simpa only [htempEq] using hinitialized.tail
      have hliveNext : next.a.Live := hcellFrame.live hlive
      rcases ih next (mainDst + 1) (tempSrc + 1) hmainTail htempTail
          hinitializedTail hliveNext with
        ⟨result, hrest, hrestSafe, hrestFrame⟩
      refine ⟨result, ?_, ?_, hcellFrame.trans hrestFrame⟩
      · simp [tempToMainValuesPhaseTraced?, TraceResult.bind, hcellResult, hrest]
      · simp only [tempToMainValuesPhaseTraced?]
        exact MovementTraceSafe.bind _ _ next hcellResult
          (tempToMainValuesTraced_safe_of_bounds state mainDst tempSrc hmainHead
            htempHead hlive hreadable) hrestSafe

private theorem tempToMainMemcpyTraced_traceSafe_of_ranges
    (site : MergeMemcpySite) (permit : site.TempToMainPermit) (count : Nat)
    (state : MergeState κ ν) (mainDst tempSrc : Int)
    (hmain : SortSlice.RangeInBounds state.data mainDst count)
    (htemp : TempRangeInBounds state.a tempSrc count)
    (hinitialized : TempRangeInitialized state.a tempSrc count)
    (hlive : state.a.Live) :
    ∃ result,
      (tempToMainMemcpyTraced? site permit count state mainDst tempSrc).result =
        some result ∧
      MovementTraceSafe
        (tempToMainMemcpyTraced? site permit count state mainDst tempSrc) ∧
      MergeMovementFrame state result := by
  rcases tempToMainKeysTraced_safe_of_ranges site permit count state mainDst
      tempSrc hmain htemp hinitialized hlive with
    ⟨keyResult, hkeys, hkeysSafe, hkeysFrame⟩
  cases hmode : state.a.hasValues with
  | false =>
      refine ⟨keyResult, ?_, ?_, hkeysFrame⟩
      · simp [tempToMainMemcpyTraced?, TraceResult.bind, TraceResult.pure,
          hkeys, hmode]
      · unfold tempToMainMemcpyTraced?
        apply MovementTraceSafe.bind _ _ keyResult hkeys hkeysSafe
        simp only [hmode, Bool.false_eq]
        exact MovementTraceSafe.pure keyResult
  | true =>
      rcases tempToMainValuesPhaseTraced_safe_of_ranges site permit count state
          mainDst tempSrc hmain htemp hinitialized hlive with
        ⟨valuesResult, hvalues, hvaluesSafe, hvaluesFrame⟩
      refine ⟨valuesResult, ?_, ?_, hvaluesFrame⟩
      · simp [tempToMainMemcpyTraced?, TraceResult.bind, hkeys, hmode, hvalues]
      · unfold tempToMainMemcpyTraced?
        apply MovementTraceSafe.bind _ _ keyResult hkeys hkeysSafe
        simpa only [hmode, Bool.true_eq, ↓reduceIte] using hvaluesSafe

/-- Public totality and complete trace-safety contract for classified
main-to-temporary bulk movement. -/
theorem mainToTempMemcpyTraced_safe
    (site : MergeMemcpySite) (permit : site.MainToTempPermit) (count : Nat)
    (state : MergeState κ ν) (tempDst mainSrc : Int)
    (htemp : TempRangeInBounds state.a tempDst count)
    (hmain : SortSlice.RangeInBounds state.data mainSrc count)
    (hlive : state.a.Live) :
    ∃ result,
      (mainToTempMemcpyTraced? site permit count state tempDst mainSrc).result =
        some result ∧
      MovementTraceSafe
        (mainToTempMemcpyTraced? site permit count state tempDst mainSrc) ∧
      MergeMovementFrame state result :=
  mainToTempMemcpyTraced_traceSafe_of_ranges site permit count state tempDst
    mainSrc htemp hmain hlive

/-- Public totality and complete trace-safety contract for classified
temporary-to-main bulk movement. -/
theorem tempToMainMemcpyTraced_safe
    (site : MergeMemcpySite) (permit : site.TempToMainPermit) (count : Nat)
    (state : MergeState κ ν) (mainDst tempSrc : Int)
    (hmain : SortSlice.RangeInBounds state.data mainDst count)
    (htemp : TempRangeInBounds state.a tempSrc count)
    (hinitialized : TempRangeInitialized state.a tempSrc count)
    (hlive : state.a.Live) :
    ∃ result,
      (tempToMainMemcpyTraced? site permit count state mainDst tempSrc).result =
        some result ∧
      MovementTraceSafe
        (tempToMainMemcpyTraced? site permit count state mainDst tempSrc) ∧
      MergeMovementFrame state result :=
  tempToMainMemcpyTraced_traceSafe_of_ranges site permit count state mainDst
    tempSrc hmain htemp hinitialized hlive

/-! ## Bulk initialization and values-mode preservation -/

theorem mainToTempCell_read_eq_some (state result : MergeState κ ν)
    (tempDst mainSrc : Int)
    (hcopy : mainToTempCell? state tempDst mainSrc = some result) :
    ∃ entry, state.data.read? mainSrc = some entry ∧
      mergeTempRead? result.a tempDst = some entry := by
  rcases Option.bind_eq_some_iff.mp hcopy with ⟨entry, hread, htail⟩
  rcases Option.bind_eq_some_iff.mp htail with ⟨storage, hwrite, hfinal⟩
  change some { state with a := storage } = some result at hfinal
  injection hfinal with hfinal
  subst result
  exact ⟨entry, hread,
    mergeTempWrite_read_self_of_eq_some state.a storage tempDst entry hwrite⟩

theorem mainToTempCell_read_of_ne (state result : MergeState κ ν)
    (tempDst mainSrc other : Int)
    (hcopy : mainToTempCell? state tempDst mainSrc = some result)
    (hne : other ≠ tempDst) :
    mergeTempRead? result.a other = mergeTempRead? state.a other := by
  rcases Option.bind_eq_some_iff.mp hcopy with ⟨entry, hread, htail⟩
  rcases Option.bind_eq_some_iff.mp htail with ⟨storage, hwrite, hfinal⟩
  change some { state with a := storage } = some result at hfinal
  injection hfinal with hfinal
  subst result
  exact mergeTempWrite_read_ne_of_eq_some state.a storage tempDst other entry
    hwrite hne

/-- A forward main-to-temporary copy preserves every cell strictly before its
destination range. -/
theorem mainToTempMemcpy_read_before_of_eq_some
    (count : Nat) (state result : MergeState κ ν)
    (tempDst mainSrc other : Int)
    (hcopy : mainToTempMemcpy? count state tempDst mainSrc = some result)
    (hother : other < tempDst) :
    mergeTempRead? result.a other = mergeTempRead? state.a other := by
  induction count generalizing state tempDst mainSrc with
  | zero =>
      simp only [mainToTempMemcpy?, Option.some.injEq] at hcopy
      subst result
      rfl
  | succ count ih =>
      simp only [mainToTempMemcpy?, bind, Option.bind] at hcopy
      split at hcopy <;> try contradiction
      rename_i next hhead
      have htail := ih next (tempDst + 1) (mainSrc + 1) hcopy (by omega)
      exact htail.trans
        (mainToTempCell_read_of_ne state next tempDst mainSrc other hhead
          (by omega))

/-- A successful forward main-to-temporary copy initializes every destination
cell and records an entry matching the source list's explicit values mode. -/
theorem mainToTempMemcpy_valuesMode_of_eq_some
    (count : Nat) (state result : MergeState κ ν)
    (tempDst mainSrc : Int)
    (hmode : SortSlice.ValuesModeInvariant state.a.hasValues state.data)
    (hcopy : mainToTempMemcpy? count state tempDst mainSrc = some result) :
    TempRangeValuesMode result.a tempDst count := by
  induction count generalizing state tempDst mainSrc with
  | zero =>
      intro offset hoffset
      omega
  | succ count ih =>
      simp only [mainToTempMemcpy?, bind, Option.bind] at hcopy
      split at hcopy <;> try contradiction
      rename_i next hhead
      have hheadFrame := mainToTempCell_frame state next tempDst mainSrc hhead
      have hdataEq := mainToTempCell_data_eq_of_eq_some state next tempDst mainSrc hhead
      have hmodeNext :
          SortSlice.ValuesModeInvariant next.a.hasValues next.data := by
        simpa only [hheadFrame.tempValuesMode, hdataEq] using hmode
      have htailMode := ih next (tempDst + 1) (mainSrc + 1) hmodeNext hcopy
      intro offset hoffset
      cases offset with
      | zero =>
          rcases mainToTempCell_read_eq_some state next tempDst mainSrc hhead with
            ⟨entry, hread, htempRead⟩
          have hpreserved := mainToTempMemcpy_read_before_of_eq_some count next
            result (tempDst + 1) (mainSrc + 1) tempDst hcopy (by omega)
          have hfinalRead : mergeTempRead? result.a tempDst = some entry :=
            hpreserved.trans htempRead
          refine ⟨entry, ?_, ?_⟩
          · rw [erase_mergeTempRead]
            have hzero : tempDst + Int.ofNat 0 = tempDst := by
              simp [Int.ofNat_eq_natCast]
            rw [hzero]
            exact hfinalRead
          · have hentryMode := hmode.read_matches_of_eq_some hread
            simpa only [hheadFrame.tempValuesMode,
              (mainToTempMemcpy_frame count next result (tempDst + 1)
                (mainSrc + 1) hcopy).tempValuesMode] using hentryMode
      | succ offset =>
          rcases htailMode offset (by omega) with ⟨entry, hread, hentryMode⟩
          refine ⟨entry, ?_, hentryMode⟩
          have hindex : tempDst + Int.ofNat (offset + 1) =
              tempDst + 1 + Int.ofNat offset := by
            simp [Int.ofNat_eq_natCast, add_left_comm, add_comm]
          simpa only [hindex] using hread

theorem mainToTempMemcpy_data_eq_of_eq_some
    (count : Nat) (state result : MergeState κ ν)
    (tempDst mainSrc : Int)
    (hcopy : mainToTempMemcpy? count state tempDst mainSrc = some result) :
    result.data = state.data := by
  induction count generalizing state tempDst mainSrc with
  | zero =>
      simp only [mainToTempMemcpy?, Option.some.injEq] at hcopy
      subst result
      rfl
  | succ count ih =>
      simp only [mainToTempMemcpy?, bind, Option.bind] at hcopy
      split at hcopy <;> try contradiction
      rename_i next hhead
      exact (ih next (tempDst + 1) (mainSrc + 1) hcopy).trans
        (mainToTempCell_data_eq_of_eq_some state next tempDst mainSrc hhead)

theorem tempToMainCell_valuesMode_of_eq_some
    (state result : MergeState κ ν) (mainDst tempSrc : Int)
    (hmainMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data)
    (hentryMode : ∀ entry, mergeTempRead? state.a tempSrc = some entry →
      SortSlice.EntryMatchesValuesMode state.a.hasValues entry)
    (hcopy : tempToMainCell? state mainDst tempSrc = some result) :
    SortSlice.ValuesModeInvariant result.a.hasValues result.data := by
  rcases Option.bind_eq_some_iff.mp hcopy with ⟨entry, hread, htail⟩
  rcases Option.bind_eq_some_iff.mp htail with ⟨data, hwrite, hfinal⟩
  change some { state with data := data } = some result at hfinal
  injection hfinal with hfinal
  subst result
  exact hmainMode.write_preserved_of_eq_some (hentryMode entry hread) hwrite

/-- A temporary-to-main copy leaves the complete temporary store unchanged. -/
theorem tempToMainMemcpy_temp_eq_of_eq_some
    (count : Nat) (state result : MergeState κ ν)
    (mainDst tempSrc : Int)
    (hcopy : tempToMainMemcpy? count state mainDst tempSrc = some result) :
    result.a = state.a := by
  induction count generalizing state mainDst tempSrc with
  | zero =>
      simp only [tempToMainMemcpy?, Option.some.injEq] at hcopy
      subst result
      rfl
  | succ count ih =>
      simp only [tempToMainMemcpy?, bind, Option.bind] at hcopy
      split at hcopy <;> try contradiction
      rename_i next hhead
      exact (ih next (mainDst + 1) (tempSrc + 1) hcopy).trans
        (tempToMainCell_temp_eq_of_eq_some state next mainDst tempSrc hhead)

/-- Initialized, mode-correct temporary input preserves the main list's
values-mode invariant through a whole forward copy. -/
theorem tempToMainMemcpy_valuesMode_of_eq_some
    (count : Nat) (state result : MergeState κ ν)
    (mainDst tempSrc : Int)
    (hmainMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data)
    (htempMode : TempRangeValuesMode state.a tempSrc count)
    (hcopy : tempToMainMemcpy? count state mainDst tempSrc = some result) :
    SortSlice.ValuesModeInvariant result.a.hasValues result.data := by
  induction count generalizing state mainDst tempSrc with
  | zero =>
      simp only [tempToMainMemcpy?, Option.some.injEq] at hcopy
      subst result
      exact hmainMode
  | succ count ih =>
      simp only [tempToMainMemcpy?, bind, Option.bind] at hcopy
      split at hcopy <;> try contradiction
      rename_i next hhead
      rcases htempMode.head with ⟨entry, hread, hentryMode⟩
      have hentry : mergeTempRead? state.a tempSrc = some entry := by
        exact hread
      have hmodeNext := tempToMainCell_valuesMode_of_eq_some state next mainDst
        tempSrc hmainMode (fun other hother => by
          rw [hentry] at hother
          injection hother with hother
          subst other
          exact hentryMode) hhead
      have htempEq := tempToMainCell_temp_eq_of_eq_some state next mainDst tempSrc hhead
      have htailMode : TempRangeValuesMode next.a (tempSrc + 1) count := by
        simpa only [htempEq] using htempMode.tail
      exact ih next (mainDst + 1) (tempSrc + 1) hmodeNext htailMode hcopy

/-! ## Exact bulk phase order -/

theorem mainToTempMemcpyTraced_phase_order
    (site : MergeMemcpySite) (permit : site.MainToTempPermit) (count : Nat)
    (state : MergeState κ ν) (tempDst mainSrc : Int)
    (hkeys : ∃ keyResult,
      (mainToTempKeysTraced? site permit count state tempDst mainSrc).result =
        some keyResult) :
    (mainToTempMemcpyTraced? site permit count state tempDst mainSrc).trace.accesses =
      (mainToTempKeysTraced? site permit count state tempDst mainSrc).trace.accesses ++
        (if state.a.hasValues then
          (mainToTempValuesPhaseTraced? site permit count state tempDst
            mainSrc).trace.accesses
        else []) := by
  rcases hkeys with ⟨keyResult, hkeys⟩
  unfold mainToTempMemcpyTraced?
  rw [TraceResult.trace_bind, hkeys]
  cases hmode : state.a.hasValues <;>
    simp [AccessTrace.compose, TraceResult.pure, AccessTrace.empty]

theorem tempToMainMemcpyTraced_phase_order
    (site : MergeMemcpySite) (permit : site.TempToMainPermit) (count : Nat)
    (state : MergeState κ ν) (mainDst tempSrc : Int)
    (hkeys : ∃ keyResult,
      (tempToMainKeysTraced? site permit count state mainDst tempSrc).result =
        some keyResult) :
    (tempToMainMemcpyTraced? site permit count state mainDst tempSrc).trace.accesses =
      (tempToMainKeysTraced? site permit count state mainDst tempSrc).trace.accesses ++
        (if state.a.hasValues then
          (tempToMainValuesPhaseTraced? site permit count state mainDst
            tempSrc).trace.accesses
        else []) := by
  rcases hkeys with ⟨keyResult, hkeys⟩
  unfold tempToMainMemcpyTraced?
  rw [TraceResult.trace_bind, hkeys]
  cases hmode : state.a.hasValues <;>
    simp [AccessTrace.compose, TraceResult.pure, AccessTrace.empty]

/-! ## Non-vacuous event witnesses -/

private theorem mainToTempKeyTraced_events
    (state : MergeState κ ν) (tempDst mainSrc : Int)
    (hmain : SortSlice.IndexInBounds state.data mainSrc) :
    (mainToTempKeyTraced? state tempDst mainSrc).trace.HasAccess
        .read .inputKeys ∧
      (mainToTempKeyTraced? state tempDst mainSrc).trace.HasTempAccess .write := by
  rcases SortSlice.read_eq_some_of_indexInBounds state.data mainSrc hmain with
    ⟨entry, hread⟩
  have hreadTraced :
      (TraceResult.sortSliceKeysRead? state.data mainSrc).result = some entry := by
    change (TraceResult.sortSliceKeysRead? state.data mainSrc).erase = some entry
    simpa using hread
  unfold mainToTempKeyTraced?
  rw [TraceResult.trace_bind, hreadTraced]
  constructor
  · apply AccessTrace.HasAccess.compose_left
    refine ⟨AccessEvent.mk .read .inputKeys mainSrc state.data.entries.size,
      ?_, rfl, rfl⟩
    simp [TraceResult.trace_sortSliceKeysRead, AccessTrace.singletonAccess]
  · apply AccessTrace.HasTempAccess.compose_right
    change (TraceResult.tempPayloadWrite? state.a tempDst entry).trace.HasTempAccess
      .write
    refine ⟨state.a.backing, ?_⟩
    refine ⟨AccessEvent.mk .write (.tempPayload state.a.backing) tempDst
      state.a.cells.size, ?_, rfl, rfl⟩
    simp [TraceResult.trace_tempPayloadWrite, AccessTrace.singletonAccess]

private theorem mainToTempValuesTraced_event
    (state : MergeState κ ν) (tempDst mainSrc : Int)
    (hmain : SortSlice.IndexInBounds state.data mainSrc) :
    (mainToTempValuesTraced? state tempDst mainSrc).trace.HasAccess
      .read .synchronizedValues := by
  rcases SortSlice.read_eq_some_of_indexInBounds state.data mainSrc hmain with
    ⟨entry, hread⟩
  have hreadTraced :
      (TraceResult.sortSliceValuesRead? state.data mainSrc).result = some entry := by
    change (TraceResult.sortSliceValuesRead? state.data mainSrc).erase = some entry
    simpa using hread
  unfold mainToTempValuesTraced?
  rw [TraceResult.trace_bind, hreadTraced]
  apply AccessTrace.HasAccess.compose_left
  refine ⟨AccessEvent.mk .read .synchronizedValues mainSrc
    state.data.entries.size, ?_, rfl, rfl⟩
  simp [TraceResult.trace_sortSliceValuesRead, AccessTrace.singletonAccess]

private theorem tempToMainKeyTraced_events
    (state : MergeState κ ν) (mainDst tempSrc : Int)
    (hreadable : ∃ entry, mergeTempRead? state.a tempSrc = some entry) :
    (tempToMainKeyTraced? state mainDst tempSrc).trace.HasTempAccess .read ∧
      (tempToMainKeyTraced? state mainDst tempSrc).trace.HasAccess
        .write .inputKeys := by
  rcases hreadable with ⟨entry, hread⟩
  have hreadTraced :
      (TraceResult.tempPayloadRead? state.a tempSrc).result = some entry := by
    change (TraceResult.tempPayloadRead? state.a tempSrc).erase = some entry
    rw [erase_mergeTempRead]
    exact hread
  unfold tempToMainKeyTraced?
  rw [TraceResult.trace_bind, hreadTraced]
  constructor
  · apply AccessTrace.HasTempAccess.compose_left
    refine ⟨state.a.backing, ?_⟩
    refine ⟨AccessEvent.mk .read (.tempPayload state.a.backing) tempSrc
      state.a.cells.size, ?_, rfl, rfl⟩
    simp [TraceResult.trace_tempPayloadRead, AccessTrace.singletonAccess]
  · apply AccessTrace.HasAccess.compose_right
    change (TraceResult.sortSliceKeysWrite? state.data mainDst entry).trace.HasAccess
      .write .inputKeys
    refine ⟨AccessEvent.mk .write .inputKeys mainDst state.data.entries.size,
      ?_, rfl, rfl⟩
    simp [TraceResult.trace_sortSliceKeysWrite, AccessTrace.singletonAccess]

private theorem tempToMainValuesTraced_event
    (state : MergeState κ ν) (mainDst tempSrc : Int)
    (hreadable : ∃ entry, mergeTempRead? state.a tempSrc = some entry) :
    (tempToMainValuesTraced? state mainDst tempSrc).trace.HasAccess
      .write .synchronizedValues := by
  rcases hreadable with ⟨entry, hread⟩
  have hreadTraced :
      (TraceResult.tempPayloadRead? state.a tempSrc).result = some entry := by
    change (TraceResult.tempPayloadRead? state.a tempSrc).erase = some entry
    rw [erase_mergeTempRead]
    exact hread
  unfold tempToMainValuesTraced?
  rw [TraceResult.trace_bind, hreadTraced]
  apply AccessTrace.HasAccess.compose_right
  change (TraceResult.sortSliceValuesWrite? state.data mainDst entry).trace.HasAccess
    .write .synchronizedValues
  refine ⟨AccessEvent.mk .write .synchronizedValues mainDst state.data.entries.size,
    ?_, rfl, rfl⟩
  simp [TraceResult.trace_sortSliceValuesWrite, AccessTrace.singletonAccess]

private theorem mainToTempKeysTraced_first_events
    (site : MergeMemcpySite) (permit : site.MainToTempPermit) (count : Nat)
    (state : MergeState κ ν) (tempDst mainSrc : Int)
    (htemp : TempRangeInBounds state.a tempDst (count + 1))
    (hmain : SortSlice.RangeInBounds state.data mainSrc (count + 1)) :
    (mainToTempKeysTraced? site permit (count + 1) state tempDst mainSrc).trace.HasAccess
        .read .inputKeys ∧
      (mainToTempKeysTraced? site permit (count + 1) state tempDst
        mainSrc).trace.HasTempAccess .write := by
  rcases mainToTempCell_eq_some_of_bounds state tempDst mainSrc htemp.head
      hmain.head with ⟨next, hcell⟩
  have hcellResult :
      (mainToTempKeyTraced? state tempDst mainSrc).result = some next := by
    change (mainToTempKeyTraced? state tempDst mainSrc).erase = some next
    rw [erase_mainToTempKeyTraced]
    exact hcell
  simp only [mainToTempKeysTraced?, TraceResult.trace_bind, hcellResult]
  rcases mainToTempKeyTraced_events state tempDst mainSrc hmain.head with
    ⟨hread, hwrite⟩
  exact ⟨hread.compose_left, hwrite.compose_left⟩

private theorem mainToTempValuesPhaseTraced_first_event
    (site : MergeMemcpySite) (permit : site.MainToTempPermit) (count : Nat)
    (state : MergeState κ ν) (tempDst mainSrc : Int)
    (htemp : TempRangeInBounds state.a tempDst (count + 1))
    (hmain : SortSlice.RangeInBounds state.data mainSrc (count + 1)) :
    (mainToTempValuesPhaseTraced? site permit (count + 1) state tempDst
      mainSrc).trace.HasAccess .read .synchronizedValues := by
  rcases mainToTempCell_eq_some_of_bounds state tempDst mainSrc htemp.head
      hmain.head with ⟨next, hcell⟩
  have hcellResult :
      (mainToTempValuesTraced? state tempDst mainSrc).result = some next := by
    change (mainToTempValuesTraced? state tempDst mainSrc).erase = some next
    rw [erase_mainToTempValuesTraced]
    exact hcell
  simp only [mainToTempValuesPhaseTraced?, TraceResult.trace_bind, hcellResult]
  exact (mainToTempValuesTraced_event state tempDst mainSrc hmain.head).compose_left

/-- Every nonempty valid main-to-temporary bulk execution has concrete main
key and temporary-write events.  Values mode additionally witnesses the
synchronized-values phase. -/
theorem mainToTempMemcpyTraced_events
    (site : MergeMemcpySite) (permit : site.MainToTempPermit) (count : Nat)
    (state : MergeState κ ν) (tempDst mainSrc : Int)
    (htemp : TempRangeInBounds state.a tempDst (count + 1))
    (hmain : SortSlice.RangeInBounds state.data mainSrc (count + 1))
    (hlive : state.a.Live) :
    (mainToTempMemcpyTraced? site permit (count + 1) state tempDst
        mainSrc).trace.HasAccess .read .inputKeys ∧
      (mainToTempMemcpyTraced? site permit (count + 1) state tempDst
        mainSrc).trace.HasTempAccess .write ∧
      (state.a.hasValues = true →
        (mainToTempMemcpyTraced? site permit (count + 1) state tempDst
          mainSrc).trace.HasAccess .read .synchronizedValues) := by
  rcases mainToTempKeysTraced_safe_of_ranges site permit (count + 1) state
      tempDst mainSrc htemp hmain hlive with ⟨keyResult, hkeys, _, _⟩
  have htrace :
      (mainToTempMemcpyTraced? site permit (count + 1) state tempDst
        mainSrc).trace =
      (mainToTempKeysTraced? site permit (count + 1) state tempDst
        mainSrc).trace.compose
        (if state.a.hasValues then
          (mainToTempValuesPhaseTraced? site permit (count + 1) state tempDst
            mainSrc).trace
        else (TraceResult.pure keyResult).trace) := by
    cases hmode : state.a.hasValues <;>
      simp [mainToTempMemcpyTraced?, TraceResult.trace_bind, hkeys, hmode]
  rw [htrace]
  rcases mainToTempKeysTraced_first_events site permit count state tempDst
      mainSrc htemp hmain with ⟨hread, hwrite⟩
  refine ⟨hread.compose_left, hwrite.compose_left, ?_⟩
  intro hmode
  simp only [hmode, ↓reduceIte]
  exact (mainToTempValuesPhaseTraced_first_event site permit count state tempDst
    mainSrc htemp hmain).compose_right

private theorem tempToMainKeysTraced_first_events
    (site : MergeMemcpySite) (permit : site.TempToMainPermit) (count : Nat)
    (state : MergeState κ ν) (mainDst tempSrc : Int)
    (hmain : SortSlice.RangeInBounds state.data mainDst (count + 1))
    (hinitialized : TempRangeInitialized state.a tempSrc (count + 1)) :
    (tempToMainKeysTraced? site permit (count + 1) state mainDst
        tempSrc).trace.HasTempAccess .read ∧
      (tempToMainKeysTraced? site permit (count + 1) state mainDst
        tempSrc).trace.HasAccess .write .inputKeys := by
  have hreadable := hinitialized.head
  rcases tempToMainCell_eq_some_of_bounds state mainDst tempSrc hmain.head
      hreadable with ⟨next, hcell⟩
  have hcellResult :
      (tempToMainKeyTraced? state mainDst tempSrc).result = some next := by
    change (tempToMainKeyTraced? state mainDst tempSrc).erase = some next
    rw [erase_tempToMainKeyTraced]
    exact hcell
  simp only [tempToMainKeysTraced?, TraceResult.trace_bind, hcellResult]
  rcases tempToMainKeyTraced_events state mainDst tempSrc hreadable with
    ⟨hread, hwrite⟩
  exact ⟨hread.compose_left, hwrite.compose_left⟩

private theorem tempToMainValuesPhaseTraced_first_event
    (site : MergeMemcpySite) (permit : site.TempToMainPermit) (count : Nat)
    (state : MergeState κ ν) (mainDst tempSrc : Int)
    (hmain : SortSlice.RangeInBounds state.data mainDst (count + 1))
    (hinitialized : TempRangeInitialized state.a tempSrc (count + 1)) :
    (tempToMainValuesPhaseTraced? site permit (count + 1) state mainDst
      tempSrc).trace.HasAccess .write .synchronizedValues := by
  have hreadable := hinitialized.head
  rcases tempToMainCell_eq_some_of_bounds state mainDst tempSrc hmain.head
      hreadable with ⟨next, hcell⟩
  have hcellResult :
      (tempToMainValuesTraced? state mainDst tempSrc).result = some next := by
    change (tempToMainValuesTraced? state mainDst tempSrc).erase = some next
    rw [erase_tempToMainValuesTraced]
    exact hcell
  simp only [tempToMainValuesPhaseTraced?, TraceResult.trace_bind, hcellResult]
  exact (tempToMainValuesTraced_event state mainDst tempSrc hreadable).compose_left

/-- Every nonempty valid temporary-to-main bulk execution has concrete
temporary-read and main-key-write events, plus a synchronized-values write in
values mode. -/
theorem tempToMainMemcpyTraced_events
    (site : MergeMemcpySite) (permit : site.TempToMainPermit) (count : Nat)
    (state : MergeState κ ν) (mainDst tempSrc : Int)
    (hmain : SortSlice.RangeInBounds state.data mainDst (count + 1))
    (htemp : TempRangeInBounds state.a tempSrc (count + 1))
    (hinitialized : TempRangeInitialized state.a tempSrc (count + 1))
    (hlive : state.a.Live) :
    (tempToMainMemcpyTraced? site permit (count + 1) state mainDst
        tempSrc).trace.HasTempAccess .read ∧
      (tempToMainMemcpyTraced? site permit (count + 1) state mainDst
        tempSrc).trace.HasAccess .write .inputKeys ∧
      (state.a.hasValues = true →
        (tempToMainMemcpyTraced? site permit (count + 1) state mainDst
          tempSrc).trace.HasAccess .write .synchronizedValues) := by
  rcases tempToMainKeysTraced_safe_of_ranges site permit (count + 1) state
      mainDst tempSrc hmain htemp hinitialized hlive with
    ⟨keyResult, hkeys, _, _⟩
  have htrace :
      (tempToMainMemcpyTraced? site permit (count + 1) state mainDst
        tempSrc).trace =
      (tempToMainKeysTraced? site permit (count + 1) state mainDst
        tempSrc).trace.compose
        (if state.a.hasValues then
          (tempToMainValuesPhaseTraced? site permit (count + 1) state mainDst
            tempSrc).trace
        else (TraceResult.pure keyResult).trace) := by
    cases hmode : state.a.hasValues <;>
      simp [tempToMainMemcpyTraced?, TraceResult.trace_bind, hkeys, hmode]
  rw [htrace]
  rcases tempToMainKeysTraced_first_events site permit count state mainDst
      tempSrc hmain hinitialized with ⟨hread, hwrite⟩
  refine ⟨hread.compose_left, hwrite.compose_left, ?_⟩
  intro hmode
  simp only [hmode, ↓reduceIte]
  exact (tempToMainValuesPhaseTraced_first_event site permit count state mainDst
    tempSrc hmain hinitialized).compose_right

/-! ## Public aggregate bulk contracts -/

structure MainToTempMemcpyPost
    (site : MergeMemcpySite) (permit : site.MainToTempPermit) (count : Nat)
    (state result : MergeState κ ν) (tempDst mainSrc : Int) : Prop where
  success :
    (mainToTempMemcpyTraced? site permit count state tempDst mainSrc).result =
      some result
  traceSafe :
    MovementTraceSafe
      (mainToTempMemcpyTraced? site permit count state tempDst mainSrc)
  exactErasure :
    (mainToTempMemcpyTraced? site permit count state tempDst mainSrc).erase =
      mainToTempMemcpy? count state tempDst mainSrc
  frame : MergeMovementFrame state result
  tempInvariant : TempStorageInv result.a result.alloced
  tempLive : result.a.Live
  valuesMode : SortSlice.ValuesModeInvariant result.a.hasValues result.data
  initialized : TempRangeInitialized result.a tempDst count
  tempValuesMode : TempRangeValuesMode result.a tempDst count
  provenance : site.backings.Distinct
  /-- The complete generic `sortslice_memcpy` safety boundary used by this
  classified call site: distinct backing is admissible, while an overlapping
  same-backing request is rejected with an empty trace. -/
  provenanceContract : MergeMemcpyCallsiteProvenanceContract κ ν
  phaseOrder :
    (mainToTempMemcpyTraced? site permit count state tempDst mainSrc).trace.accesses =
      (mainToTempKeysTraced? site permit count state tempDst mainSrc).trace.accesses ++
        (if state.a.hasValues then
          (mainToTempValuesPhaseTraced? site permit count state tempDst
            mainSrc).trace.accesses
        else [])
  inputKeyEvent : 0 < count →
    (mainToTempMemcpyTraced? site permit count state tempDst
      mainSrc).trace.HasAccess .read .inputKeys
  tempWriteEvent : 0 < count →
    (mainToTempMemcpyTraced? site permit count state tempDst
      mainSrc).trace.HasTempAccess .write
  synchronizedValuesEvent : 0 < count → state.a.hasValues = true →
    (mainToTempMemcpyTraced? site permit count state tempDst
      mainSrc).trace.HasAccess .read .synchronizedValues
  nonempty : 0 < count →
    (mainToTempMemcpyTraced? site permit count state tempDst
      mainSrc).trace.accesses ≠ []

theorem mainToTempMemcpyTraced_post
    (site : MergeMemcpySite) (permit : site.MainToTempPermit) (count : Nat)
    (state : MergeState κ ν) (tempDst mainSrc : Int)
    (htemp : TempRangeInBounds state.a tempDst count)
    (hmain : SortSlice.RangeInBounds state.data mainSrc count)
    (hinvariant : TempStorageInv state.a state.alloced)
    (hlive : state.a.Live)
    (hmode : SortSlice.ValuesModeInvariant state.a.hasValues state.data) :
    ∃ result,
      MainToTempMemcpyPost site permit count state result tempDst mainSrc := by
  rcases mainToTempMemcpyTraced_safe site permit count state tempDst mainSrc
      htemp hmain hlive with ⟨result, hresult, htraceSafe, hframe⟩
  have hcopy : mainToTempMemcpy? count state tempDst mainSrc = some result := by
    rw [← erase_mainToTempMemcpyTraced site permit count state tempDst mainSrc]
    exact hresult
  have htempMode := mainToTempMemcpy_valuesMode_of_eq_some count state result
    tempDst mainSrc hmode hcopy
  have hdataEq := mainToTempMemcpy_data_eq_of_eq_some count state result tempDst
    mainSrc hcopy
  have hresultMode :
      SortSlice.ValuesModeInvariant result.a.hasValues result.data := by
    simpa only [hframe.tempValuesMode, hdataEq] using hmode
  have hkeys : ∃ keyResult,
      (mainToTempKeysTraced? site permit count state tempDst mainSrc).result =
        some keyResult := by
    refine ⟨result, ?_⟩
    change (mainToTempKeysTraced? site permit count state tempDst mainSrc).erase =
      some result
    rw [erase_mainToTempKeysTraced]
    exact hcopy
  have hphase := mainToTempMemcpyTraced_phase_order site permit count state tempDst
    mainSrc hkeys
  refine ⟨result, ?_⟩
  refine
    { success := hresult
      traceSafe := htraceSafe
      exactErasure := erase_mainToTempMemcpyTraced site permit count state tempDst mainSrc
      frame := hframe
      tempInvariant := hframe.tempStorageInv hinvariant
      tempLive := hframe.live hlive
      valuesMode := hresultMode
      initialized := htempMode.initialized
      tempValuesMode := htempMode
      provenance := permit.distinctBacking
      provenanceContract := mergeMemcpyCallsiteProvenance
      phaseOrder := hphase
      inputKeyEvent := ?_
      tempWriteEvent := ?_
      synchronizedValuesEvent := ?_
      nonempty := ?_ }
  · intro hpositive
    cases count with
    | zero => omega
    | succ tail =>
        exact (mainToTempMemcpyTraced_events site permit tail state tempDst
          mainSrc htemp hmain hlive).1
  · intro hpositive
    cases count with
    | zero => omega
    | succ tail =>
        exact (mainToTempMemcpyTraced_events site permit tail state tempDst
          mainSrc htemp hmain hlive).2.1
  · intro hpositive hvalues
    cases count with
    | zero => omega
    | succ tail =>
        exact (mainToTempMemcpyTraced_events site permit tail state tempDst
          mainSrc htemp hmain hlive).2.2 hvalues
  · intro hpositive
    apply AccessTrace.HasAccess.accesses_ne_nil
    cases count with
    | zero => omega
    | succ tail =>
        exact (mainToTempMemcpyTraced_events site permit tail state tempDst
          mainSrc htemp hmain hlive).1

structure TempToMainMemcpyPost
    (site : MergeMemcpySite) (permit : site.TempToMainPermit) (count : Nat)
    (state result : MergeState κ ν) (mainDst tempSrc : Int) : Prop where
  success :
    (tempToMainMemcpyTraced? site permit count state mainDst tempSrc).result =
      some result
  traceSafe :
    MovementTraceSafe
      (tempToMainMemcpyTraced? site permit count state mainDst tempSrc)
  exactErasure :
    (tempToMainMemcpyTraced? site permit count state mainDst tempSrc).erase =
      tempToMainMemcpy? count state mainDst tempSrc
  frame : MergeMovementFrame state result
  tempInvariant : TempStorageInv result.a result.alloced
  tempLive : result.a.Live
  valuesMode : SortSlice.ValuesModeInvariant result.a.hasValues result.data
  initialized : TempRangeInitialized result.a tempSrc count
  tempValuesMode : TempRangeValuesMode result.a tempSrc count
  provenance : site.backings.Distinct
  /-- The complete generic `sortslice_memcpy` safety boundary used by this
  classified call site: distinct backing is admissible, while an overlapping
  same-backing request is rejected with an empty trace. -/
  provenanceContract : MergeMemcpyCallsiteProvenanceContract κ ν
  phaseOrder :
    (tempToMainMemcpyTraced? site permit count state mainDst tempSrc).trace.accesses =
      (tempToMainKeysTraced? site permit count state mainDst tempSrc).trace.accesses ++
        (if state.a.hasValues then
          (tempToMainValuesPhaseTraced? site permit count state mainDst
            tempSrc).trace.accesses
        else [])
  tempReadEvent : 0 < count →
    (tempToMainMemcpyTraced? site permit count state mainDst
      tempSrc).trace.HasTempAccess .read
  inputKeyEvent : 0 < count →
    (tempToMainMemcpyTraced? site permit count state mainDst
      tempSrc).trace.HasAccess .write .inputKeys
  synchronizedValuesEvent : 0 < count → state.a.hasValues = true →
    (tempToMainMemcpyTraced? site permit count state mainDst
      tempSrc).trace.HasAccess .write .synchronizedValues
  nonempty : 0 < count →
    (tempToMainMemcpyTraced? site permit count state mainDst
      tempSrc).trace.accesses ≠ []

theorem tempToMainMemcpyTraced_post
    (site : MergeMemcpySite) (permit : site.TempToMainPermit) (count : Nat)
    (state : MergeState κ ν) (mainDst tempSrc : Int)
    (hmain : SortSlice.RangeInBounds state.data mainDst count)
    (htemp : TempRangeInBounds state.a tempSrc count)
    (htempMode : TempRangeValuesMode state.a tempSrc count)
    (hinvariant : TempStorageInv state.a state.alloced)
    (hlive : state.a.Live)
    (hmainMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data) :
    ∃ result,
      TempToMainMemcpyPost site permit count state result mainDst tempSrc := by
  rcases tempToMainMemcpyTraced_safe site permit count state mainDst tempSrc
      hmain htemp htempMode.initialized hlive with
    ⟨result, hresult, htraceSafe, hframe⟩
  have hcopy : tempToMainMemcpy? count state mainDst tempSrc = some result := by
    rw [← erase_tempToMainMemcpyTraced site permit count state mainDst tempSrc]
    exact hresult
  have htempEq := tempToMainMemcpy_temp_eq_of_eq_some count state result mainDst
    tempSrc hcopy
  have hresultMode := tempToMainMemcpy_valuesMode_of_eq_some count state result
    mainDst tempSrc hmainMode htempMode hcopy
  have hresultTempMode : TempRangeValuesMode result.a tempSrc count := by
    simpa only [htempEq] using htempMode
  have hkeys : ∃ keyResult,
      (tempToMainKeysTraced? site permit count state mainDst tempSrc).result =
        some keyResult := by
    refine ⟨result, ?_⟩
    change (tempToMainKeysTraced? site permit count state mainDst tempSrc).erase =
      some result
    rw [erase_tempToMainKeysTraced]
    exact hcopy
  have hphase := tempToMainMemcpyTraced_phase_order site permit count state mainDst
    tempSrc hkeys
  refine ⟨result, ?_⟩
  refine
    { success := hresult
      traceSafe := htraceSafe
      exactErasure := erase_tempToMainMemcpyTraced site permit count state mainDst tempSrc
      frame := hframe
      tempInvariant := hframe.tempStorageInv hinvariant
      tempLive := hframe.live hlive
      valuesMode := hresultMode
      initialized := hresultTempMode.initialized
      tempValuesMode := hresultTempMode
      provenance := permit.distinctBacking
      provenanceContract := mergeMemcpyCallsiteProvenance
      phaseOrder := hphase
      tempReadEvent := ?_
      inputKeyEvent := ?_
      synchronizedValuesEvent := ?_
      nonempty := ?_ }
  · intro hpositive
    cases count with
    | zero => omega
    | succ tail =>
        exact (tempToMainMemcpyTraced_events site permit tail state mainDst
          tempSrc hmain htemp htempMode.initialized hlive).1
  · intro hpositive
    cases count with
    | zero => omega
    | succ tail =>
        exact (tempToMainMemcpyTraced_events site permit tail state mainDst
          tempSrc hmain htemp htempMode.initialized hlive).2.1
  · intro hpositive hvalues
    cases count with
    | zero => omega
    | succ tail =>
        exact (tempToMainMemcpyTraced_events site permit tail state mainDst
          tempSrc hmain htemp htempMode.initialized hlive).2.2 hvalues
  · intro hpositive
    apply AccessTrace.HasAccess.accesses_ne_nil
    cases count with
    | zero => omega
    | succ tail =>
        exact (tempToMainMemcpyTraced_events site permit tail state mainDst
          tempSrc hmain htemp htempMode.initialized hlive).2.1

/-! ## Main-data memmove aggregate contract -/

private def MovementTempLive (execution : TraceResult α) : Prop :=
  execution.trace.tempPayloadAccessesLive

namespace MovementTempLive

theorem pure (value : α) : MovementTempLive (TraceResult.pure value) :=
  AccessTrace.tempPayloadAccessesLive_empty

theorem map (current : TraceResult α) (transform : α → β)
    (h : MovementTempLive current) : MovementTempLive (current.map transform) := by
  exact h

theorem bind (current : TraceResult α) (next : α → TraceResult β)
    (hcurrent : MovementTempLive current)
    (hnext : ∀ value, MovementTempLive (next value)) :
    MovementTempLive (current.bind next) := by
  cases hresult : current.result with
  | none => simpa [MovementTempLive, TraceResult.trace_bind, hresult] using hcurrent
  | some value =>
      rw [MovementTempLive, TraceResult.trace_bind, hresult,
        AccessTrace.tempPayloadAccessesLive_compose]
      exact ⟨hcurrent, hnext value⟩

end MovementTempLive

private theorem keyRead_tempLive (slice : SortSlice κ ν) (index : Int) :
    MovementTempLive (TraceResult.sortSliceKeysRead? slice index) := by
  simp [MovementTempLive, TraceResult.trace_sortSliceKeysRead,
    AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
    AccessEvent.TempPayloadLive]

private theorem valuesRead_tempLive (slice : SortSlice κ ν) (index : Int) :
    MovementTempLive (TraceResult.sortSliceValuesRead? slice index) := by
  simp [MovementTempLive, TraceResult.trace_sortSliceValuesRead,
    AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
    AccessEvent.TempPayloadLive]

private theorem keyWrite_tempLive (slice : SortSlice κ ν) (index : Int)
    (entry : SortSliceEntry κ ν) :
    MovementTempLive (TraceResult.sortSliceKeysWrite? slice index entry) := by
  simp [MovementTempLive, TraceResult.trace_sortSliceKeysWrite,
    AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
    AccessEvent.TempPayloadLive]

private theorem valuesWrite_tempLive (slice : SortSlice κ ν) (index : Int)
    (entry : SortSliceEntry κ ν) :
    MovementTempLive (TraceResult.sortSliceValuesWrite? slice index entry) := by
  simp [MovementTempLive, TraceResult.trace_sortSliceValuesWrite,
    AccessTrace.tempPayloadAccessesLive, AccessTrace.singletonAccess,
    AccessEvent.TempPayloadLive]

private theorem copyKeysFrom_tempLive (destination source : SortSlice κ ν)
    (dst src : Int) :
    MovementTempLive (SortSlice.copyKeysFromTraced? destination source dst src) := by
  apply MovementTempLive.bind
  · exact keyRead_tempLive source src
  · intro entry
    exact keyWrite_tempLive destination dst entry

private theorem copyValuesFrom_tempLive (destination source : SortSlice κ ν)
    (dst src : Int) :
    MovementTempLive (SortSlice.copyValuesFromTraced? destination source dst src) := by
  apply MovementTempLive.bind
  · exact valuesRead_tempLive source src
  · intro entry
    exact valuesWrite_tempLive destination dst entry

private theorem memmoveForwardKeys_tempLive (count : Nat)
    (slice : SortSlice κ ν) (dst src : Int) :
    MovementTempLive (SortSlice.memmoveForwardKeysTraced? count slice dst src) := by
  induction count generalizing slice dst src with
  | zero => exact MovementTempLive.pure slice
  | succ count ih =>
      apply MovementTempLive.bind
      · exact copyKeysFrom_tempLive slice slice dst src
      · intro updated
        exact ih updated (dst + 1) (src + 1)

private theorem memmoveForwardValues_tempLive (count : Nat)
    (slice : SortSlice κ ν) (dst src : Int) :
    MovementTempLive (SortSlice.memmoveForwardValuesTraced? count slice dst src) := by
  induction count generalizing slice dst src with
  | zero => exact MovementTempLive.pure slice
  | succ count ih =>
      apply MovementTempLive.bind
      · exact copyValuesFrom_tempLive slice slice dst src
      · intro updated
        exact ih updated (dst + 1) (src + 1)

private theorem memmoveBackwardKeys_tempLive (count : Nat)
    (slice : SortSlice κ ν) (dst src : Int) :
    MovementTempLive (SortSlice.memmoveBackwardKeysTraced? count slice dst src) := by
  induction count generalizing slice dst src with
  | zero => exact MovementTempLive.pure slice
  | succ count ih =>
      apply MovementTempLive.bind
      · exact copyKeysFrom_tempLive slice slice (dst + Int.ofNat count)
          (src + Int.ofNat count)
      · intro updated
        exact ih updated dst src

private theorem memmoveBackwardValues_tempLive (count : Nat)
    (slice : SortSlice κ ν) (dst src : Int) :
    MovementTempLive (SortSlice.memmoveBackwardValuesTraced? count slice dst src) := by
  induction count generalizing slice dst src with
  | zero => exact MovementTempLive.pure slice
  | succ count ih =>
      apply MovementTempLive.bind
      · exact copyValuesFrom_tempLive slice slice (dst + Int.ofNat count)
          (src + Int.ofNat count)
      · intro updated
        exact ih updated dst src

private theorem sortSliceMemmove_tempLive (valuesPresent : Bool)
    (slice : SortSlice κ ν) (dst src : Int) (count : Nat) :
    MovementTempLive
      (SortSlice.memmoveTraced? valuesPresent slice dst src count) := by
  cases hdirection : SortSlice.memmoveDirection dst src with
  | forward =>
      simp only [SortSlice.memmoveTraced?, hdirection]
      apply MovementTempLive.bind
      · exact memmoveForwardKeys_tempLive count slice dst src
      · intro keyResult
        cases hvalues : valuesPresent with
        | false => simp only [Bool.false_eq]
                   exact MovementTempLive.pure keyResult
        | true => simp only [↓reduceIte]
                  exact memmoveForwardValues_tempLive count slice dst src
  | backward =>
      simp only [SortSlice.memmoveTraced?, hdirection]
      apply MovementTempLive.bind
      · exact memmoveBackwardKeys_tempLive count slice dst src
      · intro keyResult
        cases hvalues : valuesPresent with
        | false => simp only [Bool.false_eq]
                   exact MovementTempLive.pure keyResult
        | true => simp only [↓reduceIte]
                  exact memmoveBackwardValues_tempLive count slice dst src

/-! ## Main-data one-cell decrement copy -/

/-- State-level wrapper around the shared-store decrementing copy.  Cursor
arithmetic is signed, so copying cell zero legitimately returns `-1`. -/
def mainDataCopyDecrTraced? (state : MergeState κ ν) (dst src : Int) :
    TraceResult (MergeHiDataCursorResult κ ν) :=
  (SortSlice.copyDecrTraced? state.a.hasValues state.data dst src).map
    fun copied =>
      { state := { state with data := copied.slice }
        dst := copied.dst
        src := copied.src }

@[simp]
theorem erase_mainDataCopyDecrTraced (state : MergeState κ ν)
    (dst src : Int) :
    (mainDataCopyDecrTraced? state dst src).erase =
      mergeHiCopyDataDecr? state dst src := by
  rw [mainDataCopyDecrTraced?, TraceResult.erase_map,
    SortSlice.erase_copyDecrTraced]
  cases hcopy : state.data.copyDecr? dst src <;>
    simp [mergeHiCopyDataDecr?, hcopy]

private theorem sortSliceCopyFrom_accessOnly (valuesPresent : Bool)
    (destination source : SortSlice κ ν) (dst src : Int) :
    MovementAccessOnly
      (SortSlice.copyFromTraced? valuesPresent destination source dst src) := by
  apply MovementAccessOnly.bind
  · exact copyKeysFrom_accessOnly destination source dst src
  · intro keyResult
    cases valuesPresent with
    | false => exact MovementAccessOnly.pure keyResult
    | true => exact copyValuesFrom_accessOnly destination source dst src

private theorem sortSliceCopyFrom_tempLive (valuesPresent : Bool)
    (destination source : SortSlice κ ν) (dst src : Int) :
    MovementTempLive
      (SortSlice.copyFromTraced? valuesPresent destination source dst src) := by
  apply MovementTempLive.bind
  · exact copyKeysFrom_tempLive destination source dst src
  · intro keyResult
    cases valuesPresent with
    | false => exact MovementTempLive.pure keyResult
    | true => exact copyValuesFrom_tempLive destination source dst src

structure MainDataCopyDecrPost (state : MergeState κ ν) (dst src : Int)
    (result : MergeHiDataCursorResult κ ν) : Prop where
  success : (mainDataCopyDecrTraced? state dst src).result = some result
  traceSafe : MovementTraceSafe (mainDataCopyDecrTraced? state dst src)
  exactErasure : (mainDataCopyDecrTraced? state dst src).erase =
    mergeHiCopyDataDecr? state dst src
  frame : MergeMovementFrame state result.state
  tempInvariant : TempStorageInv result.state.a result.state.alloced
  tempLive : result.state.a.Live
  valuesMode :
    SortSlice.ValuesModeInvariant result.state.a.hasValues result.state.data
  dstDecrement : result.dst = dst - 1
  srcDecrement : result.src = src - 1

/-- A single main-to-main decrementing copy needs only bounds for the two
dereferences.  No cursor-positivity premise is imposed: after copying index
zero the exact signed post-cursor is the legal sentinel `-1`. -/
theorem mainDataCopyDecrTraced_safe (state : MergeState κ ν)
    (dst src : Int)
    (hinvariant : TempStorageInv state.a state.alloced)
    (hlive : state.a.Live)
    (hmode : SortSlice.ValuesModeInvariant state.a.hasValues state.data)
    (hdst : SortSlice.IndexInBounds state.data dst)
    (hsrc : SortSlice.IndexInBounds state.data src) :
    ∃ result, MainDataCopyDecrPost state dst src result := by
  rcases SortSlice.copyFromTraced_mode_safe state.a.hasValues state.data
      state.data dst src hmode hmode hdst hsrc with
    ⟨updated, hcopy, hbounds, hsize, hupdatedMode⟩
  let copied : SortSlice.CursorResult κ ν :=
    { slice := updated, dst := dst - 1, src := src - 1 }
  have hcopied :
      (SortSlice.copyDecrTraced? state.a.hasValues state.data dst src).result =
        some copied := by
    simp [SortSlice.copyDecrTraced?, SortSlice.copyFromDecrTraced?,
      TraceResult.map, hcopy, copied]
  let result : MergeHiDataCursorResult κ ν :=
    { state := { state with data := updated }
      dst := dst - 1
      src := src - 1 }
  have hresult :
      (mainDataCopyDecrTraced? state dst src).result = some result := by
    simp [mainDataCopyDecrTraced?, TraceResult.map, hcopied, result, copied]
  have haccessOnly := sortSliceCopyFrom_accessOnly state.a.hasValues state.data
    state.data dst src
  have htempAccessLive := sortSliceCopyFrom_tempLive state.a.hasValues state.data
    state.data dst src
  have htraceSafe : MovementTraceSafe (mainDataCopyDecrTraced? state dst src) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [mainDataCopyDecrTraced?, SortSlice.copyDecrTraced?,
        SortSlice.copyFromDecrTraced?, TraceResult.map,
        MovementAccessOnly] using haccessOnly.1
    · simpa [mainDataCopyDecrTraced?, SortSlice.copyDecrTraced?,
        SortSlice.copyFromDecrTraced?, TraceResult.map,
        MovementAccessOnly] using haccessOnly.2
    · simpa [mainDataCopyDecrTraced?, SortSlice.copyDecrTraced?,
        SortSlice.copyFromDecrTraced?, TraceResult.map] using hbounds
    · simpa [mainDataCopyDecrTraced?, SortSlice.copyDecrTraced?,
        SortSlice.copyFromDecrTraced?, TraceResult.map,
        MovementTempLive] using htempAccessLive
  have hframe : MergeMovementFrame state result.state := by
    dsimp [result]
    constructor <;> try rfl
    exact hsize
  have hresultMode :
      SortSlice.ValuesModeInvariant result.state.a.hasValues result.state.data := by
    exact hupdatedMode
  exact ⟨result,
    { success := hresult
      traceSafe := htraceSafe
      exactErasure := erase_mainDataCopyDecrTraced state dst src
      frame := hframe
      tempInvariant := hframe.tempStorageInv hinvariant
      tempLive := hframe.live hlive
      valuesMode := hresultMode
      dstDecrement := by rfl
      srcDecrement := by rfl }⟩

structure MainDataMemmovePost (state result : MergeState κ ν)
    (dst src : Int) (count : Nat) : Prop where
  success : (mainDataMemmoveTraced? state dst src count).result = some result
  traceSafe : MovementTraceSafe (mainDataMemmoveTraced? state dst src count)
  exactErasure : (mainDataMemmoveTraced? state dst src count).erase =
    mainDataMemmove? state dst src count
  frame : MergeMovementFrame state result
  tempInvariant : TempStorageInv result.a result.alloced
  tempLive : result.a.Live
  valuesMode : SortSlice.ValuesModeInvariant result.a.hasValues result.data
  phaseOrder :
    (mainDataMemmoveTraced? state dst src count).trace.accesses =
      match SortSlice.memmoveDirection dst src with
      | .forward =>
          (SortSlice.memmoveForwardKeysTraced? count state.data dst
            src).trace.accesses ++
            if state.a.hasValues then
              (SortSlice.memmoveForwardValuesTraced? count state.data dst
                src).trace.accesses
            else []
      | .backward =>
          (SortSlice.memmoveBackwardKeysTraced? count state.data dst
            src).trace.accesses ++
            if state.a.hasValues then
              (SortSlice.memmoveBackwardValuesTraced? count state.data dst
                src).trace.accesses
            else []

/-- Total, bounds-safe, live, mode-preserving state wrapper around the
overlap-safe `SortSlice.memmoveTraced?` contract. -/
theorem mainDataMemmoveTraced_safe (state : MergeState κ ν)
    (dst src : Int) (count : Nat)
    (hinvariant : TempStorageInv state.a state.alloced)
    (hlive : state.a.Live)
    (hmode : SortSlice.ValuesModeInvariant state.a.hasValues state.data)
    (hdst : SortSlice.RangeInBounds state.data dst count)
    (hsrc : SortSlice.RangeInBounds state.data src count) :
    ∃ result, MainDataMemmovePost state result dst src count := by
  rcases SortSlice.memmoveTraced_mode_safe state.a.hasValues state.data dst src
      count hmode hdst hsrc with ⟨data, hdataResult, hbounds, hsize, hdataMode⟩
  let result : MergeState κ ν := { state with data := data }
  have hresult :
      (mainDataMemmoveTraced? state dst src count).result = some result := by
    simp [mainDataMemmoveTraced?, TraceResult.map, hdataResult, result]
  have hframe := mainDataMemmoveTraced_frame state result dst src count hresult
  have haccessOnly := mainDataMemmoveTraced_accessOnly state dst src count
  have htempAccessLive :
      (mainDataMemmoveTraced? state dst src count).trace.tempPayloadAccessesLive := by
    exact sortSliceMemmove_tempLive state.a.hasValues state.data dst src count
  have htraceSafe :
      MovementTraceSafe (mainDataMemmoveTraced? state dst src count) :=
    ⟨haccessOnly.1, haccessOnly.2, hbounds, htempAccessLive⟩
  have hresultMode :
      SortSlice.ValuesModeInvariant result.a.hasValues result.data := by
    exact hdataMode
  refine ⟨result,
    { success := hresult
      traceSafe := htraceSafe
      exactErasure := erase_mainDataMemmoveTraced state dst src count
      frame := hframe
      tempInvariant := hframe.tempStorageInv hinvariant
      tempLive := hframe.live hlive
      valuesMode := hresultMode
      phaseOrder := ?_ }⟩
  exact SortSlice.memmoveTraced_phase_order state.a.hasValues state.data dst src
    count hdst hsrc

end CPythonListsort
