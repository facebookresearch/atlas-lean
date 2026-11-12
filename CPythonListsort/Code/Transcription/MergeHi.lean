/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Transcription.Gallop
import Code.Transcription.MergeMemory

/-!
# Right-to-left stable merge transcription

This module transcribes CPython's `merge_hi` from the pinned
`Objects/listobject.c`.  The active list remains in `MergeState.data`; the
shorter right run is copied into `MergeState.a`, whose optional cells retain
the distinction between allocated and initialized temporary storage.

The ordinary and galloping loops are represented by a fuel-bounded phase
machine.  Modeled assertion or bounds failures return `none`.  Exhaustion of
the explicit loop or of a nested gallop is instead observable through
`fuelExhausted`, while rejection by `merge_getmem` retains C's `-1` result.

Equality selects B while filling backward, leaving the equal A entry before it
in final forward order.  Galloping retains C's `na == 0` and `nb == 0` branches
for inconsistent but total comparators, including the `na - k` and `nb - k`
conversions from insertion indices to backward block lengths.

Version one has no comparator-error result.  CPython's comparator-error jumps
to `Fail` are deliberately absent, while the temp-to-data copyback shared by
C's `Succeed` and `Fail` labels remains on successful exits.  Distinct
temp/data block copies model `sortslice_memcpy`; blocks moved within `data` use
overlap-safe `SortSlice.memmove?`.
-/

namespace CPythonListsort

universe u v w x

variable {κ : Type u} {ν : Type v}

/-- Short-circuiting option composition used by the exported `merge_hi` core.
The dedicated name keeps later traced/refinement proofs independent of private
declaration names in this module. -/
def mergeHiBindOptionAcross {α : Type w} {β : Type x}
    (value : Option α) (next : α → Option β) : Option β :=
  match value with
  | none => none
  | some value => next value

/-- The three `sortslice_memcpy` sites in CPython's `merge_hi`, kept separate
so source coverage and backing direction remain machine-visible. -/
inductive MergeHiMemcpyCallsite where
  | initialDataToTemp
  | gallopTempToData
  | finalTempToData
  deriving DecidableEq, Repr

namespace MergeHiMemcpyCallsite

/-- Destination and source regions used by one pinned `merge_hi` memcpy site. -/
def backings : MergeHiMemcpyCallsite → MergeMemcpyBackings
  | .initialDataToTemp =>
      { destination := .temporary, source := .main }
  | .gallopTempToData | .finalTempToData =>
      { destination := .main, source := .temporary }

end MergeHiMemcpyCallsite

/-- Every memcpy-class bulk move in `merge_hi` crosses the main and temporary
regions.  The evaluator below couples every such move to one of these tags. -/
theorem mergeHi_memcpyCallsite_distinct (site : MergeHiMemcpyCallsite) :
    site.backings.Distinct := by
  cases site <;>
    simp [MergeHiMemcpyCallsite.backings, MergeMemcpyBackings.Distinct]

/-- Read one initialized logical entry from temporary merge storage. -/
def mergeHiTempRead? (storage : TempStorage κ ν) (index : Int) :
    Option (SortSliceEntry κ ν) :=
  if 0 ≤ index then
    match storage.cells[index.toNat]? with
    | some (some entry) => some entry
    | _ => none
  else
    none

/-- Initialize or replace one in-bounds logical temporary entry. -/
def mergeHiTempWrite? (storage : TempStorage κ ν) (index : Int)
    (entry : SortSliceEntry κ ν) : Option (TempStorage κ ν) :=
  if hnonnegative : 0 ≤ index then
    let i := index.toNat
    if hinBounds : i < storage.cells.size then
      some { storage with cells := storage.cells.set i (some entry) }
    else
      none
  else
    none

/-- At a natural index, temporary reads are exactly optional-array lookup
followed by rejection of an uninitialized cell. -/
@[simp]
theorem mergeHiTempRead_ofNat (storage : TempStorage κ ν) (index : Nat) :
    mergeHiTempRead? storage (Int.ofNat index) =
      storage.cells[index]?.bind id := by
  cases hcell : storage.cells[index]? with
  | none => simp [mergeHiTempRead?, hcell]
  | some cell => cases cell <;> simp [mergeHiTempRead?, hcell]

/-- A successful temporary write makes the written logical cell readable. -/
theorem mergeHiTempWrite_read_eq_some_of_eq_some
    (storage updated : TempStorage κ ν) (index : Int)
    (entry : SortSliceEntry κ ν)
    (hwrite : mergeHiTempWrite? storage index entry = some updated) :
    mergeHiTempRead? updated index = some entry := by
  unfold mergeHiTempWrite? at hwrite
  split at hwrite
  · rename_i hnonnegative
    dsimp only at hwrite
    split at hwrite
    · rename_i hinBounds
      injection hwrite with hwrite
      subst updated
      simp [mergeHiTempRead?, hnonnegative, hinBounds]
    · simp at hwrite
  · simp at hwrite

/-- A successful temporary write preserves reads at every other signed
logical index. -/
theorem mergeHiTempWrite_read_of_ne
    (storage updated : TempStorage κ ν) (written index : Int)
    (entry : SortSliceEntry κ ν)
    (hwrite : mergeHiTempWrite? storage written entry = some updated)
    (hne : index ≠ written) :
    mergeHiTempRead? updated index = mergeHiTempRead? storage index := by
  unfold mergeHiTempWrite? at hwrite
  split at hwrite
  · rename_i hwritten
    dsimp only at hwrite
    split at hwrite
    · rename_i hinBounds
      injection hwrite with hwrite
      subst updated
      by_cases hindex : 0 ≤ index
      · have hnatne : written.toNat ≠ index.toNat := by
          intro heq
          apply hne
          have hwrittenCast := Int.toNat_of_nonneg hwritten
          have hindexCast := Int.toNat_of_nonneg hindex
          omega
        simp [mergeHiTempRead?, hindex, Array.getElem?_set_ne _ hnatne]
      · simp [mergeHiTempRead?, hindex]
    · simp at hwrite
  · simp at hwrite

/-- Copy one main-list entry into temporary storage without advancing cursors. -/
def mergeHiCopyDataToTemp? (state : MergeState κ ν) (dst src : Int) :
    Option (MergeState κ ν) := do
  let entry ← state.data.read? src
  let storage ← mergeHiTempWrite? state.a dst entry
  pure { state with a := storage }

/-- Copy one initialized temporary entry into the main list without advancing
cursors. -/
def mergeHiCopyTempToData? (state : MergeState κ ν) (dst src : Int) :
    Option (MergeState κ ν) := do
  let entry ← mergeHiTempRead? state.a src
  let data ← state.data.write? dst entry
  pure { state with data := data }

/-- A successful main-to-temporary single-cell copy records the exact entry
read from the main list at its destination. -/
theorem mergeHiCopyDataToTemp_read_eq_some
    (state state' : MergeState κ ν) (dst src : Int)
    (hcopy : mergeHiCopyDataToTemp? state dst src = some state') :
    ∃ entry, state.data.read? src = some entry ∧
      mergeHiTempRead? state'.a dst = some entry := by
  rcases Option.bind_eq_some_iff.mp hcopy with ⟨entry, hread, htail⟩
  rcases Option.bind_eq_some_iff.mp htail with ⟨storage, hwrite, hfinal⟩
  injection hfinal with hfinal
  subst state'
  exact ⟨entry, hread,
    mergeHiTempWrite_read_eq_some_of_eq_some state.a storage dst entry hwrite⟩

/-- A main-to-temporary single-cell copy preserves all other temporary reads. -/
theorem mergeHiCopyDataToTemp_read_of_ne
    (state state' : MergeState κ ν) (dst src index : Int)
    (hcopy : mergeHiCopyDataToTemp? state dst src = some state')
    (hne : index ≠ dst) :
    mergeHiTempRead? state'.a index = mergeHiTempRead? state.a index := by
  rcases Option.bind_eq_some_iff.mp hcopy with ⟨entry, _hread, htail⟩
  rcases Option.bind_eq_some_iff.mp htail with ⟨storage, hwrite, hfinal⟩
  injection hfinal with hfinal
  subst state'
  exact mergeHiTempWrite_read_of_ne state.a storage dst index _ hwrite hne

/-- Forward bulk copy from main data to distinct temporary storage.  The
recursive memcpy implementation itself requires a pinned call-site tag and a
proof of its physical direction.  Its one-cell primitive is hardwired
data-to-temporary and is used only by this tagged bulk executor. -/
def mergeHiMemcpyDataToTemp?
    (site : MergeHiMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .temporary, source := .main }) :
    Nat → MergeState κ ν → Int → Int → Option (MergeState κ ν)
  | 0, state, _, _ => some state
  | count + 1, state, dst, src => do
      let state ← mergeHiCopyDataToTemp? state dst src
      mergeHiMemcpyDataToTemp? site hDirection count state (dst + 1) (src + 1)

/-- Forward bulk copy from temporary storage to distinct main data.  No raw
recursive temp-to-data memcpy helper exists below this tagged interface.  The
one-cell primitive is hardwired temporary-to-data and also models ordinary
`sortslice_copy`. -/
def mergeHiMemcpyTempToData?
    (site : MergeHiMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .main, source := .temporary }) :
    Nat → MergeState κ ν → Int → Int → Option (MergeState κ ν)
  | 0, state, _, _ => some state
  | count + 1, state, dst, src => do
      let state ← mergeHiCopyTempToData? state dst src
      mergeHiMemcpyTempToData? site hDirection count state (dst + 1) (src + 1)

/-- A successful forward main-to-temporary bulk copy leaves every temporary
cell strictly before its destination range unchanged. -/
theorem mergeHiMemcpyDataToTemp_read_before
    (site : MergeHiMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .temporary, source := .main })
    (count : Nat) (state state' : MergeState κ ν) (dst src index : Int)
    (hcopy : mergeHiMemcpyDataToTemp? site hDirection count state dst src =
      some state') (hindex : index < dst) :
    mergeHiTempRead? state'.a index = mergeHiTempRead? state.a index := by
  induction count generalizing state dst src with
  | zero =>
      simp only [mergeHiMemcpyDataToTemp?] at hcopy
      injection hcopy with hcopy
      subst state'
      rfl
  | succ count ih =>
      rw [mergeHiMemcpyDataToTemp?] at hcopy
      rcases Option.bind_eq_some_iff.mp hcopy with ⟨afterHead, hhead, hcopy⟩
      have htail := ih afterHead (dst + 1) (src + 1) hcopy (by omega)
      exact htail.trans
        (mergeHiCopyDataToTemp_read_of_ne state afterHead dst src index hhead
          (by omega))

/-- Every cell in a signed temporary range is initialized and readable. -/
def MergeHiTempRangeInitialized (storage : TempStorage κ ν)
    (source : Int) (count : Nat) : Prop :=
  ∀ i, i < count →
    ∃ entry,
      mergeHiTempRead? storage (source + Int.ofNat i) = some entry

/-- Every destination cell of a successful main-to-temporary bulk copy is
initialized in the final storage. -/
theorem mergeHiMemcpyDataToTemp_initialized_of_eq_some
    (site : MergeHiMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .temporary, source := .main })
    (count : Nat) (state state' : MergeState κ ν) (dst src : Int)
    (hcopy : mergeHiMemcpyDataToTemp? site hDirection count state dst src =
      some state') :
    MergeHiTempRangeInitialized state'.a dst count := by
  induction count generalizing state dst src with
  | zero =>
      unfold MergeHiTempRangeInitialized
      intro i hi
      omega
  | succ count ih =>
      rw [mergeHiMemcpyDataToTemp?] at hcopy
      rcases Option.bind_eq_some_iff.mp hcopy with ⟨afterHead, hhead, hcopy⟩
      intro i hi
      cases i with
      | zero =>
          rcases mergeHiCopyDataToTemp_read_eq_some state afterHead dst src hhead with
            ⟨entry, _hsource, hread⟩
          refine ⟨entry, ?_⟩
          have hpreserved := mergeHiMemcpyDataToTemp_read_before site hDirection
            count afterHead state' (dst + 1) (src + 1) dst hcopy (by omega)
          simpa using hpreserved.trans hread
      | succ i =>
          rcases ih afterHead (dst + 1) (src + 1) hcopy i (by omega) with
            ⟨entry, hread⟩
          exact ⟨entry, by
            have hindex :
                dst + Int.ofNat (Nat.succ i) =
                  (dst + 1) + Int.ofNat i := by
              simp [Int.ofNat_eq_natCast]
              omega
            rw [hindex]
            exact hread⟩

def mergeHiInitializedTempPrefixLoop? :
    Nat → TempStorage κ ν → Nat → Array (SortSliceEntry κ ν) →
      Option (Array (SortSliceEntry κ ν))
  | 0, _, _, entries => some entries
  | count + 1, storage, index, entries => do
      let entry ← mergeHiTempRead? storage (Int.ofNat index)
      mergeHiInitializedTempPrefixLoop? count storage (index + 1)
        (entries.push entry)

/-- Expose the initialized prefix of `ms->a` to the existing gallop
transcription.  Uninitialized capacity beyond `count` is deliberately not
read. -/
def initializedTempPrefix? (storage : TempStorage κ ν) (count : Nat) :
    Option (SortSlice κ ν) := do
  let entries ← mergeHiInitializedTempPrefixLoop? count storage 0 #[]
  pure { entries := entries }

/-- Every logical cell in the prefix is initialized and therefore readable.
This is the exact domain condition for `initializedTempPrefix?`; capacity alone
is deliberately insufficient because freshly grown storage contains `none`. -/
def MergeHiTempPrefixInitialized (storage : TempStorage κ ν)
    (count : Nat) : Prop :=
  MergeHiTempRangeInitialized storage 0 count

/-- The pinned initial `sortslice_memcpy` initializes the entire temporary
prefix that subsequent straight and galloping reads may inspect. -/
theorem mergeHiInitialDataToTemp_prefixInitialized
    (count : Nat) (state state' : MergeState κ ν) (src : Int)
    (hcopy : mergeHiMemcpyDataToTemp? .initialDataToTemp rfl count state 0 src =
      some state') :
    MergeHiTempPrefixInitialized state'.a count := by
  simpa [MergeHiTempPrefixInitialized] using
    (mergeHiMemcpyDataToTemp_initialized_of_eq_some .initialDataToTemp rfl count
      state state' 0 src hcopy)

/-- The gathering loop is total when every source cell it will visit is
initialized. -/
theorem mergeHiInitializedTempPrefixLoop_exists_of_initialized
    (count : Nat) (storage : TempStorage κ ν) (source : Nat)
    (initial : Array (SortSliceEntry κ ν))
    (hInitialized : ∀ i, i < count →
      ∃ entry,
        mergeHiTempRead? storage (Int.ofNat (source + i)) = some entry) :
    ∃ result,
      mergeHiInitializedTempPrefixLoop? count storage source initial =
        some result := by
  induction count generalizing source initial with
  | zero =>
      exact ⟨initial, rfl⟩
  | succ count ih =>
      rcases hInitialized 0 (Nat.zero_lt_succ count) with ⟨entry, hentry⟩
      have hhead :
          mergeHiTempRead? storage (Int.ofNat source) = some entry := by
        simpa using hentry
      rcases ih (source + 1) (initial.push entry) (fun i hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hInitialized (i + 1) (by omega)) with ⟨result, hresult⟩
      exact ⟨result, by
        simp only [mergeHiInitializedTempPrefixLoop?]
        rw [hhead]
        exact hresult⟩

/-- An initialized prefix always materializes successfully. -/
theorem mergeHiInitializedTempPrefix_exists_of_initialized
    (storage : TempStorage κ ν) (count : Nat)
    (hInitialized : MergeHiTempPrefixInitialized storage count) :
    ∃ slice, initializedTempPrefix? storage count = some slice := by
  rcases mergeHiInitializedTempPrefixLoop_exists_of_initialized count storage
      0 #[] (by
        simpa [MergeHiTempPrefixInitialized, MergeHiTempRangeInitialized] using
          hInitialized) with
    ⟨entries, hentries⟩
  exact ⟨{ entries := entries }, by
    simp [initializedTempPrefix?, hentries]⟩

/-- Consequently, a successful pinned initial copy makes prefix
materialization total for exactly the copied length. -/
theorem mergeHiInitialDataToTemp_initializedTempPrefix_exists
    (count : Nat) (state state' : MergeState κ ν) (src : Int)
    (hcopy : mergeHiMemcpyDataToTemp? .initialDataToTemp rfl count state 0 src =
      some state') :
    ∃ slice, initializedTempPrefix? state'.a count = some slice :=
  mergeHiInitializedTempPrefix_exists_of_initialized state'.a count
    (mergeHiInitialDataToTemp_prefixInitialized count state state' src hcopy)

theorem mergeHiInitializedTempPrefixLoop_spec (count : Nat)
    (storage : TempStorage κ ν) (source : Nat)
    (initial result : Array (SortSliceEntry κ ν))
    (hresult :
      mergeHiInitializedTempPrefixLoop? count storage source initial = some result) :
    result.size = initial.size + count ∧
      (∀ i < initial.size, result[i]? = initial[i]?) ∧
      ∀ i < count,
        result[initial.size + i]? = storage.cells[source + i]?.bind id := by
  induction count generalizing source initial with
  | zero =>
      simp only [mergeHiInitializedTempPrefixLoop?] at hresult
      injection hresult with hresult
      subst result
      simp
  | succ count ih =>
      cases hcell : storage.cells[source]? with
      | none =>
          simp [mergeHiInitializedTempPrefixLoop?, mergeHiTempRead?, hcell] at hresult
      | some cell =>
          cases cell with
          | none =>
              simp [mergeHiInitializedTempPrefixLoop?, mergeHiTempRead?, hcell] at hresult
          | some entry =>
              have hnext :
                  mergeHiInitializedTempPrefixLoop? count storage (source + 1)
                    (initial.push entry) = some result := by
                simpa [mergeHiInitializedTempPrefixLoop?, mergeHiTempRead?, hcell] using
                  hresult
              rcases ih (source + 1) (initial.push entry) hnext with
                ⟨hsize, hprefix, hgathered⟩
              refine ⟨by
                simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                  hsize, ?_, ?_⟩
              · intro i hi
                have hpreserved := hprefix i (by
                  simpa using Nat.lt_succ_of_lt hi)
                simpa [Array.getElem?_push, Nat.ne_of_lt hi] using hpreserved
              · intro i hi
                cases i with
                | zero =>
                    have hnew := hprefix initial.size (by simp)
                    simpa [Array.getElem?_push, hcell] using hnew
                | succ i =>
                    have hiCount : i < count := by omega
                    have hrest := hgathered i hiCount
                    simpa [Array.size_push, Nat.add_assoc, Nat.add_comm,
                      Nat.add_left_comm] using hrest

/-- A successful prefix materialization contains exactly the initialized
temporary cells at indices below `count`. -/
theorem initializedTempPrefix_cells_of_eq_some (storage : TempStorage κ ν)
    (count : Nat) (slice : SortSlice κ ν)
    (hresult : initializedTempPrefix? storage count = some slice) :
    slice.entries.size = count ∧
      ∀ i < count, storage.cells[i]?.bind id = slice.entries[i]? := by
  unfold initializedTempPrefix? at hresult
  cases hentries : mergeHiInitializedTempPrefixLoop? count storage 0 #[] with
  | none => simp [hentries] at hresult
  | some entries =>
      have hmaterialized :
          (some ({ entries := entries } : SortSlice κ ν)) = some slice := by
        simpa [hentries] using hresult
      injection hmaterialized with hmaterialized
      subst slice
      rcases mergeHiInitializedTempPrefixLoop_spec count storage 0 #[] entries hentries with
        ⟨hsize, _hprefix, hrange⟩
      exact ⟨by simpa using hsize, fun i hi => by
        simpa using (hrange i hi).symm⟩

/-- Successful materialization certifies that every requested temporary cell
was initialized; this rules out a proof that silently reads fresh `none`
capacity. -/
theorem mergeHiInitializedTempPrefix_initialized_of_eq_some
    (storage : TempStorage κ ν) (count : Nat) (slice : SortSlice κ ν)
    (hresult : initializedTempPrefix? storage count = some slice) :
    MergeHiTempPrefixInitialized storage count := by
  rcases initializedTempPrefix_cells_of_eq_some storage count slice hresult with
    ⟨hsize, hcells⟩
  intro i hi
  have hiSize : i < slice.entries.size := by omega
  have hslice := Array.getElem?_eq_getElem hiSize
  have hbind :
      storage.cells[i]?.bind id = some slice.entries[i] := by
    rw [hcells i hi, hslice]
  rw [Option.bind_eq_some_iff] at hbind
  rcases hbind with ⟨cell, hcell, hcellEntry⟩
  have hcellEntry' : cell = some slice.entries[i] := by
    simpa using hcellEntry
  subst cell
  exact ⟨slice.entries[i], by
    simp [mergeHiTempRead?, hcell]⟩

/-- Prefix materialization succeeds exactly for initialized logical cells. -/
theorem mergeHiInitializedTempPrefix_exists_iff_initialized
    (storage : TempStorage κ ν) (count : Nat) :
    (∃ slice, initializedTempPrefix? storage count = some slice) ↔
      MergeHiTempPrefixInitialized storage count := by
  constructor
  · rintro ⟨slice, hslice⟩
    exact mergeHiInitializedTempPrefix_initialized_of_eq_some storage count slice
      hslice
  · exact mergeHiInitializedTempPrefix_exists_of_initialized storage count

/-- State and decremented cursors produced by a single backward copy. -/
structure MergeHiDataCursorResult (κ : Type u) (ν : Type v) where
  state : MergeState κ ν
  dst : Int
  src : Int

def mergeHiCopyDataDecr? (state : MergeState κ ν) (dst src : Int) :
    Option (MergeHiDataCursorResult κ ν) := do
  let copied ← state.data.copyDecr? dst src
  pure
    { state := { state with data := copied.slice }
      dst := copied.dst
      src := copied.src }

def mergeHiCopyTempDecr? (state : MergeState κ ν) (dst src : Int) :
    Option (MergeHiDataCursorResult κ ν) := do
  let state ← mergeHiCopyTempToData? state dst src
  pure { state := state, dst := dst - 1, src := src - 1 }

/-- Observable result of `merge_hi`.  The fuel flag is separate from C's
return code so the adequacy layer can prove that the chosen bound suffices. -/
structure MergeHiResult (κ : Type u) (ν : Type v) where
  state : MergeState κ ν
  returnCode : Int
  fuelExhausted : Bool

inductive MergeHiPhase where
  | straight (aCount bCount : Nat)
  | galloping (aCount bCount : Nat)

structure MergeHiCursor (κ : Type u) (ν : Type v) where
  state : MergeState κ ν
  dest : Int
  ssa : Int
  ssb : Int
  basea : Int
  na : Nat
  nb : Nat
  minGallop : PySSize
  phase : MergeHiPhase

def mergeHiCountAtLeast (count : Nat) (threshold : PySSize) : Bool :=
  !((BitVec.ofNat 64 count).slt threshold)

/-- `min_gallop -= min_gallop > 1`, with the signed comparison used by C. -/
def mergeHiDecreaseMinGallop (minGallop : PySSize) : PySSize :=
  if (1 : PySSize).slt minGallop then minGallop - 1 else minGallop

def mergeHiFuelExhausted (cursor : MergeHiCursor κ ν) :
    MergeHiResult κ ν :=
  { state := cursor.state, returnCode := -1, fuelExhausted := true }

/-- The remainder copy shared by C's `Succeed` and `Fail` labels.  Comparator
errors are outside the total Boolean comparator model, so only the successful
entry is retained here; the modeled pre-loop allocation guard has its own
negative result. -/
def mergeHiSucceed? (cursor : MergeHiCursor κ ν) :
    Option (MergeHiResult κ ν) := do
  let state ←
    if cursor.nb = 0 then
      some cursor.state
    else
      mergeHiMemcpyTempToData? .finalTempToData rfl cursor.nb cursor.state
        (cursor.dest - Int.ofNat (cursor.nb - 1)) 0
  pure { state := state, returnCode := 0, fuelExhausted := false }

/-- The `CopyA` tail, reached with the single smallest right-run element still
in temporary storage. -/
def mergeHiCopyA? (cursor : MergeHiCursor κ ν) :
    Option (MergeHiResult κ ν) := do
  if cursor.nb = 1 ∧ 0 < cursor.na then
    let offset := 1 - Int.ofNat cursor.na
    let data ← mergeDataMemmove? .hiCopyATail cursor.state.data
      (cursor.dest + offset) (cursor.ssa + offset) cursor.na
    let state := { cursor.state with data := data }
    let state ← mergeHiCopyTempToData? state
      (cursor.dest - Int.ofNat cursor.na) cursor.ssb
    pure { state := state, returnCode := 0, fuelExhausted := false }
  else
    none

/-- The second half of one `merge_hi` galloping round, parameterized by the
recursive continuation so its structural frame can be proved independently. -/
def mergeHiGallopB? (afterB : MergeHiCursor κ ν) (aCount : Nat)
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν)) :
    Option (MergeHiResult κ ν) := do
  let left ← afterB.state.data.read? afterB.ssa
  let temp ← initializedTempPrefix? afterB.state.a afterB.nb
  mergeHiBindOptionAcross
      (gallopLeft? afterB.state temp 0 left.key
        afterB.nb (afterB.nb - 1)) fun gallopB =>
    if gallopB.fuelExhausted then
      some (mergeHiFuelExhausted afterB)
    else do
      -- C's `k = nb - k`: backward merging consumes the suffix beginning at
      -- `gallop_left`'s insertion point.
      let bCount := afterB.nb - gallopB.index
      let movedB ←
        if bCount = 0 then
          some afterB
        else do
          let dest := afterB.dest - Int.ofNat bCount
          let ssb := afterB.ssb - Int.ofNat bCount
          let state ← mergeHiMemcpyTempToData? .gallopTempToData rfl
            bCount afterB.state
            (dest + 1) (ssb + 1)
          some
            { afterB with
              state := state
              dest := dest
              ssb := ssb
              nb := afterB.nb - bCount }
      -- Preserve C's inconsistent-comparator `nb == 0` hedge; the common
      -- dispatcher distinguishes it from CopyA.
      if movedB.nb = 0 ∨ movedB.nb = 1 then
        next movedB
      else
        let copiedA ← mergeHiCopyDataDecr? movedB.state movedB.dest movedB.ssa
        let afterA : MergeHiCursor κ ν :=
          { movedB with
            state := copiedA.state
            dest := copiedA.dst
            ssa := copiedA.src
            na := movedB.na - 1 }
        if afterA.na = 0 then
          next afterA
        else if mergeHiCountAtLeast aCount MIN_GALLOP ||
            mergeHiCountAtLeast bCount MIN_GALLOP then
          next { afterA with phase := .galloping aCount bCount }
        else
          let minGallop := afterB.minGallop + 1
          let state := { afterA.state with min_gallop := minGallop }
          next
            { afterA with
              state := state
              minGallop := minGallop
              phase := .straight 0 0 }

/-- One complete `merge_hi` galloping round, parameterized by the recursive
continuation. -/
def mergeHiGallopRound? (cursor : MergeHiCursor κ ν)
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν)) :
    Option (MergeHiResult κ ν) := do
  let minGallop := mergeHiDecreaseMinGallop cursor.minGallop
  let state := { cursor.state with min_gallop := minGallop }
  let right ← mergeHiTempRead? state.a cursor.ssb
  mergeHiBindOptionAcross
      (gallopRight? state state.data cursor.basea right.key
        cursor.na (cursor.na - 1)) fun gallopA =>
    if gallopA.fuelExhausted then
      some (mergeHiFuelExhausted { cursor with state := state })
    else do
      -- C's `k = na - k`: backward merging consumes the suffix after the
      -- insertion point returned by `gallop_right`.
      let aCount := cursor.na - gallopA.index
      let movedA ←
        if aCount = 0 then
          some { cursor with state := state, minGallop := minGallop }
        else do
          let dest := cursor.dest - Int.ofNat aCount
          let ssa := cursor.ssa - Int.ofNat aCount
          let data ← mergeDataMemmove? .hiGallopA state.data
            (dest + 1) (ssa + 1) aCount
          some
            { cursor with
              state := { state with data := data }
              dest := dest
              ssa := ssa
              na := cursor.na - aCount
              minGallop := minGallop }
      if movedA.na = 0 then
        next movedA
      else
        let copiedB ← mergeHiCopyTempDecr? movedA.state movedA.dest movedA.ssb
        let afterB : MergeHiCursor κ ν :=
          { movedA with
            state := copiedB.state
            dest := copiedB.dst
            ssb := copiedB.src
            nb := movedA.nb - 1 }
        if afterB.nb = 1 then
          next afterB
        else
          mergeHiGallopB? afterB aCount next

def mergeHiLoop? :
    Nat → MergeHiCursor κ ν → Option (MergeHiResult κ ν)
  | 0, cursor =>
      if cursor.na = 0 ∨ cursor.nb = 0 then
        mergeHiSucceed? cursor
      else if cursor.nb = 1 then
        mergeHiCopyA? cursor
      else
        some (mergeHiFuelExhausted cursor)
  | fuel + 1, cursor =>
      if cursor.na = 0 ∨ cursor.nb = 0 then
        mergeHiSucceed? cursor
      else if cursor.nb = 1 then
        mergeHiCopyA? cursor
      else
        match cursor.phase with
        | .straight aCount bCount => do
            let right ← mergeHiTempRead? cursor.state.a cursor.ssb
            let left ← cursor.state.data.read? cursor.ssa
            if iflt cursor.state.key_compare right.key left.key then
              let copied ← mergeHiCopyDataDecr? cursor.state cursor.dest cursor.ssa
              let aCount := aCount + 1
              let next : MergeHiCursor κ ν :=
                { cursor with
                  state := copied.state
                  dest := copied.dst
                  ssa := copied.src
                  na := cursor.na - 1
                  phase :=
                    if mergeHiCountAtLeast aCount cursor.minGallop then
                      .galloping aCount 0
                    else
                      .straight aCount 0
                  minGallop :=
                    if mergeHiCountAtLeast aCount cursor.minGallop then
                      cursor.minGallop + 1
                    else
                      cursor.minGallop }
              mergeHiLoop? fuel next
            else
              let copied ← mergeHiCopyTempDecr? cursor.state cursor.dest cursor.ssb
              let bCount := bCount + 1
              let next : MergeHiCursor κ ν :=
                { cursor with
                  state := copied.state
                  dest := copied.dst
                  ssb := copied.src
                  nb := cursor.nb - 1
                  phase :=
                    if mergeHiCountAtLeast bCount cursor.minGallop then
                      .galloping 0 bCount
                    else
                      .straight 0 bCount
                  minGallop :=
                    if mergeHiCountAtLeast bCount cursor.minGallop then
                      cursor.minGallop + 1
                    else
                      cursor.minGallop }
              mergeHiLoop? fuel next
        | .galloping _ _ =>
            mergeHiGallopRound? cursor (mergeHiLoop? fuel)

/-! ## Review-visible control-flow equations -/

/-- Public equation exposing the main-data (A-side) cell copied by a straight
backward step and both decremented cursors. -/
theorem mergeHiCopyDataDecr_equation (state : MergeState κ ν) (dst src : Int) :
    mergeHiCopyDataDecr? state dst src = (do
      let copied ← state.data.copyDecr? dst src
      pure
        { state := { state with data := copied.slice }
          dst := copied.dst
          src := copied.src }) := by
  rfl

/-- Public equation exposing the temporary (B-side) cell copied by a straight
backward step and both decremented cursors. -/
theorem mergeHiCopyTempDecr_equation (state : MergeState κ ν) (dst src : Int) :
    mergeHiCopyTempDecr? state dst src = (do
      let state ← mergeHiCopyTempToData? state dst src
      pure { state := state, dst := dst - 1, src := src - 1 }) := by
  rfl

/-- Public equation for the `CopyA` tail's same-store block move.  The left
remainder uses the `.hiCopyATail` overlap-safe memmove wrapper before the final
temporary B entry is installed. -/
theorem mergeHiCopyA_memmove_equation (cursor : MergeHiCursor κ ν) :
    mergeHiCopyA? cursor = (do
      if cursor.nb = 1 ∧ 0 < cursor.na then
        let offset := 1 - Int.ofNat cursor.na
        let data ← mergeDataMemmove? .hiCopyATail cursor.state.data
          (cursor.dest + offset) (cursor.ssa + offset) cursor.na
        let state := { cursor.state with data := data }
        let state ← mergeHiCopyTempToData? state
          (cursor.dest - Int.ofNat cursor.na) cursor.ssb
        pure { state := state, returnCode := 0, fuelExhausted := false }
      else
        none) := by
  rfl

/-- Public equation for the B half of a backward gallop.  It pins the exact
`gallop_left(temp, left, nb, nb - 1)` call and CPython's conversion from its
insertion index to the copied suffix length, `bCount = nb - index`. -/
theorem mergeHiGallopB_equation
    (afterB : MergeHiCursor κ ν) (aCount : Nat)
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν)) :
    mergeHiGallopB? afterB aCount next = (do
      let left ← afterB.state.data.read? afterB.ssa
      let temp ← initializedTempPrefix? afterB.state.a afterB.nb
      mergeHiBindOptionAcross
          (gallopLeft? afterB.state temp 0 left.key
            afterB.nb (afterB.nb - 1)) fun gallopB =>
        if gallopB.fuelExhausted then
          some (mergeHiFuelExhausted afterB)
        else do
          let bCount := afterB.nb - gallopB.index
          let movedB ←
            if bCount = 0 then
              some afterB
            else do
              let dest := afterB.dest - Int.ofNat bCount
              let ssb := afterB.ssb - Int.ofNat bCount
              let state ← mergeHiMemcpyTempToData? .gallopTempToData rfl
                bCount afterB.state
                (dest + 1) (ssb + 1)
              some
                { afterB with
                  state := state
                  dest := dest
                  ssb := ssb
                  nb := afterB.nb - bCount }
          if movedB.nb = 0 ∨ movedB.nb = 1 then
            next movedB
          else
            let copiedA ← mergeHiCopyDataDecr? movedB.state movedB.dest movedB.ssa
            let afterA : MergeHiCursor κ ν :=
              { movedB with
                state := copiedA.state
                dest := copiedA.dst
                ssa := copiedA.src
                na := movedB.na - 1 }
            if afterA.na = 0 then
              next afterA
            else if mergeHiCountAtLeast aCount MIN_GALLOP ||
                mergeHiCountAtLeast bCount MIN_GALLOP then
              next { afterA with phase := .galloping aCount bCount }
            else
              let minGallop := afterB.minGallop + 1
              let state := { afterA.state with min_gallop := minGallop }
              next
                { afterA with
                  state := state
                  minGallop := minGallop
                  phase := .straight 0 0 }) := by
  rfl

/-- Public equation for the A half of a backward gallop.  It pins the exact
`gallop_right(data, right, na, na - 1)` call and CPython's conversion from its
insertion index to the moved suffix length, `aCount = na - index`. -/
theorem mergeHiGallopRound_equation
    (cursor : MergeHiCursor κ ν)
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν)) :
    mergeHiGallopRound? cursor next = (do
      let minGallop := mergeHiDecreaseMinGallop cursor.minGallop
      let state := { cursor.state with min_gallop := minGallop }
      let right ← mergeHiTempRead? state.a cursor.ssb
      mergeHiBindOptionAcross
          (gallopRight? state state.data cursor.basea right.key
            cursor.na (cursor.na - 1)) fun gallopA =>
        if gallopA.fuelExhausted then
          some (mergeHiFuelExhausted { cursor with state := state })
        else do
          let aCount := cursor.na - gallopA.index
          let movedA ←
            if aCount = 0 then
              some { cursor with state := state, minGallop := minGallop }
            else do
              let dest := cursor.dest - Int.ofNat aCount
              let ssa := cursor.ssa - Int.ofNat aCount
              let data ← mergeDataMemmove? .hiGallopA state.data
                (dest + 1) (ssa + 1) aCount
              some
                { cursor with
                  state := { state with data := data }
                  dest := dest
                  ssa := ssa
                  na := cursor.na - aCount
                  minGallop := minGallop }
          if movedA.na = 0 then
            next movedA
          else
            let copiedB ← mergeHiCopyTempDecr? movedA.state movedA.dest movedA.ssb
            let afterB : MergeHiCursor κ ν :=
              { movedA with
                state := copiedB.state
                dest := copiedB.dst
                ssb := copiedB.src
                nb := movedA.nb - 1 }
            if afterB.nb = 1 then
              next afterB
            else
              mergeHiGallopB? afterB aCount next) := by
  rfl

/-- In a straight `merge_hi` step, `right < left` copies A while moving
backward, increments the A streak, and resets the B streak to zero. -/
theorem mergeHiLoop_straight_copyA_equation
    (fuel : Nat) (cursor : MergeHiCursor κ ν) (aCount bCount : Nat)
    (right left : SortSliceEntry κ ν)
    (hactive : ¬ (cursor.na = 0 ∨ cursor.nb = 0))
    (hmoreB : cursor.nb ≠ 1)
    (hright : mergeHiTempRead? cursor.state.a cursor.ssb = some right)
    (hleft : cursor.state.data.read? cursor.ssa = some left)
    (hcompare : cursor.state.key_compare right.key left.key = true) :
    mergeHiLoop? (fuel + 1)
      { cursor with phase := .straight aCount bCount } = (do
        let copied ← mergeHiCopyDataDecr? cursor.state cursor.dest cursor.ssa
        let aCount := aCount + 1
        let next : MergeHiCursor κ ν :=
          { cursor with
            state := copied.state
            dest := copied.dst
            ssa := copied.src
            na := cursor.na - 1
            phase :=
              if mergeHiCountAtLeast aCount cursor.minGallop then
                .galloping aCount 0
              else
                .straight aCount 0
            minGallop :=
              if mergeHiCountAtLeast aCount cursor.minGallop then
                cursor.minGallop + 1
              else
                cursor.minGallop }
        mergeHiLoop? fuel next) := by
  rw [mergeHiLoop?]
  simp [hactive, hmoreB, hright, hleft, iflt, hcompare]

/-- In a straight `merge_hi` step, `¬(right < left)` copies B while moving
backward, increments the B streak, and resets the A streak to zero. -/
theorem mergeHiLoop_straight_copyB_equation
    (fuel : Nat) (cursor : MergeHiCursor κ ν) (aCount bCount : Nat)
    (right left : SortSliceEntry κ ν)
    (hactive : ¬ (cursor.na = 0 ∨ cursor.nb = 0))
    (hmoreB : cursor.nb ≠ 1)
    (hright : mergeHiTempRead? cursor.state.a cursor.ssb = some right)
    (hleft : cursor.state.data.read? cursor.ssa = some left)
    (hcompare : cursor.state.key_compare right.key left.key = false) :
    mergeHiLoop? (fuel + 1)
      { cursor with phase := .straight aCount bCount } = (do
        let copied ← mergeHiCopyTempDecr? cursor.state cursor.dest cursor.ssb
        let bCount := bCount + 1
        let next : MergeHiCursor κ ν :=
          { cursor with
            state := copied.state
            dest := copied.dst
            ssb := copied.src
            nb := cursor.nb - 1
            phase :=
              if mergeHiCountAtLeast bCount cursor.minGallop then
                .galloping 0 bCount
              else
                .straight 0 bCount
            minGallop :=
              if mergeHiCountAtLeast bCount cursor.minGallop then
                cursor.minGallop + 1
              else
                cursor.minGallop }
        mergeHiLoop? fuel next) := by
  rw [mergeHiLoop?]
  simp [hactive, hmoreB, hright, hleft, iflt, hcompare]

/-- Stable-equality specialization of the B-copy equation: when equal keys do
not compare less than themselves, backward merging selects B, increments B's
streak, and resets A's streak.  This leaves the equal A entry earlier in final
forward order. -/
theorem mergeHiLoop_straight_equal_keys_equation
    (fuel : Nat) (cursor : MergeHiCursor κ ν) (aCount bCount : Nat)
    (right left : SortSliceEntry κ ν)
    (hactive : ¬ (cursor.na = 0 ∨ cursor.nb = 0))
    (hmoreB : cursor.nb ≠ 1)
    (hright : mergeHiTempRead? cursor.state.a cursor.ssb = some right)
    (hleft : cursor.state.data.read? cursor.ssa = some left)
    (hkeys : right.key = left.key)
    (hirrefl : cursor.state.key_compare left.key left.key = false) :
    mergeHiLoop? (fuel + 1)
      { cursor with phase := .straight aCount bCount } = (do
        let copied ← mergeHiCopyTempDecr? cursor.state cursor.dest cursor.ssb
        let bCount := bCount + 1
        let next : MergeHiCursor κ ν :=
          { cursor with
            state := copied.state
            dest := copied.dst
            ssb := copied.src
            nb := cursor.nb - 1
            phase :=
              if mergeHiCountAtLeast bCount cursor.minGallop then
                .galloping 0 bCount
              else
                .straight 0 bCount
            minGallop :=
              if mergeHiCountAtLeast bCount cursor.minGallop then
                cursor.minGallop + 1
              else
                cursor.minGallop }
        mergeHiLoop? fuel next) := by
  apply mergeHiLoop_straight_copyB_equation fuel cursor aCount bCount
    right left hactive hmoreB hright hleft
  simpa [hkeys] using hirrefl

/-- Transcription of CPython's right-to-left stable merge.

`ssa` and `ssb` are signed base indices into `state.data`; `na` and `nb` are
their positive, signed-`Py_ssize_t`-representable lengths.  Adjacency is an
assertion-domain check.  No `na ≥ nb` check is added because the pinned C
routine documents that selection condition but does not assert it locally.
-/
def mergeHi? (state : MergeState κ ν) (ssa ssb : Int) (na nb : Nat) :
    Option (MergeHiResult κ ν) :=
  if 0 < na ∧ 0 < nb ∧ na ≤ PY_SSIZE_T_MAX ∧ nb ≤ PY_SSIZE_T_MAX ∧
      ssa + Int.ofNat na = ssb then
    let allocated := mergeGetmem state (BitVec.ofNat 64 nb)
    match allocated.outcome with
    | .guardRejected =>
        some
          { state := allocated.state
            returnCode := -1
            fuelExhausted := false }
    | .reused | .grown => do
        let state ← mergeHiMemcpyDataToTemp? .initialDataToTemp rfl
          nb allocated.state 0 ssb
        let dest := ssb + Int.ofNat (nb - 1)
        let ssaCursor := ssa + Int.ofNat (na - 1)
        let copied ← mergeHiCopyDataDecr? state dest ssaCursor
        let cursor : MergeHiCursor κ ν :=
          { state := copied.state
            dest := copied.dst
            ssa := copied.src
            ssb := Int.ofNat (nb - 1)
            basea := ssa
            na := na - 1
            nb := nb
            minGallop := copied.state.min_gallop
            phase := .straight 0 0 }
        mergeHiLoop? (na + nb) cursor
  else
    none

/-! ## Layout-relevant structural frame -/

private structure MergeHiLayoutFrame where
  listlen : PySSize
  basekeys : Nat
  dataSize : Nat
  pending : Array PendingRun

private def mergeHiLayoutFrame (state : MergeState κ ν) : MergeHiLayoutFrame :=
  { listlen := state.listlen
    basekeys := state.basekeys
    dataSize := state.data.entries.size
    pending := state.pending }

private theorem copyDataToTemp_layoutFrame
    (state state' : MergeState κ ν) (dst src : Int)
    (h : mergeHiCopyDataToTemp? state dst src = some state') :
    mergeHiLayoutFrame state' = mergeHiLayoutFrame state := by
  simp only [mergeHiCopyDataToTemp?, bind, Option.bind] at h
  split at h <;> simp_all
  split at h <;> simp_all
  subst state'
  rfl

private theorem mergeHiMemcpyDataToTemp_layoutFrame
    (site : MergeHiMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .temporary, source := .main })
    (count : Nat) (state state' : MergeState κ ν) (dst src : Int)
    (h : mergeHiMemcpyDataToTemp? site hDirection count state dst src =
      some state') :
    mergeHiLayoutFrame state' = mergeHiLayoutFrame state := by
  induction count generalizing state dst src with
  | zero =>
      have := congrArg (Option.map mergeHiLayoutFrame) h
      simpa [mergeHiMemcpyDataToTemp?] using this.symm
  | succ count ih =>
      simp only [mergeHiMemcpyDataToTemp?, bind, Option.bind] at h
      split at h
      · simp at h
      · exact (ih _ _ _ h).trans (copyDataToTemp_layoutFrame _ _ _ _ ‹_›)

private theorem copyTempToData_layoutFrame
    (state state' : MergeState κ ν) (dst src : Int)
    (h : mergeHiCopyTempToData? state dst src = some state') :
    mergeHiLayoutFrame state' = mergeHiLayoutFrame state := by
  simp only [mergeHiCopyTempToData?, bind, Option.bind] at h
  split at h <;> simp_all
  split at h <;> simp_all
  subst state'
  have hsize := SortSlice.write_entries_size_of_eq_some _ _ _ _ ‹_›
  simp [mergeHiLayoutFrame, hsize]

private theorem mergeHiMemcpyTempToData_layoutFrame
    (site : MergeHiMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .main, source := .temporary })
    (count : Nat) (state state' : MergeState κ ν) (dst src : Int)
    (h : mergeHiMemcpyTempToData? site hDirection count state dst src =
      some state') :
    mergeHiLayoutFrame state' = mergeHiLayoutFrame state := by
  induction count generalizing state dst src with
  | zero =>
      have := congrArg (Option.map mergeHiLayoutFrame) h
      simpa [mergeHiMemcpyTempToData?] using this.symm
  | succ count ih =>
      simp only [mergeHiMemcpyTempToData?, bind, Option.bind] at h
      split at h
      · simp at h
      · exact (ih _ _ _ h).trans (copyTempToData_layoutFrame _ _ _ _ ‹_›)

@[aesop safe forward]
private theorem mergeHiInitialDataToTemp_layoutFrame
    (count : Nat) (state state' : MergeState κ ν) (dst src : Int)
    (h : mergeHiMemcpyDataToTemp? .initialDataToTemp rfl count state dst src =
      some state') :
    mergeHiLayoutFrame state' = mergeHiLayoutFrame state :=
  mergeHiMemcpyDataToTemp_layoutFrame .initialDataToTemp rfl count state state'
    dst src h

@[aesop safe forward]
private theorem mergeHiGallopTempToData_layoutFrame
    (count : Nat) (state state' : MergeState κ ν) (dst src : Int)
    (h : mergeHiMemcpyTempToData? .gallopTempToData rfl count state dst src =
      some state') :
    mergeHiLayoutFrame state' = mergeHiLayoutFrame state :=
  mergeHiMemcpyTempToData_layoutFrame .gallopTempToData rfl count state state'
    dst src h

@[aesop safe forward]
private theorem mergeHiFinalTempToData_layoutFrame
    (count : Nat) (state state' : MergeState κ ν) (dst src : Int)
    (h : mergeHiMemcpyTempToData? .finalTempToData rfl count state dst src =
      some state') :
    mergeHiLayoutFrame state' = mergeHiLayoutFrame state :=
  mergeHiMemcpyTempToData_layoutFrame .finalTempToData rfl count state state'
    dst src h

private theorem copyDataDecr_layoutFrame
    (state : MergeState κ ν) (dst src : Int)
    (result : MergeHiDataCursorResult κ ν)
    (h : mergeHiCopyDataDecr? state dst src = some result) :
    mergeHiLayoutFrame result.state = mergeHiLayoutFrame state := by
  simp only [mergeHiCopyDataDecr?, bind, Option.bind] at h
  split at h <;> simp_all
  subst result
  have hsize := SortSlice.copyDecr_entries_size_of_eq_some _ _ _ _ ‹_›
  simp [mergeHiLayoutFrame, hsize]

private theorem copyTempDecr_layoutFrame
    (state : MergeState κ ν) (dst src : Int)
    (result : MergeHiDataCursorResult κ ν)
    (h : mergeHiCopyTempDecr? state dst src = some result) :
    mergeHiLayoutFrame result.state = mergeHiLayoutFrame state := by
  simp only [mergeHiCopyTempDecr?, bind, Option.bind] at h
  split at h
  · simp at h
  · rename_i state' hcopy
    have hresult :
        { state := state', dst := dst - 1, src := src - 1 } = result := by
      simpa using h
    rw [← hresult]
    exact copyTempToData_layoutFrame _ _ _ _ hcopy

attribute [aesop safe forward] copyDataDecr_layoutFrame copyTempDecr_layoutFrame
  copyTempToData_layoutFrame

attribute [aesop safe forward] SortSlice.memmove_entries_size_of_eq_some

private theorem mergeHiSucceed_layoutFrame
    (cursor : MergeHiCursor κ ν) (result : MergeHiResult κ ν)
    (h : mergeHiSucceed? cursor = some result) :
    mergeHiLayoutFrame result.state = mergeHiLayoutFrame cursor.state := by
  simp only [mergeHiSucceed?, bind, Option.bind] at h
  split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals aesop (config := { enableSimp := false })

private theorem mergeHiCopyA_layoutFrame
    (cursor : MergeHiCursor κ ν) (result : MergeHiResult κ ν)
    (h : mergeHiCopyA? cursor = some result) :
    mergeHiLayoutFrame result.state = mergeHiLayoutFrame cursor.state := by
  simp only [mergeHiCopyA?, bind, Option.bind] at h
  split at h <;> simp_all
  split at h <;> simp_all
  split at h <;> simp_all
  subst result
  have hmove := SortSlice.memmove_entries_size_of_eq_some _ _ _ _ _ ‹_›
  have hcopy := copyTempToData_layoutFrame _ _ _ _ ‹_›
  simp_all [mergeHiLayoutFrame]

@[aesop safe forward]
private theorem mergeHiFuelExhausted_layoutFrame
    (cursor : MergeHiCursor κ ν) (result : MergeHiResult κ ν)
    (h : mergeHiFuelExhausted cursor = result) :
    mergeHiLayoutFrame result.state = mergeHiLayoutFrame cursor.state := by
  subst result
  rfl

attribute [aesop safe forward] mergeHiSucceed_layoutFrame mergeHiCopyA_layoutFrame

set_option maxHeartbeats 5000000 in
-- The extracted gallop round has deeply nested option and boundary branches.
set_option maxRecDepth 10000 in
private theorem mergeHiGallopB_layoutFrame
    (afterB : MergeHiCursor κ ν) (aCount : Nat)
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν))
    (hnext : ∀ cursor result, next cursor = some result →
      mergeHiLayoutFrame result.state = mergeHiLayoutFrame cursor.state)
    (result : MergeHiResult κ ν)
    (h : mergeHiGallopB? afterB aCount next = some result) :
    mergeHiLayoutFrame result.state = mergeHiLayoutFrame afterB.state := by
  simp only [mergeHiGallopB?, bind, Option.bind, mergeHiBindOptionAcross] at h
  split at h <;> try simp only [reduceCtorEq] at h
  all_goals try split at h <;> try simp only [reduceCtorEq] at h
  all_goals try split at h <;> try simp only [reduceCtorEq] at h
  all_goals try split at h <;> try simp only [reduceCtorEq] at h
  all_goals try simp only [Option.some.injEq] at h
  all_goals try split at h <;> try simp only [reduceCtorEq] at h
  all_goals try split at h <;> try simp only [reduceCtorEq] at h
  all_goals try split at h <;> try simp only [reduceCtorEq] at h
  all_goals try split at h <;> try simp only [reduceCtorEq] at h
  all_goals try split at h <;> try simp only [reduceCtorEq] at h
  all_goals try split at h <;> try simp only [reduceCtorEq] at h
  all_goals aesop (config := {
    enableSimp := false, maxRuleApplications := 500, warnOnNonterminal := false })
  all_goals
    have hr := hnext _ _ h
    simp_all only [mergeHiLayoutFrame]

private theorem mergeHiGallopRound_layoutFrame
    (cursor : MergeHiCursor κ ν)
    (next : MergeHiCursor κ ν → Option (MergeHiResult κ ν))
    (hnext : ∀ cursor' result, next cursor' = some result →
      mergeHiLayoutFrame result.state = mergeHiLayoutFrame cursor'.state)
    (result : MergeHiResult κ ν)
    (h : mergeHiGallopRound? cursor next = some result) :
    mergeHiLayoutFrame result.state = mergeHiLayoutFrame cursor.state := by
  simp only [mergeHiGallopRound?, bind, Option.bind, mergeHiBindOptionAcross] at h
  split at h <;> try simp only [reduceCtorEq] at h
  all_goals try split at h <;> try simp only [reduceCtorEq] at h
  all_goals try split at h <;> try simp only [reduceCtorEq] at h
  all_goals try simp only [Option.some.injEq] at h
  all_goals try split at h <;> try simp only [reduceCtorEq] at h
  all_goals try split at h <;> try simp only [reduceCtorEq] at h
  all_goals try split at h <;> try simp only [reduceCtorEq] at h
  all_goals try split at h <;> try simp only [reduceCtorEq] at h
  all_goals try split at h <;> try simp only [reduceCtorEq] at h
  all_goals try aesop (config := {
    enableSimp := false, maxRuleApplications := 100, warnOnNonterminal := false })
  all_goals first
    | have hr := hnext _ _ h
      simp_all only [mergeHiLayoutFrame]
    | have hr := mergeHiGallopB_layoutFrame _ _ _ hnext _ h
      simp_all only [mergeHiLayoutFrame]

set_option maxHeartbeats 5000000 in
-- Fuel induction must follow every straight-phase comparison/result branch.
@[aesop safe forward]
private theorem mergeHiLoop_layoutFrame
    (fuel : Nat) (cursor : MergeHiCursor κ ν) (result : MergeHiResult κ ν)
    (h : mergeHiLoop? fuel cursor = some result) :
    mergeHiLayoutFrame result.state = mergeHiLayoutFrame cursor.state := by
  induction fuel generalizing cursor result with
  | zero =>
      simp only [mergeHiLoop?] at h
      split at h
      · exact mergeHiSucceed_layoutFrame _ _ h
      · split at h
        · exact mergeHiCopyA_layoutFrame _ _ h
        · have hr := Option.some.inj h
          subst result
          rfl
  | succ fuel ih =>
      simp only [mergeHiLoop?, bind, Option.bind] at h
      by_cases hstop : cursor.na = 0 ∨ cursor.nb = 0
      · rw [if_pos hstop] at h
        exact mergeHiSucceed_layoutFrame _ _ h
      · rw [if_neg hstop] at h
        by_cases hone : cursor.nb = 1
        · rw [if_pos hone] at h
          exact mergeHiCopyA_layoutFrame _ _ h
        · rw [if_neg hone] at h
          cases hphase : cursor.phase with
          | straight aCount bCount =>
              simp only [hphase] at h
              split at h <;> try simp only [reduceCtorEq] at h
              all_goals try split at h <;> try simp only [reduceCtorEq] at h
              all_goals try split at h <;> try simp only [reduceCtorEq] at h
              all_goals try split at h <;> try simp only [reduceCtorEq] at h
              all_goals try aesop (config := {
                enableSimp := false, maxRuleApplications := 100,
                warnOnNonterminal := false })
              all_goals
                have hr := ih _ _ h
                simp_all only [mergeHiLayoutFrame]
          | galloping aCount bCount =>
              simp only [hphase] at h
              exact mergeHiGallopRound_layoutFrame cursor (mergeHiLoop? fuel) ih result h

private theorem mergeGetmem_layoutFrame (state : MergeState κ ν) (need : PySSize) :
    mergeHiLayoutFrame (mergeGetmem state need).state = mergeHiLayoutFrame state := by
  simp only [mergeGetmem]
  split
  · rfl
  · split <;> simp only
    all_goals simp only [mergeFreemem]
    all_goals split <;> rfl

/-- Successful `merge_hi` executions preserve every field used by
`PendingLayout`: list length, base index, backing-array length, and pending
runs. Data contents may change. -/
theorem mergeHi_layoutFrame_of_eq_some
    (state : MergeState κ ν) (ssa ssb : Int) (na nb : Nat)
    (result : MergeHiResult κ ν)
    (h : mergeHi? state ssa ssb na nb = some result) :
    result.state.listlen = state.listlen ∧
      result.state.basekeys = state.basekeys ∧
      result.state.data.entries.size = state.data.entries.size ∧
      result.state.pending = state.pending := by
  have hframe : mergeHiLayoutFrame result.state = mergeHiLayoutFrame state := by
    simp only [mergeHi?, bind, Option.bind] at h
    split at h <;> try simp at h
    all_goals try split at h <;> try simp at h
    all_goals try split at h <;> try simp at h
    all_goals try split at h <;> try simp at h
    all_goals aesop (config := { enableSimp := false, warnOnNonterminal := false })
    all_goals
      have hmem := mergeGetmem_layoutFrame state (BitVec.ofNat 64 nb)
      simp_all only [mergeHiLayoutFrame]
  exact
    ⟨congrArg MergeHiLayoutFrame.listlen hframe,
      congrArg MergeHiLayoutFrame.basekeys hframe,
      congrArg MergeHiLayoutFrame.dataSize hframe,
      congrArg MergeHiLayoutFrame.pending hframe⟩

/-- `merge_hi` never mutates the pending-run stack. -/
theorem mergeHi_pending_eq_of_eq_some
    (state : MergeState κ ν) (ssa ssb : Int) (na nb : Nat)
    (result : MergeHiResult κ ν)
    (h : mergeHi? state ssa ssb na nb = some result) :
    result.state.pending = state.pending :=
  (mergeHi_layoutFrame_of_eq_some state ssa ssb na nb result h).2.2.2

def mergeHiGallopStabilityRegressionState : MergeState Nat Nat :=
  { min_gallop := 1
    listlen := 7
    basekeys := 0
    data :=
      { entries :=
          #[{ key := 2, value := some 20 },
            { key := 4, value := some 40 },
            { key := 6, value := some 60 },
            { key := 8, value := some 80 },
            { key := 1, value := some 11 },
            { key := 4, value := some 41 },
            { key := 5, value := some 51 }] }
    a :=
      { cells := Array.replicate 3 none
        backing := .inline
        hasValues := true }
    alloced := 3
    pending := #[]
    key_compare := fun left right => decide (left < right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

/-- Min-gallop-one output keeps the left equal occurrence first with its
payload attached; it does not expose branch entry. -/
theorem mergeHi_gallop_stability_regression :
    (mergeHi? mergeHiGallopStabilityRegressionState 0 4 4 3).map
        (fun result => (result.returnCode, result.fuelExhausted,
          result.state.data.entries.toList)) =
      some
        (0, false,
          [{ key := 1, value := some 11 },
           { key := 2, value := some 20 },
           { key := 4, value := some 40 },
           { key := 4, value := some 41 },
           { key := 5, value := some 51 },
           { key := 6, value := some 60 },
           { key := 8, value := some 80 }]) := by
  decide

/-! The next regression uses the non-irreflexive comparator `(· ≥ ·)`.  Its
second gallop consumes the whole temporary B run, after which the real loop
dispatcher reaches `mergeHiSucceed?` through its `nb = 0` guard.  A strict-`<`
control on the identical valid geometry returns the other insertion endpoint. -/

def mergeHiNbZeroHedgeRegressionState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 3
    basekeys := 0
    data :=
      { entries :=
          #[{ key := 3, value := some 30 },
            { key := 99, value := some 99 },
            { key := 98, value := some 98 }] }
    a :=
      { cells :=
          #[(some { key := 1, value := some 10 }),
            (some { key := 2, value := some 20 })]
        backing := .inline
        hasValues := true }
    alloced := 2
    pending := #[]
    key_compare := fun left right => decide (left ≥ right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

def mergeHiNbZeroHedgeRegressionCursor : MergeHiCursor Nat Nat :=
  { state := mergeHiNbZeroHedgeRegressionState
    dest := 2
    ssa := 0
    ssb := 1
    basea := 0
    na := 1
    nb := 2
    minGallop := MIN_GALLOP
    phase := .galloping 0 0 }

def mergeHiNbZeroHedgeStrictControlState : MergeState Nat Nat :=
  { mergeHiNbZeroHedgeRegressionState with
    key_compare := fun left right => decide (left < right) }

def mergeHiNbZeroHedgeStrictControlCursor : MergeHiCursor Nat Nat :=
  { mergeHiNbZeroHedgeRegressionCursor with
    state := mergeHiNbZeroHedgeStrictControlState }

/-- On one fixed cursor geometry, the non-irreflexive comparator gives
`gallop_left.index = 0`, so `bCount = nb - index` consumes all of B and reaches
the `nb = 0` success dispatch.  The strict control gives `index = nb` and a
different successful terminal path. -/
theorem mergeHi_inconsistentComparator_nbZero_succeed_regression :
    mergeHiNbZeroHedgeRegressionState.key_compare 1 1 = true ∧
    (initializedTempPrefix? mergeHiNbZeroHedgeRegressionState.a 2).bind
        (fun temp => gallopLeft? mergeHiNbZeroHedgeRegressionState
          temp 0 3 2 1) =
      some { index := 0, fuelExhausted := false } ∧
    (initializedTempPrefix? mergeHiNbZeroHedgeStrictControlState.a 2).bind
        (fun temp => gallopLeft? mergeHiNbZeroHedgeStrictControlState
          temp 0 3 2 1) =
      some { index := 2, fuelExhausted := false } ∧
    (mergeHiGallopB? mergeHiNbZeroHedgeRegressionCursor 0
      (mergeHiLoop? 1)).map
        (fun result => (result.returnCode, result.fuelExhausted,
          result.state.data.entries.toList)) =
      some
        (0, false,
          [{ key := 3, value := some 30 },
           { key := 1, value := some 10 },
           { key := 2, value := some 20 }]) ∧
    (mergeHiGallopB? mergeHiNbZeroHedgeStrictControlCursor 0
      (mergeHiLoop? 1)).map
        (fun result => (result.returnCode, result.fuelExhausted,
          result.state.data.entries.toList)) =
      some
        (0, false,
          [{ key := 1, value := some 10 },
           { key := 2, value := some 20 },
           { key := 3, value := some 30 }]) := by
  decide

end CPythonListsort
