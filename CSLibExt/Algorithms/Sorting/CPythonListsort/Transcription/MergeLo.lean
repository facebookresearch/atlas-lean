/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Transcription.Gallop
import Code.Transcription.MergeMemory

/-!
# Left-to-right merge transcription

This module transcribes CPython's `merge_lo`.  The main list remains in
`MergeState.data`; the shorter left run is copied into `MergeState.a` before
the merge starts.  Invalid assertion inputs, failed modeled accesses, and
invalid nested gallop calls return `none`.  The allocation guard and bounded
loop exhaustion remain observable and distinct in `MergeLoResult`.

The ordinary and galloping loops are represented by an explicit phase
machine.  Every recursive step consumes at least one live run entry, so the
input-size fuel is exposed only through the result flag and not as a caller
parameter.  Equality selects A while merging forward.  Galloping preserves
the C branch where an inconsistent but total comparator can consume all of A.

Version one has a pure Boolean comparator, so CPython's comparator-error jumps
to `Fail` and their negative result are deliberately absent.  The physical
temp-to-data copyback shared by C's `Succeed` and `Fail` labels remains on the
successful path.  Distinct temp/data block copies model `sortslice_memcpy`;
blocks moved within `data` use overlap-safe `SortSlice.memmove?`.
-/

namespace CPythonListsort

universe u v w x

variable {κ : Type u} {ν : Type v}

/-- Short-circuiting option composition used by the exported `merge_lo` core.
The dedicated name keeps later traced/refinement proofs independent of private
declaration names in this module. -/
def mergeLoBindOptionAcross {α : Type w} {β : Type x}
    (value : Option α) (next : α → Option β) : Option β :=
  match value with
  | none => none
  | some value => next value

/-- Observable result of the `merge_lo` transcription.  A negative return
code with `fuelExhausted = false` is the deterministic `merge_getmem` guard
failure. -/
structure MergeLoResult (κ : Type u) (ν : Type v) where
  state : MergeState κ ν
  returnCode : Int
  fuelExhausted : Bool

def mergeLoFailure (state : MergeState κ ν) : MergeLoResult κ ν :=
  { state := state, returnCode := -1, fuelExhausted := false }

def mergeLoOutOfFuel (state : MergeState κ ν) : MergeLoResult κ ν :=
  { state := state, returnCode := -1, fuelExhausted := true }

def mergeLoSuccess (state : MergeState κ ν) : MergeLoResult κ ν :=
  { state := state, returnCode := 0, fuelExhausted := false }

/-! ## Temporary-slice movement -/

/-- The three `sortslice_memcpy` sites in CPython's `merge_lo`, kept separate
so source coverage and backing direction remain machine-visible. -/
inductive MergeLoMemcpyCallsite where
  | initialDataToTemp
  | gallopTempToData
  | finalTempToData
  deriving DecidableEq, Repr

namespace MergeLoMemcpyCallsite

/-- Destination and source regions used by one pinned `merge_lo` memcpy site. -/
def backings : MergeLoMemcpyCallsite → MergeMemcpyBackings
  | .initialDataToTemp =>
      { destination := .temporary, source := .main }
  | .gallopTempToData | .finalTempToData =>
      { destination := .main, source := .temporary }

end MergeLoMemcpyCallsite

/-- Every memcpy-class bulk move in `merge_lo` crosses the main and temporary
regions.  The evaluator below couples every such move to one of these tags. -/
theorem mergeLo_memcpyCallsite_distinct (site : MergeLoMemcpyCallsite) :
    site.backings.Distinct := by
  cases site <;>
    simp [MergeLoMemcpyCallsite.backings, MergeMemcpyBackings.Distinct]

/-- Read one initialized logical entry from temporary merge storage. -/
def mergeLoTempRead? (storage : TempStorage κ ν) (index : Nat) :
    Option (SortSliceEntry κ ν) := do
  let cell ← storage.cells[index]?
  cell

/-- Initialize or replace one in-bounds logical temporary entry. -/
def mergeLoTempWrite? (storage : TempStorage κ ν) (index : Nat)
    (entry : SortSliceEntry κ ν) : Option (TempStorage κ ν) :=
  if h : index < storage.cells.size then
    some { storage with cells := storage.cells.set index (some entry) }
  else
    none

/-- Exact successful equation for an in-bounds temporary write. -/
@[simp]
theorem mergeLoTempWrite_eq_some_of_lt (storage : TempStorage κ ν)
    (index : Nat) (entry : SortSliceEntry κ ν)
    (hindex : index < storage.cells.size) :
    mergeLoTempWrite? storage index entry =
      some { storage with cells := storage.cells.set index (some entry) } := by
  simp [mergeLoTempWrite?, hindex]

/-- An out-of-bounds temporary write is rejected rather than extending the
temporary allocation. -/
@[simp]
theorem mergeLoTempWrite_eq_none_of_le (storage : TempStorage κ ν)
    (index : Nat) (entry : SortSliceEntry κ ν)
    (hindex : storage.cells.size ≤ index) :
    mergeLoTempWrite? storage index entry = none := by
  simp [mergeLoTempWrite?, Nat.not_lt.mpr hindex]

/-- A successful temporary write initializes the addressed cell. -/
theorem mergeLoTempRead_write_self_of_eq_some
    (storage updated : TempStorage κ ν) (index : Nat)
    (entry : SortSliceEntry κ ν)
    (hwrite : mergeLoTempWrite? storage index entry = some updated) :
    mergeLoTempRead? updated index = some entry := by
  simp only [mergeLoTempWrite?] at hwrite
  split at hwrite
  · injection hwrite with hwrite
    subst updated
    simp [mergeLoTempRead?]
  · simp at hwrite

/-- A successful temporary write preserves every other logical cell. -/
theorem mergeLoTempRead_write_ne_of_eq_some
    (storage updated : TempStorage κ ν) (index other : Nat)
    (entry : SortSliceEntry κ ν)
    (hwrite : mergeLoTempWrite? storage index entry = some updated)
    (hne : other ≠ index) :
    mergeLoTempRead? updated other = mergeLoTempRead? storage other := by
  simp only [mergeLoTempWrite?] at hwrite
  split at hwrite
  · injection hwrite with hwrite
    subst updated
    simp only [mergeLoTempRead?, bind, Option.bind]
    rw [Array.getElem?_set_ne _ hne.symm]
  · simp at hwrite

/-- Every cell in the indicated temporary range has been initialized.  This
is the precise precondition under which materializing that range is total. -/
def MergeLoTempRangeInitialized (storage : TempStorage κ ν)
    (source count : Nat) : Prop :=
  ∀ i, i < count →
    ∃ entry, mergeLoTempRead? storage (source + i) = some entry

/-- Copy a main-list range into the distinct temporary store.  This recursive
bulk-copy implementation itself requires a pinned call-site tag and a proof of
its physical direction, so there is no untagged memcpy-capable helper for an
evaluator call to bypass. -/
def mergeLoMemcpyDataToTemp?
    (site : MergeLoMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .temporary, source := .main }) :
    Nat → MergeState κ ν → Nat → Int → Option (MergeState κ ν)
  | 0, state, _, _ => some state
  | count + 1, state, destination, source => do
      let entry ← state.data.read? source
      let storage ← mergeLoTempWrite? state.a destination entry
      mergeLoMemcpyDataToTemp? site hDirection count
        { state with a := storage } (destination + 1) (source + 1)

/-- A data-to-temporary bulk copy never changes a cell strictly before its
destination range. -/
theorem mergeLoMemcpyDataToTemp_read_before_of_eq_some
    (site : MergeLoMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .temporary, source := .main })
    (count : Nat) (state state' : MergeState κ ν) (destination : Nat)
    (source : Int)
    (hresult : mergeLoMemcpyDataToTemp? site hDirection count state
      destination source = some state')
    (other : Nat) (hother : other < destination) :
    mergeLoTempRead? state'.a other = mergeLoTempRead? state.a other := by
  induction count generalizing state destination source with
  | zero =>
      simp only [mergeLoMemcpyDataToTemp?] at hresult
      injection hresult with hresult
      subst state'
      rfl
  | succ count ih =>
      cases hread : state.data.read? source with
      | none => simp [mergeLoMemcpyDataToTemp?, hread] at hresult
      | some entry =>
          cases hwrite : mergeLoTempWrite? state.a destination entry with
          | none =>
              simp [mergeLoMemcpyDataToTemp?, hread, hwrite] at hresult
          | some storage =>
              have htail :
                  mergeLoMemcpyDataToTemp? site hDirection count
                    { state with a := storage } (destination + 1) (source + 1) =
                      some state' := by
                simpa [mergeLoMemcpyDataToTemp?, hread, hwrite] using hresult
              have hrecursive :=
                ih { state with a := storage } (destination + 1) (source + 1)
                  htail (by omega)
              have hwriteFrame :=
                mergeLoTempRead_write_ne_of_eq_some state.a storage destination
                  other entry hwrite (Nat.ne_of_lt hother)
              exact hrecursive.trans hwriteFrame

/-- A successful data-to-temporary bulk copy initializes its whole destination
range.  In particular, this discharges the totality precondition of
`mergeLoTempRun_exists_of_initialized` for the initial `merge_lo` copy. -/
theorem mergeLoMemcpyDataToTemp_initialized_of_eq_some
    (site : MergeLoMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .temporary, source := .main })
    (count : Nat) (state state' : MergeState κ ν) (destination : Nat)
    (source : Int)
    (hresult : mergeLoMemcpyDataToTemp? site hDirection count state
      destination source = some state') :
    MergeLoTempRangeInitialized state'.a destination count := by
  induction count generalizing state destination source with
  | zero =>
      intro i hi
      omega
  | succ count ih =>
      cases hread : state.data.read? source with
      | none => simp [mergeLoMemcpyDataToTemp?, hread] at hresult
      | some entry =>
          cases hwrite : mergeLoTempWrite? state.a destination entry with
          | none =>
              simp [mergeLoMemcpyDataToTemp?, hread, hwrite] at hresult
          | some storage =>
              have htail :
                  mergeLoMemcpyDataToTemp? site hDirection count
                    { state with a := storage } (destination + 1) (source + 1) =
                      some state' := by
                simpa [mergeLoMemcpyDataToTemp?, hread, hwrite] using hresult
              have htailInitialized :=
                ih { state with a := storage } (destination + 1) (source + 1)
                  htail
              intro i hi
              cases i with
              | zero =>
                  have hpreserved :=
                    mergeLoMemcpyDataToTemp_read_before_of_eq_some site
                      hDirection count { state with a := storage } state'
                      (destination + 1) (source + 1) htail destination (by omega)
                  have hinitialized :=
                    mergeLoTempRead_write_self_of_eq_some state.a storage
                      destination entry hwrite
                  exact ⟨entry, by simpa using hpreserved.trans hinitialized⟩
              | succ i =>
                  have hiTail : i < count := by omega
                  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                    htailInitialized i hiTail

/-- Copy a temporary range into the main list.  As above, the recursive
implementation cannot be invoked without a tag proving the exact
temporary-to-main direction. -/
def mergeLoMemcpyTempToData?
    (site : MergeLoMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .main, source := .temporary }) :
    Nat → MergeState κ ν → Int → Nat → Option (MergeState κ ν)
  | 0, state, _, _ => some state
  | count + 1, state, destination, source => do
      let entry ← mergeLoTempRead? state.a source
      let data ← state.data.write? destination entry
      mergeLoMemcpyTempToData? site hDirection count
        { state with data := data } (destination + 1) (source + 1)

/-- Materialize an initialized active part of the temporary run as a
`SortSlice`, so the shared `gallop_right` transcription can inspect it. -/
def mergeLoGatherTempEntries? :
    Nat → TempStorage κ ν → Nat → Array (SortSliceEntry κ ν) →
      Option (Array (SortSliceEntry κ ν))
  | 0, _, _, entries => some entries
  | count + 1, storage, source, entries => do
      let entry ← mergeLoTempRead? storage source
      mergeLoGatherTempEntries? count storage (source + 1) (entries.push entry)

/-- Materialize an initialized temporary range as the slice consumed by
`gallop_right`. -/
def mergeLoTempRun? (storage : TempStorage κ ν) (source count : Nat) :
    Option (SortSlice κ ν) := do
  let entries ← mergeLoGatherTempEntries? count storage source #[]
  pure { entries := entries }

/-- Legacy name for the active temporary-run materializer. -/
abbrev tempRun? (storage : TempStorage κ ν) (source count : Nat) :
    Option (SortSlice κ ν) :=
  mergeLoTempRun? storage source count

theorem mergeLoGatherTempEntries_spec (count : Nat)
    (storage : TempStorage κ ν) (source : Nat)
    (initial result : Array (SortSliceEntry κ ν))
    (hresult : mergeLoGatherTempEntries? count storage source initial = some result) :
    result.size = initial.size + count ∧
      (∀ i < initial.size, result[i]? = initial[i]?) ∧
      ∀ i < count,
        result[initial.size + i]? = storage.cells[source + i]?.bind id := by
  induction count generalizing source initial with
  | zero =>
      simp only [mergeLoGatherTempEntries?] at hresult
      injection hresult with hresult
      subst result
      simp
  | succ count ih =>
      cases hcell : storage.cells[source]? with
      | none => simp [mergeLoGatherTempEntries?, mergeLoTempRead?, hcell] at hresult
      | some cell =>
          cases cell with
          | none => simp [mergeLoGatherTempEntries?, mergeLoTempRead?, hcell] at hresult
          | some entry =>
              have hnext :
                  mergeLoGatherTempEntries? count storage (source + 1)
                    (initial.push entry) = some result := by
                simpa [mergeLoGatherTempEntries?, mergeLoTempRead?, hcell] using hresult
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

/-- Gathering an initialized temporary range cannot fail. -/
theorem mergeLoGatherTempEntries_exists_of_initialized
    (storage : TempStorage κ ν) (source count : Nat)
    (initial : Array (SortSliceEntry κ ν))
    (hinitialized : MergeLoTempRangeInitialized storage source count) :
    ∃ result,
      mergeLoGatherTempEntries? count storage source initial = some result := by
  induction count generalizing source initial with
  | zero =>
      exact ⟨initial, rfl⟩
  | succ count ih =>
      rcases hinitialized 0 (by omega) with ⟨entry, hentry⟩
      have htail : MergeLoTempRangeInitialized storage (source + 1) count := by
        intro i hi
        have := hinitialized (i + 1) (by omega)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
      rcases ih (source + 1) (initial.push entry) htail with
        ⟨result, hresult⟩
      have hentry' : mergeLoTempRead? storage source = some entry := by
        simpa using hentry
      refine ⟨result, ?_⟩
      simp only [mergeLoGatherTempEntries?]
      rw [hentry']
      exact hresult

/-- A successful active-run materialization contains exactly the initialized
temporary cells from `source` through `source + count`. -/
theorem tempRun_cells_of_eq_some (storage : TempStorage κ ν)
    (source count : Nat) (slice : SortSlice κ ν)
    (hresult : tempRun? storage source count = some slice) :
    slice.entries.size = count ∧
      ∀ i < count,
        storage.cells[source + i]?.bind id = slice.entries[i]? := by
  unfold tempRun? mergeLoTempRun? at hresult
  cases hentries : mergeLoGatherTempEntries? count storage source #[] with
  | none => simp [hentries] at hresult
  | some entries =>
      have hmaterialized :
          (some ({ entries := entries } : SortSlice κ ν)) = some slice := by
        simpa [hentries] using hresult
      injection hmaterialized with hmaterialized
      subst slice
      rcases mergeLoGatherTempEntries_spec count storage source #[] entries hentries with
        ⟨hsize, _hprefix, hrange⟩
      exact ⟨by simpa using hsize, fun i hi => by
        simpa using (hrange i hi).symm⟩

/-- Merge-prefixed form of `tempRun_cells_of_eq_some` for external refinement
proofs. -/
theorem mergeLoTempRun_cells_of_eq_some (storage : TempStorage κ ν)
    (source count : Nat) (slice : SortSlice κ ν)
    (hresult : mergeLoTempRun? storage source count = some slice) :
    slice.entries.size = count ∧
      ∀ i < count,
        storage.cells[source + i]?.bind id = slice.entries[i]? :=
  tempRun_cells_of_eq_some storage source count slice hresult

/-- An initialized temporary range always materializes as a `SortSlice`. -/
theorem mergeLoTempRun_exists_of_initialized (storage : TempStorage κ ν)
    (source count : Nat)
    (hinitialized : MergeLoTempRangeInitialized storage source count) :
    ∃ slice, mergeLoTempRun? storage source count = some slice := by
  rcases mergeLoGatherTempEntries_exists_of_initialized storage source count #[]
      hinitialized with ⟨entries, hentries⟩
  refine ⟨{ entries := entries }, ?_⟩
  simp [mergeLoTempRun?, hentries]

/-- Conversely, successful materialization witnesses initialization of every
cell in the requested range. -/
theorem mergeLoTempRun_initialized_of_eq_some (storage : TempStorage κ ν)
    (source count : Nat) (slice : SortSlice κ ν)
    (hresult : mergeLoTempRun? storage source count = some slice) :
    MergeLoTempRangeInitialized storage source count := by
  rcases tempRun_cells_of_eq_some storage source count slice hresult with
    ⟨hsize, hcells⟩
  intro i hi
  have hiSize : i < slice.entries.size := by omega
  refine ⟨slice.entries[i], ?_⟩
  have hcell := hcells i hi
  rw [Array.getElem?_eq_getElem hiSize] at hcell
  simpa [mergeLoTempRead?] using hcell

/-- Materialization succeeds exactly for fully initialized temporary ranges. -/
theorem mergeLoTempRun_exists_iff_initialized (storage : TempStorage κ ν)
    (source count : Nat) :
    (∃ slice, mergeLoTempRun? storage source count = some slice) ↔
      MergeLoTempRangeInitialized storage source count := by
  constructor
  · rintro ⟨slice, hslice⟩
    exact mergeLoTempRun_initialized_of_eq_some storage source count slice hslice
  · exact mergeLoTempRun_exists_of_initialized storage source count

/-! ## Merge machine -/

structure MergeLoMachine (κ : Type u) (ν : Type v) where
  state : MergeState κ ν
  dest : Int
  aPos : Nat
  bPos : Int
  na : Nat
  nb : Nat
  minGallop : PySSize

inductive MergeLoPhase where
  | ordinary (aCount bCount : Nat)
  | galloping

/-- Compare a natural run count against a signed `Py_ssize_t`, preserving the
C signed comparison even for a raw model state with an unusual threshold. -/
def mergeLoCountAtLeastWord (count : Nat) (threshold : PySSize) : Bool :=
  !((BitVec.ofNat 64 count : PySSize).slt threshold)

def mergeLoCopyAIncr? (machine : MergeLoMachine κ ν) :
    Option (MergeLoMachine κ ν) := do
  let entry ← mergeLoTempRead? machine.state.a machine.aPos
  let data ← machine.state.data.write? machine.dest entry
  pure
    { machine with
      state := { machine.state with data := data }
      dest := machine.dest + 1
      aPos := machine.aPos + 1
      na := machine.na - 1 }

def mergeLoCopyBIncr? (machine : MergeLoMachine κ ν) :
    Option (MergeLoMachine κ ν) := do
  let entry ← machine.state.data.read? machine.bPos
  let data ← machine.state.data.write? machine.dest entry
  pure
    { machine with
      state := { machine.state with data := data }
      dest := machine.dest + 1
      bPos := machine.bPos + 1
      nb := machine.nb - 1 }

/-- The C `Succeed` label and its fallthrough into the shared remainder-copy
tail.  Comparator-error entry through C's `Fail` label is outside the total
Boolean comparator model, so this helper keeps the copyback and returns success. -/
def mergeLoSucceed? (machine : MergeLoMachine κ ν) :
    Option (MergeLoResult κ ν) := do
  let state ← mergeLoMemcpyTempToData? .finalTempToData rfl
    machine.na machine.state machine.dest machine.aPos
  pure (mergeLoSuccess state)

/-- The C `CopyB` label: shift the right remainder, then place the unique
remaining left entry at the end. -/
def mergeLoCopyB? (machine : MergeLoMachine κ ν) :
    Option (MergeLoResult κ ν) := do
  if machine.na = 1 ∧ 0 < machine.nb then
    let data ← mergeDataMemmove? .loCopyBTail machine.state.data
      machine.dest machine.bPos machine.nb
    let state := { machine.state with data := data }
    let entry ← mergeLoTempRead? state.a machine.aPos
    let data ← state.data.write? (machine.dest + Int.ofNat machine.nb) entry
    pure (mergeLoSuccess { state with data := data })
  else
    none

def mergeLoGallopFuelFailure
    (machine : MergeLoMachine κ ν) : Option (MergeLoResult κ ν) :=
  some (mergeLoOutOfFuel machine.state)

/-- One complete galloping-mode iteration.  Its continuation is supplied so
the structurally recursive driver remains the sole owner of outer fuel. -/
def mergeLoGallopRound?
    (machine : MergeLoMachine κ ν)
    (next : MergeLoMachine κ ν → Nat → Nat → Option (MergeLoResult κ ν)) :
    Option (MergeLoResult κ ν) := do
  if machine.na ≤ 1 ∨ machine.nb = 0 then
    none
  else
    let minGallop :=
      if (1 : PySSize).slt machine.minGallop then
        machine.minGallop - 1
      else
        machine.minGallop
    let state := { machine.state with min_gallop := minGallop }
    let machine := { machine with state := state, minGallop := minGallop }
    let firstB ← machine.state.data.read? machine.bPos
    let activeA ← mergeLoTempRun? machine.state.a machine.aPos machine.na
    mergeLoBindOptionAcross
        (gallopRight? machine.state activeA 0 firstB.key machine.na 0) fun gallopA =>
      if gallopA.fuelExhausted then
        mergeLoGallopFuelFailure machine
      else
        let aCount := gallopA.index
        if aCount > machine.na then
          none
        else do
          let state ← mergeLoMemcpyTempToData? .gallopTempToData rfl
            aCount machine.state machine.dest machine.aPos
          let machine : MergeLoMachine κ ν :=
            { machine with
              state := state
              dest := machine.dest + Int.ofNat aCount
              aPos := machine.aPos + aCount
              na := machine.na - aCount }
          -- Preserve C's inconsistent-comparator hedge: the gallop may consume
          -- all of A even though ordinary merge invariants expect a survivor.
          if machine.na = 0 then
            mergeLoSucceed? machine
          else if machine.na = 1 then
            mergeLoCopyB? machine
          else
            let machine ← mergeLoCopyBIncr? machine
            if machine.nb = 0 then
              mergeLoSucceed? machine
            else
              let firstA ← mergeLoTempRead? machine.state.a machine.aPos
              mergeLoBindOptionAcross
                  (gallopLeft? machine.state machine.state.data
                    machine.bPos firstA.key machine.nb 0) fun gallopB =>
                if gallopB.fuelExhausted then
                  mergeLoGallopFuelFailure machine
                else
                  let bCount := gallopB.index
                  if bCount > machine.nb then
                    none
                  else do
                    let data ← mergeDataMemmove? .loGallopB machine.state.data
                      machine.dest machine.bPos bCount
                    let machine : MergeLoMachine κ ν :=
                      { machine with
                        state := { machine.state with data := data }
                        dest := machine.dest + Int.ofNat bCount
                        bPos := machine.bPos + Int.ofNat bCount
                        nb := machine.nb - bCount }
                    if machine.nb = 0 then
                      mergeLoSucceed? machine
                    else
                      let machine ← mergeLoCopyAIncr? machine
                      if machine.na = 1 then
                        mergeLoCopyB? machine
                      else
                        next machine aCount bCount

def mergeLoLoop? :
    Nat → MergeLoMachine κ ν → MergeLoPhase → Option (MergeLoResult κ ν)
  | 0, machine, _ => some (mergeLoOutOfFuel machine.state)
  | fuel + 1, machine, .ordinary aCount bCount => do
      if machine.na ≤ 1 ∨ machine.nb = 0 then
        none
      else
        let firstA ← mergeLoTempRead? machine.state.a machine.aPos
        let firstB ← machine.state.data.read? machine.bPos
        if iflt machine.state.key_compare firstB.key firstA.key then
          let machine ← mergeLoCopyBIncr? machine
          let bCount := bCount + 1
          if machine.nb = 0 then
            mergeLoSucceed? machine
          else if mergeLoCountAtLeastWord bCount machine.minGallop then
            mergeLoLoop? fuel
              { machine with minGallop := machine.minGallop + 1 }
              .galloping
          else
            mergeLoLoop? fuel machine (.ordinary 0 bCount)
        else
          let machine ← mergeLoCopyAIncr? machine
          let aCount := aCount + 1
          if machine.na = 1 then
            mergeLoCopyB? machine
          else if mergeLoCountAtLeastWord aCount machine.minGallop then
            mergeLoLoop? fuel
              { machine with minGallop := machine.minGallop + 1 }
              .galloping
          else
            mergeLoLoop? fuel machine (.ordinary aCount 0)
  | fuel + 1, machine, .galloping =>
      mergeLoGallopRound? machine fun machine aCount bCount =>
        if MIN_GALLOP.toNat ≤ aCount ∨ MIN_GALLOP.toNat ≤ bCount then
          mergeLoLoop? fuel machine .galloping
        else
          let minGallop := machine.minGallop + 1
          let state := { machine.state with min_gallop := minGallop }
          mergeLoLoop? fuel
            { machine with state := state, minGallop := minGallop }
            (.ordinary 0 0)

/-! ## Review-visible control-flow equations -/

/-- Public equation exposing the A-side cell copied by an ordinary forward
step and every cursor/count update it performs. -/
theorem mergeLoCopyAIncr_equation (machine : MergeLoMachine κ ν) :
    mergeLoCopyAIncr? machine = (do
      let entry ← mergeLoTempRead? machine.state.a machine.aPos
      let data ← machine.state.data.write? machine.dest entry
      pure
        { machine with
          state := { machine.state with data := data }
          dest := machine.dest + 1
          aPos := machine.aPos + 1
          na := machine.na - 1 }) := by
  rfl

/-- Public equation exposing the B-side cell copied by an ordinary forward
step and every cursor/count update it performs. -/
theorem mergeLoCopyBIncr_equation (machine : MergeLoMachine κ ν) :
    mergeLoCopyBIncr? machine = (do
      let entry ← machine.state.data.read? machine.bPos
      let data ← machine.state.data.write? machine.dest entry
      pure
        { machine with
          state := { machine.state with data := data }
          dest := machine.dest + 1
          bPos := machine.bPos + 1
          nb := machine.nb - 1 }) := by
  rfl

/-- Public equation for the `CopyB` tail's same-store block move.  The right
remainder uses the `.loCopyBTail` overlap-safe memmove wrapper before the final
temporary A entry is installed. -/
theorem mergeLoCopyB_memmove_equation (machine : MergeLoMachine κ ν) :
    mergeLoCopyB? machine = (do
      if machine.na = 1 ∧ 0 < machine.nb then
        let data ← mergeDataMemmove? .loCopyBTail machine.state.data
          machine.dest machine.bPos machine.nb
        let state := { machine.state with data := data }
        let entry ← mergeLoTempRead? state.a machine.aPos
        let data ← state.data.write?
          (machine.dest + Int.ofNat machine.nb) entry
        pure (mergeLoSuccess { state with data := data })
      else
        none) := by
  rfl

/-- The complete `merge_lo` gallop round, stated as a public equation.  In
particular, the first search is `gallop_right(activeA, firstB, na, 0)` and its
insertion index is the number of A entries copied; the second is
`gallop_left(data, firstA, nb, 0)` and its insertion index is the number of B
entries moved. -/
theorem mergeLoGallopRound_equation
    (machine : MergeLoMachine κ ν)
    (next : MergeLoMachine κ ν → Nat → Nat →
      Option (MergeLoResult κ ν)) :
    mergeLoGallopRound? machine next = (do
      if machine.na ≤ 1 ∨ machine.nb = 0 then
        none
      else
        let minGallop :=
          if (1 : PySSize).slt machine.minGallop then
            machine.minGallop - 1
          else
            machine.minGallop
        let state := { machine.state with min_gallop := minGallop }
        let machine := { machine with state := state, minGallop := minGallop }
        let firstB ← machine.state.data.read? machine.bPos
        let activeA ← mergeLoTempRun? machine.state.a machine.aPos machine.na
        mergeLoBindOptionAcross
            (gallopRight? machine.state activeA 0 firstB.key machine.na 0)
            fun gallopA =>
          if gallopA.fuelExhausted then
            mergeLoGallopFuelFailure machine
          else
            let aCount := gallopA.index
            if aCount > machine.na then
              none
            else do
              let state ← mergeLoMemcpyTempToData? .gallopTempToData rfl
                aCount machine.state machine.dest machine.aPos
              let machine : MergeLoMachine κ ν :=
                { machine with
                  state := state
                  dest := machine.dest + Int.ofNat aCount
                  aPos := machine.aPos + aCount
                  na := machine.na - aCount }
              if machine.na = 0 then
                mergeLoSucceed? machine
              else if machine.na = 1 then
                mergeLoCopyB? machine
              else
                let machine ← mergeLoCopyBIncr? machine
                if machine.nb = 0 then
                  mergeLoSucceed? machine
                else
                  let firstA ← mergeLoTempRead? machine.state.a machine.aPos
                  mergeLoBindOptionAcross
                      (gallopLeft? machine.state machine.state.data
                        machine.bPos firstA.key machine.nb 0) fun gallopB =>
                    if gallopB.fuelExhausted then
                      mergeLoGallopFuelFailure machine
                    else
                      let bCount := gallopB.index
                      if bCount > machine.nb then
                        none
                      else do
                        let data ← mergeDataMemmove? .loGallopB machine.state.data
                          machine.dest machine.bPos bCount
                        let machine : MergeLoMachine κ ν :=
                          { machine with
                            state := { machine.state with data := data }
                            dest := machine.dest + Int.ofNat bCount
                            bPos := machine.bPos + Int.ofNat bCount
                            nb := machine.nb - bCount }
                        if machine.nb = 0 then
                          mergeLoSucceed? machine
                        else
                          let machine ← mergeLoCopyAIncr? machine
                          if machine.na = 1 then
                            mergeLoCopyB? machine
                          else
                            next machine aCount bCount) := by
  rfl

/-- In an ordinary `merge_lo` step, `firstB < firstA` copies B, increments the
B streak, and resets the A streak to zero on the ordinary continuation. -/
theorem mergeLoLoop_ordinary_copyB_equation
    (fuel : Nat) (machine : MergeLoMachine κ ν) (aCount bCount : Nat)
    (firstA firstB : SortSliceEntry κ ν)
    (hactive : ¬ (machine.na ≤ 1 ∨ machine.nb = 0))
    (hfirstA : mergeLoTempRead? machine.state.a machine.aPos = some firstA)
    (hfirstB : machine.state.data.read? machine.bPos = some firstB)
    (hcompare : machine.state.key_compare firstB.key firstA.key = true) :
    mergeLoLoop? (fuel + 1) machine (.ordinary aCount bCount) = (do
      let machine ← mergeLoCopyBIncr? machine
      let bCount := bCount + 1
      if machine.nb = 0 then
        mergeLoSucceed? machine
      else if mergeLoCountAtLeastWord bCount machine.minGallop then
        mergeLoLoop? fuel
          { machine with minGallop := machine.minGallop + 1 }
          .galloping
      else
        mergeLoLoop? fuel machine (.ordinary 0 bCount)) := by
  rw [mergeLoLoop?]
  simp [hactive, hfirstA, hfirstB, iflt, hcompare]

/-- In an ordinary `merge_lo` step, `¬(firstB < firstA)` copies A,
increments the A streak, and resets the B streak to zero on the ordinary
continuation. -/
theorem mergeLoLoop_ordinary_copyA_equation
    (fuel : Nat) (machine : MergeLoMachine κ ν) (aCount bCount : Nat)
    (firstA firstB : SortSliceEntry κ ν)
    (hactive : ¬ (machine.na ≤ 1 ∨ machine.nb = 0))
    (hfirstA : mergeLoTempRead? machine.state.a machine.aPos = some firstA)
    (hfirstB : machine.state.data.read? machine.bPos = some firstB)
    (hcompare : machine.state.key_compare firstB.key firstA.key = false) :
    mergeLoLoop? (fuel + 1) machine (.ordinary aCount bCount) = (do
      let machine ← mergeLoCopyAIncr? machine
      let aCount := aCount + 1
      if machine.na = 1 then
        mergeLoCopyB? machine
      else if mergeLoCountAtLeastWord aCount machine.minGallop then
        mergeLoLoop? fuel
          { machine with minGallop := machine.minGallop + 1 }
          .galloping
      else
        mergeLoLoop? fuel machine (.ordinary aCount 0)) := by
  rw [mergeLoLoop?]
  simp [hactive, hfirstA, hfirstB, iflt, hcompare]

/-- Stable-equality specialization of the A-copy equation: when equal keys do
not compare less than themselves, forward merging selects A, increments A's
streak, and resets B's streak. -/
theorem mergeLoLoop_ordinary_equal_keys_equation
    (fuel : Nat) (machine : MergeLoMachine κ ν) (aCount bCount : Nat)
    (firstA firstB : SortSliceEntry κ ν)
    (hactive : ¬ (machine.na ≤ 1 ∨ machine.nb = 0))
    (hfirstA : mergeLoTempRead? machine.state.a machine.aPos = some firstA)
    (hfirstB : machine.state.data.read? machine.bPos = some firstB)
    (hkeys : firstB.key = firstA.key)
    (hirrefl : machine.state.key_compare firstA.key firstA.key = false) :
    mergeLoLoop? (fuel + 1) machine (.ordinary aCount bCount) = (do
      let machine ← mergeLoCopyAIncr? machine
      let aCount := aCount + 1
      if machine.na = 1 then
        mergeLoCopyB? machine
      else if mergeLoCountAtLeastWord aCount machine.minGallop then
        mergeLoLoop? fuel
          { machine with minGallop := machine.minGallop + 1 }
          .galloping
      else
        mergeLoLoop? fuel machine (.ordinary aCount 0)) := by
  apply mergeLoLoop_ordinary_copyA_equation fuel machine aCount bCount
    firstA firstB hactive hfirstA hfirstB
  simpa [hkeys] using hirrefl

/-! ## Public transcription -/

/-- Transcription of CPython's stable left-to-right merge.

`ssa` and `ssb` are signed pointer-like indices into `state.data`.  The public
guard mirrors the C assertion domain: both runs are positive and representable,
and the right run begins immediately after the left run.  The caller-side
choice `na ≤ nb` and endpoint ordering are intentionally not rechecked here,
matching their status as `merge_at` obligations in the C source.
-/
def mergeLo? (state : MergeState κ ν) (ssa ssb : Int) (na nb : Nat) :
    Option (MergeLoResult κ ν) :=
  if 0 < na ∧ 0 < nb ∧ na ≤ PY_SSIZE_T_MAX ∧ nb ≤ PY_SSIZE_T_MAX ∧
      ssa + Int.ofNat na = ssb then
    let allocated := mergeGetmem state (BitVec.ofNat 64 na)
    if allocated.outcome = .guardRejected then
      some (mergeLoFailure allocated.state)
    else do
      let state ← mergeLoMemcpyDataToTemp? .initialDataToTemp rfl
        na allocated.state 0 ssa
      let machine : MergeLoMachine κ ν :=
        { state := state
          dest := ssa
          aPos := 0
          bPos := ssb
          na := na
          nb := nb
          minGallop := state.min_gallop }
      let machine ← mergeLoCopyBIncr? machine
      if machine.nb = 0 then
        mergeLoSucceed? machine
      else if machine.na = 1 then
        mergeLoCopyB? machine
      else
        mergeLoLoop? (na + nb + 1) machine (.ordinary 0 0)
  else
    none

/-! ## Layout-relevant structural frame -/

/-- The fields needed to transport `PendingLayout` across `merge_lo`.
Keeping them in one projection lets the recursive control-flow proof establish
all four frame facts at once. -/
private structure MergeLoLayoutFrame where
  listlen : PySSize
  basekeys : Nat
  dataSize : Nat
  pending : Array PendingRun

private def mergeLoLayoutFrame (state : MergeState κ ν) : MergeLoLayoutFrame :=
  { listlen := state.listlen
    basekeys := state.basekeys
    dataSize := state.data.entries.size
    pending := state.pending }

@[aesop safe forward]
private theorem dataWrite_layout (state : MergeState κ ν)
    (updated : SortSlice κ ν) (index : Int) (entry : SortSliceEntry κ ν)
    (h : state.data.write? index entry = some updated) :
    mergeLoLayoutFrame { state with data := updated } = mergeLoLayoutFrame state := by
  have hsize := SortSlice.write_entries_size_of_eq_some _ _ _ _ h
  simp [mergeLoLayoutFrame, hsize]

@[aesop safe forward]
private theorem dataMemmove_layout (state : MergeState κ ν)
    (updated : SortSlice κ ν) (dst src : Int) (count : Nat)
    (h : state.data.memmove? dst src count = some updated) :
    mergeLoLayoutFrame { state with data := updated } = mergeLoLayoutFrame state := by
  have hsize := SortSlice.memmove_entries_size_of_eq_some _ _ _ _ _ h
  simp [mergeLoLayoutFrame, hsize]

private theorem mergeLoMemcpyDataToTemp_layout
    (site : MergeLoMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .temporary, source := .main })
    (count : Nat) (state state' : MergeState κ ν) (destination : Nat)
    (source : Int)
    (h : mergeLoMemcpyDataToTemp? site hDirection count state destination source =
      some state') :
    mergeLoLayoutFrame state' = mergeLoLayoutFrame state := by
  induction count generalizing state destination source with
  | zero =>
      have := congrArg (Option.map mergeLoLayoutFrame) h
      simpa [mergeLoMemcpyDataToTemp?] using this.symm
  | succ count ih =>
      simp only [mergeLoMemcpyDataToTemp?, bind, Option.bind] at h
      split at h <;> simp_all
      split at h <;> simp_all
      simpa [mergeLoLayoutFrame] using ih _ _ _ h

private theorem mergeLoMemcpyTempToData_layout
    (site : MergeLoMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .main, source := .temporary })
    (count : Nat) (state state' : MergeState κ ν) (destination : Int)
    (source : Nat)
    (h : mergeLoMemcpyTempToData? site hDirection count state destination source =
      some state') :
    mergeLoLayoutFrame state' = mergeLoLayoutFrame state := by
  induction count generalizing state destination source with
  | zero =>
      have := congrArg (Option.map mergeLoLayoutFrame) h
      simpa [mergeLoMemcpyTempToData?] using this.symm
  | succ count ih =>
      simp only [mergeLoMemcpyTempToData?, bind, Option.bind] at h
      split at h <;> simp_all
      split at h <;> simp_all
      have htail := ih _ _ _ h
      have hsize := SortSlice.write_entries_size_of_eq_some _ _ _ _ ‹_›
      simpa [mergeLoLayoutFrame, hsize] using htail

@[aesop safe forward]
private theorem mergeLoInitialDataToTemp_layout
    (count : Nat) (state state' : MergeState κ ν) (destination : Nat)
    (source : Int)
    (h : mergeLoMemcpyDataToTemp? .initialDataToTemp rfl count state
      destination source = some state') :
    mergeLoLayoutFrame state' = mergeLoLayoutFrame state :=
  mergeLoMemcpyDataToTemp_layout .initialDataToTemp rfl count state state'
    destination source h

@[aesop safe forward]
private theorem mergeLoGallopTempToData_layout
    (count : Nat) (state state' : MergeState κ ν) (destination : Int)
    (source : Nat)
    (h : mergeLoMemcpyTempToData? .gallopTempToData rfl count state
      destination source = some state') :
    mergeLoLayoutFrame state' = mergeLoLayoutFrame state :=
  mergeLoMemcpyTempToData_layout .gallopTempToData rfl count state state'
    destination source h

@[aesop safe forward]
private theorem mergeLoFinalTempToData_layout
    (count : Nat) (state state' : MergeState κ ν) (destination : Int)
    (source : Nat)
    (h : mergeLoMemcpyTempToData? .finalTempToData rfl count state
      destination source = some state') :
    mergeLoLayoutFrame state' = mergeLoLayoutFrame state :=
  mergeLoMemcpyTempToData_layout .finalTempToData rfl count state state'
    destination source h

private theorem copyAIncr_layout
    (machine machine' : MergeLoMachine κ ν)
    (h : mergeLoCopyAIncr? machine = some machine') :
    mergeLoLayoutFrame machine'.state = mergeLoLayoutFrame machine.state := by
  simp only [mergeLoCopyAIncr?, bind, Option.bind] at h
  split at h <;> simp_all
  split at h <;> simp_all
  subst machine'
  have hsize := SortSlice.write_entries_size_of_eq_some _ _ _ _ ‹_›
  simp [mergeLoLayoutFrame, hsize]

private theorem copyBIncr_layout
    (machine machine' : MergeLoMachine κ ν)
    (h : mergeLoCopyBIncr? machine = some machine') :
    mergeLoLayoutFrame machine'.state = mergeLoLayoutFrame machine.state := by
  simp only [mergeLoCopyBIncr?, bind, Option.bind] at h
  split at h <;> simp_all
  split at h <;> simp_all
  subst machine'
  have hsize := SortSlice.write_entries_size_of_eq_some _ _ _ _ ‹_›
  simp [mergeLoLayoutFrame, hsize]

set_option linter.flexible false in
private theorem mergeLoSucceed_layout
    (machine : MergeLoMachine κ ν) (result : MergeLoResult κ ν)
    (h : mergeLoSucceed? machine = some result) :
    mergeLoLayoutFrame result.state = mergeLoLayoutFrame machine.state := by
  simp only [mergeLoSucceed?, bind, Option.bind] at h
  split at h <;> simp_all
  subst result
  apply mergeLoMemcpyTempToData_layout
  assumption

private theorem mergeLoCopyB_layout
    (machine : MergeLoMachine κ ν) (result : MergeLoResult κ ν)
    (h : mergeLoCopyB? machine = some result) :
    mergeLoLayoutFrame result.state = mergeLoLayoutFrame machine.state := by
  simp only [mergeLoCopyB?, bind, Option.bind] at h
  split at h
  · split at h <;> simp_all
    split at h <;> simp_all
    split at h <;> simp_all
    subst result
    have hmove := SortSlice.memmove_entries_size_of_eq_some _ _ _ _ _ ‹_›
    have hwrite := SortSlice.write_entries_size_of_eq_some _ _ _ _ ‹_›
    have hsize := hwrite.trans hmove
    simp [mergeLoSuccess, mergeLoLayoutFrame, hsize]
  · simp at h

attribute [aesop safe forward] copyAIncr_layout copyBIncr_layout mergeLoSucceed_layout
  mergeLoCopyB_layout

@[aesop safe forward]
private theorem layoutEqTrans (first second third : MergeLoLayoutFrame)
    (h₁ : first = second) (h₂ : second = third) : first = third :=
  h₁.trans h₂

@[aesop safe forward]
private theorem mergeLoGallopFuelFailure_layout
    (machine : MergeLoMachine κ ν) (result : MergeLoResult κ ν)
    (h : mergeLoGallopFuelFailure machine = some result) :
    mergeLoLayoutFrame result.state = mergeLoLayoutFrame machine.state := by
  simp [mergeLoGallopFuelFailure, mergeLoOutOfFuel] at h
  subst result
  rfl

@[aesop safe forward]
private theorem mergeGetmem_layout (state : MergeState κ ν) (need : PySSize) :
    mergeLoLayoutFrame (mergeGetmem state need).state = mergeLoLayoutFrame state := by
  simp only [mergeGetmem]
  split
  · rfl
  · split <;> simp only
    all_goals simp only [mergeFreemem]
    all_goals split <;> rfl

@[aesop safe forward]
private theorem mergeLoFailure_layout (state : MergeState κ ν)
    (result : MergeLoResult κ ν) (h : mergeLoFailure state = result) :
    mergeLoLayoutFrame result.state = mergeLoLayoutFrame state := by
  subst result
  rfl

set_option linter.flexible false in
set_option maxHeartbeats 5000000 in
-- The proof follows every branch of the deeply nested galloping round.
set_option maxRecDepth 10000 in
private theorem mergeLoGallopRound_layout
    (machine : MergeLoMachine κ ν)
    (next : MergeLoMachine κ ν → Nat → Nat → Option (MergeLoResult κ ν))
    (hnext : ∀ machine' aCount bCount result,
      next machine' aCount bCount = some result →
        mergeLoLayoutFrame result.state = mergeLoLayoutFrame machine'.state)
    (result : MergeLoResult κ ν)
    (h : mergeLoGallopRound? machine next = some result) :
    mergeLoLayoutFrame result.state = mergeLoLayoutFrame machine.state := by
  simp only [mergeLoGallopRound?, bind, Option.bind, mergeLoBindOptionAcross] at h
  split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try aesop (config := {
    enableSimp := false, maxRuleApplications := 500, warnOnNonterminal := false })
  all_goals
    rcases h with ⟨_, _, hresult⟩
    split at hresult
    · have hr := mergeLoCopyB_layout _ _ hresult
      aesop (config := { enableSimp := false, maxRuleApplications := 500 })
    · have hr := hnext _ _ _ _ hresult
      aesop (config := { enableSimp := false, maxRuleApplications := 500 })

set_option linter.flexible false in
set_option maxHeartbeats 5000000 in
-- The induction composes frame facts through the full merge-loop branch tree.
set_option maxRecDepth 10000 in
@[aesop safe forward]
private theorem mergeLoLoop_layout
    (fuel : Nat) (machine : MergeLoMachine κ ν) (phase : MergeLoPhase)
    (result : MergeLoResult κ ν)
    (h : mergeLoLoop? fuel machine phase = some result) :
    mergeLoLayoutFrame result.state = mergeLoLayoutFrame machine.state := by
  induction fuel generalizing machine phase result with
  | zero =>
      simp only [mergeLoLoop?] at h
      have := congrArg (fun r => mergeLoLayoutFrame r.state) (Option.some.inj h)
      simpa [mergeLoOutOfFuel] using this.symm
  | succ fuel ih =>
      cases phase with
      | ordinary aCount bCount =>
          simp only [mergeLoLoop?, bind, Option.bind] at h
          split at h <;> try simp at h
          all_goals try split at h <;> try simp at h
          all_goals try split at h <;> try simp at h
          all_goals try split at h <;> try simp at h
          all_goals try split at h <;> try simp at h
          all_goals try split at h <;> try simp at h
          all_goals try split at h <;> try simp at h
          all_goals try aesop (config := {
            enableSimp := false, maxRuleApplications := 500,
            warnOnNonterminal := false })
          all_goals exact (ih _ _ _ h).trans fwd
      | galloping =>
          let next : MergeLoMachine κ ν → Nat → Nat → Option (MergeLoResult κ ν) :=
            fun machine' aCount bCount =>
            if MIN_GALLOP.toNat ≤ aCount ∨ MIN_GALLOP.toNat ≤ bCount then
              mergeLoLoop? fuel machine' .galloping
            else
              let minGallop := machine'.minGallop + 1
              let state := { machine'.state with min_gallop := minGallop }
              mergeLoLoop? fuel
                { machine' with state := state, minGallop := minGallop }
                (.ordinary 0 0)
          have hround : mergeLoGallopRound? machine next = some result := by
            simpa only [mergeLoLoop?] using h
          apply mergeLoGallopRound_layout machine next _ result hround
          · intro machine' aCount bCount result' hresult
            dsimp only [next] at hresult
            split at hresult
            · exact ih machine' .galloping result' hresult
            · have hframe := ih _ (.ordinary 0 0) result' hresult
              simpa [mergeLoLayoutFrame] using hframe

set_option linter.flexible false in
/-- A successful `merge_lo` preserves every structural field used by
`PendingLayout`, even though it may rewrite entries in the fixed-size data
array and mutate merge-specific state. -/
theorem mergeLo_layout_frame_of_eq_some
    (state : MergeState κ ν) (ssa ssb : Int) (na nb : Nat)
    (result : MergeLoResult κ ν)
    (h : mergeLo? state ssa ssb na nb = some result) :
    result.state.listlen = state.listlen ∧
      result.state.basekeys = state.basekeys ∧
      result.state.data.entries.size = state.data.entries.size ∧
      result.state.pending = state.pending := by
  have hframe :
      mergeLoLayoutFrame result.state = mergeLoLayoutFrame state := by
    simp only [mergeLo?, bind, Option.bind] at h
    split at h <;> try simp at h
    all_goals try split at h <;> try simp at h
    all_goals try split at h <;> try simp at h
    all_goals try split at h <;> try simp at h
    all_goals try split at h <;> try simp at h
    all_goals try split at h <;> try simp at h
    all_goals aesop (config := { enableSimp := false, warnOnNonterminal := false })
    all_goals first
      | simpa [mergeLoFailure] using
          (mergeGetmem_layout state (BitVec.ofNat 64 na))
      | apply Eq.trans ?_ (mergeGetmem_layout state (BitVec.ofNat 64 na))
        assumption
  exact
    ⟨congrArg MergeLoLayoutFrame.listlen hframe,
      congrArg MergeLoLayoutFrame.basekeys hframe,
      congrArg MergeLoLayoutFrame.dataSize hframe,
      congrArg MergeLoLayoutFrame.pending hframe⟩

/-- `merge_lo` mutates data, temporary storage, allocation metadata, and the
adaptive gallop threshold, but never the pending-run stack. -/
theorem mergeLo_pending_eq_of_eq_some
    (state : MergeState κ ν) (ssa ssb : Int) (na nb : Nat)
    (result : MergeLoResult κ ν)
    (h : mergeLo? state ssa ssb na nb = some result) :
    result.state.pending = state.pending :=
  (mergeLo_layout_frame_of_eq_some state ssa ssb na nb result h).2.2.2

/-! Public executable regressions pin the ordinary-mode argument order and
stable equality branch. -/

def mergeLoStabilityRegressionState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 5
    basekeys := 0
    data :=
      { entries :=
          #[{ key := 3, value := some 30 },
            { key := 4, value := some 40 },
            { key := 2, value := some 20 },
            { key := 3, value := some 32 },
            { key := 3, value := some 33 }] }
    a :=
      { cells := Array.replicate 2 none
        backing := .inline
        hasValues := true }
    alloced := 2
    pending := #[]
    key_compare := fun left right => decide (left < right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

/-- Equal keys from the left run precede equal keys from the right run. -/
theorem mergeLo_straight_stability_regression :
    (mergeLo? mergeLoStabilityRegressionState 0 2 2 3).map
        (fun result => (result.returnCode, result.fuelExhausted,
          result.state.data.entries.toList)) =
      some
        (0, false,
          [{ key := 2, value := some 20 },
           { key := 3, value := some 30 },
           { key := 3, value := some 32 },
           { key := 3, value := some 33 },
           { key := 4, value := some 40 }]) := by
  decide

def mergeLoGallopStabilityRegressionState : MergeState Nat Nat :=
  { mergeLoStabilityRegressionState with
    min_gallop := 1
    listlen := 6
    data :=
      { entries :=
          #[{ key := 3, value := some 30 },
            { key := 4, value := some 40 },
            { key := 5, value := some 50 },
            { key := 1, value := some 10 },
            { key := 2, value := some 20 },
            { key := 3, value := some 31 }] }
    a :=
      { cells := Array.replicate 3 none
        backing := .inline
        hasValues := true }
    alloced := 3 }

/-- Min-gallop-one output keeps the left equal key first; it does not expose branch entry. -/
theorem mergeLo_gallop_stability_regression :
    (mergeLo? mergeLoGallopStabilityRegressionState 0 3 3 3).map
        (fun result => (result.returnCode, result.fuelExhausted,
          result.state.min_gallop, result.state.data.entries.toList)) =
      some
        (0, false, 1,
          [{ key := 1, value := some 10 },
           { key := 2, value := some 20 },
           { key := 3, value := some 30 },
           { key := 3, value := some 31 },
           { key := 4, value := some 40 },
           { key := 5, value := some 50 }]) := by
  decide

/-! The next regression deliberately uses the non-irreflexive comparator
`(· ≥ ·)`.  Its continuation always fails, so the successful result is an
observable witness that the first gallop's `index = na` result took the
`na = 0` Succeed hedge rather than continuing the round.  A strict-`<` control
on the identical geometry returns index zero and a different final ordering. -/

def mergeLoNaZeroHedgeRegressionState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 3
    basekeys := 0
    data :=
      { entries :=
          #[{ key := 99, value := some 99 },
            { key := 98, value := some 98 },
            { key := 0, value := some 0 }] }
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

def mergeLoNaZeroHedgeRegressionMachine : MergeLoMachine Nat Nat :=
  { state := mergeLoNaZeroHedgeRegressionState
    dest := 0
    aPos := 0
    bPos := 2
    na := 2
    nb := 1
    minGallop := MIN_GALLOP }

def mergeLoNaZeroHedgeStrictControlState : MergeState Nat Nat :=
  { mergeLoNaZeroHedgeRegressionState with
    key_compare := fun left right => decide (left < right) }

def mergeLoNaZeroHedgeStrictControlMachine : MergeLoMachine Nat Nat :=
  { mergeLoNaZeroHedgeRegressionMachine with
    state := mergeLoNaZeroHedgeStrictControlState }

/-- On one fixed machine geometry, the non-irreflexive comparator gives
`gallop_right.index = na` and reaches the `na = 0` success hedge, whereas the
strict control gives index zero and a different successful terminal path. -/
theorem mergeLo_inconsistentComparator_naZero_succeed_regression :
    mergeLoNaZeroHedgeRegressionState.key_compare 1 1 = true ∧
    ((mergeLoTempRun? mergeLoNaZeroHedgeRegressionState.a 0 2).bind
      (fun activeA => gallopRight? mergeLoNaZeroHedgeRegressionState
        activeA 0 0 2 0)) =
      some { index := 2, fuelExhausted := false } ∧
    ((mergeLoTempRun? mergeLoNaZeroHedgeStrictControlState.a 0 2).bind
      (fun activeA => gallopRight? mergeLoNaZeroHedgeStrictControlState
        activeA 0 0 2 0)) =
      some { index := 0, fuelExhausted := false } ∧
    (mergeLoGallopRound? mergeLoNaZeroHedgeRegressionMachine
      (fun _ _ _ => none)).map
        (fun result => (result.returnCode, result.fuelExhausted,
          result.state.data.entries.toList)) =
      some
        (0, false,
          [{ key := 1, value := some 10 },
           { key := 2, value := some 20 },
           { key := 0, value := some 0 }]) ∧
    (mergeLoGallopRound? mergeLoNaZeroHedgeStrictControlMachine
      (fun _ _ _ => none)).map
        (fun result => (result.returnCode, result.fuelExhausted,
          result.state.data.entries.toList)) =
      some
        (0, false,
          [{ key := 0, value := some 0 },
           { key := 1, value := some 10 },
           { key := 2, value := some 20 }]) := by
  decide

end CPythonListsort
