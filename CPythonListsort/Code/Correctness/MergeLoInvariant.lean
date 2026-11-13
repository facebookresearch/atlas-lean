/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.GallopCorrectness
import Code.Assembly.MergeLoSafety
import Code.Correctness.MergeSemanticPre
import Code.Correctness.MergeMovementCorrectness
import Code.Correctness.SortSliceRange
import Code.Correctness.StableMerge

/-!
# Semantic invariant for `merge_lo`

The reviewed safety invariant describes cursor geometry and storage validity.
This separate correctness invariant fixes immutable snapshots of the two
trimmed input runs and relates the emitted prefix, the live temporary suffix,
and the live main-data suffix to one shared stable-merge target.  Keeping this
layer separate prevents correctness-only order hypotheses from leaking into
the arbitrary-comparator safety theorem.
-/

namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-- Whole entries in the post-trimming left run copied by `merge_lo`. -/
def mergeLoLeftEntries (call : MergeAtCall (Occurrence alpha) nu) :
    List (SortSliceEntry (Occurrence alpha) nu) :=
  (sortSliceRangeEntries call.state.data call.ssa.toNat call.na).toList

/-- Whole entries in the adjacent post-trimming right run. -/
def mergeLoRightEntries (call : MergeAtCall (Occurrence alpha) nu) :
    List (SortSliceEntry (Occurrence alpha) nu) :=
  (sortSliceRangeEntries call.state.data call.ssb.toNat call.nb).toList

/-- Shared mathematical target of the physical left-to-right merge. -/
def mergeLoTargetEntries (lt : BoolComparator alpha)
    (call : MergeAtCall (Occurrence alpha) nu) :
    List (SortSliceEntry (Occurrence alpha) nu) :=
  stableEntryMerge lt (mergeLoLeftEntries call) (mergeLoRightEntries call)

@[simp]
theorem mergeLoLeftEntries_map_key
    (call : MergeAtCall (Occurrence alpha) nu) :
    (mergeLoLeftEntries call).map SortSliceEntry.key =
      (sortSliceRangeKeys call.state.data call.ssa.toNat call.na).toList := by
  simp [mergeLoLeftEntries, sortSliceRangeKeys]

@[simp]
theorem mergeLoRightEntries_map_key
    (call : MergeAtCall (Occurrence alpha) nu) :
    (mergeLoRightEntries call).map SortSliceEntry.key =
      (sortSliceRangeKeys call.state.data call.ssb.toNat call.nb).toList := by
  simp [mergeLoRightEntries, sortSliceRangeKeys]

/-! ## Public semantic input contract -/

/-- Direction-specific name for the shared post-trimming run contract. -/
abbrev MergeLoSemanticPre
    (lt : BoolComparator alpha)
    (call : MergeAtCall (Occurrence alpha) nu) : Prop :=
  MergeSemanticPre lt call

/-- Named bridge from the public `Sorted` field to the mapped-key relation
consumed by pure stable-merge correctness. -/
theorem MergeLoSemanticPre.leftKeysPairwise
    {lt : BoolComparator alpha}
    {call : MergeAtCall (Occurrence alpha) nu}
    (h : MergeLoSemanticPre lt call) :
    ((mergeLoLeftEntries call).map SortSliceEntry.key).Pairwise
      (DescendingRunSpec.SortedRelation lt) := by
  change ((mergeLoLeftEntries call).map SortSliceEntry.key).Pairwise
    (fun earlier later => lt later.value earlier.value = false)
  simpa [Sorted, occurrenceComparator] using h.leftSorted

/-- Named mapped-key bridge for the retained right run. -/
theorem MergeLoSemanticPre.rightKeysPairwise
    {lt : BoolComparator alpha}
    {call : MergeAtCall (Occurrence alpha) nu}
    (h : MergeLoSemanticPre lt call) :
    ((mergeLoRightEntries call).map SortSliceEntry.key).Pairwise
      (DescendingRunSpec.SortedRelation lt) := by
  change ((mergeLoRightEntries call).map SortSliceEntry.key).Pairwise
    (fun earlier later => lt later.value earlier.value = false)
  simpa [Sorted, occurrenceComparator] using h.rightSorted

/-- List-facing bridge from shared left-run `Sorted` to the relation used by
the direct temporary gallop source. -/
theorem MergeLoSemanticPre.leftPairwise
    {lt : BoolComparator alpha}
    {call : MergeAtCall (Occurrence alpha) nu}
    (h : MergeLoSemanticPre lt call) :
    (mergeLoLeftEntries call).Pairwise (fun earlier later =>
      lt later.key.value earlier.key.value = false) := by
  exact (List.pairwise_map.mp h.leftKeysPairwise :
    (mergeLoLeftEntries call).Pairwise (fun earlier later =>
      lt later.key.value earlier.key.value = false))

/-- List-facing bridge from shared right-run `Sorted` to the same internal
pointwise relation. -/
theorem MergeLoSemanticPre.rightPairwise
    {lt : BoolComparator alpha}
    {call : MergeAtCall (Occurrence alpha) nu}
    (h : MergeLoSemanticPre lt call) :
    (mergeLoRightEntries call).Pairwise (fun earlier later =>
      lt later.key.value earlier.key.value = false) := by
  exact (List.pairwise_map.mp h.rightKeysPairwise :
    (mergeLoRightEntries call).Pairwise (fun earlier later =>
      lt later.key.value earlier.key.value = false))

/-- Number of entries already emitted by a live forward cursor. -/
def mergeLoEmittedCount (call : MergeAtCall (Occurrence alpha) nu)
    (machine : MergeLoMachine (Occurrence alpha) nu) : Nat :=
  call.na + call.nb - (machine.na + machine.nb)

/-- Entries already emitted at the beginning of the affected main range. -/
def mergeLoEmittedEntries (call : MergeAtCall (Occurrence alpha) nu)
    (machine : MergeLoMachine (Occurrence alpha) nu) :
    List (SortSliceEntry (Occurrence alpha) nu) :=
  (sortSliceRangeEntries machine.state.data call.ssa.toNat
    (mergeLoEmittedCount call machine)).toList

/-- Exact logical contents of the active temporary A suffix. -/
def MergeLoTempSuffixMatches
    (storage : TempStorage (Occurrence alpha) nu)
    (left : List (SortSliceEntry (Occurrence alpha) nu))
    (source count : Nat) : Prop :=
  source + count ≤ left.length ∧
    ∀ i, i < count →
      mergeLoTempRead? storage (source + i) = left[source + i]?

/-- Exact logical contents of the active main-data B suffix. -/
def MergeLoMainSuffixMatches
    (data : SortSlice (Occurrence alpha) nu)
    (right : List (SortSliceEntry (Occurrence alpha) nu))
    (source : Int) (consumed count : Nat) : Prop :=
  consumed + count ≤ right.length ∧
    ∀ i, i < count →
      data.read? (source + Int.ofNat i) = right[consumed + i]?

/-- Functional invariant of every live `merge_lo` machine.

The decomposition is deliberately stated against immutable whole-entry lists.
It therefore pins key/payload pairing as well as sortedness and stability.
`lastStrict` is the correctness form of the trimmed right-end sentinel used by
the `na = 1` tail. -/
structure MergeLoSemanticMachineInvariant
    (lt : BoolComparator alpha)
    (call : MergeAtCall (Occurrence alpha) nu)
    (machine : MergeLoMachine (Occurrence alpha) nu) : Prop where
  safety : MergeLoMachineInvariant (mergeLoAllocated call).state call.na
    (call.ssb + Int.ofNat call.nb) machine
  comparator : machine.state.key_compare = occurrenceComparator lt
  leftCount : machine.na ≤ call.na
  rightCount : machine.nb ≤ call.nb
  leftPositive : 0 < machine.na
  tempActive :
    MergeLoTempSuffixMatches machine.state.a (mergeLoLeftEntries call)
      machine.aPos machine.na
  mainActive :
    MergeLoMainSuffixMatches machine.state.data (mergeLoRightEntries call)
      machine.bPos (call.nb - machine.nb) machine.nb
  emittedTarget :
    mergeLoEmittedEntries call machine =
      (mergeLoTargetEntries lt call).take (mergeLoEmittedCount call machine)
  remainingTarget :
    stableEntryMerge lt
        ((mergeLoLeftEntries call).drop machine.aPos)
        ((mergeLoRightEntries call).drop (call.nb - machine.nb)) =
      (mergeLoTargetEntries lt call).drop (mergeLoEmittedCount call machine)
  frame :
    SortSlice.EqualOutsideRange call.state.data machine.state.data
      call.ssa.toNat (call.na + call.nb)
  lastStrict : machine.nb > 0 →
    ∃ lastLeft lastRight,
      mergeLoTempRead? machine.state.a
          (machine.aPos + machine.na - 1) = some lastLeft ∧
      machine.state.data.read?
          (machine.bPos + Int.ofNat (machine.nb - 1)) = some lastRight ∧
      lt lastRight.key.value lastLeft.key.value = true

/-- A range of length `leftCount + rightCount` splits at `leftCount` while
retaining complete entries. -/
theorem sortSliceRangeEntries_toList_add_lo
    (slice : SortSlice alpha nu) (start leftCount rightCount : Nat) :
    (sortSliceRangeEntries slice start (leftCount + rightCount)).toList =
      (sortSliceRangeEntries slice start leftCount).toList ++
        (sortSliceRangeEntries slice (start + leftCount) rightCount).toList := by
  simp only [sortSliceRangeEntries_toList, List.take_add, List.drop_drop]

/-- Actual `merge_at` geometry transports signed adjacency to natural range
arithmetic. -/
theorem mergeLo_ssa_add_na_toNat
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call) :
    call.ssa.toNat + call.na = call.ssb.toNat := by
  have hadjacent := hgeometry.adjacent
  have hssa : Int.ofNat call.ssa.toNat = call.ssa :=
    Int.toNat_of_nonneg hgeometry.ssaNonnegative
  have hssb : Int.ofNat call.ssb.toNat = call.ssb :=
    Int.toNat_of_nonneg hgeometry.ssbNonnegative
  rw [← hssa, ← hssb] at hadjacent
  exact Int.ofNat_inj.mp (by simpa using hadjacent)

/-- The pre-state affected range is exactly the two adjacent trimmed runs. -/
theorem mergeLoCombinedEntries_eq_append
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call) :
    (sortSliceRangeEntries call.state.data call.ssa.toNat
        (call.na + call.nb)).toList =
      mergeLoLeftEntries call ++ mergeLoRightEntries call := by
  rw [sortSliceRangeEntries_toList_add_lo]
  simp only [mergeLoLeftEntries, mergeLoRightEntries]
  rw [mergeLo_ssa_add_na_toNat hgeometry]

/-- The mathematical target contains exactly the two input-run lengths. -/
@[simp]
theorem mergeLoTargetEntries_length (lt : BoolComparator alpha)
    (call : MergeAtCall (Occurrence alpha) nu) :
    (mergeLoTargetEntries lt call).length =
      (mergeLoLeftEntries call).length + (mergeLoRightEntries call).length := by
  simp [mergeLoTargetEntries, stableEntryMerge, List.length_merge]

/-- Comparator transport from the semantic binding to the tagged order. -/
theorem MergeLoSemanticMachineInvariant.order
    {lt : BoolComparator alpha}
    {call : MergeAtCall (Occurrence alpha) nu}
    {machine : MergeLoMachine (Occurrence alpha) nu}
    (horder : BoolStrictWeakOrder lt)
    (h : MergeLoSemanticMachineInvariant lt call machine) :
    BoolStrictWeakOrder machine.state.key_compare := by
  rw [h.comparator]
  exact horder.occurrenceComparator

/-! ## Pure forward stable-merge equations -/

/-- Forward merge selects the left whole entry whenever the right head is not
strictly before it. -/
theorem stableEntryMerge_cons_left_of_not_lt
    (lt : BoolComparator alpha)
    (leftHead rightHead : SortSliceEntry (Occurrence alpha) nu)
    (left right : List (SortSliceEntry (Occurrence alpha) nu))
    (hcompare : lt rightHead.key.value leftHead.key.value = false) :
    stableEntryMerge lt (leftHead :: left) (rightHead :: right) =
      leftHead :: stableEntryMerge lt left (rightHead :: right) := by
  simp [stableEntryMerge, stableEntryLE, stableOccurrenceLE, hcompare]

/-- Forward merge selects the right whole entry exactly on a strict
right-before-left comparison. -/
theorem stableEntryMerge_cons_right_of_lt
    (lt : BoolComparator alpha)
    (leftHead rightHead : SortSliceEntry (Occurrence alpha) nu)
    (left right : List (SortSliceEntry (Occurrence alpha) nu))
    (hcompare : lt rightHead.key.value leftHead.key.value = true) :
    stableEntryMerge lt (leftHead :: left) (rightHead :: right) =
      rightHead :: stableEntryMerge lt (leftHead :: left) right := by
  simp [stableEntryMerge, stableEntryLE, stableOccurrenceLE, hcompare]

/-- A left prefix whose entries all belong before the current right head peels
unchanged from a stable forward merge. -/
theorem stableEntryMerge_left_prefix
    (lt : BoolComparator alpha)
    (block left : List (SortSliceEntry (Occurrence alpha) nu))
    (rightHead : SortSliceEntry (Occurrence alpha) nu)
    (right : List (SortSliceEntry (Occurrence alpha) nu))
    (hblock : ∀ entry ∈ block,
      lt rightHead.key.value entry.key.value = false) :
    stableEntryMerge lt (block ++ left) (rightHead :: right) =
      block ++ stableEntryMerge lt left (rightHead :: right) := by
  induction block with
  | nil => rfl
  | cons head tail ih =>
      rw [List.cons_append,
        stableEntryMerge_cons_left_of_not_lt lt head rightHead
          (tail ++ left) right (hblock head (by simp))]
      rw [ih (fun entry hentry => hblock entry (by simp [hentry]))]
      rfl

/-- A right prefix whose entries are all strictly before the current left head
peels unchanged from a stable forward merge. -/
theorem stableEntryMerge_right_prefix
    (lt : BoolComparator alpha)
    (leftHead : SortSliceEntry (Occurrence alpha) nu)
    (left block right : List (SortSliceEntry (Occurrence alpha) nu))
    (hblock : ∀ entry ∈ block,
      lt entry.key.value leftHead.key.value = true) :
    stableEntryMerge lt (leftHead :: left) (block ++ right) =
      block ++ stableEntryMerge lt (leftHead :: left) right := by
  induction block with
  | nil => rfl
  | cons head tail ih =>
      rw [List.cons_append,
        stableEntryMerge_cons_right_of_lt lt leftHead head left
          (tail ++ right) (hblock head (by simp))]
      rw [ih (fun entry hentry => hblock entry (by simp [hentry]))]
      rfl

/-- The immutable left snapshot has exactly the call-site left length. -/
theorem mergeLoLeftEntries_length
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call) :
    (mergeLoLeftEntries call).length = call.na := by
  simp only [mergeLoLeftEntries, Array.length_toList]
  exact sortSliceRangeEntries_size call.state.data call.ssa.toNat call.na (by
    have hmerged := hgeometry.mergedRange
    have hssa : Int.ofNat call.ssa.toNat = call.ssa :=
      Int.toNat_of_nonneg hgeometry.ssaNonnegative
    rw [← hssa] at hmerged
    simp only [Int.ofNat_eq_natCast, Nat.cast_add] at hmerged
    omega)

/-- The immutable right snapshot has exactly the call-site right length. -/
theorem mergeLoRightEntries_length
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call) :
    (mergeLoRightEntries call).length = call.nb := by
  simp only [mergeLoRightEntries, Array.length_toList]
  exact sortSliceRangeEntries_size call.state.data call.ssb.toNat call.nb (by
    have hright := hgeometry.rightRange
    have hssb : Int.ofNat call.ssb.toNat = call.ssb :=
      Int.toNat_of_nonneg hgeometry.ssbNonnegative
    rw [← hssb] at hright
    exact Int.ofNat_le.mp (by simpa only [Int.ofNat_eq_natCast, Nat.cast_add]
      using hright))

/-- Pointwise signed read of the immutable left snapshot. -/
theorem mergeLoLeftEntries_getElem?_eq_read
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call)
    (offset : Nat) (hoffset : offset < call.na) :
    (mergeLoLeftEntries call)[offset]? =
      call.state.data.read? (call.ssa + Int.ofNat offset) := by
  have hssa : Int.ofNat call.ssa.toNat = call.ssa :=
    Int.toNat_of_nonneg hgeometry.ssaNonnegative
  have hleftStop : call.ssa.toNat + call.na ≤
      call.state.data.entries.size := by
    have hmerged := hgeometry.mergedRange
    rw [← hssa] at hmerged
    apply Int.ofNat_le.mp
    simp only [Int.ofNat_eq_natCast, Nat.cast_add] at hmerged ⊢
    omega
  have hget := sortSliceRangeEntries_getElem call.state.data call.ssa.toNat
    call.na offset hleftStop hoffset
  rw [mergeLoLeftEntries, List.getElem?_eq_getElem (by
    simp only [Array.length_toList]
    rw [sortSliceRangeEntries_size _ _ _ hleftStop]
    exact hoffset)]
  simp only [Array.getElem_toList]
  rw [hget]
  have hindex : call.ssa + Int.ofNat offset =
      Int.ofNat (call.ssa.toNat + offset) := by
    simp only [Int.ofNat_eq_natCast, Nat.cast_add]
    have hssa' : (call.ssa.toNat : Int) = call.ssa := hssa
    rw [hssa']
  rw [hindex, SortSlice.read?_ofNat]
  simp [show call.ssa.toNat + offset < call.state.data.entries.size by omega]

/-- Pointwise signed read of the immutable right snapshot. -/
theorem mergeLoRightEntries_getElem?_eq_read
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call)
    (offset : Nat) (hoffset : offset < call.nb) :
    (mergeLoRightEntries call)[offset]? =
      call.state.data.read? (call.ssb + Int.ofNat offset) := by
  have hssb : Int.ofNat call.ssb.toNat = call.ssb :=
    Int.toNat_of_nonneg hgeometry.ssbNonnegative
  have hrightStop : call.ssb.toNat + call.nb ≤
      call.state.data.entries.size := by
    have hright := hgeometry.rightRange
    rw [← hssb] at hright
    apply Int.ofNat_le.mp
    simpa only [Int.ofNat_eq_natCast, Nat.cast_add] using hright
  have hget := sortSliceRangeEntries_getElem call.state.data call.ssb.toNat
    call.nb offset hrightStop hoffset
  rw [mergeLoRightEntries, List.getElem?_eq_getElem (by
    simp only [Array.length_toList]
    rw [sortSliceRangeEntries_size _ _ _ hrightStop]
    exact hoffset)]
  simp only [Array.getElem_toList]
  rw [hget]
  have hindex : call.ssb + Int.ofNat offset =
      Int.ofNat (call.ssb.toNat + offset) := by
    simp only [Int.ofNat_eq_natCast, Nat.cast_add]
    have hssb' : (call.ssb.toNat : Int) = call.ssb := hssb
    rw [hssb']
  rw [hindex, SortSlice.read?_ofNat]
  simp [show call.ssb.toNat + offset < call.state.data.entries.size by omega]

/-- Safety cursor accounting identifies the physical destination with the
number of mathematical entries already emitted. -/
theorem MergeLoSemanticMachineInvariant.dest_toNat
    {lt : BoolComparator alpha}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {machine : MergeLoMachine (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call)
    (h : MergeLoSemanticMachineInvariant lt call machine) :
    machine.dest.toNat = call.ssa.toNat + mergeLoEmittedCount call machine := by
  have hssa : Int.ofNat call.ssa.toNat = call.ssa :=
    Int.toNat_of_nonneg hgeometry.ssaNonnegative
  have hdest : Int.ofNat machine.dest.toNat = machine.dest :=
    Int.toNat_of_nonneg h.safety.destNonnegative
  have hadjCall := hgeometry.adjacent
  have hadjMachine := h.safety.adjacency
  have hrightMachine := h.safety.rightAccounting
  have hleftCount := h.leftCount
  have hrightCount := h.rightCount
  have hcounts : machine.na + machine.nb ≤ call.na + call.nb := by omega
  have htotalInt :
      machine.dest + Int.ofNat (machine.na + machine.nb) =
        call.ssa + Int.ofNat (call.na + call.nb) := by
    simp only [Int.ofNat_eq_natCast, Nat.cast_add]
    simp only [Int.ofNat_eq_natCast] at hadjCall hadjMachine hrightMachine
    omega
  unfold mergeLoEmittedCount
  apply Int.ofNat_inj.mp
  change Int.ofNat machine.dest.toNat =
    Int.ofNat (call.ssa.toNat +
      (call.na + call.nb - (machine.na + machine.nb)))
  rw [hdest]
  simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_sub hcounts]
  have hssa' : (call.ssa.toNat : Int) = call.ssa := hssa
  rw [hssa']
  simp only [Int.ofNat_eq_natCast, Nat.cast_add] at htotalInt
  omega

/-! ## Generic forward-fill preservation -/

/-- A block written immediately after the already-correct emitted prefix
extends that prefix and composes its local frame into the full merge range. -/
theorem mergeLo_forwardFillBlock
    {origin before after : SortSlice alpha nu}
    {base total emitted count : Nat}
    {target block : List (SortSliceEntry alpha nu)}
    (hbound : emitted + count ≤ total)
    (hcurrentFrame :
      SortSlice.EqualOutsideRange origin before base total)
    (hstepFrame : SortSlice.EqualOutsideRange before after
      (base + emitted) count)
    (hblock :
      (sortSliceRangeEntries after (base + emitted) count).toList = block)
    (hemitted :
      (sortSliceRangeEntries before base emitted).toList = target.take emitted)
    (hassemble : target.take emitted ++ block = target.take (emitted + count)) :
    (sortSliceRangeEntries after base (emitted + count)).toList =
        target.take (emitted + count) ∧
      SortSlice.EqualOutsideRange origin after base total := by
  have hprefix :
      (sortSliceRangeEntries after base emitted).toList =
        (sortSliceRangeEntries before base emitted).toList := by
    have hentries := hstepFrame.entries_eq_of_disjoint base emitted
      (Or.inl (by omega))
    exact congrArg Array.toList hentries.symm
  constructor
  · rw [sortSliceRangeEntries_toList_add, hprefix, hemitted, hblock, hassemble]
  · exact hcurrentFrame.trans
      (hstepFrame.widen (by omega) (by omega))

/-- One semantic merge step can be discharged from four exact facts: the
physical block written next, its local frame, the corresponding stable-merge
peel equation, and exact descriptions of the two new active suffixes.  This is
shared by ordinary cells and both gallop blocks. -/
theorem MergeLoSemanticMachineInvariant.advance
    {lt : BoolComparator alpha}
    {call : MergeAtCall (Occurrence alpha) nu}
    {machine next : MergeLoMachine (Occurrence alpha) nu}
    (h : MergeLoSemanticMachineInvariant lt call machine)
    (count : Nat) (block : List (SortSliceEntry (Occurrence alpha) nu))
    (hsafety : MergeLoMachineInvariant (mergeLoAllocated call).state call.na
      (call.ssb + Int.ofNat call.nb) next)
    (hcomparator : next.state.key_compare = occurrenceComparator lt)
    (hleftCount : next.na ≤ call.na)
    (hrightCount : next.nb ≤ call.nb)
    (hleftPositive : 0 < next.na)
    (htempActive : MergeLoTempSuffixMatches next.state.a
      (mergeLoLeftEntries call) next.aPos next.na)
    (hmainActive : MergeLoMainSuffixMatches next.state.data
      (mergeLoRightEntries call) next.bPos (call.nb - next.nb) next.nb)
    (hemit : mergeLoEmittedCount call next =
      mergeLoEmittedCount call machine + count)
    (hblockLength : block.length = count)
    (hblockRange :
      (sortSliceRangeEntries next.state.data
        (call.ssa.toNat + mergeLoEmittedCount call machine) count).toList = block)
    (hstepFrame : SortSlice.EqualOutsideRange machine.state.data next.state.data
      (call.ssa.toNat + mergeLoEmittedCount call machine) count)
    (hpeel :
      stableEntryMerge lt
          ((mergeLoLeftEntries call).drop machine.aPos)
          ((mergeLoRightEntries call).drop (call.nb - machine.nb)) =
        block ++
          stableEntryMerge lt
            ((mergeLoLeftEntries call).drop next.aPos)
            ((mergeLoRightEntries call).drop (call.nb - next.nb)))
    (hlastStrict : next.nb > 0 →
      ∃ lastLeft lastRight,
        mergeLoTempRead? next.state.a (next.aPos + next.na - 1) = some lastLeft ∧
        next.state.data.read?
            (next.bPos + Int.ofNat (next.nb - 1)) = some lastRight ∧
        lt lastRight.key.value lastLeft.key.value = true) :
    MergeLoSemanticMachineInvariant lt call next := by
  let emitted := mergeLoEmittedCount call machine
  let target := mergeLoTargetEntries lt call
  let remaining := stableEntryMerge lt
    ((mergeLoLeftEntries call).drop next.aPos)
    ((mergeLoRightEntries call).drop (call.nb - next.nb))
  have hnextCounts : next.na + next.nb ≤ call.na + call.nb := by omega
  have hemitBound : emitted + count ≤ call.na + call.nb := by
    rw [← hemit]
    unfold mergeLoEmittedCount
    omega
  have hblockTarget : block = (target.drop emitted).take count := by
    have hdecomp : block ++ remaining = target.drop emitted := by
      exact hpeel.symm.trans h.remainingTarget
    have htaken := congrArg (List.take count) hdecomp
    simpa [hblockLength] using htaken
  have hremaining : remaining = target.drop (emitted + count) := by
    have hdecomp : block ++ remaining = target.drop emitted := by
      exact hpeel.symm.trans h.remainingTarget
    have hdropped := congrArg (List.drop count) hdecomp
    simpa [hblockLength, List.drop_drop] using hdropped
  have hassemble : target.take emitted ++ block =
      target.take (emitted + count) := by
    rw [hblockTarget]
    exact List.take_add.symm
  have hfilled := mergeLo_forwardFillBlock hemitBound h.frame hstepFrame
    hblockRange h.emittedTarget hassemble
  refine
    { safety := hsafety
      comparator := hcomparator
      leftCount := hleftCount
      rightCount := hrightCount
      leftPositive := hleftPositive
      tempActive := htempActive
      mainActive := hmainActive
      emittedTarget := ?_
      remainingTarget := ?_
      frame := hfilled.2
      lastStrict := hlastStrict }
  · simpa [mergeLoEmittedEntries, emitted, target, hemit] using hfilled.1
  · simpa [remaining, target, emitted, hemit] using hremaining

/-! ## Active-head views -/

/-- A successful read of the active temporary head exposes the corresponding
head/tail decomposition of the immutable left snapshot. -/
theorem MergeLoSemanticMachineInvariant.left_drop_eq_cons
    {lt : BoolComparator alpha}
    {call : MergeAtCall (Occurrence alpha) nu}
    {machine : MergeLoMachine (Occurrence alpha) nu}
    (h : MergeLoSemanticMachineInvariant lt call machine)
    (entry : SortSliceEntry (Occurrence alpha) nu)
    (hread : mergeLoTempRead? machine.state.a machine.aPos = some entry) :
    (mergeLoLeftEntries call).drop machine.aPos =
      entry :: (mergeLoLeftEntries call).drop (machine.aPos + 1) := by
  have hactive := h.tempActive.2 0 h.leftPositive
  simp only [Nat.add_zero] at hactive
  have hget : (mergeLoLeftEntries call)[machine.aPos]? = some entry :=
    hactive.symm.trans hread
  rcases List.getElem?_eq_some_iff.mp hget with ⟨hin, heq⟩
  rw [List.drop_eq_getElem_cons hin, heq]

/-- A successful read of the active main head exposes the corresponding
head/tail decomposition of the immutable right snapshot. -/
theorem MergeLoSemanticMachineInvariant.right_drop_eq_cons
    {lt : BoolComparator alpha}
    {call : MergeAtCall (Occurrence alpha) nu}
    {machine : MergeLoMachine (Occurrence alpha) nu}
    (h : MergeLoSemanticMachineInvariant lt call machine)
    (hnb : 0 < machine.nb)
    (entry : SortSliceEntry (Occurrence alpha) nu)
    (hread : machine.state.data.read? machine.bPos = some entry) :
    (mergeLoRightEntries call).drop (call.nb - machine.nb) =
      entry ::
        (mergeLoRightEntries call).drop (call.nb - machine.nb + 1) := by
  have hactive := h.mainActive.2 0 hnb
  have hactive' : machine.state.data.read? machine.bPos =
      (mergeLoRightEntries call)[call.nb - machine.nb]? := by
    simpa using hactive
  have hget :
      (mergeLoRightEntries call)[call.nb - machine.nb]? = some entry :=
    hactive'.symm.trans hread
  rcases List.getElem?_eq_some_iff.mp hget with ⟨hin, heq⟩
  rw [List.drop_eq_getElem_cons hin, heq]

/-! ## Ordinary one-cell preservation -/

/-- The ordinary A branch preserves the semantic invariant and emits the left
head.  The false comparison is the stable tie direction. -/
theorem MergeLoSemanticMachineInvariant.copyA
    {lt : BoolComparator alpha}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {machine next : MergeLoMachine (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call)
    (h : MergeLoSemanticMachineInvariant lt call machine)
    (hna : 1 < machine.na) (hnb : 0 < machine.nb)
    (leftHead rightHead : SortSliceEntry (Occurrence alpha) nu)
    (hleftRead : mergeLoTempRead? machine.state.a machine.aPos = some leftHead)
    (hrightRead : machine.state.data.read? machine.bPos = some rightHead)
    (hcompare : lt rightHead.key.value leftHead.key.value = false)
    (hcopy : mergeLoCopyAIncr? machine = some next)
    (hsafety : MergeLoMachineInvariant (mergeLoAllocated call).state call.na
      (call.ssb + Int.ofNat call.nb) next) :
    MergeLoSemanticMachineInvariant lt call next := by
  rcases mergeLoCopyAIncr_spec_of_eq_some machine next hcopy with
    ⟨hdest, haPos, hbPos, hnaNext, hnbNext, hcomparator, htemp,
      hdestRead, hreadFrame⟩
  have hdestCast : Int.ofNat machine.dest.toNat = machine.dest :=
    Int.toNat_of_nonneg h.safety.destNonnegative
  have hstepFrame0 : SortSlice.EqualOutsideRange machine.state.data
      next.state.data machine.dest.toNat 1 := by
    rw [← hdestCast] at hreadFrame
    exact hreadFrame.equalOutsideRange_ofNat
  have hdestNat := h.dest_toNat hgeometry
  have hstepFrame : SortSlice.EqualOutsideRange machine.state.data
      next.state.data
        (call.ssa.toNat + mergeLoEmittedCount call machine) 1 := by
    simpa only [hdestNat] using hstepFrame0
  have hdestIndex := h.safety.destInBounds (by omega)
  have hdestBound : machine.dest.toNat + 1 ≤ next.state.data.entries.size := by
    rw [SortSlice.IndexInBounds] at hdestIndex
    have hlt : machine.dest.toNat < machine.state.data.entries.size := by
      apply Int.ofNat_lt.mp
      have hdestCast' : (machine.dest.toNat : Int) = machine.dest := hdestCast
      rw [hdestCast']
      exact hdestIndex.2
    rw [← hreadFrame.1]
    omega
  have hblock0 :
      (sortSliceRangeEntries next.state.data machine.dest.toNat 1).toList =
        [leftHead] := by
    apply sortSliceRangeEntries_toList_eq_of_reads _ _ _ _ hdestBound (by simp)
    intro offset hoffset
    have hoffsetZero : offset = 0 := by omega
    subst offset
    simpa only [Nat.add_zero, hdestCast, List.getElem?_cons_zero] using
      hdestRead.trans hleftRead
  have hblock :
      (sortSliceRangeEntries next.state.data
        (call.ssa.toNat + mergeLoEmittedCount call machine) 1).toList =
          [leftHead] := by
    simpa only [← hdestNat] using hblock0
  have htempActive : MergeLoTempSuffixMatches next.state.a
      (mergeLoLeftEntries call) next.aPos next.na := by
    constructor
    · rw [haPos, hnaNext]
      have := h.tempActive.1
      omega
    · intro offset hoffset
      have hoffset' : offset + 1 < machine.na := by
        rw [hnaNext] at hoffset
        omega
      rw [htemp, haPos]
      have hread := h.tempActive.2 (offset + 1) hoffset'
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hread
  have hmainActive : MergeLoMainSuffixMatches next.state.data
      (mergeLoRightEntries call) next.bPos (call.nb - next.nb) next.nb := by
    constructor
    · simpa only [hnbNext] using h.mainActive.1
    · intro offset hoffset
      have hoffset' : offset < machine.nb := by
        simpa only [hnbNext] using hoffset
      rw [hbPos, hnbNext]
      have hpreserved := hreadFrame.2
        (machine.bPos + Int.ofNat offset) (Or.inr (by
          have hadj := h.safety.adjacency
          simp only [Int.ofNat_eq_natCast] at hadj ⊢
          omega))
      exact hpreserved.trans (h.mainActive.2 offset hoffset')
  have hemit : mergeLoEmittedCount call next =
      mergeLoEmittedCount call machine + 1 := by
    unfold mergeLoEmittedCount
    rw [hnaNext, hnbNext]
    have hleft := h.leftCount
    have hright := h.rightCount
    omega
  have hleftDrop := h.left_drop_eq_cons leftHead hleftRead
  have hrightDrop := h.right_drop_eq_cons hnb rightHead hrightRead
  have hpeel :
      stableEntryMerge lt
          ((mergeLoLeftEntries call).drop machine.aPos)
          ((mergeLoRightEntries call).drop (call.nb - machine.nb)) =
        [leftHead] ++
          stableEntryMerge lt
            ((mergeLoLeftEntries call).drop next.aPos)
            ((mergeLoRightEntries call).drop (call.nb - next.nb)) := by
    rw [hleftDrop, hrightDrop]
    rw [stableEntryMerge_cons_left_of_not_lt lt leftHead rightHead _ _ hcompare]
    rw [← hrightDrop]
    simp only [haPos, hnbNext, List.singleton_append]
  have hlastStrict : next.nb > 0 →
      ∃ lastLeft lastRight,
        mergeLoTempRead? next.state.a (next.aPos + next.na - 1) = some lastLeft ∧
        next.state.data.read?
            (next.bPos + Int.ofNat (next.nb - 1)) = some lastRight ∧
        lt lastRight.key.value lastLeft.key.value = true := by
    intro hnextNb
    rcases h.lastStrict (by simpa only [hnbNext] using hnextNb) with
      ⟨lastLeft, lastRight, hlastLeft, hlastRight, hstrict⟩
    refine ⟨lastLeft, lastRight, ?_, ?_, hstrict⟩
    · have hindex : machine.aPos + 1 + (machine.na - 1) - 1 =
          machine.aPos + machine.na - 1 := by omega
      rw [htemp, haPos, hnaNext, hindex]
      exact hlastLeft
    · rw [hbPos, hnbNext]
      have hpreserved := hreadFrame.2
        (machine.bPos + Int.ofNat (machine.nb - 1)) (Or.inr (by
          have hadj := h.safety.adjacency
          simp only [Int.ofNat_eq_natCast] at hadj ⊢
          omega))
      exact hpreserved.trans hlastRight
  apply h.advance 1 [leftHead] hsafety (hcomparator.trans h.comparator)
    (by rw [hnaNext]; exact (Nat.sub_le machine.na 1).trans h.leftCount)
    (by rw [hnbNext]; exact h.rightCount)
    (by rw [hnaNext]; omega) htempActive hmainActive hemit (by simp)
    hblock hstepFrame hpeel hlastStrict

/-- The ordinary B branch preserves the semantic invariant and emits the right
head exactly when it compares strictly before the left head. -/
theorem MergeLoSemanticMachineInvariant.copyB
    {lt : BoolComparator alpha}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {machine next : MergeLoMachine (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call)
    (h : MergeLoSemanticMachineInvariant lt call machine)
    (hna : 0 < machine.na) (hnb : 0 < machine.nb)
    (leftHead rightHead : SortSliceEntry (Occurrence alpha) nu)
    (hleftRead : mergeLoTempRead? machine.state.a machine.aPos = some leftHead)
    (hrightRead : machine.state.data.read? machine.bPos = some rightHead)
    (hcompare : lt rightHead.key.value leftHead.key.value = true)
    (hcopy : mergeLoCopyBIncr? machine = some next)
    (hsafety : MergeLoMachineInvariant (mergeLoAllocated call).state call.na
      (call.ssb + Int.ofNat call.nb) next) :
    MergeLoSemanticMachineInvariant lt call next := by
  rcases mergeLoCopyBIncr_spec_of_eq_some machine next hcopy with
    ⟨hdest, haPos, hbPos, hnaNext, hnbNext, hcomparator, htemp,
      hdestRead, hreadFrame⟩
  have hdestCast : Int.ofNat machine.dest.toNat = machine.dest :=
    Int.toNat_of_nonneg h.safety.destNonnegative
  have hstepFrame0 : SortSlice.EqualOutsideRange machine.state.data
      next.state.data machine.dest.toNat 1 := by
    rw [← hdestCast] at hreadFrame
    exact hreadFrame.equalOutsideRange_ofNat
  have hdestNat := h.dest_toNat hgeometry
  have hstepFrame : SortSlice.EqualOutsideRange machine.state.data
      next.state.data
        (call.ssa.toNat + mergeLoEmittedCount call machine) 1 := by
    simpa only [hdestNat] using hstepFrame0
  have hdestIndex := h.safety.destInBounds (by omega)
  have hdestBound : machine.dest.toNat + 1 ≤ next.state.data.entries.size := by
    rw [SortSlice.IndexInBounds] at hdestIndex
    have hlt : machine.dest.toNat < machine.state.data.entries.size := by
      apply Int.ofNat_lt.mp
      have hdestCast' : (machine.dest.toNat : Int) = machine.dest := hdestCast
      rw [hdestCast']
      exact hdestIndex.2
    rw [← hreadFrame.1]
    omega
  have hblock0 :
      (sortSliceRangeEntries next.state.data machine.dest.toNat 1).toList =
        [rightHead] := by
    apply sortSliceRangeEntries_toList_eq_of_reads _ _ _ _ hdestBound (by simp)
    intro offset hoffset
    have hoffsetZero : offset = 0 := by omega
    subst offset
    simpa only [Nat.add_zero, hdestCast, List.getElem?_cons_zero] using
      hdestRead.trans hrightRead
  have hblock :
      (sortSliceRangeEntries next.state.data
        (call.ssa.toNat + mergeLoEmittedCount call machine) 1).toList =
          [rightHead] := by
    simpa only [← hdestNat] using hblock0
  have hconsumed : call.nb - next.nb = call.nb - machine.nb + 1 := by
    rw [hnbNext]
    have := h.rightCount
    omega
  have htempActive : MergeLoTempSuffixMatches next.state.a
      (mergeLoLeftEntries call) next.aPos next.na := by
    rw [htemp, haPos, hnaNext]
    exact h.tempActive
  have hmainActive : MergeLoMainSuffixMatches next.state.data
      (mergeLoRightEntries call) next.bPos (call.nb - next.nb) next.nb := by
    constructor
    · rw [hconsumed, hnbNext]
      have := h.mainActive.1
      omega
    · intro offset hoffset
      have hoffsetOld : offset + 1 < machine.nb := by
        rw [hnbNext] at hoffset
        omega
      rw [hbPos, hconsumed]
      have hpreserved := hreadFrame.2
        (machine.bPos + 1 + Int.ofNat offset) (Or.inr (by
          have hadj := h.safety.adjacency
          simp only [Int.ofNat_eq_natCast] at hadj ⊢
          omega))
      have hold := h.mainActive.2 (offset + 1) hoffsetOld
      have hidxInt : machine.bPos + Int.ofNat (offset + 1) =
          machine.bPos + 1 + Int.ofNat offset := by
        simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one]
        omega
      have hidxNat : call.nb - machine.nb + (offset + 1) =
          call.nb - machine.nb + 1 + offset := by omega
      rw [hidxInt, hidxNat] at hold
      have hold' : machine.state.data.read?
            (machine.bPos + 1 + Int.ofNat offset) =
          (mergeLoRightEntries call)[call.nb - machine.nb + 1 + offset]? := by
        exact hold
      exact hpreserved.trans hold'
  have hemit : mergeLoEmittedCount call next =
      mergeLoEmittedCount call machine + 1 := by
    unfold mergeLoEmittedCount
    rw [hnaNext, hnbNext]
    have hleft := h.leftCount
    have hright := h.rightCount
    omega
  have hleftDrop := h.left_drop_eq_cons leftHead hleftRead
  have hrightDrop := h.right_drop_eq_cons hnb rightHead hrightRead
  have hpeel :
      stableEntryMerge lt
          ((mergeLoLeftEntries call).drop machine.aPos)
          ((mergeLoRightEntries call).drop (call.nb - machine.nb)) =
        [rightHead] ++
          stableEntryMerge lt
            ((mergeLoLeftEntries call).drop next.aPos)
            ((mergeLoRightEntries call).drop (call.nb - next.nb)) := by
    rw [hleftDrop, hrightDrop]
    rw [stableEntryMerge_cons_right_of_lt lt leftHead rightHead _ _ hcompare]
    rw [← hleftDrop]
    simp only [haPos, hconsumed, List.singleton_append]
  have hlastStrict : next.nb > 0 →
      ∃ lastLeft lastRight,
        mergeLoTempRead? next.state.a (next.aPos + next.na - 1) = some lastLeft ∧
        next.state.data.read?
            (next.bPos + Int.ofNat (next.nb - 1)) = some lastRight ∧
        lt lastRight.key.value lastLeft.key.value = true := by
    intro hnextNb
    have holdNb : 0 < machine.nb := hnb
    rcases h.lastStrict holdNb with
      ⟨lastLeft, lastRight, hlastLeft, hlastRight, hstrict⟩
    refine ⟨lastLeft, lastRight, ?_, ?_, hstrict⟩
    · simpa only [htemp, haPos, hnaNext] using hlastLeft
    · have hindex : machine.bPos + 1 + Int.ofNat (machine.nb - 1 - 1) =
          machine.bPos + Int.ofNat (machine.nb - 1) := by
        simp only [Int.ofNat_eq_natCast, Nat.cast_sub (by omega : 1 ≤ machine.nb - 1),
          Nat.cast_one]
        omega
      rw [hbPos, hnbNext, hindex]
      have hpreserved := hreadFrame.2
        (machine.bPos + Int.ofNat (machine.nb - 1)) (Or.inr (by
          have hadj := h.safety.adjacency
          simp only [Int.ofNat_eq_natCast] at hadj ⊢
          omega))
      exact hpreserved.trans hlastRight
  apply h.advance 1 [rightHead] hsafety (hcomparator.trans h.comparator)
    (by rw [hnaNext]; exact h.leftCount)
    (by rw [hnbNext]; exact (Nat.sub_le machine.nb 1).trans h.rightCount)
    (by rw [hnaNext]; exact h.leftPositive) htempActive hmainActive hemit (by simp)
    hblock hstepFrame hpeel hlastStrict

/-! ## Terminal extraction -/

/-- Exact semantic output carried by either successful terminal helper. -/
structure MergeLoSemanticOutput
    (lt : BoolComparator alpha)
    (call : MergeAtCall (Occurrence alpha) nu)
    (state : MergeState (Occurrence alpha) nu) : Prop where
  exactRange :
    (sortSliceRangeEntries state.data call.ssa.toNat
      (call.na + call.nb)).toList = mergeLoTargetEntries lt call
  frame : SortSlice.EqualOutsideRange call.state.data state.data
    call.ssa.toNat (call.na + call.nb)

/-- When B is exhausted, `Succeed` copies the exact remaining A suffix after
the already-correct prefix, yielding the complete stable-merge target. -/
theorem MergeLoSemanticMachineInvariant.succeed
    {lt : BoolComparator alpha}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {machine : MergeLoMachine (Occurrence alpha) nu}
    {result : MergeLoResult (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call)
    (h : MergeLoSemanticMachineInvariant lt call machine)
    (hnb : machine.nb = 0)
    (hresult : mergeLoSucceed? machine = some result) :
    MergeLoSemanticOutput lt call result.state := by
  rw [mergeLoSucceed?] at hresult
  rcases Option.bind_eq_some_iff.mp hresult with ⟨copied, hcopy, hfinal⟩
  injection hfinal with hfinal
  subst result
  have hdestCast : Int.ofNat machine.dest.toNat = machine.dest :=
    Int.toNat_of_nonneg h.safety.destNonnegative
  have hreadFrame := mergeLoMemcpyTempToData_readFrame_of_eq_some
    .finalTempToData rfl machine.na machine.state copied machine.dest
      machine.aPos hcopy
  have hstepFrame0 : SortSlice.EqualOutsideRange machine.state.data copied.data
      machine.dest.toNat machine.na := by
    rw [← hdestCast] at hreadFrame
    exact hreadFrame.equalOutsideRange_ofNat
  have hdestNat := h.dest_toNat hgeometry
  have hstepFrame : SortSlice.EqualOutsideRange machine.state.data copied.data
      (call.ssa.toNat + mergeLoEmittedCount call machine) machine.na := by
    simpa only [hdestNat] using hstepFrame0
  have hleftLength := mergeLoLeftEntries_length hgeometry
  have hblockLength :
      ((mergeLoLeftEntries call).drop machine.aPos).length = machine.na := by
    rw [List.length_drop, hleftLength]
    have haccount := h.safety.tempAccounting
    omega
  have hdestRange := h.safety.destRange machine.na (by rfl)
  have hstop : machine.dest.toNat + machine.na ≤ copied.data.entries.size := by
    have hsigned : Int.ofNat (machine.dest.toNat + machine.na) ≤
        Int.ofNat machine.state.data.entries.size := by
      simp only [Int.ofNat_eq_natCast, Nat.cast_add]
      have hdestCast' : (machine.dest.toNat : Int) = machine.dest := hdestCast
      rw [hdestCast']
      exact hdestRange.2
    have hnat := Int.ofNat_le.mp hsigned
    rw [← hreadFrame.1]
    exact hnat
  have hblock0 :
      (sortSliceRangeEntries copied.data machine.dest.toNat machine.na).toList =
        (mergeLoLeftEntries call).drop machine.aPos := by
    apply sortSliceRangeEntries_toList_eq_of_reads _ _ _ _ hstop hblockLength
    intro offset hoffset
    have hcopied := mergeLoMemcpyTempToData_read_range_of_eq_some
      .finalTempToData rfl machine.na machine.state copied machine.dest
        machine.aPos hcopy offset hoffset
    have hactive := h.tempActive.2 offset hoffset
    rw [List.getElem?_drop]
    have hindex : Int.ofNat (machine.dest.toNat + offset) =
        machine.dest + Int.ofNat offset := by
      simp only [Int.ofNat_eq_natCast, Nat.cast_add]
      have hdestCast' : (machine.dest.toNat : Int) = machine.dest := hdestCast
      rw [hdestCast']
    rw [hindex]
    exact hcopied.trans hactive
  have hblock :
      (sortSliceRangeEntries copied.data
        (call.ssa.toNat + mergeLoEmittedCount call machine) machine.na).toList =
          (mergeLoLeftEntries call).drop machine.aPos := by
    simpa only [← hdestNat] using hblock0
  have hrightLength := mergeLoRightEntries_length hgeometry
  have hrightEmpty :
      (mergeLoRightEntries call).drop (call.nb - machine.nb) = [] := by
    rw [hnb, Nat.sub_zero, List.drop_eq_nil_iff.mpr]
    exact hrightLength.le
  have hremaining :
      (mergeLoLeftEntries call).drop machine.aPos =
        (mergeLoTargetEntries lt call).drop
          (mergeLoEmittedCount call machine) := by
    simpa [hrightEmpty, stableEntryMerge] using h.remainingTarget
  have hblockTarget :
      (mergeLoLeftEntries call).drop machine.aPos =
        ((mergeLoTargetEntries lt call).drop
          (mergeLoEmittedCount call machine)).take machine.na := by
    rw [← hremaining]
    simp [hblockLength]
  have hassemble :
      (mergeLoTargetEntries lt call).take (mergeLoEmittedCount call machine) ++
          (mergeLoLeftEntries call).drop machine.aPos =
        (mergeLoTargetEntries lt call).take
          (mergeLoEmittedCount call machine + machine.na) := by
    rw [hblockTarget]
    exact List.take_add.symm
  have htotal : mergeLoEmittedCount call machine + machine.na =
      call.na + call.nb := by
    unfold mergeLoEmittedCount
    have hleft := h.leftCount
    have hright := h.rightCount
    omega
  have hfilled := mergeLo_forwardFillBlock (by omega) h.frame hstepFrame
    hblock h.emittedTarget hassemble
  refine ⟨?_, hfilled.2⟩
  change (sortSliceRangeEntries copied.data call.ssa.toNat
    (call.na + call.nb)).toList = mergeLoTargetEntries lt call
  rw [← htotal]
  rw [hfilled.1]
  have htargetLength : (mergeLoTargetEntries lt call).length =
      call.na + call.nb := by
    rw [mergeLoTargetEntries_length, hleftLength, hrightLength]
  exact List.take_of_length_le (by rw [htargetLength]; omega)

/-- With one A entry left, `CopyB` moves the exact remaining B suffix and then
places that A entry after it.  Sortedness plus the strict high-end sentinel
proves this physical block is precisely the remaining stable merge. -/
theorem MergeLoSemanticMachineInvariant.copyBTail
    {lt : BoolComparator alpha}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {machine : MergeLoMachine (Occurrence alpha) nu}
    {result : MergeLoResult (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call)
    (horder : BoolStrictWeakOrder lt)
    (hsemantic : MergeLoSemanticPre lt call)
    (h : MergeLoSemanticMachineInvariant lt call machine)
    (hna : machine.na = 1) (hnb : 0 < machine.nb)
    (hresult : mergeLoCopyB? machine = some result) :
    MergeLoSemanticOutput lt call result.state := by
  rw [mergeLoCopyB?, if_pos ⟨hna, hnb⟩] at hresult
  rcases Option.bind_eq_some_iff.mp hresult with ⟨movedData, hmove, hresult⟩
  rcases Option.bind_eq_some_iff.mp hresult with ⟨lastLeft, hleftRead, hresult⟩
  rcases Option.bind_eq_some_iff.mp hresult with ⟨finalData, hwrite, hfinal⟩
  injection hfinal with hfinal
  subst result
  let movedState : MergeState (Occurrence alpha) nu :=
    { machine.state with data := movedData }
  let finalState : MergeState (Occurrence alpha) nu :=
    { movedState with data := finalData }
  change MergeLoSemanticOutput lt call finalState
  have hdestCast : Int.ofNat machine.dest.toNat = machine.dest :=
    Int.toNat_of_nonneg h.safety.destNonnegative
  have hfinalIndexNonnegative :
      0 ≤ machine.dest + Int.ofNat machine.nb :=
    add_nonneg h.safety.destNonnegative (Int.natCast_nonneg _)
  have hfinalIndexNat :
      (machine.dest + Int.ofNat machine.nb).toNat =
        machine.dest.toNat + machine.nb := by
    apply Int.ofNat_inj.mp
    rw [Int.toNat_of_nonneg hfinalIndexNonnegative]
    simp only [Int.ofNat_eq_natCast, Nat.cast_add]
    have hdestCast' : (machine.dest.toNat : Int) = machine.dest := hdestCast
    rw [hdestCast']
  have hmoveFrame := mergeDataMemmove_equalOutsideRange_of_eq_some
    .loCopyBTail machine.state.data movedData machine.dest machine.bPos
      machine.nb hmove
  have hwriteFrame := SortSlice.write_equalOutsideRange_of_eq_some
    movedData finalData (machine.dest + Int.ofNat machine.nb) lastLeft hwrite
  rw [hfinalIndexNat] at hwriteFrame
  have hstepFrame0 : SortSlice.EqualOutsideRange machine.state.data finalData
      machine.dest.toNat (machine.nb + 1) :=
    (hmoveFrame.widen (by omega) (by omega)).trans
      (hwriteFrame.widen (by omega) (by omega))
  have hdestNat := h.dest_toNat hgeometry
  have hstepFrame : SortSlice.EqualOutsideRange machine.state.data finalData
      (call.ssa.toNat + mergeLoEmittedCount call machine)
        (machine.nb + 1) := by
    simpa only [hdestNat] using hstepFrame0
  let right := (mergeLoRightEntries call).drop (call.nb - machine.nb)
  have hrightLengthAll := mergeLoRightEntries_length hgeometry
  have hrightLength : right.length = machine.nb := by
    dsimp only [right]
    rw [List.length_drop, hrightLengthAll]
    have := h.rightCount
    omega
  have hrightNe : right ≠ [] := by
    intro hempty
    have : right.length = 0 := by simp [hempty]
    omega
  have hrightPairwiseAll :
      (mergeLoRightEntries call).Pairwise (fun earlier later =>
        lt later.key.value earlier.key.value = false) :=
    hsemantic.rightPairwise
  have hrightPairwise : right.Pairwise (fun earlier later =>
      lt later.key.value earlier.key.value = false) := by
    exact hrightPairwiseAll.drop
  rcases h.lastStrict hnb with
    ⟨sentinelLeft, lastRight, hsentinelLeft, hlastRight, hstrict⟩
  have hleftEq : sentinelLeft = lastLeft := by
    have hsentinelAtHead :
        mergeLoTempRead? machine.state.a machine.aPos = some sentinelLeft := by
      simpa [hna] using hsentinelLeft
    exact Option.some.inj (hsentinelAtHead.symm.trans hleftRead)
  subst sentinelLeft
  have hrightLast : right.getLast? = some lastRight := by
    rw [List.getLast?_eq_getElem?, hrightLength, List.getElem?_drop]
    have hactive := h.mainActive.2 (machine.nb - 1) (by omega)
    have hindexNat : call.nb - machine.nb + (machine.nb - 1) =
        call.nb - 1 := by
      have := h.rightCount
      omega
    have hindexInt : machine.bPos + Int.ofNat (machine.nb - 1) =
        machine.bPos + Int.ofNat (machine.nb - 1) := rfl
    rw [hindexNat]
    rw [hindexNat] at hactive
    exact hactive.symm.trans hlastRight
  have hallRight : ∀ entry ∈ right,
      lt entry.key.value lastLeft.key.value = true := by
    have hall := all_right_lt_suffix_of_pairwise_of_last_lt horder right
      [lastLeft] hrightNe hrightPairwise (by
        intro suffixEntry hsuffix
        simp only [List.mem_singleton] at hsuffix
        subst suffixEntry
        have hgetLast : right.getLast hrightNe = lastRight :=
          (List.getLast_eq_iff_getLast?_eq_some hrightNe).2 hrightLast
        rw [hgetLast]
        exact hstrict)
    intro entry hentry
    exact hall entry hentry lastLeft (by simp)
  have hleftDrop :
      (mergeLoLeftEntries call).drop machine.aPos = [lastLeft] := by
    have hhead := h.left_drop_eq_cons lastLeft hleftRead
    have hleftLength := mergeLoLeftEntries_length hgeometry
    have hdropLength :
        ((mergeLoLeftEntries call).drop machine.aPos).length = 1 := by
      rw [List.length_drop, hleftLength]
      have haccount := h.safety.tempAccounting
      omega
    rw [hhead]
    have htailLength :
        ((mergeLoLeftEntries call).drop (machine.aPos + 1)).length = 0 := by
      simpa [hhead] using hdropLength
    rw [List.length_eq_zero_iff.mp htailLength]
  have hpureRemaining : stableEntryMerge lt
      ((mergeLoLeftEntries call).drop machine.aPos) right =
        right ++ [lastLeft] := by
    rw [hleftDrop]
    simpa [stableEntryMerge] using
      stableEntryMerge_snoc_left_of_all_right_lt lt [] right lastLeft hallRight
  have hremaining : right ++ [lastLeft] =
      (mergeLoTargetEntries lt call).drop
        (mergeLoEmittedCount call machine) := by
    exact hpureRemaining.symm.trans h.remainingTarget
  have hmoveStop : machine.dest.toNat + machine.nb ≤ movedData.entries.size := by
    have hrange := h.safety.destTotalRange machine.nb (by omega)
    have hsigned : Int.ofNat (machine.dest.toNat + machine.nb) ≤
        Int.ofNat machine.state.data.entries.size := by
      simp only [Int.ofNat_eq_natCast, Nat.cast_add]
      have hdestCast' : (machine.dest.toNat : Int) = machine.dest := hdestCast
      rw [hdestCast']
      exact hrange.2
    have hnat := Int.ofNat_le.mp hsigned
    have hframe := mergeDataMemmove_readFrame_of_eq_some .loCopyBTail
      machine.state.data movedData machine.dest machine.bPos machine.nb hmove
    rw [← hframe.1]
    exact hnat
  have hmoveBlock :
      (sortSliceRangeEntries movedData machine.dest.toNat machine.nb).toList =
        right := by
    apply sortSliceRangeEntries_toList_eq_of_reads _ _ _ _ hmoveStop hrightLength
    intro offset hoffset
    rw [List.getElem?_drop]
    have hcopied := mergeDataMemmove_copiesRange_of_eq_some .loCopyBTail
      machine.state.data movedData machine.dest machine.bPos machine.nb hmove
      offset hoffset
    have hactive := h.mainActive.2 offset hoffset
    have hindex : Int.ofNat (machine.dest.toNat + offset) =
        machine.dest + Int.ofNat offset := by
      simp only [Int.ofNat_eq_natCast, Nat.cast_add]
      have hdestCast' : (machine.dest.toNat : Int) = machine.dest := hdestCast
      rw [hdestCast']
    rw [hindex]
    exact hcopied.trans hactive
  have hfinalPrefix :
      (sortSliceRangeEntries finalData machine.dest.toNat machine.nb).toList =
        right := by
    have heq := hwriteFrame.entries_eq_of_disjoint machine.dest.toNat machine.nb
      (Or.inl (by omega))
    rw [← hmoveBlock]
    exact congrArg Array.toList heq.symm
  have hfinalSingleton :
      (sortSliceRangeEntries finalData (machine.dest.toNat + machine.nb) 1).toList =
        [lastLeft] := by
    have hwriteSelf := SortSlice.write_read_self_of_eq_some movedData finalData
      (machine.dest + Int.ofNat machine.nb) lastLeft hwrite
    have hsize := SortSlice.write_entries_size_of_eq_some movedData finalData
      (machine.dest + Int.ofNat machine.nb) lastLeft hwrite
    have hbound : machine.dest.toNat + machine.nb + 1 ≤ finalData.entries.size := by
      have hfinalIndex := (SortSlice.write_eq_some_spec movedData finalData
        (machine.dest + Int.ofNat machine.nb) lastLeft hwrite).2
      rcases hfinalIndex with ⟨hin, _⟩
      rw [hfinalIndexNat] at hin
      omega
    apply sortSliceRangeEntries_toList_eq_of_reads _ _ _ _ hbound (by simp)
    intro offset hoffset
    have hoffsetZero : offset = 0 := by omega
    subst offset
    have hindex : Int.ofNat (machine.dest.toNat + machine.nb + 0) =
        machine.dest + Int.ofNat machine.nb := by
      simp only [Nat.add_zero, Int.ofNat_eq_natCast, Nat.cast_add]
      have hdestCast' : (machine.dest.toNat : Int) = machine.dest := hdestCast
      rw [hdestCast']
    simpa only [hindex, List.getElem?_cons_zero] using hwriteSelf
  have hblock0 :
      (sortSliceRangeEntries finalData machine.dest.toNat
        (machine.nb + 1)).toList = right ++ [lastLeft] := by
    rw [sortSliceRangeEntries_toList_add, hfinalPrefix, hfinalSingleton]
  have hblock :
      (sortSliceRangeEntries finalData
        (call.ssa.toNat + mergeLoEmittedCount call machine)
          (machine.nb + 1)).toList = right ++ [lastLeft] := by
    simpa only [← hdestNat] using hblock0
  have hblockLength : (right ++ [lastLeft]).length = machine.nb + 1 := by
    simp [hrightLength]
  have hblockTarget : right ++ [lastLeft] =
      ((mergeLoTargetEntries lt call).drop
        (mergeLoEmittedCount call machine)).take (machine.nb + 1) := by
    rw [← hremaining]
    simp [hblockLength]
  have hassemble :
      (mergeLoTargetEntries lt call).take (mergeLoEmittedCount call machine) ++
          (right ++ [lastLeft]) =
        (mergeLoTargetEntries lt call).take
          (mergeLoEmittedCount call machine + (machine.nb + 1)) := by
    rw [hblockTarget]
    exact List.take_add.symm
  have htotal : mergeLoEmittedCount call machine + (machine.nb + 1) =
      call.na + call.nb := by
    unfold mergeLoEmittedCount
    have hleft := h.leftCount
    have hright := h.rightCount
    omega
  have hfilled := mergeLo_forwardFillBlock (by omega) h.frame hstepFrame
    hblock h.emittedTarget hassemble
  refine ⟨?_, hfilled.2⟩
  change (sortSliceRangeEntries finalData call.ssa.toNat
    (call.na + call.nb)).toList = mergeLoTargetEntries lt call
  rw [← htotal, hfilled.1]
  have htargetLength : (mergeLoTargetEntries lt call).length =
      call.na + call.nb := by
    rw [mergeLoTargetEntries_length, mergeLoLeftEntries_length hgeometry,
      mergeLoRightEntries_length hgeometry]
  exact List.take_of_length_le (by rw [htargetLength]; omega)

/-! ## Call-entry initialization -/

/-- The safety preparation stage's exact initial copy establishes the semantic
invariant on the machine installed by the transcription, before its mandatory
first B move. -/
theorem mergeLoSemantic_initialMachine
    {lt : BoolComparator alpha}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {copied : MergeState (Occurrence alpha) nu}
    (stage : MergeLoInitialStage pre scanned i call copied)
    (hcomparator : call.state.key_compare = occurrenceComparator lt)
    (hsemantic : MergeLoSemanticPre lt call) :
    MergeLoSemanticMachineInvariant lt call
      (mergeLoInitialMachine call copied) := by
  have hmainCopy : mainToTempMemcpy? call.na (mergeLoAllocated call).state
      0 call.ssa = some copied := by
    rw [← stage.copyPost.exactErasure]
    exact stage.copyPost.success
  have hdirection : MergeLoMemcpyCallsite.initialDataToTemp.backings =
      { destination := .temporary, source := .main } := rfl
  have hcopy : mergeLoMemcpyDataToTemp? .initialDataToTemp hdirection call.na
      (mergeLoAllocated call).state 0 call.ssa = some copied := by
    exact (mainToTempMemcpy_eq_mergeLo .initialDataToTemp hdirection call.na
      (mergeLoAllocated call).state 0 call.ssa).symm ▸ hmainCopy
  have hdataAllocated : (mergeLoAllocated call).state.data = call.state.data :=
    stage.allocationPost.data_eq
  have hdataCopied : copied.data = call.state.data :=
    (mergeLoMemcpyDataToTemp_data_eq_of_eq_some .initialDataToTemp hdirection
      call.na (mergeLoAllocated call).state copied 0 call.ssa hcopy).trans
        hdataAllocated
  have hleftLength := mergeLoLeftEntries_length stage.geometry
  have hrightLength := mergeLoRightEntries_length stage.geometry
  have htempActive : MergeLoTempSuffixMatches copied.a
      (mergeLoLeftEntries call) 0 call.na := by
    constructor
    · simp [hleftLength]
    · intro offset hoffset
      have hcopied := mergeLoMemcpyDataToTemp_read_range_of_eq_some
        .initialDataToTemp hdirection call.na (mergeLoAllocated call).state copied
          0 call.ssa hcopy offset hoffset
      have hsource := mergeLoLeftEntries_getElem?_eq_read stage.geometry
        offset hoffset
      rw [hdataAllocated] at hcopied
      simpa only [Nat.zero_add] using hcopied.trans hsource.symm
  have hmainActive : MergeLoMainSuffixMatches copied.data
      (mergeLoRightEntries call) call.ssb 0 call.nb := by
    constructor
    · simp [hrightLength]
    · intro offset hoffset
      rw [hdataCopied]
      simpa only [Nat.zero_add] using
        (mergeLoRightEntries_getElem?_eq_read stage.geometry offset hoffset).symm
  have hlastStrict : call.nb > 0 →
      ∃ lastLeft lastRight,
        mergeLoTempRead? copied.a (call.na - 1) = some lastLeft ∧
        copied.data.read? (call.ssb + Int.ofNat (call.nb - 1)) = some lastRight ∧
        lt lastRight.key.value lastLeft.key.value = true := by
    intro hnb
    rcases hsemantic.lastStrict with
      ⟨lastLeft, lastRight, hleftLast, hrightLast, hstrict⟩
    refine ⟨lastLeft, lastRight, ?_, ?_, hstrict⟩
    · have hread := htempActive.2 (call.na - 1) (by
        exact Nat.sub_lt hsemantic.leftNonempty (by omega))
      have hread' : mergeLoTempRead? copied.a (call.na - 1) =
          (mergeLoLeftEntries call)[call.na - 1]? := by
        simpa only [Nat.zero_add] using hread
      have hsnapshot := mergeLoLeftEntries_getElem?_eq_read stage.geometry
        (call.na - 1) (Nat.sub_lt hsemantic.leftNonempty (by omega))
      exact hread'.trans (hsnapshot.trans hleftLast)
    · have hread := hmainActive.2 (call.nb - 1) (by omega)
      have hread' : copied.data.read?
          (call.ssb + Int.ofNat (call.nb - 1)) =
            (mergeLoRightEntries call)[call.nb - 1]? := by
        simpa only [Nat.zero_add] using hread
      have hsnapshot := mergeLoRightEntries_getElem?_eq_read stage.geometry
        (call.nb - 1) (Nat.sub_lt hsemantic.rightNonempty (by omega))
      exact hread'.trans (hsnapshot.trans hrightLast)
  refine
    { safety := stage.initialInvariant
      comparator := ?_
      leftCount := by simp [mergeLoInitialMachine]
      rightCount := by simp [mergeLoInitialMachine]
      leftPositive := by simpa [mergeLoInitialMachine] using
        hsemantic.leftNonempty
      tempActive := by simpa [mergeLoInitialMachine] using htempActive
      mainActive := by simpa [mergeLoInitialMachine] using hmainActive
      emittedTarget := ?_
      remainingTarget := ?_
      frame := ?_
      lastStrict := ?_ }
  · simpa [mergeLoInitialMachine] using
      (stage.copyPost.frame.comparator.trans
        stage.allocationPost.keyCompare_eq).trans hcomparator
  · simp [mergeLoInitialMachine, mergeLoEmittedEntries, mergeLoEmittedCount]
  · simp [mergeLoInitialMachine, mergeLoEmittedCount, mergeLoTargetEntries]
  · exact SortSlice.EqualOutsideRange.of_eq hdataCopied.symm call.ssa.toNat
      (call.na + call.nb)
  · simpa [mergeLoInitialMachine] using hlastStrict

/-- Initialization plus the transcription's mandatory first B copy.  The
strict low-end trimming sentinel is used here to identify that forced physical
move with the first element of the mathematical stable merge. -/
theorem mergeLoSemantic_afterForcedB
    {lt : BoolComparator alpha}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {copied : MergeState (Occurrence alpha) nu}
    (stage : MergeLoInitialStage pre scanned i call copied)
    (hcomparator : call.state.key_compare = occurrenceComparator lt)
    (hsemantic : MergeLoSemanticPre lt call) :
    ∃ afterB,
      mergeLoCopyBIncr? (mergeLoInitialMachine call copied) = some afterB ∧
      MergeLoSemanticMachineInvariant lt call afterB := by
  let initial := mergeLoInitialMachine call copied
  have hinitial : MergeLoSemanticMachineInvariant lt call initial := by
    simpa only [initial] using
      mergeLoSemantic_initialMachine stage hcomparator hsemantic
  rcases hsemantic.firstStrict with
    ⟨firstLeft, firstRight, hfirstLeft, hfirstRight, hstrict⟩
  have hleftRead : mergeLoTempRead? initial.state.a initial.aPos = some firstLeft := by
    have hread := hinitial.tempActive.2 0 (by
      simpa [initial, mergeLoInitialMachine] using hsemantic.leftNonempty)
    have hread' : mergeLoTempRead? initial.state.a initial.aPos =
        (mergeLoLeftEntries call)[0]? := by
      simpa [initial, mergeLoInitialMachine] using hread
    have hsnapshot := mergeLoLeftEntries_getElem?_eq_read stage.geometry 0
      hsemantic.leftNonempty
    have hfirstLeft' : call.state.data.read?
        (call.ssa + Int.ofNat 0) = some firstLeft := by
      simpa using hfirstLeft
    exact hread'.trans (hsnapshot.trans hfirstLeft')
  have hrightRead : initial.state.data.read? initial.bPos = some firstRight := by
    have hread := hinitial.mainActive.2 0 (by
      simpa [initial, mergeLoInitialMachine] using hsemantic.rightNonempty)
    have hread' : initial.state.data.read? initial.bPos =
        (mergeLoRightEntries call)[0]? := by
      simpa [initial, mergeLoInitialMachine] using hread
    have hsnapshot := mergeLoRightEntries_getElem?_eq_read stage.geometry 0
      hsemantic.rightNonempty
    have hfirstRight' : call.state.data.read?
        (call.ssb + Int.ofNat 0) = some firstRight := by
      simpa using hfirstRight
    exact hread'.trans (hsnapshot.trans hfirstRight')
  rcases mergeLoCopyBIncrTraced_safe (mergeLoAllocated call).state call.na
      (mergeLoEndIndex call)
      initial stage.initialInvariant hsemantic.leftNonempty
      hsemantic.rightNonempty with
    ⟨afterB, htrace, _htraceSafe, hafterSafety, _hna, _hnb⟩
  have hcopy : mergeLoCopyBIncr? initial = some afterB := by
    rw [← erase_mergeLoCopyBIncrTraced]
    exact htrace
  refine ⟨afterB, hcopy, ?_⟩
  apply hinitial.copyB stage.geometry hsemantic.leftNonempty
    hsemantic.rightNonempty firstLeft firstRight hleftRead hrightRead hstrict
    hcopy
  simpa [mergeLoEndIndex] using hafterSafety

/-! ## Gallop-block preservation -/

/-- Copying the upper-bound A prefix returned by `gallop_right` preserves the
semantic invariant.  The caller supplies the partition's comparison clause and
the strict survivor fact; the latter is derived from the high-end sentinel for
the actual gallop result. -/
theorem MergeLoSemanticMachineInvariant.copyABlock
    {lt : BoolComparator alpha}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {machine : MergeLoMachine (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call)
    (h : MergeLoSemanticMachineInvariant lt call machine)
    (count : Nat) (hcount : count < machine.na)
    (hnb : 0 < machine.nb)
    (rightHead : SortSliceEntry (Occurrence alpha) nu)
    (hrightRead : machine.state.data.read? machine.bPos = some rightHead)
    (hbefore : ∀ entry ∈
      ((mergeLoLeftEntries call).drop machine.aPos).take count,
        lt rightHead.key.value entry.key.value = false)
    (copied : MergeState (Occurrence alpha) nu)
    (hcopy : mergeLoMemcpyTempToData? .gallopTempToData rfl count
      machine.state machine.dest machine.aPos = some copied)
    (hsafety : MergeLoMachineInvariant (mergeLoAllocated call).state call.na
      (call.ssb + Int.ofNat call.nb)
      { machine with
        state := copied
        dest := machine.dest + Int.ofNat count
        aPos := machine.aPos + count
        na := machine.na - count }) :
    MergeLoSemanticMachineInvariant lt call
      { machine with
        state := copied
        dest := machine.dest + Int.ofNat count
        aPos := machine.aPos + count
        na := machine.na - count } := by
  let next : MergeLoMachine (Occurrence alpha) nu :=
    { machine with
      state := copied
      dest := machine.dest + Int.ofNat count
      aPos := machine.aPos + count
      na := machine.na - count }
  let block := ((mergeLoLeftEntries call).drop machine.aPos).take count
  have htemp := mergeLoMemcpyTempToData_temp_eq_of_eq_some
    .gallopTempToData rfl count machine.state copied machine.dest machine.aPos hcopy
  have hreadFrame := mergeLoMemcpyTempToData_readFrame_of_eq_some
    .gallopTempToData rfl count machine.state copied machine.dest machine.aPos hcopy
  have hdestCast : Int.ofNat machine.dest.toNat = machine.dest :=
    Int.toNat_of_nonneg h.safety.destNonnegative
  have hstepFrame0 : SortSlice.EqualOutsideRange machine.state.data copied.data
      machine.dest.toNat count := by
    rw [← hdestCast] at hreadFrame
    exact hreadFrame.equalOutsideRange_ofNat
  have hdestNat := h.dest_toNat hgeometry
  have hstepFrame : SortSlice.EqualOutsideRange machine.state.data copied.data
      (call.ssa.toNat + mergeLoEmittedCount call machine) count := by
    simpa only [hdestNat] using hstepFrame0
  have hleftLength := mergeLoLeftEntries_length hgeometry
  have hactiveLength :
      ((mergeLoLeftEntries call).drop machine.aPos).length = machine.na := by
    rw [List.length_drop, hleftLength]
    have haccount := h.safety.tempAccounting
    omega
  have hblockLength : block.length = count := by
    dsimp only [block]
    rw [List.length_take, hactiveLength]
    omega
  have hdestRange := h.safety.destTotalRange count (by omega)
  have hstop : machine.dest.toNat + count ≤ copied.data.entries.size := by
    have hsigned : Int.ofNat (machine.dest.toNat + count) ≤
        Int.ofNat machine.state.data.entries.size := by
      simp only [Int.ofNat_eq_natCast, Nat.cast_add]
      have hdestCast' : (machine.dest.toNat : Int) = machine.dest := hdestCast
      rw [hdestCast']
      exact hdestRange.2
    have hnat := Int.ofNat_le.mp hsigned
    rw [← hreadFrame.1]
    exact hnat
  have hblock0 :
      (sortSliceRangeEntries copied.data machine.dest.toNat count).toList = block := by
    apply sortSliceRangeEntries_toList_eq_of_reads _ _ _ _ hstop hblockLength
    intro offset hoffset
    have hcopied := mergeLoMemcpyTempToData_read_range_of_eq_some
      .gallopTempToData rfl count machine.state copied machine.dest machine.aPos
        hcopy offset hoffset
    have hactive := h.tempActive.2 offset (by omega)
    have hblockGet : block[offset]? =
        (mergeLoLeftEntries call)[machine.aPos + offset]? := by
      dsimp only [block]
      rw [List.getElem?_take, List.getElem?_drop]
      simp only [if_pos hoffset]
    have hindex : Int.ofNat (machine.dest.toNat + offset) =
        machine.dest + Int.ofNat offset := by
      simp only [Int.ofNat_eq_natCast, Nat.cast_add]
      have hdestCast' : (machine.dest.toNat : Int) = machine.dest := hdestCast
      rw [hdestCast']
    rw [hindex, hblockGet]
    exact hcopied.trans hactive
  have hblockRange :
      (sortSliceRangeEntries copied.data
        (call.ssa.toNat + mergeLoEmittedCount call machine) count).toList = block := by
    simpa only [← hdestNat] using hblock0
  have htempActive : MergeLoTempSuffixMatches next.state.a
      (mergeLoLeftEntries call) next.aPos next.na := by
    constructor
    · dsimp only [next]
      have := h.tempActive.1
      omega
    · intro offset hoffset
      dsimp only [next] at hoffset ⊢
      rw [htemp]
      have hread := h.tempActive.2 (count + offset) (by omega)
      simpa only [Nat.add_assoc] using hread
  have hmainActive : MergeLoMainSuffixMatches next.state.data
      (mergeLoRightEntries call) next.bPos (call.nb - next.nb) next.nb := by
    constructor
    · simpa [next] using h.mainActive.1
    · intro offset hoffset
      dsimp only [next] at hoffset ⊢
      have hpreserved := hreadFrame.2
        (machine.bPos + Int.ofNat offset) (Or.inr (by
          have hadj := h.safety.adjacency
          simp only [Int.ofNat_eq_natCast] at hadj ⊢
          omega))
      exact hpreserved.trans (h.mainActive.2 offset hoffset)
  have hemit : mergeLoEmittedCount call next =
      mergeLoEmittedCount call machine + count := by
    unfold mergeLoEmittedCount
    change call.na + call.nb - ((machine.na - count) + machine.nb) =
      call.na + call.nb - (machine.na + machine.nb) + count
    have hleft := h.leftCount
    have hright := h.rightCount
    omega
  have hrightDrop := h.right_drop_eq_cons hnb rightHead hrightRead
  have hleftSplit : (mergeLoLeftEntries call).drop machine.aPos =
      block ++ (mergeLoLeftEntries call).drop (machine.aPos + count) := by
    dsimp only [block]
    rw [← List.drop_drop]
    exact (List.take_append_drop count _).symm
  have hpeel :
      stableEntryMerge lt
          ((mergeLoLeftEntries call).drop machine.aPos)
          ((mergeLoRightEntries call).drop (call.nb - machine.nb)) =
        block ++
          stableEntryMerge lt
            ((mergeLoLeftEntries call).drop next.aPos)
            ((mergeLoRightEntries call).drop (call.nb - next.nb)) := by
    rw [hleftSplit, hrightDrop]
    rw [stableEntryMerge_left_prefix lt block _ rightHead _ hbefore]
  have hlastStrict : next.nb > 0 →
      ∃ lastLeft lastRight,
        mergeLoTempRead? next.state.a (next.aPos + next.na - 1) = some lastLeft ∧
        next.state.data.read?
            (next.bPos + Int.ofNat (next.nb - 1)) = some lastRight ∧
        lt lastRight.key.value lastLeft.key.value = true := by
    intro hnb
    rcases h.lastStrict (by simpa [next] using hnb) with
      ⟨lastLeft, lastRight, hlastLeft, hlastRight, hstrict⟩
    refine ⟨lastLeft, lastRight, ?_, ?_, hstrict⟩
    · dsimp only [next]
      rw [htemp]
      have hindex : machine.aPos + count + (machine.na - count) - 1 =
          machine.aPos + machine.na - 1 := by omega
      rw [hindex]
      exact hlastLeft
    · dsimp only [next]
      have hpreserved := hreadFrame.2
        (machine.bPos + Int.ofNat (machine.nb - 1)) (Or.inr (by
          have hadj := h.safety.adjacency
          simp only [Int.ofNat_eq_natCast] at hadj ⊢
          omega))
      exact hpreserved.trans hlastRight
  have hallocatedComparator :
      (mergeLoAllocated call).state.key_compare = occurrenceComparator lt :=
    h.safety.stableFrame.comparator.symm.trans h.comparator
  apply h.advance count block hsafety
    (hsafety.stableFrame.comparator.trans hallocatedComparator)
    (by dsimp [next]; exact (Nat.sub_le _ _).trans h.leftCount)
    (by simpa [next] using h.rightCount) (by dsimp [next]; omega)
    htempActive hmainActive hemit hblockLength hblockRange hstepFrame hpeel
    hlastStrict

/-- Copying the strict B prefix returned by `gallop_left` preserves the
semantic invariant.  Unlike the A gallop, this block may exhaust B; the
resulting zero-right state is consumed by `succeed`. -/
theorem MergeLoSemanticMachineInvariant.copyBBlock
    {lt : BoolComparator alpha}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {machine : MergeLoMachine (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call)
    (h : MergeLoSemanticMachineInvariant lt call machine)
    (count : Nat) (hcount : count ≤ machine.nb)
    (leftHead : SortSliceEntry (Occurrence alpha) nu)
    (hleftRead : mergeLoTempRead? machine.state.a machine.aPos = some leftHead)
    (hbefore : ∀ entry ∈
      ((mergeLoRightEntries call).drop (call.nb - machine.nb)).take count,
        lt entry.key.value leftHead.key.value = true)
    (copiedData : SortSlice (Occurrence alpha) nu)
    (hcopy : mergeDataMemmove? .loGallopB machine.state.data
      machine.dest machine.bPos count = some copiedData)
    (hsafety : MergeLoMachineInvariant (mergeLoAllocated call).state call.na
      (call.ssb + Int.ofNat call.nb)
      { machine with
        state := { machine.state with data := copiedData }
        dest := machine.dest + Int.ofNat count
        bPos := machine.bPos + Int.ofNat count
        nb := machine.nb - count }) :
    MergeLoSemanticMachineInvariant lt call
      { machine with
        state := { machine.state with data := copiedData }
        dest := machine.dest + Int.ofNat count
        bPos := machine.bPos + Int.ofNat count
        nb := machine.nb - count } := by
  let next : MergeLoMachine (Occurrence alpha) nu :=
    { machine with
      state := { machine.state with data := copiedData }
      dest := machine.dest + Int.ofNat count
      bPos := machine.bPos + Int.ofNat count
      nb := machine.nb - count }
  let consumed := call.nb - machine.nb
  let block := ((mergeLoRightEntries call).drop consumed).take count
  have hcopies := mergeDataMemmove_copiesRange_of_eq_some .loGallopB
    machine.state.data copiedData machine.dest machine.bPos count hcopy
  have hreadFrame := mergeDataMemmove_readFrame_of_eq_some .loGallopB
    machine.state.data copiedData machine.dest machine.bPos count hcopy
  have hstepFrame0 := mergeDataMemmove_equalOutsideRange_of_eq_some .loGallopB
    machine.state.data copiedData machine.dest machine.bPos count hcopy
  have hdestNat := h.dest_toNat hgeometry
  have hstepFrame : SortSlice.EqualOutsideRange machine.state.data copiedData
      (call.ssa.toNat + mergeLoEmittedCount call machine) count := by
    simpa only [hdestNat] using hstepFrame0
  have hrightLength := mergeLoRightEntries_length hgeometry
  have hactiveLength :
      ((mergeLoRightEntries call).drop consumed).length = machine.nb := by
    dsimp only [consumed]
    rw [List.length_drop, hrightLength]
    have := h.rightCount
    omega
  have hblockLength : block.length = count := by
    dsimp only [block]
    rw [List.length_take, hactiveLength]
    omega
  have hdestRange := h.safety.destTotalRange count (by omega)
  have hdestCast : Int.ofNat machine.dest.toNat = machine.dest :=
    Int.toNat_of_nonneg h.safety.destNonnegative
  have hstop : machine.dest.toNat + count ≤ copiedData.entries.size := by
    have hsigned : Int.ofNat (machine.dest.toNat + count) ≤
        Int.ofNat machine.state.data.entries.size := by
      simp only [Int.ofNat_eq_natCast, Nat.cast_add]
      have hdestCast' : (machine.dest.toNat : Int) = machine.dest := hdestCast
      rw [hdestCast']
      exact hdestRange.2
    have hnat := Int.ofNat_le.mp hsigned
    rw [← hreadFrame.1]
    exact hnat
  have hblock0 :
      (sortSliceRangeEntries copiedData machine.dest.toNat count).toList =
        block := by
    apply sortSliceRangeEntries_toList_eq_of_reads _ _ _ _ hstop hblockLength
    intro offset hoffset
    have hcopied := hcopies offset hoffset
    have hactive := h.mainActive.2 offset (by omega)
    have hblockGet : block[offset]? =
        (mergeLoRightEntries call)[consumed + offset]? := by
      dsimp only [block]
      rw [List.getElem?_take, List.getElem?_drop]
      simp only [if_pos hoffset]
    have hindex : Int.ofNat (machine.dest.toNat + offset) =
        machine.dest + Int.ofNat offset := by
      simp only [Int.ofNat_eq_natCast, Nat.cast_add]
      have hdestCast' : (machine.dest.toNat : Int) = machine.dest := hdestCast
      rw [hdestCast']
    rw [hindex, hblockGet]
    exact hcopied.trans hactive
  have hblockRange :
      (sortSliceRangeEntries copiedData
        (call.ssa.toNat + mergeLoEmittedCount call machine) count).toList =
          block := by
    simpa only [← hdestNat] using hblock0
  have htempActive : MergeLoTempSuffixMatches next.state.a
      (mergeLoLeftEntries call) next.aPos next.na := by
    simpa only [next] using h.tempActive
  have hconsumed : call.nb - next.nb = consumed + count := by
    dsimp only [next, consumed]
    have := h.rightCount
    omega
  have hmainActive : MergeLoMainSuffixMatches next.state.data
      (mergeLoRightEntries call) next.bPos (call.nb - next.nb) next.nb := by
    constructor
    · rw [hconsumed]
      dsimp only [next]
      have := h.mainActive.1
      omega
    · intro offset hoffset
      dsimp only [next] at hoffset ⊢
      rw [hconsumed]
      have hoffsetOld : count + offset < machine.nb := by omega
      have hpreserved := hreadFrame.2
        (machine.bPos + Int.ofNat count + Int.ofNat offset) (Or.inr (by
          have hadj := h.safety.adjacency
          simp only [Int.ofNat_eq_natCast] at hadj ⊢
          omega))
      have hold := h.mainActive.2 (count + offset) hoffsetOld
      have hidxInt : machine.bPos + Int.ofNat (count + offset) =
          machine.bPos + Int.ofNat count + Int.ofNat offset := by
        simp only [Int.ofNat_eq_natCast, Nat.cast_add]
        omega
      have hidxNat : consumed + (count + offset) =
          consumed + count + offset := by omega
      rw [hidxInt, hidxNat] at hold
      exact hpreserved.trans hold
  have hemit : mergeLoEmittedCount call next =
      mergeLoEmittedCount call machine + count := by
    unfold mergeLoEmittedCount
    change call.na + call.nb - (machine.na + (machine.nb - count)) =
      call.na + call.nb - (machine.na + machine.nb) + count
    have hleft := h.leftCount
    have hright := h.rightCount
    omega
  have hleftDrop := h.left_drop_eq_cons leftHead hleftRead
  have hrightSplit : (mergeLoRightEntries call).drop consumed =
      block ++ (mergeLoRightEntries call).drop (consumed + count) := by
    dsimp only [block]
    rw [← List.drop_drop]
    exact (List.take_append_drop count _).symm
  have hpeel :
      stableEntryMerge lt
          ((mergeLoLeftEntries call).drop machine.aPos)
          ((mergeLoRightEntries call).drop (call.nb - machine.nb)) =
        block ++
          stableEntryMerge lt
            ((mergeLoLeftEntries call).drop next.aPos)
            ((mergeLoRightEntries call).drop (call.nb - next.nb)) := by
    change stableEntryMerge lt
        ((mergeLoLeftEntries call).drop machine.aPos)
        ((mergeLoRightEntries call).drop consumed) = _
    rw [hleftDrop, hrightSplit]
    rw [stableEntryMerge_right_prefix lt leftHead _ block _ hbefore]
    rw [← hleftDrop, ← hconsumed]
  have hlastStrict : next.nb > 0 →
      ∃ lastLeft lastRight,
        mergeLoTempRead? next.state.a (next.aPos + next.na - 1) = some lastLeft ∧
        next.state.data.read?
            (next.bPos + Int.ofNat (next.nb - 1)) = some lastRight ∧
        lt lastRight.key.value lastLeft.key.value = true := by
    intro hnextNb
    rcases h.lastStrict (by dsimp only [next] at hnextNb; omega) with
      ⟨lastLeft, lastRight, hlastLeft, hlastRight, hstrict⟩
    refine ⟨lastLeft, lastRight, ?_, ?_, hstrict⟩
    · simpa only [next] using hlastLeft
    · dsimp only [next]
      have hindex : machine.bPos + Int.ofNat count +
            Int.ofNat (machine.nb - count - 1) =
          machine.bPos + Int.ofNat (machine.nb - 1) := by
        simp only [Int.ofNat_eq_natCast]
        omega
      rw [hindex]
      have hpreserved := hreadFrame.2
        (machine.bPos + Int.ofNat (machine.nb - 1)) (Or.inr (by
          have hadj := h.safety.adjacency
          simp only [Int.ofNat_eq_natCast] at hadj ⊢
          omega))
      exact hpreserved.trans hlastRight
  apply h.advance count block hsafety h.comparator
    (by simpa only [next] using h.leftCount)
    (by dsimp only [next]; exact (Nat.sub_le _ _).trans h.rightCount)
    (by simpa only [next] using h.leftPositive)
    htempActive hmainActive hemit hblockLength hblockRange hstepFrame hpeel
    hlastStrict

/-! ## Gallop search interfaces and control-only updates -/

/-- The live temporary suffix is a sorted direct gallop source because it is
pointwise equal to a suffix of the immutable sorted left run. -/
theorem MergeLoSemanticMachineInvariant.temporaryGallopSorted
    {lt : BoolComparator alpha}
    {call : MergeAtCall (Occurrence alpha) nu}
    {machine : MergeLoMachine (Occurrence alpha) nu}
    (hsemantic : MergeLoSemanticPre lt call)
    (h : MergeLoSemanticMachineInvariant lt call machine) :
    GallopSortedRange machine.state.key_compare
      (.temporary machine.state.a (Int.ofNat machine.aPos)) machine.na := by
  have hpair : ((mergeLoLeftEntries call).drop machine.aPos).Pairwise
      (fun earlier later =>
        lt later.key.value earlier.key.value = false) :=
    hsemantic.leftPairwise.drop
  intro leftIndex rightIndex hleftIndex hrightIndex hindex earlier later
      hearlier hlater
  have hleftPhysical : Int.ofNat machine.aPos + Int.ofNat leftIndex =
      Int.ofNat (machine.aPos + leftIndex) := by
    simp only [Int.ofNat_eq_natCast, Nat.cast_add]
  have hrightPhysical : Int.ofNat machine.aPos + Int.ofNat rightIndex =
      Int.ofNat (machine.aPos + rightIndex) := by
    simp only [Int.ofNat_eq_natCast, Nat.cast_add]
  have hearlierTemp : mergeLoTempRead? machine.state.a
      (machine.aPos + leftIndex) = some earlier := by
    change mergeTempRead? machine.state.a
      (Int.ofNat machine.aPos + Int.ofNat leftIndex) = some earlier at hearlier
    rw [hleftPhysical, mergeTempRead_ofNat] at hearlier
    exact hearlier
  have hlaterTemp : mergeLoTempRead? machine.state.a
      (machine.aPos + rightIndex) = some later := by
    change mergeTempRead? machine.state.a
      (Int.ofNat machine.aPos + Int.ofNat rightIndex) = some later at hlater
    rw [hrightPhysical, mergeTempRead_ofNat] at hlater
    exact hlater
  have hearlierGet :
      ((mergeLoLeftEntries call).drop machine.aPos)[leftIndex]? =
        some earlier := by
    rw [List.getElem?_drop]
    exact (h.tempActive.2 leftIndex hleftIndex).symm.trans hearlierTemp
  have hlaterGet :
      ((mergeLoLeftEntries call).drop machine.aPos)[rightIndex]? =
        some later := by
    rw [List.getElem?_drop]
    exact (h.tempActive.2 rightIndex hrightIndex).symm.trans hlaterTemp
  rcases List.getElem?_eq_some_iff.mp hearlierGet with ⟨hearlierIn, hearlierEq⟩
  rcases List.getElem?_eq_some_iff.mp hlaterGet with ⟨hlaterIn, hlaterEq⟩
  have hearlierEq' :
      ((mergeLoLeftEntries call).drop machine.aPos).get
          ⟨leftIndex, hearlierIn⟩ = earlier := hearlierEq
  have hlaterEq' :
      ((mergeLoLeftEntries call).drop machine.aPos).get
          ⟨rightIndex, hlaterIn⟩ = later := hlaterEq
  have hrel := hpair.rel_get_of_lt
    (a := ⟨leftIndex, hearlierIn⟩) (b := ⟨rightIndex, hlaterIn⟩)
    (by simpa using hindex)
  rw [h.comparator]
  rw [hearlierEq', hlaterEq'] at hrel
  exact hrel

/-- The live main-data suffix is a sorted direct gallop source because it is
pointwise equal to a suffix of the immutable sorted right run. -/
theorem MergeLoSemanticMachineInvariant.mainGallopSorted
    {lt : BoolComparator alpha}
    {call : MergeAtCall (Occurrence alpha) nu}
    {machine : MergeLoMachine (Occurrence alpha) nu}
    (hsemantic : MergeLoSemanticPre lt call)
    (h : MergeLoSemanticMachineInvariant lt call machine) :
    GallopSortedRange machine.state.key_compare
      (.main machine.state.data machine.bPos) machine.nb := by
  have hpair :
      ((mergeLoRightEntries call).drop (call.nb - machine.nb)).Pairwise
        (fun earlier later =>
          lt later.key.value earlier.key.value = false) :=
    hsemantic.rightPairwise.drop
  intro leftIndex rightIndex hleftIndex hrightIndex hindex earlier later
      hearlier hlater
  change machine.state.data.read?
      (machine.bPos + Int.ofNat leftIndex) = some earlier at hearlier
  change machine.state.data.read?
      (machine.bPos + Int.ofNat rightIndex) = some later at hlater
  have hearlierGet :
      ((mergeLoRightEntries call).drop (call.nb - machine.nb))[leftIndex]? =
        some earlier := by
    rw [List.getElem?_drop]
    exact (h.mainActive.2 leftIndex hleftIndex).symm.trans hearlier
  have hlaterGet :
      ((mergeLoRightEntries call).drop (call.nb - machine.nb))[rightIndex]? =
        some later := by
    rw [List.getElem?_drop]
    exact (h.mainActive.2 rightIndex hrightIndex).symm.trans hlater
  rcases List.getElem?_eq_some_iff.mp hearlierGet with ⟨hearlierIn, hearlierEq⟩
  rcases List.getElem?_eq_some_iff.mp hlaterGet with ⟨hlaterIn, hlaterEq⟩
  have hearlierEq' :
      ((mergeLoRightEntries call).drop (call.nb - machine.nb)).get
          ⟨leftIndex, hearlierIn⟩ = earlier := hearlierEq
  have hlaterEq' :
      ((mergeLoRightEntries call).drop (call.nb - machine.nb)).get
          ⟨rightIndex, hlaterIn⟩ = later := hlaterEq
  have hrel := hpair.rel_get_of_lt
    (a := ⟨leftIndex, hearlierIn⟩) (b := ⟨rightIndex, hlaterIn⟩)
    (by simpa using hindex)
  rw [h.comparator]
  rw [hearlierEq', hlaterEq'] at hrel
  exact hrel

/-- Correctness of the exact right-biased gallop used on the live temporary
A suffix. -/
theorem MergeLoSemanticMachineInvariant.gallopRight_exists
    {lt : BoolComparator alpha}
    {call : MergeAtCall (Occurrence alpha) nu}
    {machine : MergeLoMachine (Occurrence alpha) nu}
    (horder : BoolStrictWeakOrder lt)
    (hsemantic : MergeLoSemanticPre lt call)
    (h : MergeLoSemanticMachineInvariant lt call machine)
    (firstB : SortSliceEntry (Occurrence alpha) nu)
    (activeA : SortSlice (Occurrence alpha) nu)
    (hactiveA : mergeLoTempRun? machine.state.a machine.aPos machine.na =
      some activeA) :
    ∃ result,
      gallopRight? machine.state activeA 0 firstB.key machine.na 0 =
        some result ∧
      result.fuelExhausted = false ∧
      GallopRightPartition machine.state.key_compare activeA 0 firstB.key
        machine.na result.index := by
  exact gallopRight_correct machine.state
    (.temporary machine.state.a (Int.ofNat machine.aPos)) activeA 0 firstB.key
    machine.na 0 h.safety.temporaryValidRange
    (tempRun_agreesWithSlice_of_eq_some machine.state.a machine.aPos machine.na
      activeA hactiveA)
    (h.order horder) (h.temporaryGallopSorted hsemantic) h.leftPositive
    h.leftPositive h.safety.leftWordBound

/-- Correctness of the exact left-biased gallop used on the live main B
suffix. -/
theorem MergeLoSemanticMachineInvariant.gallopLeft_exists
    {lt : BoolComparator alpha}
    {call : MergeAtCall (Occurrence alpha) nu}
    {machine : MergeLoMachine (Occurrence alpha) nu}
    (horder : BoolStrictWeakOrder lt)
    (hsemantic : MergeLoSemanticPre lt call)
    (h : MergeLoSemanticMachineInvariant lt call machine)
    (hnb : 0 < machine.nb)
    (firstA : SortSliceEntry (Occurrence alpha) nu) :
    ∃ result,
      gallopLeft? machine.state machine.state.data machine.bPos firstA.key
        machine.nb 0 = some result ∧
      result.fuelExhausted = false ∧
      GallopLeftPartition machine.state.key_compare machine.state.data
        machine.bPos firstA.key machine.nb result.index := by
  exact gallopLeft_correct machine.state
    (.main machine.state.data machine.bPos) machine.state.data machine.bPos
    firstA.key machine.nb 0 h.safety.rightValidRange
    (GallopKeySource.main_agreesWithSlice machine.state.data machine.bPos
      machine.nb)
    (h.order horder) (h.mainGallopSorted hsemantic) hnb (by omega)
    h.safety.rightWordBound

/-- Under the strict high-end sentinel and a strict weak order, the
right-biased A gallop cannot consume all of A.  This discharges the raw
evaluator's `na = 0` adversarial-comparator hedge without an extra premise. -/
theorem MergeLoSemanticMachineInvariant.gallopRightIndex_lt
    {lt : BoolComparator alpha}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {machine : MergeLoMachine (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call)
    (horder : BoolStrictWeakOrder lt)
    (hsemantic : MergeLoSemanticPre lt call)
    (h : MergeLoSemanticMachineInvariant lt call machine)
    (hnb : 0 < machine.nb)
    (firstB : SortSliceEntry (Occurrence alpha) nu)
    (hfirstB : machine.state.data.read? machine.bPos = some firstB)
    (activeA : SortSlice (Occurrence alpha) nu)
    (hactiveA : mergeLoTempRun? machine.state.a machine.aPos machine.na =
      some activeA)
    (index : Nat)
    (hpartition : GallopRightPartition machine.state.key_compare activeA 0
      firstB.key machine.na index) :
    index < machine.na := by
  have hindexLe := hpartition.1
  by_contra hnotLt
  have hna := h.leftPositive
  have hindexEq : index = machine.na := by omega
  have hlastOffset : machine.na - 1 < machine.na := by omega
  rcases hpartition.2.1 (machine.na - 1) (by omega) with
    ⟨partitionLast, hpartitionRead, hpartitionCompare⟩
  rcases h.lastStrict hnb with
    ⟨lastLeft, lastRight, hlastLeft, hlastRight, hstrict⟩
  have hagrees := tempRun_agreesWithSlice_of_eq_some machine.state.a
    machine.aPos machine.na activeA hactiveA
  have hphysical : Int.ofNat machine.aPos + Int.ofNat (machine.na - 1) =
      Int.ofNat (machine.aPos + (machine.na - 1)) := by
    simp only [Int.ofNat_eq_natCast, Nat.cast_add]
  have hsourceLast :
      (GallopKeySource.temporary machine.state.a
        (Int.ofNat machine.aPos)).read? (Int.ofNat (machine.na - 1)) =
          some lastLeft := by
    change mergeTempRead? machine.state.a
      (Int.ofNat machine.aPos + Int.ofNat (machine.na - 1)) = some lastLeft
    rw [hphysical, mergeTempRead_ofNat]
    have hindex : machine.aPos + (machine.na - 1) =
        machine.aPos + machine.na - 1 := by omega
    rw [hindex]
    exact hlastLeft
  have hagreeLast := hagrees (Int.ofNat (machine.na - 1))
    (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hlastOffset)
  have hsliceLast : activeA.read? (0 + Int.ofNat (machine.na - 1)) =
      some lastLeft := hagreeLast.symm.trans hsourceLast
  have hpartitionLastEq : partitionLast = lastLeft := by
    exact Option.some.inj (hpartitionRead.symm.trans hsliceLast)
  subst partitionLast
  let hright := (mergeLoRightEntries call).drop (call.nb - machine.nb)
  have hrightLength : hright.length = machine.nb := by
    dsimp only [hright]
    rw [List.length_drop, mergeLoRightEntries_length hgeometry]
    have := h.rightCount
    omega
  have hrightDrop := h.right_drop_eq_cons hnb firstB hfirstB
  have hrightNe : hright ≠ [] := by
    dsimp only [hright]
    rw [hrightDrop]
    simp
  have hrightPairwise : hright.Pairwise (fun earlier later =>
      lt later.key.value earlier.key.value = false) := by
    dsimp only [hright]
    exact hsemantic.rightPairwise.drop
  have hrightLast : hright.getLast? = some lastRight := by
    dsimp only [hright]
    rw [List.getLast?_eq_getElem?, hrightLength, List.getElem?_drop]
    have hactive := h.mainActive.2 (machine.nb - 1) (by omega)
    exact hactive.symm.trans hlastRight
  have hrightLastGet : hright.getLast hrightNe = lastRight := by
    exact (List.getLast_eq_iff_getLast?_eq_some hrightNe).2 hrightLast
  have hfirstBMem : firstB ∈ hright := by
    dsimp only [hright]
    rw [hrightDrop]
    simp
  have hnotReverse : lt lastRight.key.value firstB.key.value = false := by
    have hrel := hrightPairwise.rel_getLast_of_rel_getLast_getLast hfirstBMem
      (Bool.eq_false_iff.mpr (horder.irrefl
        (hright.getLast hrightNe).key.value))
    simpa only [hrightLastGet] using hrel
  have hfirstBStrict : lt firstB.key.value lastLeft.key.value = true :=
    horder.strict_of_not_reverse_of_strict hnotReverse hstrict
  rw [h.comparator] at hpartitionCompare
  exact Bool.noConfusion (hpartitionCompare.symm.trans hfirstBStrict)

/-- The prefix clause of the A gallop partition transports through temporary
materialization to the immutable whole-entry left suffix. -/
theorem MergeLoSemanticMachineInvariant.gallopRight_beforeBlock
    {lt : BoolComparator alpha}
    {call : MergeAtCall (Occurrence alpha) nu}
    {machine : MergeLoMachine (Occurrence alpha) nu}
    (h : MergeLoSemanticMachineInvariant lt call machine)
    (firstB : SortSliceEntry (Occurrence alpha) nu)
    (activeA : SortSlice (Occurrence alpha) nu)
    (hactiveA : mergeLoTempRun? machine.state.a machine.aPos machine.na =
      some activeA)
    (index : Nat)
    (hpartition : GallopRightPartition machine.state.key_compare activeA 0
      firstB.key machine.na index) :
    ∀ entry ∈
      ((mergeLoLeftEntries call).drop machine.aPos).take index,
      lt firstB.key.value entry.key.value = false := by
  intro entry hentry
  rcases List.mem_iff_getElem.mp hentry with ⟨offset, hoffset, hentryEq⟩
  have hindexBound := hpartition.1
  have hoffsetIndex : offset < index := by
    simp only [List.length_take] at hoffset
    exact hoffset.trans_le (Nat.min_le_left _ _)
  have hoffsetNa : offset < machine.na := by omega
  have hgetTake :
      (((mergeLoLeftEntries call).drop machine.aPos).take index)[offset]? =
        some entry :=
    List.getElem?_eq_some_iff.mpr ⟨hoffset, hentryEq⟩
  rw [List.getElem?_take, if_pos hoffsetIndex, List.getElem?_drop] at hgetTake
  have htemp : mergeLoTempRead? machine.state.a
      (machine.aPos + offset) = some entry :=
    (h.tempActive.2 offset hoffsetNa).trans hgetTake
  have hsource :
      (GallopKeySource.temporary machine.state.a
        (Int.ofNat machine.aPos)).read? (Int.ofNat offset) = some entry := by
    change mergeTempRead? machine.state.a
      (Int.ofNat machine.aPos + Int.ofNat offset) = some entry
    have hphysical : Int.ofNat machine.aPos + Int.ofNat offset =
        Int.ofNat (machine.aPos + offset) := by
      simp only [Int.ofNat_eq_natCast, Nat.cast_add]
    rw [hphysical, mergeTempRead_ofNat]
    exact htemp
  have hagrees := tempRun_agreesWithSlice_of_eq_some machine.state.a
    machine.aPos machine.na activeA hactiveA
  have hagree := hagrees (Int.ofNat offset) (Int.natCast_nonneg _)
    (Int.ofNat_lt.mpr hoffsetNa)
  have hslice : activeA.read? (0 + Int.ofNat offset) = some entry :=
    hagree.symm.trans hsource
  rcases hpartition.2.1 offset hoffsetIndex with
    ⟨partitionEntry, hpartitionRead, hcompare⟩
  have heq : partitionEntry = entry :=
    Option.some.inj (hpartitionRead.symm.trans hslice)
  subst partitionEntry
  rw [h.comparator] at hcompare
  exact hcompare

/-- The prefix clause of the B gallop partition transports to the immutable
whole-entry right suffix. -/
theorem MergeLoSemanticMachineInvariant.gallopLeft_beforeBlock
    {lt : BoolComparator alpha}
    {call : MergeAtCall (Occurrence alpha) nu}
    {machine : MergeLoMachine (Occurrence alpha) nu}
    (h : MergeLoSemanticMachineInvariant lt call machine)
    (firstA : SortSliceEntry (Occurrence alpha) nu)
    (index : Nat)
    (hpartition : GallopLeftPartition machine.state.key_compare
      machine.state.data machine.bPos firstA.key machine.nb index) :
    ∀ entry ∈
      ((mergeLoRightEntries call).drop (call.nb - machine.nb)).take index,
      lt entry.key.value firstA.key.value = true := by
  intro entry hentry
  rcases List.mem_iff_getElem.mp hentry with ⟨offset, hoffset, hentryEq⟩
  have hindexBound := hpartition.1
  have hoffsetIndex : offset < index := by
    simp only [List.length_take] at hoffset
    exact hoffset.trans_le (Nat.min_le_left _ _)
  have hoffsetNb : offset < machine.nb := by omega
  have hgetTake :
      (((mergeLoRightEntries call).drop
        (call.nb - machine.nb)).take index)[offset]? = some entry :=
    List.getElem?_eq_some_iff.mpr ⟨hoffset, hentryEq⟩
  rw [List.getElem?_take, if_pos hoffsetIndex, List.getElem?_drop] at hgetTake
  have hmain : machine.state.data.read?
      (machine.bPos + Int.ofNat offset) = some entry :=
    (h.mainActive.2 offset hoffsetNb).trans hgetTake
  rcases hpartition.2.1 offset hoffsetIndex with
    ⟨partitionEntry, hpartitionRead, hcompare⟩
  have heq : partitionEntry = entry :=
    Option.some.inj (hpartitionRead.symm.trans hmain)
  subst partitionEntry
  rw [h.comparator] at hcompare
  exact hcompare

/-- Updating only the driver's adaptive threshold leaves the functional
invariant unchanged. -/
theorem MergeLoSemanticMachineInvariant.setMachineMinGallop
    {lt : BoolComparator alpha}
    {call : MergeAtCall (Occurrence alpha) nu}
    {machine : MergeLoMachine (Occurrence alpha) nu}
    (h : MergeLoSemanticMachineInvariant lt call machine)
    (minGallop : PySSize) :
    MergeLoSemanticMachineInvariant lt call
      { machine with minGallop := minGallop } := by
  exact { h with safety := h.safety.setMachineMinGallop minGallop }

/-- Writing the adaptive threshold back to both state and driver also leaves
all semantic data unchanged. -/
theorem MergeLoSemanticMachineInvariant.setMinGallop
    {lt : BoolComparator alpha}
    {call : MergeAtCall (Occurrence alpha) nu}
    {machine : MergeLoMachine (Occurrence alpha) nu}
    (h : MergeLoSemanticMachineInvariant lt call machine)
    (minGallop : PySSize) :
    MergeLoSemanticMachineInvariant lt call
      { machine with
        state := { machine.state with min_gallop := minGallop }
        minGallop := minGallop } := by
  exact { h with safety := h.safety.setMinGallop minGallop }

end CPythonListsort
