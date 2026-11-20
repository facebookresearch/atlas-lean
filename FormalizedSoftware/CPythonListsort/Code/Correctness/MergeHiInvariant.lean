/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.GallopCorrectness
import Code.Assembly.MergeHiSafety
import Code.Correctness.MergeMovementCorrectness
import Code.Correctness.MergeSemanticPre
import Code.Correctness.SortSliceRange
import Code.Correctness.StableMerge

/-!
# Semantic invariant for `merge_hi`

The safety invariant for `merge_hi` deliberately records only cursor geometry,
storage validity, and stable state fields.  Functional correctness needs a
separate immutable snapshot of the two post-trimming runs and a description of
the suffix already filled by the right-to-left loop.  This module introduces
that semantic vocabulary without changing the reviewed safety certificate.
-/

namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-- Whole entries in the post-trimming left run consumed by `merge_hi`. -/
def mergeHiLeftEntries (call : MergeAtCall (Occurrence alpha) nu) :
    List (SortSliceEntry (Occurrence alpha) nu) :=
  (sortSliceRangeEntries call.state.data call.ssa.toNat call.na).toList

/-- Whole entries in the post-trimming right run copied to temporary storage. -/
def mergeHiRightEntries (call : MergeAtCall (Occurrence alpha) nu) :
    List (SortSliceEntry (Occurrence alpha) nu) :=
  (sortSliceRangeEntries call.state.data call.ssb.toNat call.nb).toList

/-- Shared mathematical target of the physical right-to-left merge. -/
def mergeHiTargetEntries (lt : BoolComparator alpha)
    (call : MergeAtCall (Occurrence alpha) nu) :
    List (SortSliceEntry (Occurrence alpha) nu) :=
  stableEntryMerge lt (mergeHiLeftEntries call) (mergeHiRightEntries call)

@[simp]
theorem mergeHiLeftEntries_map_key
    (call : MergeAtCall (Occurrence alpha) nu) :
    (mergeHiLeftEntries call).map SortSliceEntry.key =
      (sortSliceRangeKeys call.state.data call.ssa.toNat call.na).toList := by
  simp [mergeHiLeftEntries, sortSliceRangeKeys]

@[simp]
theorem mergeHiRightEntries_map_key
    (call : MergeAtCall (Occurrence alpha) nu) :
    (mergeHiRightEntries call).map SortSliceEntry.key =
      (sortSliceRangeKeys call.state.data call.ssb.toNat call.nb).toList := by
  simp [mergeHiRightEntries, sortSliceRangeKeys]

/-- Entries in the main-data suffix already filled by a live backward cursor. -/
def mergeHiFilledEntries (call : MergeAtCall (Occurrence alpha) nu)
    (cursor : MergeHiCursor (Occurrence alpha) nu) :
    List (SortSliceEntry (Occurrence alpha) nu) :=
  (sortSliceRangeEntries cursor.state.data
    (call.ssa.toNat + cursor.na + cursor.nb)
    (call.na + call.nb - (cursor.na + cursor.nb))).toList

/-- Pointwise whole-entry description of the initialized temporary prefix.

Using reads rather than the optional-cell representation keeps the invariant
aligned with both the reviewed prefix materializer and the direct traced gallop
source. -/
def MergeHiTempPrefixMatches
    (storage : TempStorage (Occurrence alpha) nu)
    (right : List (SortSliceEntry (Occurrence alpha) nu))
    (count : Nat) : Prop :=
  count <= right.length ∧
    ∀ i, i < count →
      mergeHiTempRead? storage (Int.ofNat i) = right[i]?

/-- `merge_hi` consumes exactly the shared post-trimming semantic contract.
The direction-specific name is retained as an abbreviation so downstream
statements remain readable while both merge directions are definitionally
obligated to the same predicate shape. -/
abbrev MergeHiSemanticPre
    (lt : BoolComparator alpha)
    (call : MergeAtCall (Occurrence alpha) nu) : Prop :=
  MergeSemanticPre lt call

/-- Named bridge from the public left-run `Sorted` field to the mapped-key
relation consumed by pure stable-merge correctness. -/
theorem MergeHiSemanticPre.leftKeysPairwise
    {lt : BoolComparator alpha}
    {call : MergeAtCall (Occurrence alpha) nu}
    (h : MergeHiSemanticPre lt call) :
    ((mergeHiLeftEntries call).map SortSliceEntry.key).Pairwise
      (DescendingRunSpec.SortedRelation lt) := by
  change ((mergeHiLeftEntries call).map SortSliceEntry.key).Pairwise
    (fun earlier later => lt later.value earlier.value = false)
  simpa [Sorted, occurrenceComparator] using h.leftSorted

/-- Named mapped-key bridge for the retained right run. -/
theorem MergeHiSemanticPre.rightKeysPairwise
    {lt : BoolComparator alpha}
    {call : MergeAtCall (Occurrence alpha) nu}
    (h : MergeHiSemanticPre lt call) :
    ((mergeHiRightEntries call).map SortSliceEntry.key).Pairwise
      (DescendingRunSpec.SortedRelation lt) := by
  change ((mergeHiRightEntries call).map SortSliceEntry.key).Pairwise
    (fun earlier later => lt later.value earlier.value = false)
  simpa [Sorted, occurrenceComparator] using h.rightSorted

/-- List-facing bridge from the shared array-level left-run sortedness field.
Internal reverse-loop lemmas use this form; it is derived rather than stored as
a surrogate field in the public semantic precondition. -/
theorem MergeHiSemanticPre.leftEntriesPairwise
    {lt : BoolComparator alpha}
    {call : MergeAtCall (Occurrence alpha) nu}
    (h : MergeHiSemanticPre lt call) :
    (mergeHiLeftEntries call).Pairwise
      (fun earlier later => lt later.key.value earlier.key.value = false) := by
  exact (List.pairwise_map.mp h.leftKeysPairwise :
    (mergeHiLeftEntries call).Pairwise
      (fun earlier later => lt later.key.value earlier.key.value = false))

/-- List-facing bridge from the shared array-level right-run sortedness field.
As with the left bridge, no second sortedness notion enters the contract. -/
theorem MergeHiSemanticPre.rightEntriesPairwise
    {lt : BoolComparator alpha}
    {call : MergeAtCall (Occurrence alpha) nu}
    (h : MergeHiSemanticPre lt call) :
    (mergeHiRightEntries call).Pairwise
      (fun earlier later => lt later.key.value earlier.key.value = false) := by
  exact (List.pairwise_map.mp h.rightKeysPairwise :
    (mergeHiRightEntries call).Pairwise
      (fun earlier later => lt later.key.value earlier.key.value = false))

/-- Functional invariant of every live `merge_hi` cursor.

`remainingTarget` and `filledTarget` are the two halves of the immutable target
at the current count boundary.  `lowSentinel` is deliberately about the first
entries of the two retained runs, not the moving high-end heads.  Together with
`rightPositive`, it is the correctness-only fact excluding CPython's
inconsistent-comparator `nb == 0` hedge; that branch remains present and
safety-checked in the evaluator. -/
structure MergeHiSemanticCursorInvariant
    (lt : BoolComparator alpha)
    (call : MergeAtCall (Occurrence alpha) nu)
    (cursor : MergeHiCursor (Occurrence alpha) nu) : Prop where
  safety : MergeHiCursorInvariant (mergeHiAllocated call).state call.nb cursor
  basea_eq : cursor.basea = call.ssa
  comparator : cursor.state.key_compare = occurrenceComparator lt
  leftCount : cursor.na <= call.na
  rightCount : cursor.nb <= call.nb
  rightPositive : 0 < cursor.nb
  activeLeft :
    (sortSliceRangeEntries cursor.state.data call.ssa.toNat cursor.na).toList =
      (mergeHiLeftEntries call).take cursor.na
  activeRight :
    MergeHiTempPrefixMatches cursor.state.a (mergeHiRightEntries call) cursor.nb
  remainingTarget :
    stableEntryMerge lt
        ((mergeHiLeftEntries call).take cursor.na)
        ((mergeHiRightEntries call).take cursor.nb) =
      (mergeHiTargetEntries lt call).take (cursor.na + cursor.nb)
  filledTarget :
    mergeHiFilledEntries call cursor =
      (mergeHiTargetEntries lt call).drop (cursor.na + cursor.nb)
  frame :
    SortSlice.EqualOutsideRange call.state.data cursor.state.data
      call.ssa.toNat (call.na + call.nb)
  lowSentinel :
    ∃ leftFirst rightFirst,
      cursor.state.data.read? call.ssa = some leftFirst ∧
      mergeHiTempRead? cursor.state.a 0 = some rightFirst ∧
      lt rightFirst.key.value leftFirst.key.value = true

/-- Raw initial-copy equality extracted from the reviewed traced preparation. -/
theorem MergeHiPrepared.initialCopyRaw
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {copied : MergeState (Occurrence alpha) nu}
    {forced : MergeHiDataCursorResult (Occurrence alpha) nu}
    (h : MergeHiPrepared pre scanned i call copied forced) :
    mergeHiMemcpyDataToTemp? .initialDataToTemp rfl call.nb
      (mergeHiAllocated call).state 0 call.ssb = some copied := by
  have hraw : mainToTempMemcpy? call.nb (mergeHiAllocated call).state
      0 call.ssb = some copied := by
    rw [← h.initialCopy.exactErasure]
    exact h.initialCopy.success
  rw [← mainToTempMemcpy_eq_mergeHiMemcpyDataToTemp
    .initialDataToTemp rfl call.nb (mergeHiAllocated call).state 0 call.ssb]
  exact hraw

/-- Raw forced-cell equality extracted from the reviewed traced preparation. -/
theorem MergeHiPrepared.forcedRaw
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {copied : MergeState (Occurrence alpha) nu}
    {forced : MergeHiDataCursorResult (Occurrence alpha) nu}
    (h : MergeHiPrepared pre scanned i call copied forced) :
    mergeHiCopyDataDecr? copied
      (call.ssb + Int.ofNat (call.nb - 1))
      (call.ssa + Int.ofNat (call.na - 1)) = some forced := by
  rw [← erase_mergeHiCopyDataDecrTraced]
  exact h.forcedResult

/-- Preparation changes only temporary storage before the forced output write;
the main data snapshot is still the call-entry data. -/
theorem MergeHiPrepared.copiedData_eq
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {copied : MergeState (Occurrence alpha) nu}
    {forced : MergeHiDataCursorResult (Occurrence alpha) nu}
    (h : MergeHiPrepared pre scanned i call copied forced) :
    copied.data = call.state.data := by
  have hdata := mainToTempMemcpy_data_eq_of_eq_some call.nb
    (mergeHiAllocated call).state copied 0 call.ssb (by
      rw [mainToTempMemcpy_eq_mergeHiMemcpyDataToTemp
        .initialDataToTemp rfl call.nb (mergeHiAllocated call).state 0 call.ssb]
      exact h.initialCopyRaw)
  exact hdata.trans h.allocation.data_eq

/-- Generic right-to-left fill step.  A block written immediately before the
already-correct suffix extends that suffix, preserves the still-active prefix,
and composes into the enclosing public frame. -/
theorem mergeHi_backwardFillBlock
    {origin before after : SortSlice alpha nu}
    {base total oldRemaining newRemaining count : Nat}
    {target block : List (SortSliceEntry alpha nu)}
    (hold : oldRemaining = newRemaining + count)
    (holdBound : oldRemaining ≤ total)
    (hcurrentFrame :
      SortSlice.EqualOutsideRange origin before base total)
    (hstepFrame : SortSlice.EqualOutsideRange before after
      (base + newRemaining) count)
    (hblock :
      (sortSliceRangeEntries after (base + newRemaining) count).toList =
        block)
    (hfilled :
      (sortSliceRangeEntries before (base + oldRemaining)
        (total - oldRemaining)).toList = target.drop oldRemaining)
    (hassemble : block ++ target.drop oldRemaining =
      target.drop newRemaining) :
    (sortSliceRangeEntries after (base + newRemaining)
        (total - newRemaining)).toList = target.drop newRemaining ∧
      (sortSliceRangeEntries after base newRemaining).toList =
        (sortSliceRangeEntries before base newRemaining).toList ∧
      SortSlice.EqualOutsideRange origin after base total := by
  have hnewBound : newRemaining ≤ total := by omega
  have htailCount :
      total - newRemaining = count + (total - oldRemaining) := by omega
  have htailStart :
      base + newRemaining + count = base + oldRemaining := by omega
  have htailEq :
      (sortSliceRangeEntries after (base + oldRemaining)
        (total - oldRemaining)).toList =
      (sortSliceRangeEntries before (base + oldRemaining)
        (total - oldRemaining)).toList := by
    have hentries := hstepFrame.entries_eq_of_disjoint
      (base + oldRemaining) (total - oldRemaining) (Or.inr (by omega))
    exact congrArg Array.toList hentries.symm
  have hprefixEq :
      (sortSliceRangeEntries after base newRemaining).toList =
      (sortSliceRangeEntries before base newRemaining).toList := by
    have hentries := hstepFrame.entries_eq_of_disjoint base newRemaining
      (Or.inl (by omega))
    exact congrArg Array.toList hentries.symm
  refine ⟨?_, hprefixEq, hcurrentFrame.trans
    (hstepFrame.widen (by omega) (by omega))⟩
  rw [htailCount, sortSliceRangeEntries_toList_add, htailStart,
    hblock, htailEq, hfilled, hassemble]

theorem mergeHi_rangeEntries_prefix
    (slice : SortSlice alpha nu) (start prefixCount whole : Nat)
    (hle : prefixCount ≤ whole) :
    (sortSliceRangeEntries slice start prefixCount).toList =
      (sortSliceRangeEntries slice start whole).toList.take prefixCount := by
  simp only [sortSliceRangeEntries_toList, List.take_take]
  rw [Nat.min_eq_left hle]

/-- Range-list consequence of the shared signed snapshot-copy contract. -/
theorem sortSliceRangeEntries_toList_eq_of_copiesRange
    {before after : SortSlice alpha nu} {dst src count : Nat}
    (hcopy : SortSlice.CopiesRange before after (Int.ofNat dst)
      (Int.ofNat src) count)
    (hsrcStop : src + count ≤ before.entries.size)
    (hdstStop : dst + count ≤ after.entries.size) :
    (sortSliceRangeEntries after dst count).toList =
      (sortSliceRangeEntries before src count).toList := by
  apply sortSliceRangeEntries_toList_eq_of_reads
  · exact hdstStop
  · simp [sortSliceRangeEntries_size _ _ _ hsrcStop]
  · intro offset hoffset
    have hcopied := hcopy offset hoffset
    have hsource : before.read? (Int.ofNat (src + offset)) =
        ((sortSliceRangeEntries before src count).toList)[offset]? := by
      rw [SortSlice.read?_ofNat, sortSliceRangeEntries_toList]
      simp [hoffset]
    simpa only [Int.ofNat_eq_natCast, Nat.cast_add] using
      hcopied.trans hsource

/-- Pure prefix/suffix accounting after the backward merge peels one block
from the end of its remaining mathematical merge. -/
theorem mergeHi_target_peel
    {target oldMerged newMerged block : List alpha}
    {oldRemaining newRemaining : Nat}
    (hold : oldRemaining = newRemaining + block.length)
    (_htarget : oldRemaining ≤ target.length)
    (hnewLength : newMerged.length = newRemaining)
    (holdTarget : oldMerged = target.take oldRemaining)
    (hpeel : oldMerged = newMerged ++ block) :
    newMerged = target.take newRemaining ∧
      block ++ target.drop oldRemaining = target.drop newRemaining := by
  have hprefix : newMerged = target.take newRemaining := by
    have htake := congrArg (List.take newRemaining)
      (hpeel.symm.trans holdTarget)
    simp only [List.take_append, hnewLength, Nat.sub_self,
      List.take_zero, List.append_nil] at htake
    rw [List.take_take, Nat.min_eq_left (by omega)] at htake
    rw [List.take_of_length_le (by omega)] at htake
    exact htake
  refine ⟨hprefix, ?_⟩
  apply List.append_cancel_left
  calc
    target.take newRemaining ++
        (block ++ target.drop oldRemaining) =
        (newMerged ++ block) ++ target.drop oldRemaining := by
          rw [hprefix]
          simp only [List.append_assoc]
    _ = target.take oldRemaining ++ target.drop oldRemaining := by
          rw [← hpeel, holdTarget]
    _ = target := List.take_append_drop oldRemaining target
    _ = target.take newRemaining ++ target.drop newRemaining := by
          rw [List.take_append_drop]

/-- Actual `merge_at` safety geometry turns the signed adjacency equation into
the natural-indexed split used by range semantics. -/
theorem mergeHi_ssa_add_na_toNat
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

/-- The exact affected pre-state range is the concatenation of the two trimmed
runs retained in `MergeAtCall`. -/
theorem mergeHiCombinedEntries_eq_append
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call) :
    (sortSliceRangeEntries call.state.data call.ssa.toNat
        (call.na + call.nb)).toList =
      mergeHiLeftEntries call ++ mergeHiRightEntries call := by
  rw [sortSliceRangeEntries_toList_add]
  simp only [mergeHiLeftEntries, mergeHiRightEntries]
  rw [mergeHi_ssa_add_na_toNat hgeometry]

/-- Signed merged-range geometry in the natural indexing used by semantic
ranges. -/
theorem MergeAtSafetyGeometry.naturalMergedRange
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    (h : MergeAtSafetyGeometry pre scanned i call) :
    call.ssa.toNat + (call.na + call.nb) ≤
      call.state.data.entries.size := by
  have hbase : Int.ofNat call.ssa.toNat = call.ssa :=
    Int.toNat_of_nonneg h.ssaNonnegative
  have hrange := h.mergedRange
  rw [← hbase] at hrange
  apply Int.ofNat_le.mp
  simpa only [Int.ofNat_eq_natCast, Nat.cast_add] using hrange

/-- Signed right-run geometry in natural indexing. -/
theorem MergeAtSafetyGeometry.naturalRightRange
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    (h : MergeAtSafetyGeometry pre scanned i call) :
    call.ssb.toNat + call.nb ≤ call.state.data.entries.size := by
  have hbase : Int.ofNat call.ssb.toNat = call.ssb :=
    Int.toNat_of_nonneg h.ssbNonnegative
  have hrange := h.rightRange
  rw [← hbase] at hrange
  apply Int.ofNat_le.mp
  simpa only [Int.ofNat_eq_natCast, Nat.cast_add] using hrange

@[simp]
theorem mergeHiLeftEntries_length_of_geometry
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    (h : MergeAtSafetyGeometry pre scanned i call) :
    (mergeHiLeftEntries call).length = call.na := by
  change (sortSliceRangeEntries call.state.data call.ssa.toNat call.na).size =
    call.na
  apply sortSliceRangeEntries_size
  have := h.naturalMergedRange
  omega

@[simp]
theorem mergeHiRightEntries_length_of_geometry
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    (h : MergeAtSafetyGeometry pre scanned i call) :
    (mergeHiRightEntries call).length = call.nb := by
  change (sortSliceRangeEntries call.state.data call.ssb.toNat call.nb).size =
    call.nb
  exact sortSliceRangeEntries_size _ _ _ h.naturalRightRange

/-- The mathematical merge target has the combined input length. -/
@[simp]
theorem mergeHiTargetEntries_length (lt : BoolComparator alpha)
    (call : MergeAtCall (Occurrence alpha) nu) :
    (mergeHiTargetEntries lt call).length =
      (mergeHiLeftEntries call).length + (mergeHiRightEntries call).length := by
  simp [mergeHiTargetEntries, stableEntryMerge, List.length_merge]

@[simp]
theorem mergeHiTargetEntries_length_of_geometry
    (lt : BoolComparator alpha)
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    (h : MergeAtSafetyGeometry pre scanned i call) :
    (mergeHiTargetEntries lt call).length = call.na + call.nb := by
  rw [mergeHiTargetEntries_length,
    mergeHiLeftEntries_length_of_geometry h,
    mergeHiRightEntries_length_of_geometry h]

/-- Pointwise snapshot read for the immutable trimmed left run. -/
theorem mergeHiLeftEntries_getElem?_of_geometry
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    (h : MergeAtSafetyGeometry pre scanned i call)
    (offset : Nat) (hoffset : offset < call.na) :
    (mergeHiLeftEntries call)[offset]? =
      call.state.data.read? (call.ssa + Int.ofNat offset) := by
  have hstop := h.naturalMergedRange
  have hleftStop : call.ssa.toNat + call.na ≤
      call.state.data.entries.size := by omega
  have hcast : call.ssa + Int.ofNat offset =
      Int.ofNat (call.ssa.toNat + offset) := by
    rw [← Int.toNat_of_nonneg h.ssaNonnegative]
    simp
  rw [hcast, SortSlice.read?_ofNat]
  simp only [mergeHiLeftEntries, Array.getElem?_toList]
  rw [Array.getElem?_eq_getElem (by
      rw [sortSliceRangeEntries_size _ _ _ hleftStop]
      exact hoffset),
    sortSliceRangeEntries_getElem _ _ _ _ hleftStop hoffset,
    ← Array.getElem?_eq_getElem (by omega)]

/-- Pointwise snapshot read for the immutable trimmed right run. -/
theorem mergeHiRightEntries_getElem?_of_geometry
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    (h : MergeAtSafetyGeometry pre scanned i call)
    (offset : Nat) (hoffset : offset < call.nb) :
    (mergeHiRightEntries call)[offset]? =
      call.state.data.read? (call.ssb + Int.ofNat offset) := by
  have hstop := h.naturalRightRange
  have hcast : call.ssb + Int.ofNat offset =
      Int.ofNat (call.ssb.toNat + offset) := by
    rw [← Int.toNat_of_nonneg h.ssbNonnegative]
    simp
  rw [hcast, SortSlice.read?_ofNat]
  simp only [mergeHiRightEntries, Array.getElem?_toList]
  rw [Array.getElem?_eq_getElem (by
      rw [sortSliceRangeEntries_size _ _ _ hstop]
      exact hoffset),
    sortSliceRangeEntries_getElem _ _ _ _ hstop hoffset,
    ← Array.getElem?_eq_getElem (by omega)]

/-- Exact high-end read gives the immutable left-run snoc decomposition. -/
theorem mergeHiLeftEntries_snoc_of_geometry
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    (h : MergeAtSafetyGeometry pre scanned i call)
    (entry : SortSliceEntry (Occurrence alpha) nu)
    (hread : call.state.data.read?
      (call.ssa + Int.ofNat (call.na - 1)) = some entry) :
    mergeHiLeftEntries call =
      (mergeHiLeftEntries call).take (call.na - 1) ++ [entry] := by
  have hna := h.leftPositive
  have hget := mergeHiLeftEntries_getElem?_of_geometry h (call.na - 1)
    (by omega)
  rw [hread] at hget
  have hbound : call.na - 1 < (mergeHiLeftEntries call).length := by
    rw [mergeHiLeftEntries_length_of_geometry h]
    omega
  have heq : (mergeHiLeftEntries call)[call.na - 1] = entry := by
    rw [List.getElem?_eq_getElem hbound] at hget
    exact Option.some.inj hget
  calc
    mergeHiLeftEntries call =
        (mergeHiLeftEntries call).take (mergeHiLeftEntries call).length :=
      List.take_length.symm
    _ = (mergeHiLeftEntries call).take call.na := by
      rw [mergeHiLeftEntries_length_of_geometry h]
    _ = (mergeHiLeftEntries call).take (call.na - 1) ++ [entry] := by
      rw [show call.na = call.na - 1 + 1 by omega,
        List.take_succ_eq_append_getElem hbound, heq]
      simp only [Nat.add_sub_cancel]

/-- Exact high-end read gives the immutable right-run snoc decomposition. -/
theorem mergeHiRightEntries_snoc_of_geometry
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    (h : MergeAtSafetyGeometry pre scanned i call)
    (entry : SortSliceEntry (Occurrence alpha) nu)
    (hread : call.state.data.read?
      (call.ssb + Int.ofNat (call.nb - 1)) = some entry) :
    mergeHiRightEntries call =
      (mergeHiRightEntries call).take (call.nb - 1) ++ [entry] := by
  have hnb := h.rightPositive
  have hget := mergeHiRightEntries_getElem?_of_geometry h (call.nb - 1)
    (by omega)
  rw [hread] at hget
  have hbound : call.nb - 1 < (mergeHiRightEntries call).length := by
    rw [mergeHiRightEntries_length_of_geometry h]
    omega
  have heq : (mergeHiRightEntries call)[call.nb - 1] = entry := by
    rw [List.getElem?_eq_getElem hbound] at hget
    exact Option.some.inj hget
  calc
    mergeHiRightEntries call =
        (mergeHiRightEntries call).take (mergeHiRightEntries call).length :=
      List.take_length.symm
    _ = (mergeHiRightEntries call).take call.nb := by
      rw [mergeHiRightEntries_length_of_geometry h]
    _ = (mergeHiRightEntries call).take (call.nb - 1) ++ [entry] := by
      rw [show call.nb = call.nb - 1 + 1 by omega,
        List.take_succ_eq_append_getElem hbound, heq]
      simp only [Nat.add_sub_cancel]

/-- Comparator transport supplied by the safety invariant and the call-entry
comparator binding. -/
theorem MergeHiSemanticCursorInvariant.order
    {lt : BoolComparator alpha}
    {call : MergeAtCall (Occurrence alpha) nu}
    {cursor : MergeHiCursor (Occurrence alpha) nu}
    (horder : BoolStrictWeakOrder lt)
    (h : MergeHiSemanticCursorInvariant lt call cursor) :
    BoolStrictWeakOrder cursor.state.key_compare := by
  rw [h.comparator]
  exact horder.occurrenceComparator

/-- Control-only cursor updates preserve every semantic component.  This is
the semantic counterpart of `MergeHiCursorInvariant.setControl` and keeps the
loop proof independent of streak counters and the local gallop threshold. -/
theorem MergeHiSemanticCursorInvariant.setControl
    {lt : BoolComparator alpha}
    {call : MergeAtCall (Occurrence alpha) nu}
    {cursor : MergeHiCursor (Occurrence alpha) nu}
    (h : MergeHiSemanticCursorInvariant lt call cursor)
    (minGallop : PySSize) (phase : MergeHiPhase) :
    MergeHiSemanticCursorInvariant lt call
      { cursor with minGallop := minGallop, phase := phase } := by
  exact
    { safety := h.safety.setControl minGallop phase
      basea_eq := h.basea_eq
      comparator := h.comparator
      leftCount := h.leftCount
      rightCount := h.rightCount
      rightPositive := h.rightPositive
      activeLeft := h.activeLeft
      activeRight := h.activeRight
      remainingTarget := h.remainingTarget
      filledTarget := h.filledTarget
      frame := h.frame
      lowSentinel := h.lowSentinel }

/-- Updating the state/local gallop threshold together changes no semantic
data.  It is used at the beginning and end of a galloping round. -/
theorem MergeHiSemanticCursorInvariant.setMinGallop
    {lt : BoolComparator alpha}
    {call : MergeAtCall (Occurrence alpha) nu}
    {cursor : MergeHiCursor (Occurrence alpha) nu}
    (h : MergeHiSemanticCursorInvariant lt call cursor)
    (minGallop : PySSize) :
    MergeHiSemanticCursorInvariant lt call
      { cursor with
        state := { cursor.state with min_gallop := minGallop }
        minGallop := minGallop } := by
  exact
    { safety := h.safety.setMinGallop minGallop
      basea_eq := h.basea_eq
      comparator := h.comparator
      leftCount := h.leftCount
      rightCount := h.rightCount
      rightPositive := h.rightPositive
      activeLeft := h.activeLeft
      activeRight := h.activeRight
      remainingTarget := h.remainingTarget
      filledTarget := h.filledTarget
      frame := h.frame
      lowSentinel := h.lowSentinel }

/-- Natural-indexed form of the live cursor's signed main-range bound. -/
theorem MergeHiSemanticCursorInvariant.naturalMainRange
    {lt : BoolComparator alpha}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {cursor : MergeHiCursor (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call)
    (h : MergeHiSemanticCursorInvariant lt call cursor) :
    call.ssa.toNat + (cursor.na + cursor.nb) ≤
      cursor.state.data.entries.size := by
  have hbase : Int.ofNat call.ssa.toNat = call.ssa :=
    Int.toNat_of_nonneg hgeometry.ssaNonnegative
  have hrange := h.safety.mainRange
  rw [h.basea_eq, ← hbase] at hrange
  apply Int.ofNat_le.mp
  simpa only [Int.ofNat_eq_natCast, Nat.cast_add] using hrange

/-- Generic semantic closure for one backward block write.  Primitive-specific
lemmas only have to establish the new active prefixes, the exact written
block, and the local frame; target prefix/suffix accounting is centralized
here. -/
theorem MergeHiSemanticCursorInvariant.peelBlock
    {lt : BoolComparator alpha}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {cursor next : MergeHiCursor (Occurrence alpha) nu}
    {block : List (SortSliceEntry (Occurrence alpha) nu)}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call)
    (h : MergeHiSemanticCursorInvariant lt call cursor)
    (hsafety : MergeHiCursorInvariant (mergeHiAllocated call).state call.nb next)
    (hbasea : next.basea = call.ssa)
    (hcomparator : next.state.key_compare = occurrenceComparator lt)
    (hleftCount : next.na ≤ call.na)
    (hrightCount : next.nb ≤ call.nb)
    (hrightPositive : 0 < next.nb)
    (hactiveLeft :
      (sortSliceRangeEntries next.state.data call.ssa.toNat next.na).toList =
        (mergeHiLeftEntries call).take next.na)
    (hactiveRight :
      MergeHiTempPrefixMatches next.state.a (mergeHiRightEntries call) next.nb)
    (hcount : cursor.na + cursor.nb = next.na + next.nb + block.length)
    (hpeel :
      stableEntryMerge lt
          ((mergeHiLeftEntries call).take cursor.na)
          ((mergeHiRightEntries call).take cursor.nb) =
        stableEntryMerge lt
            ((mergeHiLeftEntries call).take next.na)
            ((mergeHiRightEntries call).take next.nb) ++ block)
    (hstepFrame : SortSlice.EqualOutsideRange cursor.state.data next.state.data
      (call.ssa.toNat + next.na + next.nb) block.length)
    (hblock :
      (sortSliceRangeEntries next.state.data
        (call.ssa.toNat + next.na + next.nb) block.length).toList = block)
    (hlowSentinel :
      ∃ leftFirst rightFirst,
        next.state.data.read? call.ssa = some leftFirst ∧
        mergeHiTempRead? next.state.a 0 = some rightFirst ∧
        lt rightFirst.key.value leftFirst.key.value = true) :
    MergeHiSemanticCursorInvariant lt call next := by
  have htargetLength :
      (mergeHiTargetEntries lt call).length = call.na + call.nb :=
    mergeHiTargetEntries_length_of_geometry lt hgeometry
  have holdBound : cursor.na + cursor.nb ≤ call.na + call.nb :=
    Nat.add_le_add h.leftCount h.rightCount
  have hnewLeftLength :
      ((mergeHiLeftEntries call).take next.na).length = next.na := by
    rw [List.length_take, mergeHiLeftEntries_length_of_geometry hgeometry,
      Nat.min_eq_left hleftCount]
  have hnewRightLength :
      ((mergeHiRightEntries call).take next.nb).length = next.nb := by
    rw [List.length_take, mergeHiRightEntries_length_of_geometry hgeometry,
      Nat.min_eq_left hrightCount]
  have hnewMergedLength :
      (stableEntryMerge lt
        ((mergeHiLeftEntries call).take next.na)
        ((mergeHiRightEntries call).take next.nb)).length = next.na + next.nb := by
    simp only [stableEntryMerge, List.length_merge, hnewLeftLength,
      hnewRightLength]
  rcases mergeHi_target_peel hcount (by simpa [htargetLength] using holdBound)
      hnewMergedLength
      h.remainingTarget hpeel with ⟨hremaining, hassemble⟩
  have hfilledBefore :
      (sortSliceRangeEntries cursor.state.data
        (call.ssa.toNat + (cursor.na + cursor.nb))
        (call.na + call.nb - (cursor.na + cursor.nb))).toList =
      (mergeHiTargetEntries lt call).drop (cursor.na + cursor.nb) := by
    simpa [mergeHiFilledEntries, Nat.add_assoc] using h.filledTarget
  rcases mergeHi_backwardFillBlock hcount holdBound h.frame
      (by simpa [Nat.add_assoc] using hstepFrame)
      (by simpa [Nat.add_assoc] using hblock)
      hfilledBefore hassemble with ⟨hfilled, _hprefix, hframe⟩
  exact
    { safety := hsafety
      basea_eq := hbasea
      comparator := hcomparator
      leftCount := hleftCount
      rightCount := hrightCount
      rightPositive := hrightPositive
      activeLeft := hactiveLeft
      activeRight := hactiveRight
      remainingTarget := hremaining
      filledTarget := by
        simpa [mergeHiFilledEntries, Nat.add_assoc] using hfilled
      frame := hframe
      lowSentinel := hlowSentinel }

/-- The active main-run cursor reads the final entry of the active immutable
left prefix, together with the exact snoc decomposition used by reverse
single-cell and gallop transitions. -/
theorem MergeHiSemanticCursorInvariant.activeLeft_snoc
    {lt : BoolComparator alpha}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {cursor : MergeHiCursor (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call)
    (h : MergeHiSemanticCursorInvariant lt call cursor)
    (hna : 0 < cursor.na) :
    ∃ entry,
      cursor.state.data.read? cursor.ssa = some entry ∧
      (mergeHiLeftEntries call).take cursor.na =
        (mergeHiLeftEntries call).take (cursor.na - 1) ++ [entry] := by
  rcases SortSlice.read_eq_some_of_indexInBounds cursor.state.data cursor.ssa
      (h.safety.ssaInBounds hna) with ⟨entry, hread⟩
  refine ⟨entry, hread, ?_⟩
  have hbase : Int.ofNat call.ssa.toNat = call.ssa :=
    Int.toNat_of_nonneg hgeometry.ssaNonnegative
  have hssa : cursor.ssa = Int.ofNat (call.ssa.toNat + cursor.na - 1) := by
    have heq := h.safety.ssaEquation
    rw [h.basea_eq, ← hbase] at heq
    simp only [Int.ofNat_eq_natCast] at heq ⊢
    omega
  have hssa' :
      cursor.ssa = Int.ofNat (call.ssa.toNat + (cursor.na - 1)) := by
    rw [hssa]
    congr 1
    omega
  have hstop : call.ssa.toNat + cursor.na ≤
      cursor.state.data.entries.size := by
    have hrange := h.safety.mainRange
    rw [h.basea_eq, ← hbase] at hrange
    simp only [Int.ofNat_eq_natCast, Nat.cast_add] at hrange
    exact_mod_cast (show call.ssa.toNat + cursor.na ≤
      cursor.state.data.entries.size by omega)
  have hindex :
      ((sortSliceRangeEntries cursor.state.data call.ssa.toNat
        cursor.na).toList)[cursor.na - 1]? = some entry := by
    have hreadNat : cursor.state.data.entries[
        call.ssa.toNat + (cursor.na - 1)]? = some entry := by
      rw [← SortSlice.read?_ofNat]
      rw [← hssa']
      exact hread
    rw [Array.getElem?_toList, Array.getElem?_eq_getElem (by
      rw [sortSliceRangeEntries_size _ _ _ hstop]
      omega),
      sortSliceRangeEntries_getElem cursor.state.data call.ssa.toNat
        cursor.na (cursor.na - 1) hstop (by omega),
      ← Array.getElem?_eq_getElem (by omega), hreadNat]
  rw [h.activeLeft] at hindex
  have hlen : cursor.na ≤ (mergeHiLeftEntries call).length := by
    rw [mergeHiLeftEntries_length_of_geometry hgeometry]
    exact h.leftCount
  have hentry : (mergeHiLeftEntries call)[cursor.na - 1]? = some entry := by
    have hindex' : 0 < cursor.na ∧
        (mergeHiLeftEntries call)[cursor.na - 1]? = some entry := by
      simpa [List.getElem?_take, hlen] using hindex
    exact hindex'.2
  have hbound : cursor.na - 1 < (mergeHiLeftEntries call).length := by omega
  have heq : (mergeHiLeftEntries call)[cursor.na - 1] = entry := by
    rw [List.getElem?_eq_getElem hbound] at hentry
    exact Option.some.inj hentry
  conv_lhs =>
    rw [show cursor.na = (cursor.na - 1) + 1 by omega,
      List.take_succ_eq_append_getElem hbound, heq]

/-- The temporary cursor reads the final entry of the active immutable right
prefix. -/
theorem MergeHiSemanticCursorInvariant.activeRight_snoc
    {lt : BoolComparator alpha}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {cursor : MergeHiCursor (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call)
    (h : MergeHiSemanticCursorInvariant lt call cursor) :
    ∃ entry,
      mergeHiTempRead? cursor.state.a cursor.ssb = some entry ∧
      (mergeHiRightEntries call).take cursor.nb =
        (mergeHiRightEntries call).take (cursor.nb - 1) ++ [entry] := by
  have hnb := h.rightPositive
  rcases h.safety.tempReadable hnb with ⟨entry, hread⟩
  rw [mergeTempRead_eq_mergeHiTempRead] at hread
  refine ⟨entry, hread, ?_⟩
  have hssb : cursor.ssb = Int.ofNat (cursor.nb - 1) := by
    have heq := h.safety.ssbEquation
    simp only [Int.ofNat_eq_natCast] at heq ⊢
    omega
  have hmatch := h.activeRight.2 (cursor.nb - 1) (by omega)
  rw [← hssb, hread] at hmatch
  have hlen : cursor.nb ≤ (mergeHiRightEntries call).length := by
    rw [mergeHiRightEntries_length_of_geometry hgeometry]
    exact h.rightCount
  have hbound : cursor.nb - 1 < (mergeHiRightEntries call).length := by omega
  have heq : (mergeHiRightEntries call)[cursor.nb - 1] = entry := by
    rw [List.getElem?_eq_getElem hbound] at hmatch
    exact Option.some.inj hmatch.symm
  conv_lhs =>
    rw [show cursor.nb = (cursor.nb - 1) + 1 by omega,
      List.take_succ_eq_append_getElem hbound, heq]

/-! ## Exact one-cell semantic transitions -/

/-- A successful ordinary A-side copy peels the final active left entry from
the mathematical merge and installs that same whole entry at the next output
position.  Safety of the concrete updated cursor is supplied by the reviewed
traced step theorem used by the loop proof. -/
theorem MergeHiSemanticCursorInvariant.copyA
    {lt : BoolComparator alpha}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {cursor : MergeHiCursor (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call)
    (horder : BoolStrictWeakOrder lt)
    (hrightSorted : (mergeHiRightEntries call).Pairwise
      (fun earlier later => lt later.key.value earlier.key.value = false))
    (h : MergeHiSemanticCursorInvariant lt call cursor)
    (hna : 0 < cursor.na)
    (left right : SortSliceEntry (Occurrence alpha) nu)
    (hleft : cursor.state.data.read? cursor.ssa = some left)
    (hright : mergeHiTempRead? cursor.state.a cursor.ssb = some right)
    (hcompare : lt right.key.value left.key.value = true)
    (copied : MergeHiDataCursorResult (Occurrence alpha) nu)
    (hcopy : mergeHiCopyDataDecr? cursor.state cursor.dest cursor.ssa =
      some copied)
    (hsafety : MergeHiCursorInvariant (mergeHiAllocated call).state call.nb
      { cursor with
        state := copied.state
        dest := copied.dst
        ssa := copied.src
        na := cursor.na - 1 }) :
    MergeHiSemanticCursorInvariant lt call
      { cursor with
        state := copied.state
        dest := copied.dst
        ssa := copied.src
        na := cursor.na - 1 } := by
  let next : MergeHiCursor (Occurrence alpha) nu :=
    { cursor with
      state := copied.state
      dest := copied.dst
      ssa := copied.src
      na := cursor.na - 1 }
  rcases mergeHiCopyDataDecr_spec_of_eq_some cursor.state cursor.dest cursor.ssa
      copied hcopy with ⟨hdst, hsrc, htemp, hdestRead, hreadFrame⟩
  have hbaseCast : Int.ofNat call.ssa.toNat = call.ssa :=
    Int.toNat_of_nonneg hgeometry.ssaNonnegative
  have hdest :
      cursor.dest = Int.ofNat
        (call.ssa.toNat + ((cursor.na - 1) + cursor.nb)) := by
    have heq := h.safety.destEquation
    rw [h.basea_eq, ← hbaseCast] at heq
    simp only [Int.ofNat_eq_natCast, Nat.cast_add] at heq ⊢
    omega
  have hstepFrame : SortSlice.EqualOutsideRange cursor.state.data
      copied.state.data
      (call.ssa.toNat + (cursor.na - 1) + cursor.nb) 1 := by
    rw [hdest] at hreadFrame
    simpa [Nat.add_assoc] using hreadFrame.equalOutsideRange_ofNat
  have hstop : call.ssa.toNat + (cursor.na + cursor.nb) ≤
      copied.state.data.entries.size := by
    have hold := h.naturalMainRange hgeometry
    rw [← hreadFrame.1]
    exact hold
  have hblock :
      (sortSliceRangeEntries copied.state.data
        (call.ssa.toNat + (cursor.na - 1) + cursor.nb) 1).toList = [left] := by
    apply sortSliceRangeEntries_toList_eq_of_reads
    · omega
    · simp
    · intro offset hoffset
      have hoffsetZero : offset = 0 := by omega
      subst offset
      have hdestRead' : copied.state.data.read?
          (Int.ofNat (call.ssa.toNat + ((cursor.na - 1) + cursor.nb))) =
          some left := by
        rw [← hdest]
        exact hdestRead.trans hleft
      simpa [Nat.add_assoc] using hdestRead'
  rcases h.activeLeft_snoc hgeometry hna with
    ⟨left', hleft', hleftSnoc⟩
  have hleftEq : left' = left := by
    rw [hleft] at hleft'
    exact Option.some.inj hleft'.symm
  subst left'
  rcases h.activeRight_snoc hgeometry with
    ⟨right', hright', hrightSnoc⟩
  have hrightEq : right' = right := by
    rw [hright] at hright'
    exact Option.some.inj hright'.symm
  subst right'
  have hrightTakeSorted :
      ((mergeHiRightEntries call).take cursor.nb).Pairwise
        (fun earlier later =>
          lt later.key.value earlier.key.value = false) :=
    hrightSorted.take
  have hrightLast :
      ((mergeHiRightEntries call).take cursor.nb).getLast? = some right := by
    rw [hrightSnoc]
    simp
  have hrightNe : (mergeHiRightEntries call).take cursor.nb ≠ [] := by
    rw [hrightSnoc]
    simp
  have hrightLastEq :
      ((mergeHiRightEntries call).take cursor.nb).getLast hrightNe = right :=
    (List.getLast_eq_iff_getLast?_eq_some hrightNe).2 hrightLast
  have hallRightSuffix := all_right_lt_suffix_of_pairwise_of_last_lt horder
    ((mergeHiRightEntries call).take cursor.nb) [left] hrightNe
    hrightTakeSorted (by
      intro suffixEntry hsuffix
      simp only [List.mem_singleton] at hsuffix
      subst suffixEntry
      simpa only [hrightLastEq] using hcompare)
  have hallRight : ∀ entry ∈ (mergeHiRightEntries call).take cursor.nb,
      lt entry.key.value left.key.value = true := by
    intro entry hentry
    exact hallRightSuffix entry hentry left (by simp)
  have hpure :
      stableEntryMerge lt
          ((mergeHiLeftEntries call).take cursor.na)
          ((mergeHiRightEntries call).take cursor.nb) =
        stableEntryMerge lt
            ((mergeHiLeftEntries call).take (cursor.na - 1))
            ((mergeHiRightEntries call).take cursor.nb) ++ [left] := by
    rw [hleftSnoc]
    exact stableEntryMerge_snoc_left_of_all_right_lt lt _ _ left hallRight
  have hactiveLeft :
      (sortSliceRangeEntries copied.state.data call.ssa.toNat
        (cursor.na - 1)).toList =
      (mergeHiLeftEntries call).take (cursor.na - 1) := by
    calc
      _ = (sortSliceRangeEntries cursor.state.data call.ssa.toNat
          (cursor.na - 1)).toList := by
            exact congrArg Array.toList
              (hstepFrame.entries_eq_of_disjoint call.ssa.toNat
                (cursor.na - 1) (Or.inl (by omega))).symm
      _ = (sortSliceRangeEntries cursor.state.data call.ssa.toNat
          cursor.na).toList.take (cursor.na - 1) :=
            mergeHi_rangeEntries_prefix _ _ _ _ (by omega)
      _ = ((mergeHiLeftEntries call).take cursor.na).take
          (cursor.na - 1) := by rw [h.activeLeft]
      _ = (mergeHiLeftEntries call).take (cursor.na - 1) := by
            rw [List.take_take, Nat.min_eq_left (by omega)]
  have hactiveRight : MergeHiTempPrefixMatches copied.state.a
      (mergeHiRightEntries call) cursor.nb := by
    simpa [MergeHiTempPrefixMatches, htemp] using h.activeRight
  have hlow :
      ∃ leftFirst rightFirst,
        copied.state.data.read? call.ssa = some leftFirst ∧
        mergeHiTempRead? copied.state.a 0 = some rightFirst ∧
        lt rightFirst.key.value leftFirst.key.value = true := by
    rcases h.lowSentinel with
      ⟨leftFirst, rightFirst, hfirstLeft, hfirstRight, hfirstCompare⟩
    refine ⟨leftFirst, rightFirst, ?_, ?_, hfirstCompare⟩
    · have hbaseLtDest : call.ssa < cursor.dest := by
        have hnb := h.rightPositive
        rw [← hbaseCast, hdest]
        exact Int.ofNat_lt.mpr (by omega)
      have hpreserve := hreadFrame.2 call.ssa (Or.inl hbaseLtDest)
      exact hpreserve.trans hfirstLeft
    · simpa [htemp] using hfirstRight
  apply h.peelBlock hgeometry hsafety
  · exact h.basea_eq
  · exact hsafety.stableFrame.comparator.trans
      (h.safety.stableFrame.comparator.symm.trans h.comparator)
  · exact (Nat.sub_le cursor.na 1).trans h.leftCount
  · exact h.rightCount
  · exact h.rightPositive
  · exact hactiveLeft
  · exact hactiveRight
  · change cursor.na + cursor.nb =
      cursor.na - 1 + cursor.nb + [left].length
    simp only [List.length_singleton]
    omega
  · exact hpure
  · simpa [next, Nat.add_assoc] using hstepFrame
  · simpa [next, Nat.add_assoc] using hblock
  · exact hlow

/-- A successful ordinary B-side copy peels the final active right entry.
The false comparison premise includes comparator-equivalent ties, which is
the reverse-fill choice needed for left-biased forward stability. -/
theorem MergeHiSemanticCursorInvariant.copyB
    {lt : BoolComparator alpha}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {cursor : MergeHiCursor (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call)
    (horder : BoolStrictWeakOrder lt)
    (hleftSorted : (mergeHiLeftEntries call).Pairwise
      (fun earlier later => lt later.key.value earlier.key.value = false))
    (h : MergeHiSemanticCursorInvariant lt call cursor)
    (hna : 0 < cursor.na) (hnb : 1 < cursor.nb)
    (left right : SortSliceEntry (Occurrence alpha) nu)
    (hleft : cursor.state.data.read? cursor.ssa = some left)
    (hright : mergeHiTempRead? cursor.state.a cursor.ssb = some right)
    (hcompare : lt right.key.value left.key.value = false)
    (copied : MergeHiDataCursorResult (Occurrence alpha) nu)
    (hcopy : mergeHiCopyTempDecr? cursor.state cursor.dest cursor.ssb =
      some copied)
    (hsafety : MergeHiCursorInvariant (mergeHiAllocated call).state call.nb
      { cursor with
        state := copied.state
        dest := copied.dst
        ssb := copied.src
        nb := cursor.nb - 1 }) :
    MergeHiSemanticCursorInvariant lt call
      { cursor with
        state := copied.state
        dest := copied.dst
        ssb := copied.src
        nb := cursor.nb - 1 } := by
  let next : MergeHiCursor (Occurrence alpha) nu :=
    { cursor with
      state := copied.state
      dest := copied.dst
      ssb := copied.src
      nb := cursor.nb - 1 }
  rcases mergeHiCopyTempDecr_spec_of_eq_some cursor.state cursor.dest cursor.ssb
      copied hcopy with ⟨hdst, hsrc, htemp, hdestRead, hreadFrame⟩
  have hbaseCast : Int.ofNat call.ssa.toNat = call.ssa :=
    Int.toNat_of_nonneg hgeometry.ssaNonnegative
  have hdest : cursor.dest = Int.ofNat
      (call.ssa.toNat + (cursor.na + (cursor.nb - 1))) := by
    have heq := h.safety.destEquation
    rw [h.basea_eq, ← hbaseCast] at heq
    simp only [Int.ofNat_eq_natCast, Nat.cast_add] at heq ⊢
    omega
  have hstepFrame : SortSlice.EqualOutsideRange cursor.state.data
      copied.state.data
      (call.ssa.toNat + cursor.na + (cursor.nb - 1)) 1 := by
    rw [hdest] at hreadFrame
    simpa [Nat.add_assoc] using hreadFrame.equalOutsideRange_ofNat
  have hstop : call.ssa.toNat + (cursor.na + cursor.nb) ≤
      copied.state.data.entries.size := by
    have hold := h.naturalMainRange hgeometry
    rw [← hreadFrame.1]
    exact hold
  have hblock :
      (sortSliceRangeEntries copied.state.data
        (call.ssa.toNat + cursor.na + (cursor.nb - 1)) 1).toList = [right] := by
    apply sortSliceRangeEntries_toList_eq_of_reads
    · omega
    · simp
    · intro offset hoffset
      have hoffsetZero : offset = 0 := by omega
      subst offset
      have hdestRead' : copied.state.data.read?
          (Int.ofNat (call.ssa.toNat + (cursor.na + (cursor.nb - 1)))) =
          some right := by
        rw [← hdest]
        exact hdestRead.trans hright
      simpa [Nat.add_assoc] using hdestRead'
  rcases h.activeLeft_snoc hgeometry hna with
    ⟨left', hleft', hleftSnoc⟩
  have hleftEq : left' = left := by
    rw [hleft] at hleft'
    exact Option.some.inj hleft'.symm
  subst left'
  rcases h.activeRight_snoc hgeometry with
    ⟨right', hright', hrightSnoc⟩
  have hrightEq : right' = right := by
    rw [hright] at hright'
    exact Option.some.inj hright'.symm
  subst right'
  have hleftTakeSorted :
      ((mergeHiLeftEntries call).take cursor.na).Pairwise
        (fun earlier later =>
          lt later.key.value earlier.key.value = false) :=
    hleftSorted.take
  have hleftLast :
      ((mergeHiLeftEntries call).take cursor.na).getLast? = some left := by
    rw [hleftSnoc]
    simp
  have hleftNe : (mergeHiLeftEntries call).take cursor.na ≠ [] := by
    rw [hleftSnoc]
    simp
  have hleftLastEq :
      ((mergeHiLeftEntries call).take cursor.na).getLast hleftNe = left :=
    (List.getLast_eq_iff_getLast?_eq_some hleftNe).2 hleftLast
  have hallLeftSuffix := all_suffix_not_lt_left_of_pairwise_of_not_lt_last
    horder ((mergeHiLeftEntries call).take cursor.na) [right] hleftNe
    hleftTakeSorted (by
      intro suffixEntry hsuffix
      simp only [List.mem_singleton] at hsuffix
      subst suffixEntry
      simpa only [hleftLastEq] using hcompare)
  have hallLeft : ∀ entry ∈ (mergeHiLeftEntries call).take cursor.na,
      lt right.key.value entry.key.value = false := by
    intro entry hentry
    exact hallLeftSuffix entry hentry right (by simp)
  have hpure :
      stableEntryMerge lt
          ((mergeHiLeftEntries call).take cursor.na)
          ((mergeHiRightEntries call).take cursor.nb) =
        stableEntryMerge lt
            ((mergeHiLeftEntries call).take cursor.na)
            ((mergeHiRightEntries call).take (cursor.nb - 1)) ++ [right] := by
    rw [hrightSnoc]
    exact stableEntryMerge_snoc_right_of_all_not_lt lt _ _ right hallLeft
  have hactiveLeft :
      (sortSliceRangeEntries copied.state.data call.ssa.toNat cursor.na).toList =
      (mergeHiLeftEntries call).take cursor.na := by
    calc
      _ = (sortSliceRangeEntries cursor.state.data call.ssa.toNat
          cursor.na).toList := by
            exact congrArg Array.toList
              (hstepFrame.entries_eq_of_disjoint call.ssa.toNat cursor.na
                (Or.inl (by omega))).symm
      _ = _ := h.activeLeft
  have hactiveRight : MergeHiTempPrefixMatches copied.state.a
      (mergeHiRightEntries call) (cursor.nb - 1) := by
    refine ⟨?_, ?_⟩
    · exact (Nat.sub_le cursor.nb 1).trans h.activeRight.1
    · intro offset hoffset
      rw [htemp]
      exact h.activeRight.2 offset (by omega)
  have hlow :
      ∃ leftFirst rightFirst,
        copied.state.data.read? call.ssa = some leftFirst ∧
        mergeHiTempRead? copied.state.a 0 = some rightFirst ∧
        lt rightFirst.key.value leftFirst.key.value = true := by
    rcases h.lowSentinel with
      ⟨leftFirst, rightFirst, hfirstLeft, hfirstRight, hfirstCompare⟩
    refine ⟨leftFirst, rightFirst, ?_, ?_, hfirstCompare⟩
    · have hbaseLtDest : call.ssa < cursor.dest := by
        rw [← hbaseCast, hdest]
        exact Int.ofNat_lt.mpr (by omega)
      exact (hreadFrame.2 call.ssa (Or.inl hbaseLtDest)).trans hfirstLeft
    · simpa [htemp] using hfirstRight
  apply h.peelBlock hgeometry hsafety
  · exact h.basea_eq
  · exact hsafety.stableFrame.comparator.trans
      (h.safety.stableFrame.comparator.symm.trans h.comparator)
  · exact h.leftCount
  · exact (Nat.sub_le cursor.nb 1).trans h.rightCount
  · exact Nat.sub_pos_of_lt hnb
  · exact hactiveLeft
  · exact hactiveRight
  · change cursor.na + cursor.nb =
      cursor.na + (cursor.nb - 1) + [right].length
    simp only [List.length_singleton]
    omega
  · exact hpure
  · simpa [next, Nat.add_assoc] using hstepFrame
  · simpa [next, Nat.add_assoc] using hblock
  · exact hlow

/-! ## Actual entry-stage initialization -/

/-- The allocation, exact initial main-to-temp copy, and CPython's forced
first A copy establish the semantic invariant consumed by the phase loop. -/
theorem MergeHiPrepared.semanticInitial
    {lt : BoolComparator alpha}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {copied : MergeState (Occurrence alpha) nu}
    {forced : MergeHiDataCursorResult (Occurrence alpha) nu}
    (h : MergeHiPrepared pre scanned i call copied forced)
    (horder : BoolStrictWeakOrder lt)
    (hcomparator : call.state.key_compare = occurrenceComparator lt)
    (hsemantic : MergeHiSemanticPre lt call) :
  MergeHiSemanticCursorInvariant lt call
      (mergeHiInitialCursor call forced) := by
  have hgeometry := h.geometry
  have hna := hsemantic.leftNonempty
  have hnb := hsemantic.rightNonempty
  rcases hsemantic.lastStrict with
    ⟨leftLast, rightLast, hleftLastRead, hrightLastRead, hhighCompare⟩
  have hforcedRaw := h.forcedRaw
  rcases mergeHiCopyDataDecr_spec_of_eq_some copied
      (call.ssb + Int.ofNat (call.nb - 1))
      (call.ssa + Int.ofNat (call.na - 1)) forced hforcedRaw with
    ⟨hdst, hsrc, htemp, hforcedRead, hforcedFrame⟩
  have hbaseCast : Int.ofNat call.ssa.toNat = call.ssa :=
    Int.toNat_of_nonneg hgeometry.ssaNonnegative
  have hdest : call.ssb + Int.ofNat (call.nb - 1) =
      Int.ofNat (call.ssa.toNat + ((call.na - 1) + call.nb)) := by
    have hadjacent := hgeometry.adjacent
    rw [← hbaseCast] at hadjacent ⊢
    simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_sub hnb] at hadjacent ⊢
    omega
  have hstepFrame : SortSlice.EqualOutsideRange copied.data forced.state.data
      (call.ssa.toNat + (call.na - 1) + call.nb) 1 := by
    rw [hdest] at hforcedFrame
    simpa [Nat.add_assoc] using hforcedFrame.equalOutsideRange_ofNat
  have htempCopied : MergeHiTempPrefixMatches copied.a
      (mergeHiRightEntries call) call.nb := by
    refine ⟨?_, ?_⟩
    · rw [mergeHiRightEntries_length_of_geometry hgeometry]
    · intro offset hoffset
      have hcopyRead := mergeHiMemcpyDataToTemp_read_range_of_eq_some
        .initialDataToTemp rfl call.nb (mergeHiAllocated call).state copied
        0 call.ssb h.initialCopyRaw offset hoffset
      calc
        mergeHiTempRead? copied.a (Int.ofNat offset) =
            (mergeHiAllocated call).state.data.read?
              (call.ssb + Int.ofNat offset) := by simpa using hcopyRead
        _ = call.state.data.read? (call.ssb + Int.ofNat offset) := by
              rw [h.allocation.data_eq]
        _ = (mergeHiRightEntries call)[offset]? :=
              (mergeHiRightEntries_getElem?_of_geometry hgeometry offset
                hoffset).symm
  have hactiveRight : MergeHiTempPrefixMatches forced.state.a
      (mergeHiRightEntries call) call.nb := by
    simpa [htemp] using htempCopied
  have hactiveLeft :
      (sortSliceRangeEntries forced.state.data call.ssa.toNat
        (call.na - 1)).toList =
      (mergeHiLeftEntries call).take (call.na - 1) := by
    calc
      _ = (sortSliceRangeEntries copied.data call.ssa.toNat
          (call.na - 1)).toList := by
            exact congrArg Array.toList
              (hstepFrame.entries_eq_of_disjoint call.ssa.toNat
                (call.na - 1) (Or.inl (by omega))).symm
      _ = (sortSliceRangeEntries call.state.data call.ssa.toNat
          (call.na - 1)).toList := by rw [h.copiedData_eq]
      _ = (sortSliceRangeEntries call.state.data call.ssa.toNat
          call.na).toList.take (call.na - 1) :=
            mergeHi_rangeEntries_prefix _ _ _ _ (by omega)
      _ = (mergeHiLeftEntries call).take (call.na - 1) := by
            rfl
  have hleftSnoc := mergeHiLeftEntries_snoc_of_geometry hgeometry leftLast
    hleftLastRead
  have hrightSnoc := mergeHiRightEntries_snoc_of_geometry hgeometry rightLast
    hrightLastRead
  have hrightNe : mergeHiRightEntries call ≠ [] := by
    rw [hrightSnoc]
    simp
  have hrightLast : (mergeHiRightEntries call).getLast hrightNe = rightLast := by
    apply (List.getLast_eq_iff_getLast?_eq_some hrightNe).2
    rw [hrightSnoc]
    simp
  have hallRightSuffix := all_right_lt_suffix_of_pairwise_of_last_lt horder
    (mergeHiRightEntries call) [leftLast] hrightNe
      hsemantic.rightEntriesPairwise (by
      intro suffixEntry hsuffix
      simp only [List.mem_singleton] at hsuffix
      subst suffixEntry
      simpa only [hrightLast] using hhighCompare)
  have hallRight : ∀ entry ∈ mergeHiRightEntries call,
      lt entry.key.value leftLast.key.value = true := by
    intro entry hentry
    exact hallRightSuffix entry hentry leftLast (by simp)
  have hpure : mergeHiTargetEntries lt call =
      stableEntryMerge lt
          ((mergeHiLeftEntries call).take (call.na - 1))
          (mergeHiRightEntries call) ++ [leftLast] := by
    calc
      mergeHiTargetEntries lt call =
          stableEntryMerge lt (mergeHiLeftEntries call)
            (mergeHiRightEntries call) := rfl
      _ = stableEntryMerge lt
          ((mergeHiLeftEntries call).take (call.na - 1) ++ [leftLast])
          (mergeHiRightEntries call) := by rw [← hleftSnoc]
      _ = _ := stableEntryMerge_snoc_left_of_all_right_lt lt _ _ leftLast
        hallRight
  have hnewMergedLength :
      (stableEntryMerge lt
        ((mergeHiLeftEntries call).take (call.na - 1))
        (mergeHiRightEntries call)).length = (call.na - 1) + call.nb := by
    simp only [stableEntryMerge, List.length_merge, List.length_take,
      mergeHiLeftEntries_length_of_geometry hgeometry,
      mergeHiRightEntries_length_of_geometry hgeometry,
      Nat.min_eq_left (Nat.sub_le call.na 1)]
  have htargetWhole : mergeHiTargetEntries lt call =
      (mergeHiTargetEntries lt call).take (call.na + call.nb) := by
    rw [List.take_of_length_le]
    rw [mergeHiTargetEntries_length_of_geometry lt hgeometry]
  rcases mergeHi_target_peel (block := [leftLast]) (oldRemaining := call.na + call.nb)
      (newRemaining := (call.na - 1) + call.nb) (by simp; omega)
      (by rw [mergeHiTargetEntries_length_of_geometry lt hgeometry])
      hnewMergedLength htargetWhole hpure with ⟨hremaining, hassemble⟩
  have hcurrentFrame : SortSlice.EqualOutsideRange call.state.data copied.data
      call.ssa.toNat (call.na + call.nb) :=
    SortSlice.EqualOutsideRange.of_eq h.copiedData_eq.symm _ _
  have hstop : call.ssa.toNat + (call.na + call.nb) ≤
      forced.state.data.entries.size := by
    rw [← hforcedFrame.1, h.copiedData_eq]
    exact hgeometry.naturalMergedRange
  have hblock :
      (sortSliceRangeEntries forced.state.data
        (call.ssa.toNat + (call.na - 1) + call.nb) 1).toList = [leftLast] := by
    apply sortSliceRangeEntries_toList_eq_of_reads
    · omega
    · simp
    · intro offset hoffset
      have hoffsetZero : offset = 0 := by omega
      subst offset
      have hread' : forced.state.data.read?
          (Int.ofNat (call.ssa.toNat + ((call.na - 1) + call.nb))) =
          some leftLast := by
        rw [← hdest]
        exact hforcedRead.trans (by
          rw [h.copiedData_eq]
          exact hleftLastRead)
      simpa [Nat.add_assoc] using hread'
  have hfilledBefore :
      (sortSliceRangeEntries copied.data
        (call.ssa.toNat + (call.na + call.nb))
        (call.na + call.nb - (call.na + call.nb))).toList =
      (mergeHiTargetEntries lt call).drop (call.na + call.nb) := by
    simp [mergeHiTargetEntries_length_of_geometry lt hgeometry]
  rcases mergeHi_backwardFillBlock (target := mergeHiTargetEntries lt call)
      (block := [leftLast]) (count := 1) (by omega) (le_refl _)
      hcurrentFrame (by simpa [Nat.add_assoc] using hstepFrame)
      (by simpa [Nat.add_assoc] using hblock) hfilledBefore hassemble with
    ⟨hfilled, _hprefix, hframe⟩
  have hlow :
      ∃ leftFirst rightFirst,
        forced.state.data.read? call.ssa = some leftFirst ∧
        mergeHiTempRead? forced.state.a 0 = some rightFirst ∧
        lt rightFirst.key.value leftFirst.key.value = true := by
    rcases hsemantic.firstStrict with
      ⟨leftFirst, rightFirst, hleftFirst, hrightFirst, hlowCompare⟩
    refine ⟨leftFirst, rightFirst, ?_, ?_, hlowCompare⟩
    · have hbaseLtDest : call.ssa <
          call.ssb + Int.ofNat (call.nb - 1) := by
        rw [hdest, ← hbaseCast]
        exact Int.ofNat_lt.mpr (by omega)
      exact (hforcedFrame.2 call.ssa (Or.inl hbaseLtDest)).trans (by
        rw [h.copiedData_eq]
        exact hleftFirst)
    · rw [htemp]
      have hcopyRead := mergeHiMemcpyDataToTemp_read_range_of_eq_some
        .initialDataToTemp rfl call.nb (mergeHiAllocated call).state copied
        0 call.ssb h.initialCopyRaw 0 hnb
      calc
        mergeHiTempRead? copied.a 0 =
            (mergeHiAllocated call).state.data.read? call.ssb := by
              simpa using hcopyRead
        _ = call.state.data.read? call.ssb := by rw [h.allocation.data_eq]
        _ = some rightFirst := hrightFirst
  exact
    { safety := h.initialInvariant
      basea_eq := rfl
      comparator := h.initialInvariant.stableFrame.comparator.trans
        (h.allocation.keyCompare_eq.trans hcomparator)
      leftCount := Nat.sub_le call.na 1
      rightCount := le_rfl
      rightPositive := hnb
      activeLeft := hactiveLeft
      activeRight := hactiveRight
      remainingTarget := by
        have hrightTake :
            (mergeHiRightEntries call).take call.nb =
              mergeHiRightEntries call := by
          apply List.take_of_length_le
          rw [mergeHiRightEntries_length_of_geometry hgeometry]
        simpa [mergeHiInitialCursor, hrightTake] using hremaining
      filledTarget := by
        simpa [mergeHiFilledEntries, mergeHiInitialCursor, Nat.add_assoc]
          using hfilled
      frame := hframe
      lowSentinel := hlow }

/-- The immutable low sentinel is strictly below every still-active left
entry.  This is the shared order fact for the CopyA tail and for proving that
the B gallop's insertion index cannot be zero. -/
theorem MergeHiSemanticCursorInvariant.lowSentinel_lt_activeLeft
    {lt : BoolComparator alpha}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {cursor : MergeHiCursor (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call)
    (horder : BoolStrictWeakOrder lt)
    (hleftSorted : (mergeHiLeftEntries call).Pairwise
      (fun earlier later => lt later.key.value earlier.key.value = false))
    (h : MergeHiSemanticCursorInvariant lt call cursor)
    (hna : 0 < cursor.na) :
    ∃ rightFirst,
      mergeHiTempRead? cursor.state.a 0 = some rightFirst ∧
      ∀ leftEntry ∈ (mergeHiLeftEntries call).take cursor.na,
        lt rightFirst.key.value leftEntry.key.value = true := by
  rcases h.lowSentinel with
    ⟨leftFirst, rightFirst, hleftFirst, hrightFirst, hstrict⟩
  have hbaseCast : Int.ofNat call.ssa.toNat = call.ssa :=
    Int.toNat_of_nonneg hgeometry.ssaNonnegative
  have hstop : call.ssa.toNat + cursor.na ≤
      cursor.state.data.entries.size := by
    have hrange := h.naturalMainRange hgeometry
    omega
  have hreadNat : cursor.state.data.entries[call.ssa.toNat]? =
      some leftFirst := by
    rw [← SortSlice.read?_ofNat, hbaseCast]
    exact hleftFirst
  have hindex :
      ((sortSliceRangeEntries cursor.state.data call.ssa.toNat
        cursor.na).toList)[0]? = some leftFirst := by
    rw [Array.getElem?_toList, Array.getElem?_eq_getElem (by
      rw [sortSliceRangeEntries_size _ _ _ hstop]
      exact hna),
      sortSliceRangeEntries_getElem cursor.state.data call.ssa.toNat
        cursor.na 0 hstop hna,
      ← Array.getElem?_eq_getElem (by omega), Nat.add_zero, hreadNat]
  rw [h.activeLeft] at hindex
  have htakeSorted :
      ((mergeHiLeftEntries call).take cursor.na).Pairwise
        (fun earlier later =>
          lt later.key.value earlier.key.value = false) :=
    hleftSorted.take
  cases htake : (mergeHiLeftEntries call).take cursor.na with
  | nil => simp [htake] at hindex
  | cons head tail =>
      have hhead : head = leftFirst := by
        rw [htake] at hindex
        simpa using hindex
      subst head
      rw [htake, List.pairwise_cons] at htakeSorted
      refine ⟨rightFirst, hrightFirst, ?_⟩
      intro leftEntry hentry
      have hnotReverse : lt leftEntry.key.value leftFirst.key.value = false := by
        rcases List.mem_cons.mp hentry with hsame | htail
        · subst leftEntry
          exact Bool.eq_false_iff.mpr
            (horder.irrefl leftFirst.key.value)
        · exact htakeSorted.1 leftEntry htail
      exact horder.strict_of_strict_of_not_reverse hstrict hnotReverse

/-- The active main prefix is a sorted gallop source. -/
theorem MergeHiSemanticCursorInvariant.mainGallopSorted
    {lt : BoolComparator alpha}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {cursor : MergeHiCursor (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call)
    (hleftSorted : (mergeHiLeftEntries call).Pairwise
      (fun earlier later => lt later.key.value earlier.key.value = false))
    (h : MergeHiSemanticCursorInvariant lt call cursor) :
    GallopSortedRange cursor.state.key_compare
      (.main cursor.state.data cursor.basea) cursor.na := by
  intro firstIndex laterIndex hfirstBound hlaterBound hindexLt
    earlier later hfirstRead hlaterRead
  have hbaseCast : Int.ofNat call.ssa.toNat = call.ssa :=
    Int.toNat_of_nonneg hgeometry.ssaNonnegative
  have hstop : call.ssa.toNat + cursor.na ≤
      cursor.state.data.entries.size := by
    have hrange := h.naturalMainRange hgeometry
    omega
  have sourceEntry : ∀ index, index < cursor.na →
      ∀ entry,
        (GallopKeySource.main cursor.state.data cursor.basea).read?
            (Int.ofNat index) = some entry →
        ((mergeHiLeftEntries call).take cursor.na)[index]? = some entry := by
    intro index hindex entry hread
    have haddr : cursor.basea + Int.ofNat index =
        Int.ofNat (call.ssa.toNat + index) := by
      rw [h.basea_eq, ← hbaseCast]
      simp
    have hreadNat : cursor.state.data.entries[call.ssa.toNat + index]? =
        some entry := by
      change cursor.state.data.read?
          (cursor.basea + Int.ofNat index) = some entry at hread
      rw [haddr] at hread
      rw [← SortSlice.read?_ofNat]
      exact hread
    have hrangeRead :
        ((sortSliceRangeEntries cursor.state.data call.ssa.toNat
          cursor.na).toList)[index]? = some entry := by
      rw [Array.getElem?_toList, Array.getElem?_eq_getElem (by
        rw [sortSliceRangeEntries_size _ _ _ hstop]
        exact hindex),
        sortSliceRangeEntries_getElem _ _ _ _ hstop hindex,
        ← Array.getElem?_eq_getElem (by omega), hreadNat]
    rw [h.activeLeft] at hrangeRead
    exact hrangeRead
  have hfirstOpt := sourceEntry firstIndex hfirstBound earlier hfirstRead
  have hlaterOpt := sourceEntry laterIndex hlaterBound later hlaterRead
  have hfirstListBound : firstIndex <
      ((mergeHiLeftEntries call).take cursor.na).length := by
    rw [List.length_take,
      mergeHiLeftEntries_length_of_geometry hgeometry,
      Nat.min_eq_left h.leftCount]
    exact hfirstBound
  have hlaterListBound : laterIndex <
      ((mergeHiLeftEntries call).take cursor.na).length := by
    rw [List.length_take,
      mergeHiLeftEntries_length_of_geometry hgeometry,
      Nat.min_eq_left h.leftCount]
    exact hlaterBound
  have hfirstEq :
      ((mergeHiLeftEntries call).take cursor.na)[firstIndex] = earlier := by
    rw [List.getElem?_eq_getElem hfirstListBound] at hfirstOpt
    exact Option.some.inj hfirstOpt
  have hlaterEq :
      ((mergeHiLeftEntries call).take cursor.na)[laterIndex] = later := by
    rw [List.getElem?_eq_getElem hlaterListBound] at hlaterOpt
    exact Option.some.inj hlaterOpt
  have hpair := (List.pairwise_iff_getElem.mp hleftSorted.take)
    firstIndex laterIndex hfirstListBound hlaterListBound hindexLt
  rw [hfirstEq, hlaterEq] at hpair
  simpa [h.comparator, occurrenceComparator] using hpair

/-- The initialized active temporary prefix is a sorted gallop source. -/
theorem MergeHiSemanticCursorInvariant.temporaryGallopSorted
    {lt : BoolComparator alpha}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {cursor : MergeHiCursor (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call)
    (hrightSorted : (mergeHiRightEntries call).Pairwise
      (fun earlier later => lt later.key.value earlier.key.value = false))
    (h : MergeHiSemanticCursorInvariant lt call cursor) :
    GallopSortedRange cursor.state.key_compare
      (.temporary cursor.state.a 0) cursor.nb := by
  intro firstIndex laterIndex hfirstBound hlaterBound hindexLt
    earlier later hfirstRead hlaterRead
  have sourceEntry : ∀ index, index < cursor.nb →
      ∀ entry,
        (GallopKeySource.temporary cursor.state.a 0).read?
            (Int.ofNat index) = some entry →
        ((mergeHiRightEntries call).take cursor.nb)[index]? = some entry := by
    intro index hindex entry hread
    have htempRead : mergeHiTempRead? cursor.state.a (Int.ofNat index) =
        some entry := by
      rw [mergeHiTempRead_ofNat]
      simpa [GallopKeySource.read?, GallopKeySource.base] using hread
    have hsnapshot := h.activeRight.2 index hindex
    rw [htempRead] at hsnapshot
    rw [List.getElem?_take, if_pos hindex]
    exact hsnapshot.symm
  have hfirstOpt := sourceEntry firstIndex hfirstBound earlier hfirstRead
  have hlaterOpt := sourceEntry laterIndex hlaterBound later hlaterRead
  have hfirstListBound : firstIndex <
      ((mergeHiRightEntries call).take cursor.nb).length := by
    rw [List.length_take,
      mergeHiRightEntries_length_of_geometry hgeometry,
      Nat.min_eq_left h.rightCount]
    exact hfirstBound
  have hlaterListBound : laterIndex <
      ((mergeHiRightEntries call).take cursor.nb).length := by
    rw [List.length_take,
      mergeHiRightEntries_length_of_geometry hgeometry,
      Nat.min_eq_left h.rightCount]
    exact hlaterBound
  have hfirstEq :
      ((mergeHiRightEntries call).take cursor.nb)[firstIndex] = earlier := by
    rw [List.getElem?_eq_getElem hfirstListBound] at hfirstOpt
    exact Option.some.inj hfirstOpt
  have hlaterEq :
      ((mergeHiRightEntries call).take cursor.nb)[laterIndex] = later := by
    rw [List.getElem?_eq_getElem hlaterListBound] at hlaterOpt
    exact Option.some.inj hlaterOpt
  have hpair := (List.pairwise_iff_getElem.mp hrightSorted.take)
    firstIndex laterIndex hfirstListBound hlaterListBound hindexLt
  rw [hfirstEq, hlaterEq] at hpair
  simpa [h.comparator, occurrenceComparator] using hpair

/-- The left-biased B gallop cannot return insertion index zero under the
semantic precondition.  This is the explicit proof that the transcription's
adversarial-comparator `nb == 0` hedge is unreachable for a strict weak order;
the hedge remains present in the raw evaluator. -/
theorem MergeHiSemanticCursorInvariant.gallopLeftIndex_pos
    {lt : BoolComparator alpha}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {cursor : MergeHiCursor (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call)
    (horder : BoolStrictWeakOrder lt)
    (hleftSorted : (mergeHiLeftEntries call).Pairwise
      (fun earlier later => lt later.key.value earlier.key.value = false))
    (h : MergeHiSemanticCursorInvariant lt call cursor)
    (hna : 0 < cursor.na)
    (left : SortSliceEntry (Occurrence alpha) nu)
    (hleft : cursor.state.data.read? cursor.ssa = some left)
    (temp : SortSlice (Occurrence alpha) nu)
    (htemp : initializedTempPrefix? cursor.state.a cursor.nb = some temp)
    (index : Nat)
    (hpartition : GallopLeftPartition cursor.state.key_compare temp 0
      left.key cursor.nb index) :
    0 < index := by
  rcases h.lowSentinel_lt_activeLeft hgeometry horder hleftSorted hna with
    ⟨rightFirst, hrightFirst, hallLeft⟩
  rcases h.activeLeft_snoc hgeometry hna with
    ⟨left', hleft', hleftSnoc⟩
  have hleftEq : left' = left := by
    rw [hleft] at hleft'
    exact Option.some.inj hleft'.symm
  subst left'
  have hleftMem : left ∈ (mergeHiLeftEntries call).take cursor.na := by
    rw [hleftSnoc]
    simp
  have hstrict : lt rightFirst.key.value left.key.value = true :=
    hallLeft left hleftMem
  have htempRead : temp.read? 0 = some rightFirst := by
    rcases initializedTempPrefix_cells_of_eq_some cursor.state.a cursor.nb
        temp htemp with ⟨_hsize, hcells⟩
    change temp.read? (Int.ofNat 0) = some rightFirst
    rw [SortSlice.read?_ofNat, ← hcells 0 h.rightPositive,
      ← mergeHiTempRead_ofNat]
    exact hrightFirst
  by_contra hnotPositive
  have hindexZero : index = 0 := by omega
  subst index
  rcases hpartition.2.2 0 (by omega) h.rightPositive with
    ⟨entry, hentryRead, hfalse⟩
  have hentryEq : entry = rightFirst := by
    have hentryRead' : temp.read? 0 = some entry := by simpa using hentryRead
    rw [htempRead] at hentryRead'
    exact Option.some.inj hentryRead'.symm
  subst entry
  have hfalse' : lt rightFirst.key.value left.key.value = false := by
    simpa [h.comparator, occurrenceComparator] using hfalse
  exact Bool.noConfusion (hfalse'.symm.trans hstrict)

/-! ## Exact gallop-block semantic transitions -/

/-- A nonempty same-store A gallop copies exactly the consumed left suffix to
the output suffix and peels that block from the pure stable merge. -/
theorem MergeHiSemanticCursorInvariant.copyABlock
    {lt : BoolComparator alpha}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {cursor : MergeHiCursor (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call)
    (horder : BoolStrictWeakOrder lt)
    (hrightSorted : (mergeHiRightEntries call).Pairwise
      (fun earlier later => lt later.key.value earlier.key.value = false))
    (h : MergeHiSemanticCursorInvariant lt call cursor)
    (count : Nat) (hcountPositive : 0 < count) (hcount : count ≤ cursor.na)
    (right : SortSliceEntry (Occurrence alpha) nu)
    (hright : mergeHiTempRead? cursor.state.a cursor.ssb = some right)
    (hboundary : ∀ suffixEntry ∈
      ((mergeHiLeftEntries call).take cursor.na).drop (cursor.na - count),
      lt right.key.value suffixEntry.key.value = true)
    (data : SortSlice (Occurrence alpha) nu)
    (hmove : mergeDataMemmove? .hiGallopA cursor.state.data
      (cursor.dest - Int.ofNat count + 1)
      (cursor.ssa - Int.ofNat count + 1) count = some data)
    (hsafety : MergeHiCursorInvariant (mergeHiAllocated call).state call.nb
      { cursor with
        state := { cursor.state with data := data }
        dest := cursor.dest - Int.ofNat count
        ssa := cursor.ssa - Int.ofNat count
        na := cursor.na - count }) :
    MergeHiSemanticCursorInvariant lt call
      { cursor with
        state := { cursor.state with data := data }
        dest := cursor.dest - Int.ofNat count
        ssa := cursor.ssa - Int.ofNat count
        na := cursor.na - count } := by
  let next : MergeHiCursor (Occurrence alpha) nu :=
    { cursor with
      state := { cursor.state with data := data }
      dest := cursor.dest - Int.ofNat count
      ssa := cursor.ssa - Int.ofNat count
      na := cursor.na - count }
  let block := ((mergeHiLeftEntries call).take cursor.na).drop
    (cursor.na - count)
  have hblockLength : block.length = count := by
    dsimp only [block]
    rw [List.length_drop, List.length_take,
      mergeHiLeftEntries_length_of_geometry hgeometry,
      Nat.min_eq_left h.leftCount]
    omega
  have hleftSplit : (mergeHiLeftEntries call).take cursor.na =
      (mergeHiLeftEntries call).take (cursor.na - count) ++ block := by
    dsimp only [block]
    calc
      _ = ((mergeHiLeftEntries call).take cursor.na).take
            (cursor.na - count) ++
          ((mergeHiLeftEntries call).take cursor.na).drop
            (cursor.na - count) :=
        (List.take_append_drop (cursor.na - count) _).symm
      _ = _ := by
        rw [List.take_take,
          Nat.min_eq_left (Nat.sub_le cursor.na count)]
  rcases h.activeRight_snoc hgeometry with
    ⟨right', hright', hrightSnoc⟩
  have hrightEq : right' = right := by
    rw [hright] at hright'
    exact Option.some.inj hright'.symm
  subst right'
  have hrightTakeSorted :
      ((mergeHiRightEntries call).take cursor.nb).Pairwise
        (fun earlier later =>
          lt later.key.value earlier.key.value = false) :=
    hrightSorted.take
  have hrightNe : (mergeHiRightEntries call).take cursor.nb ≠ [] := by
    rw [hrightSnoc]
    simp
  have hrightLast :
      ((mergeHiRightEntries call).take cursor.nb).getLast hrightNe = right := by
    apply (List.getLast_eq_iff_getLast?_eq_some hrightNe).2
    rw [hrightSnoc]
    simp
  have hallRight := all_right_lt_suffix_of_pairwise_of_last_lt horder
    ((mergeHiRightEntries call).take cursor.nb) block hrightNe
    hrightTakeSorted (by
      intro suffixEntry hsuffix
      simpa only [hrightLast] using hboundary suffixEntry hsuffix)
  have hpure :
      stableEntryMerge lt
          ((mergeHiLeftEntries call).take cursor.na)
          ((mergeHiRightEntries call).take cursor.nb) =
        stableEntryMerge lt
            ((mergeHiLeftEntries call).take (cursor.na - count))
            ((mergeHiRightEntries call).take cursor.nb) ++ block := by
    calc
      _ = stableEntryMerge lt
          ((mergeHiLeftEntries call).take (cursor.na - count) ++ block)
          ((mergeHiRightEntries call).take cursor.nb) := by rw [← hleftSplit]
      _ = _ := stableEntryMerge_append_left_block lt block _ _ hallRight
  have hbaseCast : Int.ofNat call.ssa.toNat = call.ssa :=
    Int.toNat_of_nonneg hgeometry.ssaNonnegative
  have hsrcStart : cursor.ssa - Int.ofNat count + 1 =
      Int.ofNat (call.ssa.toNat + (cursor.na - count)) := by
    have heq := h.safety.ssaEquation
    rw [h.basea_eq, ← hbaseCast] at heq
    rw [← hbaseCast]
    simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_sub hcount] at heq ⊢
    omega
  have hdstStart : cursor.dest - Int.ofNat count + 1 =
      Int.ofNat (call.ssa.toNat + ((cursor.na - count) + cursor.nb)) := by
    have heq := h.safety.destEquation
    rw [h.basea_eq, ← hbaseCast] at heq
    rw [← hbaseCast]
    simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_sub hcount] at heq ⊢
    omega
  have hcopies := mergeDataMemmove_copiesRange_of_eq_some .hiGallopA
    cursor.state.data data _ _ count hmove
  rw [hsrcStart, hdstStart] at hcopies
  have hframeSigned := mergeDataMemmove_readFrame_of_eq_some .hiGallopA
    cursor.state.data data _ _ count hmove
  rw [hdstStart] at hframeSigned
  have hstepFrame := hframeSigned.equalOutsideRange_ofNat
  have hsourceStop : call.ssa.toNat + (cursor.na - count) + count ≤
      cursor.state.data.entries.size := by
    have hrange := h.naturalMainRange hgeometry
    omega
  have hdestStop :
      call.ssa.toNat + ((cursor.na - count) + cursor.nb) + count ≤
        data.entries.size := by
    have hrange := h.naturalMainRange hgeometry
    rw [← hframeSigned.1]
    omega
  have hsourceBlock :
      (sortSliceRangeEntries cursor.state.data
        (call.ssa.toNat + (cursor.na - count)) count).toList = block := by
    calc
      _ = (sortSliceRangeEntries cursor.state.data call.ssa.toNat
          cursor.na).toList.drop (cursor.na - count) := by
            rw [sortSliceRangeEntries_toList_drop]
            congr 2
            omega
      _ = ((mergeHiLeftEntries call).take cursor.na).drop
          (cursor.na - count) := by rw [h.activeLeft]
      _ = block := rfl
  have hblock :
      (sortSliceRangeEntries data
        (call.ssa.toNat + ((cursor.na - count) + cursor.nb)) count).toList =
        block := by
    rw [sortSliceRangeEntries_toList_eq_of_copiesRange hcopies hsourceStop
      hdestStop, hsourceBlock]
  have hactiveLeft :
      (sortSliceRangeEntries data call.ssa.toNat (cursor.na - count)).toList =
      (mergeHiLeftEntries call).take (cursor.na - count) := by
    calc
      _ = (sortSliceRangeEntries cursor.state.data call.ssa.toNat
          (cursor.na - count)).toList := by
            exact congrArg Array.toList
              (hstepFrame.entries_eq_of_disjoint call.ssa.toNat
                (cursor.na - count) (Or.inl (by omega))).symm
      _ = (sortSliceRangeEntries cursor.state.data call.ssa.toNat
          cursor.na).toList.take (cursor.na - count) :=
            mergeHi_rangeEntries_prefix _ _ _ _ (Nat.sub_le _ _)
      _ = ((mergeHiLeftEntries call).take cursor.na).take
          (cursor.na - count) := by rw [h.activeLeft]
      _ = (mergeHiLeftEntries call).take (cursor.na - count) := by
            rw [List.take_take, Nat.min_eq_left (Nat.sub_le _ _)]
  have hlow :
      ∃ leftFirst rightFirst,
        data.read? call.ssa = some leftFirst ∧
        mergeHiTempRead? cursor.state.a 0 = some rightFirst ∧
        lt rightFirst.key.value leftFirst.key.value = true := by
    rcases h.lowSentinel with
      ⟨leftFirst, rightFirst, hleftFirst, hrightFirst, hstrict⟩
    refine ⟨leftFirst, rightFirst, ?_, hrightFirst, hstrict⟩
    have hnb := h.rightPositive
    have hbaseBefore : call.ssa <
        Int.ofNat (call.ssa.toNat + ((cursor.na - count) + cursor.nb)) := by
      rw [← hbaseCast]
      exact Int.ofNat_lt.mpr (by omega)
    exact (hframeSigned.2 call.ssa (Or.inl hbaseBefore)).trans hleftFirst
  apply h.peelBlock hgeometry hsafety
  · exact h.basea_eq
  · exact hsafety.stableFrame.comparator.trans
      (h.safety.stableFrame.comparator.symm.trans h.comparator)
  · exact (Nat.sub_le _ _).trans h.leftCount
  · exact h.rightCount
  · exact h.rightPositive
  · exact hactiveLeft
  · exact h.activeRight
  · dsimp only [next]
    rw [hblockLength]
    omega
  · exact hpure
  · simpa [next, Nat.add_assoc, hblockLength] using hstepFrame
  · simpa [next, Nat.add_assoc, hblockLength] using hblock
  · simpa [next] using hlow

/-- A nonempty temporary-to-main B gallop copies exactly the consumed right
suffix.  The strict inequality on `count` is the semantic consequence of the
separately proved positive insertion index and preserves `rightPositive`. -/
theorem MergeHiSemanticCursorInvariant.copyBBlock
    {lt : BoolComparator alpha}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {cursor : MergeHiCursor (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call)
    (horder : BoolStrictWeakOrder lt)
    (hleftSorted : (mergeHiLeftEntries call).Pairwise
      (fun earlier later => lt later.key.value earlier.key.value = false))
    (h : MergeHiSemanticCursorInvariant lt call cursor)
    (hna : 0 < cursor.na)
    (count : Nat) (hcountPositive : 0 < count) (hcount : count < cursor.nb)
    (left : SortSliceEntry (Occurrence alpha) nu)
    (hleft : cursor.state.data.read? cursor.ssa = some left)
    (hboundary : ∀ suffixEntry ∈
      ((mergeHiRightEntries call).take cursor.nb).drop (cursor.nb - count),
      lt suffixEntry.key.value left.key.value = false)
    (state : MergeState (Occurrence alpha) nu)
    (hmove : mergeHiMemcpyTempToData? .gallopTempToData rfl count
      cursor.state (cursor.dest - Int.ofNat count + 1)
      (cursor.ssb - Int.ofNat count + 1) = some state)
    (hsafety : MergeHiCursorInvariant (mergeHiAllocated call).state call.nb
      { cursor with
        state := state
        dest := cursor.dest - Int.ofNat count
        ssb := cursor.ssb - Int.ofNat count
        nb := cursor.nb - count }) :
    MergeHiSemanticCursorInvariant lt call
      { cursor with
        state := state
        dest := cursor.dest - Int.ofNat count
        ssb := cursor.ssb - Int.ofNat count
        nb := cursor.nb - count } := by
  let next : MergeHiCursor (Occurrence alpha) nu :=
    { cursor with
      state := state
      dest := cursor.dest - Int.ofNat count
      ssb := cursor.ssb - Int.ofNat count
      nb := cursor.nb - count }
  let block := ((mergeHiRightEntries call).take cursor.nb).drop
    (cursor.nb - count)
  have hcountLe : count ≤ cursor.nb := Nat.le_of_lt hcount
  have hblockLength : block.length = count := by
    dsimp only [block]
    rw [List.length_drop, List.length_take,
      mergeHiRightEntries_length_of_geometry hgeometry,
      Nat.min_eq_left h.rightCount]
    omega
  have hrightSplit : (mergeHiRightEntries call).take cursor.nb =
      (mergeHiRightEntries call).take (cursor.nb - count) ++ block := by
    dsimp only [block]
    calc
      _ = ((mergeHiRightEntries call).take cursor.nb).take
            (cursor.nb - count) ++
          ((mergeHiRightEntries call).take cursor.nb).drop
            (cursor.nb - count) :=
        (List.take_append_drop (cursor.nb - count) _).symm
      _ = _ := by
        rw [List.take_take,
          Nat.min_eq_left (Nat.sub_le cursor.nb count)]
  rcases h.activeLeft_snoc hgeometry hna with
    ⟨left', hleft', hleftSnoc⟩
  have hleftEq : left' = left := by
    rw [hleft] at hleft'
    exact Option.some.inj hleft'.symm
  subst left'
  have hleftTakeSorted :
      ((mergeHiLeftEntries call).take cursor.na).Pairwise
        (fun earlier later =>
          lt later.key.value earlier.key.value = false) :=
    hleftSorted.take
  have hleftNe : (mergeHiLeftEntries call).take cursor.na ≠ [] := by
    rw [hleftSnoc]
    simp
  have hleftLast :
      ((mergeHiLeftEntries call).take cursor.na).getLast hleftNe = left := by
    apply (List.getLast_eq_iff_getLast?_eq_some hleftNe).2
    rw [hleftSnoc]
    simp
  have hallLeft := all_suffix_not_lt_left_of_pairwise_of_not_lt_last horder
    ((mergeHiLeftEntries call).take cursor.na) block hleftNe
    hleftTakeSorted (by
      intro suffixEntry hsuffix
      simpa only [hleftLast] using hboundary suffixEntry hsuffix)
  have hpure :
      stableEntryMerge lt
          ((mergeHiLeftEntries call).take cursor.na)
          ((mergeHiRightEntries call).take cursor.nb) =
        stableEntryMerge lt
            ((mergeHiLeftEntries call).take cursor.na)
            ((mergeHiRightEntries call).take (cursor.nb - count)) ++ block := by
    calc
      _ = stableEntryMerge lt
          ((mergeHiLeftEntries call).take cursor.na)
          ((mergeHiRightEntries call).take (cursor.nb - count) ++ block) := by
            rw [← hrightSplit]
      _ = _ := stableEntryMerge_append_right_block lt block _ _ hallLeft
  have hbaseCast : Int.ofNat call.ssa.toNat = call.ssa :=
    Int.toNat_of_nonneg hgeometry.ssaNonnegative
  have hsrcStart : cursor.ssb - Int.ofNat count + 1 =
      Int.ofNat (cursor.nb - count) := by
    have heq := h.safety.ssbEquation
    simp only [Int.ofNat_eq_natCast, Nat.cast_sub hcountLe] at heq ⊢
    omega
  have hdstStart : cursor.dest - Int.ofNat count + 1 =
      Int.ofNat (call.ssa.toNat + (cursor.na + (cursor.nb - count))) := by
    have heq := h.safety.destEquation
    rw [h.basea_eq, ← hbaseCast] at heq
    rw [← hbaseCast]
    simp only [Int.ofNat_eq_natCast, Nat.cast_add,
      Nat.cast_sub hcountLe] at heq ⊢
    omega
  have htempEq := mergeHiMemcpyTempToData_temp_eq_of_eq_some
    .gallopTempToData rfl count cursor.state state _ _ hmove
  have hframeSigned := mergeHiMemcpyTempToData_readFrame_of_eq_some
    .gallopTempToData rfl count cursor.state state _ _ hmove
  rw [hdstStart] at hframeSigned
  have hstepFrame := hframeSigned.equalOutsideRange_ofNat
  have hdestRead := mergeHiMemcpyTempToData_read_range_of_eq_some
    .gallopTempToData rfl count cursor.state state
    (cursor.dest - Int.ofNat count + 1)
    (cursor.ssb - Int.ofNat count + 1) hmove
  have hstop : call.ssa.toNat + (cursor.na + cursor.nb) ≤
      state.data.entries.size := by
    have hrange := h.naturalMainRange hgeometry
    rw [← hframeSigned.1]
    exact hrange
  have hblock :
      (sortSliceRangeEntries state.data
        (call.ssa.toNat + (cursor.na + (cursor.nb - count))) count).toList =
        block := by
    apply sortSliceRangeEntries_toList_eq_of_reads
    · omega
    · exact hblockLength
    · intro offset hoffset
      have hread := hdestRead offset hoffset
      rw [hdstStart, hsrcStart] at hread
      have htempRead := h.activeRight.2 (cursor.nb - count + offset) (by
        omega)
      have hblockGet : block[offset]? =
          (mergeHiRightEntries call)[cursor.nb - count + offset]? := by
        dsimp only [block]
        rw [List.getElem?_drop, List.getElem?_take]
        rw [if_pos (by omega)]
      simpa only [Int.ofNat_eq_natCast, Nat.cast_add] using
        hread.trans (htempRead.trans hblockGet.symm)
  have hactiveLeft :
      (sortSliceRangeEntries state.data call.ssa.toNat cursor.na).toList =
      (mergeHiLeftEntries call).take cursor.na := by
    calc
      _ = (sortSliceRangeEntries cursor.state.data call.ssa.toNat
          cursor.na).toList := by
            exact congrArg Array.toList
              (hstepFrame.entries_eq_of_disjoint call.ssa.toNat cursor.na
                (Or.inl (by omega))).symm
      _ = _ := h.activeLeft
  have hactiveRight : MergeHiTempPrefixMatches state.a
      (mergeHiRightEntries call) (cursor.nb - count) := by
    refine ⟨?_, ?_⟩
    · exact (Nat.sub_le _ _).trans h.activeRight.1
    · intro offset hoffset
      rw [htempEq]
      exact h.activeRight.2 offset (by omega)
  have hlow :
      ∃ leftFirst rightFirst,
        state.data.read? call.ssa = some leftFirst ∧
        mergeHiTempRead? state.a 0 = some rightFirst ∧
        lt rightFirst.key.value leftFirst.key.value = true := by
    rcases h.lowSentinel with
      ⟨leftFirst, rightFirst, hleftFirst, hrightFirst, hstrict⟩
    refine ⟨leftFirst, rightFirst, ?_, ?_, hstrict⟩
    · have hnewNb : 0 < cursor.nb - count := Nat.sub_pos_of_lt hcount
      have hbaseBefore : call.ssa <
          Int.ofNat (call.ssa.toNat + (cursor.na + (cursor.nb - count))) := by
        rw [← hbaseCast]
        exact Int.ofNat_lt.mpr (by omega)
      exact (hframeSigned.2 call.ssa (Or.inl hbaseBefore)).trans hleftFirst
    · simpa [htempEq] using hrightFirst
  apply h.peelBlock hgeometry hsafety
  · exact h.basea_eq
  · exact hsafety.stableFrame.comparator.trans
      (h.safety.stableFrame.comparator.symm.trans h.comparator)
  · exact h.leftCount
  · exact (Nat.sub_le _ _).trans h.rightCount
  · exact Nat.sub_pos_of_lt hcount
  · exact hactiveLeft
  · exact hactiveRight
  · dsimp only [next]
    rw [hblockLength]
    omega
  · exact hpure
  · simpa [next, Nat.add_assoc, hblockLength] using hstepFrame
  · simpa [next, Nat.add_assoc, hblockLength] using hblock
  · exact hlow

/-! ## Terminal semantic effects -/

/-- If the sole right entry is strictly below every remaining left entry,
left-biased stable merge emits it first and then the untouched left list. -/
theorem stableEntryMerge_singleton_right_of_all_lt
    (lt : BoolComparator alpha)
    (right : SortSliceEntry (Occurrence alpha) nu) :
    ∀ left : List (SortSliceEntry (Occurrence alpha) nu),
      (∀ leftEntry ∈ left,
        lt right.key.value leftEntry.key.value = true) →
      stableEntryMerge lt left [right] = right :: left
  | [], _ => by simp [stableEntryMerge]
  | leftHead :: leftTail, hstrict => by
      unfold stableEntryMerge
      rw [List.cons_merge_cons]
      have hnot : ¬stableEntryLE lt leftHead right = true := by
        simp [stableEntryLE, stableOccurrenceLE,
          hstrict leftHead (by simp)]
      rw [if_neg hnot]
      simp

/-- The Succeed tail reached with no A entries copies the entire remaining
temporary prefix into the output prefix and completes the exact target. -/
theorem MergeHiSemanticCursorInvariant.succeed_of_na_zero
    {lt : BoolComparator alpha}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {cursor : MergeHiCursor (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call)
    (h : MergeHiSemanticCursorInvariant lt call cursor)
    (hna : cursor.na = 0)
    (state : MergeState (Occurrence alpha) nu)
    (hcopy : mergeHiMemcpyTempToData? .finalTempToData rfl cursor.nb
      cursor.state (cursor.dest - Int.ofNat (cursor.nb - 1)) 0 = some state) :
    (sortSliceRangeEntries state.data call.ssa.toNat
        (call.na + call.nb)).toList = mergeHiTargetEntries lt call ∧
      SortSlice.EqualOutsideRange call.state.data state.data
        call.ssa.toNat (call.na + call.nb) := by
  have hbaseCast : Int.ofNat call.ssa.toNat = call.ssa :=
    Int.toNat_of_nonneg hgeometry.ssaNonnegative
  have hdstStart : cursor.dest - Int.ofNat (cursor.nb - 1) = call.ssa := by
    have heq := h.safety.destEquation
    rw [h.basea_eq, hna] at heq
    simp only [zero_add, Int.ofNat_eq_natCast,
      Nat.cast_sub h.rightPositive] at heq ⊢
    omega
  have hframeSigned := mergeHiMemcpyTempToData_readFrame_of_eq_some
    .finalTempToData rfl cursor.nb cursor.state state
    (cursor.dest - Int.ofNat (cursor.nb - 1)) 0 hcopy
  rw [hdstStart, ← hbaseCast] at hframeSigned
  have hstepFrame := hframeSigned.equalOutsideRange_ofNat
  have hdestRead := mergeHiMemcpyTempToData_read_range_of_eq_some
    .finalTempToData rfl cursor.nb cursor.state state
    (cursor.dest - Int.ofNat (cursor.nb - 1)) 0 hcopy
  have hrightLength :
      ((mergeHiRightEntries call).take cursor.nb).length = cursor.nb := by
    rw [List.length_take,
      mergeHiRightEntries_length_of_geometry hgeometry,
      Nat.min_eq_left h.rightCount]
  have hstop : call.ssa.toNat + cursor.nb ≤ state.data.entries.size := by
    have hrange := h.naturalMainRange hgeometry
    rw [hna, zero_add] at hrange
    rw [← hframeSigned.1]
    exact hrange
  have hblock :
      (sortSliceRangeEntries state.data call.ssa.toNat cursor.nb).toList =
        (mergeHiRightEntries call).take cursor.nb := by
    apply sortSliceRangeEntries_toList_eq_of_reads
    · exact hstop
    · exact hrightLength
    · intro offset hoffset
      have hread := hdestRead offset hoffset
      rw [hdstStart] at hread
      have htempRead := h.activeRight.2 offset hoffset
      have haddr : call.ssa + Int.ofNat offset =
          Int.ofNat (call.ssa.toNat + offset) := by
        rw [← hbaseCast]
        simp
      have hread' : state.data.read?
          (Int.ofNat (call.ssa.toNat + offset)) =
          mergeHiTempRead? cursor.state.a (Int.ofNat offset) := by
        rw [← haddr]
        simpa using hread
      have htakeGet :
          ((mergeHiRightEntries call).take cursor.nb)[offset]? =
            (mergeHiRightEntries call)[offset]? := by
        rw [List.getElem?_take, if_pos hoffset]
      exact hread'.trans (htempRead.trans htakeGet.symm)
  have hremaining : (mergeHiRightEntries call).take cursor.nb =
      (mergeHiTargetEntries lt call).take cursor.nb := by
    simpa [hna, stableEntryMerge] using h.remainingTarget
  have hfilledBefore :
      (sortSliceRangeEntries cursor.state.data
        (call.ssa.toNat + cursor.nb)
        (call.na + call.nb - cursor.nb)).toList =
      (mergeHiTargetEntries lt call).drop cursor.nb := by
    simpa [mergeHiFilledEntries, hna, Nat.add_assoc] using h.filledTarget
  have hassemble : (mergeHiRightEntries call).take cursor.nb ++
      (mergeHiTargetEntries lt call).drop cursor.nb =
      (mergeHiTargetEntries lt call).drop 0 := by
    rw [hremaining, List.take_append_drop]
    simp
  rcases mergeHi_backwardFillBlock (target := mergeHiTargetEntries lt call)
      (block := (mergeHiRightEntries call).take cursor.nb)
      (oldRemaining := cursor.nb) (newRemaining := 0)
      (count := cursor.nb) (by simp)
      (h.rightCount.trans (Nat.le_add_left call.nb call.na)) h.frame
      (by simpa using hstepFrame) (by simpa using hblock)
      hfilledBefore hassemble with ⟨hexact, _hprefix, hframe⟩
  simpa using And.intro hexact hframe

/-- The CopyA tail (`nb = 1`) shifts the remaining A prefix one cell right
and installs the immutable smallest B entry at the low endpoint, completing
the same forward stable target. -/
theorem MergeHiSemanticCursorInvariant.copyATail_of_nb_one
    {lt : BoolComparator alpha}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {cursor : MergeHiCursor (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call)
    (horder : BoolStrictWeakOrder lt)
    (hleftSorted : (mergeHiLeftEntries call).Pairwise
      (fun earlier later => lt later.key.value earlier.key.value = false))
    (h : MergeHiSemanticCursorInvariant lt call cursor)
    (hna : 0 < cursor.na) (hnb : cursor.nb = 1)
    (data : SortSlice (Occurrence alpha) nu)
    (hmove : mergeDataMemmove? .hiCopyATail cursor.state.data
      (cursor.dest + (1 - Int.ofNat cursor.na))
      (cursor.ssa + (1 - Int.ofNat cursor.na)) cursor.na = some data)
    (state : MergeState (Occurrence alpha) nu)
    (hcell : mergeHiCopyTempToData? { cursor.state with data := data }
      (cursor.dest - Int.ofNat cursor.na) cursor.ssb = some state) :
    (sortSliceRangeEntries state.data call.ssa.toNat
        (call.na + call.nb)).toList = mergeHiTargetEntries lt call ∧
      SortSlice.EqualOutsideRange call.state.data state.data
        call.ssa.toNat (call.na + call.nb) := by
  have hbaseCast : Int.ofNat call.ssa.toNat = call.ssa :=
    Int.toNat_of_nonneg hgeometry.ssaNonnegative
  have hsrcStart : cursor.ssa + (1 - Int.ofNat cursor.na) = call.ssa := by
    have heq := h.safety.ssaEquation
    rw [h.basea_eq] at heq
    simp only [Int.ofNat_eq_natCast] at heq ⊢
    omega
  have hdstStart : cursor.dest + (1 - Int.ofNat cursor.na) =
      call.ssa + 1 := by
    have heq := h.safety.destEquation
    rw [h.basea_eq, hnb] at heq
    simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] at heq ⊢
    omega
  have hcellDst : cursor.dest - Int.ofNat cursor.na = call.ssa := by
    have heq := h.safety.destEquation
    rw [h.basea_eq, hnb] at heq
    simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] at heq ⊢
    omega
  have hssb : cursor.ssb = 0 := by
    have heq := h.safety.ssbEquation
    rw [hnb] at heq
    simpa using heq
  have hmoveCopies := mergeDataMemmove_copiesRange_of_eq_some .hiCopyATail
    cursor.state.data data _ _ cursor.na hmove
  rw [hsrcStart, hdstStart, ← hbaseCast] at hmoveCopies
  have hmoveFrame := mergeDataMemmove_readFrame_of_eq_some .hiCopyATail
    cursor.state.data data _ _ cursor.na hmove
  rw [hdstStart, ← hbaseCast] at hmoveFrame
  have hmoveEor := hmoveFrame.equalOutsideRange_ofNat
  rcases mergeHiCopyTempToData_frame_of_eq_some
    { cursor.state with data := data } state
      (cursor.dest - Int.ofNat cursor.na) cursor.ssb hcell with
    ⟨htempEq, hcellFrame⟩
  rw [hcellDst, ← hbaseCast] at hcellFrame
  have hcellEor := hcellFrame.equalOutsideRange_ofNat
  have hcellRead := mergeHiCopyTempToData_read_destination_of_eq_some
    { cursor.state with data := data } state
      (cursor.dest - Int.ofNat cursor.na) cursor.ssb hcell
  rcases h.activeRight_snoc hgeometry with
    ⟨right, hright, hrightSnoc⟩
  have hrightPrefix : (mergeHiRightEntries call).take cursor.nb = [right] := by
    rw [hrightSnoc, hnb]
    simp
  have hrightZero : mergeHiTempRead? cursor.state.a 0 = some right := by
    simpa [hssb] using hright
  have hcellExact : state.data.read? call.ssa = some right := by
    rw [← hcellDst]
    exact hcellRead.trans (by simpa [hssb] using hright)
  have hsourceStop : call.ssa.toNat + cursor.na ≤
      cursor.state.data.entries.size := by
    have hrange := h.naturalMainRange hgeometry
    rw [hnb] at hrange
    omega
  have hdestStop : call.ssa.toNat + 1 + cursor.na ≤ data.entries.size := by
    have hrange := h.naturalMainRange hgeometry
    rw [hnb, hmoveFrame.1] at hrange
    omega
  have hshifted :
      (sortSliceRangeEntries data (call.ssa.toNat + 1) cursor.na).toList =
        (mergeHiLeftEntries call).take cursor.na := by
    calc
      _ = (sortSliceRangeEntries cursor.state.data call.ssa.toNat
          cursor.na).toList :=
            sortSliceRangeEntries_toList_eq_of_copiesRange hmoveCopies
              hsourceStop hdestStop
      _ = _ := h.activeLeft
  have htailPreserved :
      (sortSliceRangeEntries state.data (call.ssa.toNat + 1)
        cursor.na).toList =
      (sortSliceRangeEntries data (call.ssa.toNat + 1) cursor.na).toList := by
    exact congrArg Array.toList
      (hcellEor.entries_eq_of_disjoint (call.ssa.toNat + 1) cursor.na
        (Or.inr (by omega))).symm
  have hfirstRange :
      (sortSliceRangeEntries state.data call.ssa.toNat 1).toList = [right] := by
    apply sortSliceRangeEntries_toList_eq_of_reads
    · have hrange := h.naturalMainRange hgeometry
      rw [hnb] at hrange
      rw [← hcellFrame.1, ← hmoveFrame.1]
      omega
    · simp
    · intro offset hoffset
      have hoffsetZero : offset = 0 := by omega
      subst offset
      have hcellExact' : state.data.read? (Int.ofNat call.ssa.toNat) =
          some right := by
        rw [hbaseCast]
        exact hcellExact
      simpa using hcellExact'
  have hremainingBlock :
      (sortSliceRangeEntries state.data call.ssa.toNat
      (cursor.na + cursor.nb)).toList =
        right :: (mergeHiLeftEntries call).take cursor.na := by
    rw [show cursor.na + cursor.nb = 1 + cursor.na by omega,
      sortSliceRangeEntries_toList_add]
    rw [hfirstRange, htailPreserved, hshifted]
    rfl
  rcases h.lowSentinel_lt_activeLeft hgeometry horder hleftSorted hna with
    ⟨rightFirst, hrightFirst, hallLeftFirst⟩
  have hrightEq : rightFirst = right := by
    rw [hrightZero] at hrightFirst
    exact Option.some.inj hrightFirst.symm
  subst rightFirst
  have hpure : stableEntryMerge lt
      ((mergeHiLeftEntries call).take cursor.na)
      ((mergeHiRightEntries call).take cursor.nb) =
      right :: (mergeHiLeftEntries call).take cursor.na := by
    rw [hrightPrefix]
    exact stableEntryMerge_singleton_right_of_all_lt lt right _ hallLeftFirst
  have hblockTarget : right :: (mergeHiLeftEntries call).take cursor.na =
      (mergeHiTargetEntries lt call).take (cursor.na + cursor.nb) := by
    rw [← hpure]
    exact h.remainingTarget
  have hstepFrame : SortSlice.EqualOutsideRange cursor.state.data state.data
      call.ssa.toNat (cursor.na + cursor.nb) := by
    have htotal : cursor.na + cursor.nb = cursor.na + 1 := by omega
    rw [htotal]
    have hmoveStart : call.ssa.toNat ≤ call.ssa.toNat + 1 := by omega
    have hmoveStop : (call.ssa.toNat + 1) + cursor.na ≤
        call.ssa.toNat + (cursor.na + 1) := by
      apply Nat.le_of_eq
      ac_rfl
    have hcellStop : call.ssa.toNat + 1 ≤
        call.ssa.toNat + (cursor.na + 1) := by omega
    exact (hmoveEor.widen hmoveStart hmoveStop).trans
      (hcellEor.widen (le_refl _) hcellStop)
  have hfilledBefore :
      (sortSliceRangeEntries cursor.state.data
        (call.ssa.toNat + (cursor.na + cursor.nb))
        (call.na + call.nb - (cursor.na + cursor.nb))).toList =
      (mergeHiTargetEntries lt call).drop (cursor.na + cursor.nb) := by
    simpa [mergeHiFilledEntries, Nat.add_assoc] using h.filledTarget
  have hassemble : (right :: (mergeHiLeftEntries call).take cursor.na) ++
      (mergeHiTargetEntries lt call).drop (cursor.na + cursor.nb) =
      (mergeHiTargetEntries lt call).drop 0 := by
    rw [hblockTarget, List.take_append_drop]
    simp
  rcases mergeHi_backwardFillBlock (target := mergeHiTargetEntries lt call)
      (block := right :: (mergeHiLeftEntries call).take cursor.na)
      (oldRemaining := cursor.na + cursor.nb) (newRemaining := 0)
      (count := cursor.na + cursor.nb) (by simp)
      (Nat.add_le_add h.leftCount h.rightCount) h.frame hstepFrame
      hremainingBlock hfilledBefore hassemble with
    ⟨hexact, _hprefix, hframe⟩
  simpa using And.intro hexact hframe

/-- In the B-gallop conversion `bCount = nb - index`, a positive insertion
index leaves exactly that index as the new B count. -/
theorem mergeHi_sub_sub_to_index {n index : Nat} (hindex : index <= n) :
    n - (n - index) = index := by
  omega

/-! ## Reverse-head order propagation -/

/-- In a sorted entry list, strict comparison of its last entry with a higher
entry propagates to every earlier entry. -/
theorem all_entries_lt_of_last_lt
    {lt : BoolComparator alpha} (horder : BoolStrictWeakOrder lt)
    {entries : List (SortSliceEntry (Occurrence alpha) nu)}
    (hsorted : entries.Pairwise (fun earlier later =>
      lt later.key.value earlier.key.value = false))
    {last high : SortSliceEntry (Occurrence alpha) nu}
    (hlast : entries.getLast? = some last)
    (hcompare : lt last.key.value high.key.value = true) :
    ∀ entry ∈ entries, lt entry.key.value high.key.value = true := by
  have hne : entries ≠ [] := by
    intro hempty
    subst entries
    simp at hlast
  have hlastEq : entries.getLast hne = last :=
    (List.getLast_eq_iff_getLast?_eq_some hne).2 hlast
  intro entry hentry
  have hnotReverse :
      lt (entries.getLast hne).key.value entry.key.value = false :=
    hsorted.rel_getLast_of_rel_getLast_getLast hentry (by
      exact Bool.eq_false_iff.mpr
        (horder.irrefl (entries.getLast hne).key.value))
  rw [hlastEq] at hnotReverse
  exact horder.strict_of_not_reverse_of_strict hnotReverse hcompare

/-- In a sorted entry list, if a candidate is not below its last entry, it is
not below any earlier entry either.  This includes the comparator-equivalent
tie case and is exactly the backward B-selection rule. -/
theorem all_entries_not_lt_of_not_lt_last
    {lt : BoolComparator alpha} (horder : BoolStrictWeakOrder lt)
    {entries : List (SortSliceEntry (Occurrence alpha) nu)}
    (hsorted : entries.Pairwise (fun earlier later =>
      lt later.key.value earlier.key.value = false))
    {last candidate : SortSliceEntry (Occurrence alpha) nu}
    (hlast : entries.getLast? = some last)
    (hcompare : lt candidate.key.value last.key.value = false) :
    ∀ entry ∈ entries, lt candidate.key.value entry.key.value = false := by
  have hne : entries ≠ [] := by
    intro hempty
    subst entries
    simp at hlast
  have hlastEq : entries.getLast hne = last :=
    (List.getLast_eq_iff_getLast?_eq_some hne).2 hlast
  intro entry hentry
  have hnotReverse :
      lt (entries.getLast hne).key.value entry.key.value = false :=
    hsorted.rel_getLast_of_rel_getLast_getLast hentry (by
      exact Bool.eq_false_iff.mpr
        (horder.irrefl (entries.getLast hne).key.value))
  rw [hlastEq] at hnotReverse
  exact horder.false_trans hnotReverse hcompare

end CPythonListsort
