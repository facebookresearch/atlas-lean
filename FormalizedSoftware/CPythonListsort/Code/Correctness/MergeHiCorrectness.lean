/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Correctness.EntrySnapshotPermutation
import Code.Correctness.MergeHiInvariant

/-!
# Public functional postcondition for `merge_hi`

The physical algorithm fills its output from right to left, but its observable
specification is the ordinary forward, left-biased `stableEntryMerge` of the
two post-trimming input runs.  Keeping the exact whole-entry equality in the
public postcondition makes sortedness, occurrence stability, payload
permutation, framing, and persistent input snapshots consequences of one
semantic result rather than independent key-only claims.
-/

namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-- Functional correctness certificate for the exact traced `merge_hi`
execution selected by `prepareMergeAt?`.

`exactRange` is the central result: the affected whole-entry range is exactly
the shared left-biased mathematical merge.  The remaining fields expose the
standard public sortedness, stability, whole-entry permutation, and frame
interfaces without asking downstream clients to unfold that target. -/
structure MergeHiCorrectnessPost
    (lt : BoolComparator alpha) (canonical : List (Occurrence alpha))
    (pre : MergeState (Occurrence alpha) nu) (scanned i : Nat)
    (call : MergeAtCall (Occurrence alpha) nu)
    (result : MergeHiResult (Occurrence alpha) nu) : Prop where
  safety : MergeHiSafetyPost pre scanned i call
    (mergeHiTraced? call.state call.ssa call.ssb call.na call.nb) result
  exactRange :
    (sortSliceRangeEntries result.state.data call.ssa.toNat
      (call.na + call.nb)).toList = mergeHiTargetEntries lt call
  sorted : Sorted (occurrenceComparator lt)
    (sortSliceRangeKeys result.state.data call.ssa.toNat
      (call.na + call.nb))
  stable : StableOccurrencePermutation lt canonical
    (sortSliceRangeKeys result.state.data call.ssa.toNat
      (call.na + call.nb)).toList
  rangeEntriesPerm :
    (sortSliceRangeEntries result.state.data call.ssa.toNat
      (call.na + call.nb)).toList.Perm
      (sortSliceRangeEntries call.state.data call.ssa.toNat
        (call.na + call.nb)).toList
  frame : SortSlice.EqualOutsideRange call.state.data result.state.data
    call.ssa.toNat (call.na + call.nb)

/-- Functional portion proved against the untraced transcription.  Separating
this certificate from `MergeHiSafetyPost` keeps the reverse-loop induction
focused on whole-entry movement while the public join below identifies its
result with the actual traced execution by exact erasure. -/
structure MergeHiRawCorrectnessPost
    (lt : BoolComparator alpha)
    (call : MergeAtCall (Occurrence alpha) nu)
    (result : MergeHiResult (Occurrence alpha) nu) : Prop where
  resultEq : mergeHi? call.state call.ssa call.ssb call.na call.nb = some result
  exactRange :
    (sortSliceRangeEntries result.state.data call.ssa.toNat
      (call.na + call.nb)).toList = mergeHiTargetEntries lt call
  frame : SortSlice.EqualOutsideRange call.state.data result.state.data
    call.ssa.toNat (call.na + call.nb)

/-- Projecting keys from the exact whole-entry result gives the exact key
sequence of the mathematical stable merge. -/
theorem mergeHiExactRange_keys
    {lt : BoolComparator alpha}
    {call : MergeAtCall (Occurrence alpha) nu}
    {result : MergeHiResult (Occurrence alpha) nu}
    (hexact :
      (sortSliceRangeEntries result.state.data call.ssa.toNat
        (call.na + call.nb)).toList = mergeHiTargetEntries lt call) :
    (sortSliceRangeKeys result.state.data call.ssa.toNat
      (call.na + call.nb)).toList =
      (mergeHiTargetEntries lt call).map SortSliceEntry.key := by
  simpa [sortSliceRangeKeys] using
    congrArg (List.map SortSliceEntry.key) hexact

/-- Algebraic closure of the central exact-range result.

This theorem contains no evaluator assumption hidden in a rewrite: safety is
passed explicitly for the actual traced execution, while exact whole-entry
output and the physical frame are the two semantic obligations discharged by
the reverse-loop proof.  Pure stable-merge correctness supplies all remaining
public claims. -/
theorem mergeHiCorrectnessPost_of_exactRange
    {lt : BoolComparator alpha} (horder : BoolStrictWeakOrder lt)
    (canonical : List (Occurrence alpha))
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {result : MergeHiResult (Occurrence alpha) nu}
    (hsafety : MergeHiSafetyPost pre scanned i call
      (mergeHiTraced? call.state call.ssa call.ssb call.na call.nb) result)
    (hsemantic : MergeHiSemanticPre lt call)
    (hstable : StableOccurrencePermutation lt canonical
      ((sortSliceRangeKeys call.state.data call.ssa.toNat call.na).toList ++
        (sortSliceRangeKeys call.state.data call.ssb.toNat call.nb).toList))
    (hexact :
      (sortSliceRangeEntries result.state.data call.ssa.toNat
        (call.na + call.nb)).toList = mergeHiTargetEntries lt call)
    (hframe : SortSlice.EqualOutsideRange call.state.data result.state.data
      call.ssa.toNat (call.na + call.nb)) :
    MergeHiCorrectnessPost lt canonical pre scanned i call result := by
  have hleftPairwise :
      ((mergeHiLeftEntries call).map SortSliceEntry.key).Pairwise
        (DescendingRunSpec.SortedRelation lt) :=
    hsemantic.leftKeysPairwise
  have hrightPairwise :
      ((mergeHiRightEntries call).map SortSliceEntry.key).Pairwise
        (DescendingRunSpec.SortedRelation lt) :=
    hsemantic.rightKeysPairwise
  have hstableEntries : StableOccurrencePermutation lt canonical
      ((mergeHiLeftEntries call).map SortSliceEntry.key ++
        (mergeHiRightEntries call).map SortSliceEntry.key) := by
    simpa using hstable
  have hpure := stableEntryMerge_correct horder canonical
    (mergeHiLeftEntries call) (mergeHiRightEntries call)
    hleftPairwise hrightPairwise hstableEntries
  have hkeys := mergeHiExactRange_keys hexact
  refine
    { safety := hsafety
      exactRange := hexact
      sorted := ?_
      stable := ?_
      rangeEntriesPerm := ?_
      frame := hframe }
  · unfold Sorted
    rw [hkeys]
    exact hpure.1
  · rw [hkeys]
    exact hpure.2.1
  · rw [hexact, mergeHiCombinedEntries_eq_append hsafety.geometry]
    exact hpure.2.2

/-- The safety certificate's signed main-range bound, expressed at the natural
index used by range and snapshot correctness. -/
theorem MergeHiSafetyPost.naturalMergedRange
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {result : MergeHiResult (Occurrence alpha) nu}
    (h : MergeHiSafetyPost pre scanned i call
      (mergeHiTraced? call.state call.ssa call.ssb call.na call.nb) result) :
    call.ssa.toNat + (call.na + call.nb) ≤ call.state.data.entries.size := by
  exact h.geometry.naturalMergedRange

/-- A correct `merge_hi` preserves the persistent whole-entry input snapshot.
This corollary uses the public local permutation and frame, so keyed payloads
remain paired with their original occurrence-tagged keys. -/
theorem MergeHiCorrectnessPost.preserve_entrySnapshot
    {lt : BoolComparator alpha} {canonical : List (Occurrence alpha)}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {result : MergeHiResult (Occurrence alpha) nu}
    (h : MergeHiCorrectnessPost lt canonical pre scanned i call result)
    {source : SortSlice alpha nu}
    (snapshot : EntrySnapshotPermutation source call.state.data) :
    EntrySnapshotPermutation source result.state.data := by
  exact snapshot.preserve_local h.frame h.safety.naturalMergedRange
    h.rangeEntriesPerm

/-- Exact raw-erasure bridge used by the eventual reverse-loop theorem.  It
pins that the successful result observed by the traced safety proof is the
same result returned by the untraced transcription; it does not assume any
functional property of that result. -/
theorem MergeHiSafetyPost.rawResultEq
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {result : MergeHiResult (Occurrence alpha) nu}
    (h : MergeHiSafetyPost pre scanned i call
      (mergeHiTraced? call.state call.ssa call.ssb call.na call.nb) result) :
    mergeHi? call.state call.ssa call.ssb call.na call.nb = some result := by
  have hresult := h.resultEq
  rw [← h.exactErasure]
  exact hresult

/-! ## Raw reverse-loop correctness -/

/-- The two semantic facts carried from a live reverse-fill cursor to a
successful raw result. -/
def MergeHiSemanticResult
    (lt : BoolComparator alpha)
    (call : MergeAtCall (Occurrence alpha) nu)
    (result : MergeHiResult (Occurrence alpha) nu) : Prop :=
  (sortSliceRangeEntries result.state.data call.ssa.toNat
      (call.na + call.nb)).toList = mergeHiTargetEntries lt call ∧
    SortSlice.EqualOutsideRange call.state.data result.state.data
      call.ssa.toNat (call.na + call.nb)

/-- The raw `Succeed` tail realizes the semantic cursor invariant when the A
side is empty.  The invariant's positive B count rules out the evaluator's
adversarial `nb = 0` arm. -/
theorem mergeHiSucceed_semantic
    {lt : BoolComparator alpha}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {cursor : MergeHiCursor (Occurrence alpha) nu}
    {result : MergeHiResult (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call)
    (h : MergeHiSemanticCursorInvariant lt call cursor)
    (hna : cursor.na = 0)
    (heval : mergeHiSucceed? cursor = some result) :
    MergeHiSemanticResult lt call result := by
  have hnb : cursor.nb ≠ 0 := Nat.ne_of_gt h.rightPositive
  unfold mergeHiSucceed? at heval
  simp only [hnb, ↓reduceIte] at heval
  rcases Option.bind_eq_some_iff.mp heval with ⟨state, hcopy, hresult⟩
  injection hresult with hresult
  subst result
  exact h.succeed_of_na_zero hgeometry hna state hcopy

/-- The raw `CopyA` tail realizes the semantic cursor invariant when one B
entry remains. -/
theorem mergeHiCopyATail_semantic
    {lt : BoolComparator alpha}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {cursor : MergeHiCursor (Occurrence alpha) nu}
    {result : MergeHiResult (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call)
    (horder : BoolStrictWeakOrder lt)
    (hleftSorted : (mergeHiLeftEntries call).Pairwise
      (fun earlier later => lt later.key.value earlier.key.value = false))
    (h : MergeHiSemanticCursorInvariant lt call cursor)
    (hna : 0 < cursor.na) (hnb : cursor.nb = 1)
    (heval : mergeHiCopyA? cursor = some result) :
    MergeHiSemanticResult lt call result := by
  unfold mergeHiCopyA? at heval
  simp only [hnb, hna, and_self, ↓reduceIte] at heval
  rcases Option.bind_eq_some_iff.mp heval with ⟨data, hmoveRaw, htail⟩
  have hmove : mergeDataMemmove? .hiCopyATail cursor.state.data
      (cursor.dest + (1 - Int.ofNat cursor.na))
      (cursor.ssa + (1 - Int.ofNat cursor.na)) cursor.na = some data := by
    simpa [mergeDataMemmove_eq] using hmoveRaw
  rcases Option.bind_eq_some_iff.mp htail with ⟨state, hcell, hresult⟩
  injection hresult with hresult
  subst result
  exact h.copyATail_of_nb_one hgeometry horder hleftSorted hna hnb
    data hmove state hcell

/-- Semantic preservation for the exact nonempty A-block state constructed by
the raw gallop evaluator. -/
theorem mergeHiMoveABlock_semantic_of_eq_some
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
      (cursor.ssa - Int.ofNat count + 1) count = some data) :
    MergeHiSemanticCursorInvariant lt call
      { cursor with
        state := { cursor.state with data := data }
        dest := cursor.dest - Int.ofNat count
        ssa := cursor.ssa - Int.ofNat count
        na := cursor.na - count } := by
  let moved : MergeHiCursor (Occurrence alpha) nu :=
    { cursor with
      state := { cursor.state with data := data }
      dest := cursor.dest - Int.ofNat count
      ssa := cursor.ssa - Int.ofNat count
      na := cursor.na - count }
  have hmain : mainDataMemmove? cursor.state
      (cursor.dest - Int.ofNat count + 1)
      (cursor.ssa - Int.ofNat count + 1) count =
      some { cursor.state with data := data } := by
    unfold mainDataMemmove?
    rw [show cursor.state.data.memmove?
      (cursor.dest - Int.ofNat count + 1)
      (cursor.ssa - Int.ofNat count + 1) count = some data by
        simpa using hmove]
    rfl
  have hraw : mergeHiMoveABlock? cursor count = some moved := by
    rw [mergeHiMoveABlock?]
    simp only [Nat.ne_of_gt hcountPositive, ↓reduceIte]
    rw [hmain]
    rfl
  rcases mergeHiMoveABlockTraced_safe (mergeHiAllocated call).state call.nb
      cursor h.safety
      count hcount with ⟨moved', htraced, _hsafe, hmovedSafety, _hna, _hnb⟩
  have hraw' : mergeHiMoveABlock? cursor count = some moved' := by
    rw [← erase_mergeHiMoveABlockTraced]
    exact htraced
  rw [hraw] at hraw'
  injection hraw' with hmoved
  subst moved'
  exact h.copyABlock hgeometry horder hrightSorted count hcountPositive
    hcount right hright hboundary data hmove hmovedSafety

/-- Semantic preservation for the exact nonempty B-block state constructed by
the raw gallop evaluator. -/
theorem mergeHiMoveBBlock_semantic_of_eq_some
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
      (cursor.ssb - Int.ofNat count + 1) = some state) :
    MergeHiSemanticCursorInvariant lt call
      { cursor with
        state := state
        dest := cursor.dest - Int.ofNat count
        ssb := cursor.ssb - Int.ofNat count
        nb := cursor.nb - count } := by
  let moved : MergeHiCursor (Occurrence alpha) nu :=
    { cursor with
      state := state
      dest := cursor.dest - Int.ofNat count
      ssb := cursor.ssb - Int.ofNat count
      nb := cursor.nb - count }
  have hraw : mergeHiMoveBBlock? cursor count = some moved := by
    rw [mergeHiMoveBBlock?]
    simp only [Nat.ne_of_gt hcountPositive, ↓reduceIte]
    rw [hmove]
    rfl
  have hcountLe : count ≤ cursor.nb := Nat.le_of_lt hcount
  rcases mergeHiMoveBBlockTraced_safe (mergeHiAllocated call).state call.nb
      cursor h.safety
      count hcountLe with ⟨moved', htraced, _hsafe, hmovedSafety, _hna, _hnb⟩
  have hraw' : mergeHiMoveBBlock? cursor count = some moved' := by
    rw [← erase_mergeHiMoveBBlockTraced]
    exact htraced
  rw [hraw] at hraw'
  injection hraw' with hmoved
  subst moved'
  exact h.copyBBlock hgeometry horder hleftSorted hna count hcountPositive
    hcount left hleft hboundary state hmove hmovedSafety

/-! ### Gallop partitions on immutable semantic prefixes -/

/-- A physical read in the active main gallop source is the corresponding
entry of the immutable active-left prefix. -/
theorem MergeHiSemanticCursorInvariant.mainSourceEntry
    {lt : BoolComparator alpha}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {cursor : MergeHiCursor (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call)
    (h : MergeHiSemanticCursorInvariant lt call cursor)
    (index : Nat) (hindex : index < cursor.na)
    (entry : SortSliceEntry (Occurrence alpha) nu)
    (hread : (GallopKeySource.main cursor.state.data cursor.basea).read?
      (Int.ofNat index) = some entry) :
    ((mergeHiLeftEntries call).take cursor.na)[index]? = some entry := by
  have hbaseCast : Int.ofNat call.ssa.toNat = call.ssa :=
    Int.toNat_of_nonneg hgeometry.ssaNonnegative
  have hstop : call.ssa.toNat + cursor.na ≤
      cursor.state.data.entries.size := by
    have := h.naturalMainRange hgeometry
    omega
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

/-- A read in a materialized active temporary gallop slice is the
corresponding entry of the immutable active-right prefix. -/
theorem MergeHiSemanticCursorInvariant.temporarySourceEntry
    {lt : BoolComparator alpha}
    {call : MergeAtCall (Occurrence alpha) nu}
    {cursor : MergeHiCursor (Occurrence alpha) nu}
    (h : MergeHiSemanticCursorInvariant lt call cursor)
    (temp : SortSlice (Occurrence alpha) nu)
    (htemp : initializedTempPrefix? cursor.state.a cursor.nb = some temp)
    (index : Nat) (hindex : index < cursor.nb)
    (entry : SortSliceEntry (Occurrence alpha) nu)
    (hread : temp.read? (Int.ofNat index) = some entry) :
    ((mergeHiRightEntries call).take cursor.nb)[index]? = some entry := by
  have hagrees := initializedTempPrefix_agreesWithSlice_of_eq_some
    cursor.state.a cursor.nb temp htemp
  have hsource :
      (GallopKeySource.temporary cursor.state.a 0).read?
        (Int.ofNat index) = some entry := by
    rw [hagrees (Int.ofNat index) (Int.natCast_nonneg index)
      (Int.ofNat_lt.mpr hindex)]
    simpa using hread
  have htempRead : mergeHiTempRead? cursor.state.a (Int.ofNat index) =
      some entry := by
    rw [mergeHiTempRead_ofNat]
    simpa [GallopKeySource.read?, GallopKeySource.base] using hsource
  have hsnapshot := h.activeRight.2 index hindex
  rw [htempRead] at hsnapshot
  rw [List.getElem?_take, if_pos hindex]
  exact hsnapshot.symm

/-- The right-biased A gallop's prefix consists exactly of entries not
strictly after the current right entry. -/
theorem MergeHiSemanticCursorInvariant.gallopRightPrefixBoundary
    {lt : BoolComparator alpha}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {cursor : MergeHiCursor (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call)
    (h : MergeHiSemanticCursorInvariant lt call cursor)
    (right : SortSliceEntry (Occurrence alpha) nu) (index : Nat)
    (hpartition : GallopRightPartition cursor.state.key_compare
      cursor.state.data cursor.basea right.key cursor.na index) :
    ∀ entry ∈ ((mergeHiLeftEntries call).take cursor.na).take index,
      lt right.key.value entry.key.value = false := by
  intro entry hentry
  rcases List.mem_iff_getElem?.mp hentry with ⟨j, hj⟩
  have hjBound : j <
      (((mergeHiLeftEntries call).take cursor.na).take index).length :=
    (List.getElem?_eq_some_iff.mp hj).choose
  have hjIndex : j < index := by
    have hlen := List.length_take_le index
      ((mergeHiLeftEntries call).take cursor.na)
    omega
  have hjActive :
      ((mergeHiLeftEntries call).take cursor.na)[j]? = some entry := by
    rw [List.getElem?_take, if_pos hjIndex] at hj
    exact hj
  have hjNa : j < cursor.na := by
    have := (List.getElem?_eq_some_iff.mp hjActive).choose
    rw [List.length_take,
      mergeHiLeftEntries_length_of_geometry hgeometry,
      Nat.min_eq_left h.leftCount] at this
    exact this
  rcases hpartition.2.1 j hjIndex with ⟨found, hread, hcompare⟩
  have hfound := h.mainSourceEntry hgeometry j hjNa found (by
    simpa [GallopKeySource.read?, GallopKeySource.base] using hread)
  rw [hjActive] at hfound
  injection hfound with hfound
  subst found
  simpa [h.comparator, occurrenceComparator] using hcompare

/-- The right-biased A gallop's suffix consists exactly of entries strictly
after the current right entry. -/
theorem MergeHiSemanticCursorInvariant.gallopRightSuffixBoundary
    {lt : BoolComparator alpha}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {cursor : MergeHiCursor (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call)
    (h : MergeHiSemanticCursorInvariant lt call cursor)
    (right : SortSliceEntry (Occurrence alpha) nu) (index : Nat)
    (hpartition : GallopRightPartition cursor.state.key_compare
      cursor.state.data cursor.basea right.key cursor.na index) :
    ∀ entry ∈ ((mergeHiLeftEntries call).take cursor.na).drop index,
      lt right.key.value entry.key.value = true := by
  intro entry hentry
  rcases List.mem_iff_getElem?.mp hentry with ⟨offset, hoffset⟩
  rw [List.getElem?_drop] at hoffset
  have hjBound : index + offset <
      ((mergeHiLeftEntries call).take cursor.na).length :=
    (List.getElem?_eq_some_iff.mp hoffset).choose
  have hjNa : index + offset < cursor.na := by
    rw [List.length_take,
      mergeHiLeftEntries_length_of_geometry hgeometry,
      Nat.min_eq_left h.leftCount] at hjBound
    exact hjBound
  rcases hpartition.2.2 (index + offset) (by omega) hjNa with
    ⟨found, hread, hcompare⟩
  have hfound := h.mainSourceEntry hgeometry (index + offset) hjNa found (by
    simpa [GallopKeySource.read?, GallopKeySource.base] using hread)
  rw [hoffset] at hfound
  injection hfound with hfound
  subst found
  simpa [h.comparator, occurrenceComparator] using hcompare

/-- The left-biased B gallop's prefix consists exactly of strict predecessors
of the current left entry. -/
theorem MergeHiSemanticCursorInvariant.gallopLeftPrefixBoundary
    {lt : BoolComparator alpha}
    {call : MergeAtCall (Occurrence alpha) nu}
    {cursor : MergeHiCursor (Occurrence alpha) nu}
    (h : MergeHiSemanticCursorInvariant lt call cursor)
    (temp : SortSlice (Occurrence alpha) nu)
    (htemp : initializedTempPrefix? cursor.state.a cursor.nb = some temp)
    (left : SortSliceEntry (Occurrence alpha) nu) (index : Nat)
    (hpartition : GallopLeftPartition cursor.state.key_compare temp 0
      left.key cursor.nb index) :
    ∀ entry ∈ ((mergeHiRightEntries call).take cursor.nb).take index,
      lt entry.key.value left.key.value = true := by
  intro entry hentry
  rcases List.mem_iff_getElem?.mp hentry with ⟨j, hj⟩
  have hjBound : j <
      (((mergeHiRightEntries call).take cursor.nb).take index).length :=
    (List.getElem?_eq_some_iff.mp hj).choose
  have hjIndex : j < index := by
    have hlen := List.length_take_le index
      ((mergeHiRightEntries call).take cursor.nb)
    omega
  have hjActive :
      ((mergeHiRightEntries call).take cursor.nb)[j]? = some entry := by
    rw [List.getElem?_take, if_pos hjIndex] at hj
    exact hj
  have hjNb : j < cursor.nb := by
    have := (List.getElem?_eq_some_iff.mp hjActive).choose
    exact lt_of_lt_of_le this (List.length_take_le _ _)
  rcases hpartition.2.1 j hjIndex with ⟨found, hread, hcompare⟩
  have hfound := h.temporarySourceEntry temp htemp j hjNb found (by
    simpa using hread)
  rw [hjActive] at hfound
  injection hfound with hfound
  subst found
  simpa [h.comparator, occurrenceComparator] using hcompare

/-- The left-biased B gallop's suffix consists exactly of entries which are
not strict predecessors of the current left entry, including stable ties. -/
theorem MergeHiSemanticCursorInvariant.gallopLeftSuffixBoundary
    {lt : BoolComparator alpha}
    {call : MergeAtCall (Occurrence alpha) nu}
    {cursor : MergeHiCursor (Occurrence alpha) nu}
    (h : MergeHiSemanticCursorInvariant lt call cursor)
    (temp : SortSlice (Occurrence alpha) nu)
    (htemp : initializedTempPrefix? cursor.state.a cursor.nb = some temp)
    (left : SortSliceEntry (Occurrence alpha) nu) (index : Nat)
    (hpartition : GallopLeftPartition cursor.state.key_compare temp 0
      left.key cursor.nb index) :
    ∀ entry ∈ ((mergeHiRightEntries call).take cursor.nb).drop index,
      lt entry.key.value left.key.value = false := by
  intro entry hentry
  rcases List.mem_iff_getElem?.mp hentry with ⟨offset, hoffset⟩
  rw [List.getElem?_drop] at hoffset
  have hjBound : index + offset <
      ((mergeHiRightEntries call).take cursor.nb).length :=
    (List.getElem?_eq_some_iff.mp hoffset).choose
  have hjNb : index + offset < cursor.nb :=
    lt_of_lt_of_le hjBound (List.length_take_le _ _)
  rcases hpartition.2.2 (index + offset) (by omega) hjNb with
    ⟨found, hread, hcompare⟩
  have hfound := h.temporarySourceEntry temp htemp (index + offset) hjNb
    found (by simpa using hread)
  rw [hoffset] at hfound
  injection hfound with hfound
  subst found
  simpa [h.comparator, occurrenceComparator] using hcompare

/-! ### Total semantic block movers -/

/-- The raw A-block helper is total on a live cursor and returns a cursor
satisfying the semantic invariant. -/
theorem mergeHiMoveABlock_semantic
    {lt : BoolComparator alpha}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {cursor : MergeHiCursor (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call)
    (horder : BoolStrictWeakOrder lt)
    (hrightSorted : (mergeHiRightEntries call).Pairwise
      (fun earlier later => lt later.key.value earlier.key.value = false))
    (h : MergeHiSemanticCursorInvariant lt call cursor)
    (count : Nat) (hcount : count ≤ cursor.na)
    (right : SortSliceEntry (Occurrence alpha) nu)
    (hright : mergeHiTempRead? cursor.state.a cursor.ssb = some right)
    (hboundary : ∀ suffixEntry ∈
      ((mergeHiLeftEntries call).take cursor.na).drop (cursor.na - count),
      lt right.key.value suffixEntry.key.value = true) :
    ∃ moved, mergeHiMoveABlock? cursor count = some moved ∧
      MergeHiSemanticCursorInvariant lt call moved := by
  by_cases hzero : count = 0
  · subst count
    exact ⟨cursor, by simp [mergeHiMoveABlock?], h⟩
  · rcases mergeHiMoveABlockTraced_safe (mergeHiAllocated call).state call.nb cursor
        h.safety count hcount with
      ⟨moved, htraced, _hsafe, _hmovedSafety, _hna, _hnb⟩
    have hraw : mergeHiMoveABlock? cursor count = some moved := by
      rw [← erase_mergeHiMoveABlockTraced]
      exact htraced
    have hrawCopy := hraw
    rw [mergeHiMoveABlock?, if_neg hzero] at hrawCopy
    rcases Option.bind_eq_some_iff.mp hrawCopy with
      ⟨state, hmain, hmoved⟩
    unfold mainDataMemmove? at hmain
    rcases Option.bind_eq_some_iff.mp hmain with ⟨data, hdata, hstate⟩
    injection hstate with hstate
    subst state
    injection hmoved with hmoved
    subst moved
    have hmove : mergeDataMemmove? .hiGallopA cursor.state.data
        (cursor.dest - Int.ofNat count + 1)
        (cursor.ssa - Int.ofNat count + 1) count = some data := by
      simpa using hdata
    exact ⟨_, hraw,
      mergeHiMoveABlock_semantic_of_eq_some hgeometry horder hrightSorted h
        count (Nat.pos_of_ne_zero hzero) hcount right hright hboundary data
        hmove⟩

/-- The raw B-block helper is total on a live cursor; a count strictly below
`nb` preserves the positive-right semantic invariant. -/
theorem mergeHiMoveBBlock_semantic
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
    (count : Nat) (hcount : count < cursor.nb)
    (left : SortSliceEntry (Occurrence alpha) nu)
    (hleft : cursor.state.data.read? cursor.ssa = some left)
    (hboundary : ∀ suffixEntry ∈
      ((mergeHiRightEntries call).take cursor.nb).drop (cursor.nb - count),
      lt suffixEntry.key.value left.key.value = false) :
    ∃ moved, mergeHiMoveBBlock? cursor count = some moved ∧
      MergeHiSemanticCursorInvariant lt call moved := by
  by_cases hzero : count = 0
  · subst count
    exact ⟨cursor, by simp [mergeHiMoveBBlock?], h⟩
  · rcases mergeHiMoveBBlockTraced_safe (mergeHiAllocated call).state call.nb cursor
        h.safety count (Nat.le_of_lt hcount) with
      ⟨moved, htraced, _hsafe, _hmovedSafety, _hna, _hnb⟩
    have hraw : mergeHiMoveBBlock? cursor count = some moved := by
      rw [← erase_mergeHiMoveBBlockTraced]
      exact htraced
    have hrawCopy := hraw
    rw [mergeHiMoveBBlock?, if_neg hzero] at hrawCopy
    rcases Option.bind_eq_some_iff.mp hrawCopy with
      ⟨state, hmove, hmoved⟩
    injection hmoved with hmoved
    subst moved
    exact ⟨_, hraw,
      mergeHiMoveBBlock_semantic_of_eq_some hgeometry horder hleftSorted h
        hna count (Nat.pos_of_ne_zero hzero) hcount left hleft hboundary state
        hmove⟩

/-- Total semantic ordinary A step. -/
theorem mergeHiCopyA_semantic
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
    (hcompare : lt right.key.value left.key.value = true) :
    ∃ copied,
      mergeHiCopyDataDecr? cursor.state cursor.dest cursor.ssa = some copied ∧
      MergeHiSemanticCursorInvariant lt call
        { cursor with
          state := copied.state
          dest := copied.dst
          ssa := copied.src
          na := cursor.na - 1 } := by
  rcases mergeHiCopyDataDecrTraced_safe (mergeHiAllocated call).state call.nb
      cursor h.safety hna
      with ⟨copied, htraced, _hsafe, hsafety, _hdst, _hsrc⟩
  have hraw : mergeHiCopyDataDecr? cursor.state cursor.dest cursor.ssa =
      some copied := by
    rw [← erase_mergeHiCopyDataDecrTraced]
    exact htraced
  exact ⟨copied, hraw,
    h.copyA hgeometry horder hrightSorted hna left right hleft hright
      hcompare copied hraw hsafety⟩

/-- Total semantic ordinary B step, including comparator-equivalent ties. -/
theorem mergeHiCopyB_semantic
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
    (hcompare : lt right.key.value left.key.value = false) :
    ∃ copied,
      mergeHiCopyTempDecr? cursor.state cursor.dest cursor.ssb = some copied ∧
      MergeHiSemanticCursorInvariant lt call
        { cursor with
          state := copied.state
          dest := copied.dst
          ssb := copied.src
          nb := cursor.nb - 1 } := by
  rcases mergeHiCopyTempDecrTraced_safe (mergeHiAllocated call).state call.nb
      cursor h.safety
      (Nat.zero_lt_of_lt hnb) with
    ⟨copied, htraced, _hsafe, hsafety, _hdst, _hsrc⟩
  have hraw : mergeHiCopyTempDecr? cursor.state cursor.dest cursor.ssb =
      some copied := by
    rw [← erase_mergeHiCopyTempDecrTraced]
    exact htraced
  exact ⟨copied, hraw,
    h.copyB hgeometry horder hleftSorted hna hnb left right hleft hright
      hcompare copied hraw hsafety⟩

/-- Semantic contract required of the recursive continuation passed to a
single galloping round. -/
def MergeHiSemanticContinuation
    (lt : BoolComparator alpha)
    (call : MergeAtCall (Occurrence alpha) nu)
    (next : MergeHiCursor (Occurrence alpha) nu →
      Option (MergeHiResult (Occurrence alpha) nu)) : Prop :=
  ∀ cursor result, MergeHiSemanticCursorInvariant lt call cursor →
    next cursor = some result → result.fuelExhausted = false →
      MergeHiSemanticResult lt call result

/-- The direction witness on a typed merge `memcpy` is proof-only and cannot
change its successful result. -/
theorem mergeHiMemcpyTempToData_result_unique
    (site : MergeHiMemcpyCallsite)
    (p q : site.backings =
      { destination := .main, source := .temporary })
    (count : Nat) (state : MergeState κ ν) (dst src : Int)
    {first second : MergeState κ ν}
    (hfirst : mergeHiMemcpyTempToData? site p count state dst src =
      some first)
    (hsecond : mergeHiMemcpyTempToData? site q count state dst src =
      some second) :
    first = second := by
  have hpq : p = q := Subsingleton.elim _ _
  cases hpq
  rw [hfirst] at hsecond
  exact Option.some.inj hsecond

/-- Functional correctness of the B half of one galloping round.  The proof
uses the positive low sentinel to discharge the raw evaluator's observable
`nb = 0` hedge, while retaining that case split in the evaluator equation. -/
theorem mergeHiGallopB_semantic
    {lt : BoolComparator alpha}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {afterB : MergeHiCursor (Occurrence alpha) nu}
    {next : MergeHiCursor (Occurrence alpha) nu →
      Option (MergeHiResult (Occurrence alpha) nu)}
    {result : MergeHiResult (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call)
    (horder : BoolStrictWeakOrder lt)
    (hsemantic : MergeHiSemanticPre lt call)
    (h : MergeHiSemanticCursorInvariant lt call afterB)
    (hna : 0 < afterB.na) (hnb : 1 < afterB.nb)
    (aCount : Nat)
    (hnext : MergeHiSemanticContinuation lt call next)
    (hresultFuel : result.fuelExhausted = false)
    (heval : mergeHiGallopB? afterB aCount next = some result) :
    MergeHiSemanticResult lt call result := by
  rcases h.activeLeft_snoc hgeometry hna with ⟨left, hleft, hleftSnoc⟩
  have hprefixInitialized : MergeHiTempPrefixInitialized afterB.state.a
      afterB.nb := by
    intro offset hoffset
    rcases h.safety.tempValuesMode offset hoffset with
      ⟨entry, hread, _hmode⟩
    rw [erase_mergeTempRead] at hread
    refine ⟨entry, ?_⟩
    simpa [mergeTempRead_eq_mergeHiTempRead] using hread
  rcases mergeHiInitializedTempPrefix_exists_of_initialized afterB.state.a
      afterB.nb hprefixInitialized with ⟨temp, htemp⟩
  have hagrees := initializedTempPrefix_agreesWithSlice_of_eq_some
    afterB.state.a afterB.nb temp htemp
  rcases gallopLeft_correct afterB.state
      (.temporary afterB.state.a 0) temp 0 left.key afterB.nb
      (afterB.nb - 1) h.safety.temporaryValidRange hagrees
      (h.order horder) (h.temporaryGallopSorted hgeometry
        hsemantic.rightEntriesPairwise) (by omega) (by omega)
      h.safety.rightWordBound with
    ⟨gallopB, hgallop, hgallopFuel, hpartition⟩
  have hindexPositive := h.gallopLeftIndex_pos hgeometry horder
    hsemantic.leftEntriesPairwise hna left hleft temp htemp gallopB.index
      hpartition
  let bCount := afterB.nb - gallopB.index
  have hcountLt : bCount < afterB.nb := by
    dsimp only [bCount]
    omega
  have hnewNb : afterB.nb - bCount = gallopB.index := by
    dsimp only [bCount]
    exact mergeHi_sub_sub_to_index hpartition.1
  have hboundary : ∀ suffixEntry ∈
      ((mergeHiRightEntries call).take afterB.nb).drop
        (afterB.nb - bCount),
      lt suffixEntry.key.value left.key.value = false := by
    rw [hnewNb]
    exact h.gallopLeftSuffixBoundary temp htemp left gallopB.index
      hpartition
  rcases mergeHiMoveBBlock_semantic hgeometry horder
      hsemantic.leftEntriesPairwise h
      hna bCount hcountLt left hleft hboundary with
    ⟨movedB, hmove, hmoved⟩
  have hmovedNb : movedB.nb = gallopB.index := by
    rcases mergeHiMoveBBlockTraced_safe (mergeHiAllocated call).state call.nb
        afterB h.safety
        bCount (Nat.le_of_lt hcountLt) with
      ⟨movedB', htraced, _hsafe, _hinv, _hnaEq, hnbEq⟩
    have hraw' : mergeHiMoveBBlock? afterB bCount = some movedB' := by
      rw [← erase_mergeHiMoveBBlockTraced]
      exact htraced
    rw [hmove] at hraw'
    injection hraw' with heq
    subst movedB'
    exact hnbEq.trans hnewNb
  have hmovedNa : movedB.na = afterB.na := by
    rcases mergeHiMoveBBlockTraced_safe (mergeHiAllocated call).state call.nb
        afterB h.safety
        bCount (Nat.le_of_lt hcountLt) with
      ⟨movedB', htraced, _hsafe, _hinv, hnaEq, _hnbEq⟩
    have hraw' : mergeHiMoveBBlock? afterB bCount = some movedB' := by
      rw [← erase_mergeHiMoveBBlockTraced]
      exact htraced
    rw [hmove] at hraw'
    injection hraw' with heq
    subst movedB'
    exact hnaEq
  have hmovedNbPositive : 0 < movedB.nb := by
    rw [hmovedNb]
    exact hindexPositive
  have hevalFinish :
      (if movedB.nb = 0 ∨ movedB.nb = 1 then next movedB
      else (mergeHiCopyDataDecr? movedB.state movedB.dest movedB.ssa).bind
        fun copiedA =>
          let afterA : MergeHiCursor (Occurrence alpha) nu :=
            { movedB with
              state := copiedA.state
              dest := copiedA.dst
              ssa := copiedA.src
              na := movedB.na - 1 }
          if afterA.na = 0 then next afterA
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
                phase := .straight 0 0 }) = some result := by
    by_cases hbzero : bCount = 0
    · have hmovedEq : movedB = afterB := by
        have hm := hmove
        rw [mergeHiMoveBBlock?, if_pos hbzero] at hm
        exact Option.some.inj hm.symm
      subst movedB
      simpa [mergeHiGallopB_equation, hleft, htemp,
        mergeHiBindOptionAcross, hgallop, hgallopFuel, bCount, hbzero]
        using heval
    · have hm := hmove
      rw [mergeHiMoveBBlock?, if_neg hbzero] at hm
      rcases Option.bind_eq_some_iff.mp hm with ⟨state, hstate, hmovedEq⟩
      injection hmovedEq with hmovedEq
      subst movedB
      have hevalMove := heval
      simp only [mergeHiGallopB_equation, hleft, bind, Option.bind, htemp,
        mergeHiBindOptionAcross, hgallop, hgallopFuel, Bool.false_eq_true,
        if_false, bCount, hbzero] at hevalMove
      rcases Option.bind_eq_some_iff.mp hevalMove with
        ⟨state', hstate', hfinish⟩
      have hstateEq : state' = state := by
        dsimp only [bCount] at hstate
        exact mergeHiMemcpyTempToData_result_unique _ _ _ _ _ _ _
          hstate' hstate
      subst state'
      simpa [bCount, bind, Option.bind] using hfinish
  simp only [hmovedNbPositive.ne', false_or] at hevalFinish
  by_cases hmovedOne : movedB.nb = 1
  · rw [if_pos hmovedOne] at hevalFinish
    exact hnext movedB result hmoved hevalFinish hresultFuel
  · rw [if_neg hmovedOne] at hevalFinish
    have hmovedMore : 1 < movedB.nb := by omega
    rcases hmoved.activeLeft_snoc hgeometry (by omega) with
      ⟨left', hleft', hleftSnoc'⟩
    have hleftEq : left' = left := by
      rw [hmovedNa] at hleftSnoc'
      have htail := List.append_cancel_left (hleftSnoc'.symm.trans hleftSnoc)
      simpa using htail
    subst left'
    rcases hmoved.activeRight_snoc hgeometry with
      ⟨right, hright, hrightSnoc⟩
    have hrightMem : right ∈
        ((mergeHiRightEntries call).take afterB.nb).take gallopB.index := by
      have hmem : right ∈ (mergeHiRightEntries call).take movedB.nb := by
        rw [hrightSnoc]
        simp
      rw [List.take_take, Nat.min_eq_left hpartition.1]
      simpa [hmovedNb] using hmem
    have hcompare := h.gallopLeftPrefixBoundary temp htemp left
      gallopB.index hpartition right hrightMem
    rcases mergeHiCopyA_semantic hgeometry horder
        hsemantic.rightEntriesPairwise
        hmoved (by omega) left right hleft' hright hcompare with
      ⟨copiedA, hcopyA, hafterA⟩
    rw [hcopyA] at hevalFinish
    let afterA : MergeHiCursor (Occurrence alpha) nu :=
      { movedB with
        state := copiedA.state
        dest := copiedA.dst
        ssa := copiedA.src
        na := movedB.na - 1 }
    change (if afterA.na = 0 then next afterA
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
            phase := .straight 0 0 }) = some result at hevalFinish
    by_cases hafterZero : afterA.na = 0
    · rw [if_pos hafterZero] at hevalFinish
      exact hnext afterA result hafterA hevalFinish hresultFuel
    · rw [if_neg hafterZero] at hevalFinish
      by_cases hstay : mergeHiCountAtLeast aCount MIN_GALLOP ||
          mergeHiCountAtLeast bCount MIN_GALLOP
      · rw [if_pos hstay] at hevalFinish
        exact hnext _ result
          (hafterA.setControl afterA.minGallop
            (.galloping aCount bCount)) hevalFinish hresultFuel
      · rw [if_neg hstay] at hevalFinish
        let minGallop := afterB.minGallop + 1
        exact hnext _ result
          ((hafterA.setMinGallop minGallop).setControl minGallop
            (.straight 0 0)) hevalFinish hresultFuel

/-- Functional correctness of one complete galloping round, including its A
suffix, forced B cell, and optional B gallop. -/
theorem mergeHiGallopRound_semantic
    {lt : BoolComparator alpha}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    {cursor : MergeHiCursor (Occurrence alpha) nu}
    {next : MergeHiCursor (Occurrence alpha) nu →
      Option (MergeHiResult (Occurrence alpha) nu)}
    {result : MergeHiResult (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call)
    (horder : BoolStrictWeakOrder lt)
    (hsemantic : MergeHiSemanticPre lt call)
    (h : MergeHiSemanticCursorInvariant lt call cursor)
    (hna : 0 < cursor.na) (hnb : 1 < cursor.nb)
    (hnext : MergeHiSemanticContinuation lt call next)
    (hresultFuel : result.fuelExhausted = false)
    (heval : mergeHiGallopRound? cursor next = some result) :
    MergeHiSemanticResult lt call result := by
  let minGallop := mergeHiDecreaseMinGallop cursor.minGallop
  let state : MergeState (Occurrence alpha) nu :=
    { cursor.state with min_gallop := minGallop }
  let adjusted : MergeHiCursor (Occurrence alpha) nu :=
    { cursor with state := state, minGallop := minGallop }
  have hadjusted : MergeHiSemanticCursorInvariant lt call adjusted := by
    exact h.setMinGallop minGallop
  rcases hadjusted.activeRight_snoc hgeometry with
    ⟨right, hright, hrightSnoc⟩
  rcases gallopRight_correct state (.main state.data cursor.basea)
      state.data cursor.basea right.key cursor.na (cursor.na - 1)
      hadjusted.safety.mainValidRange
      (GallopKeySource.main_agreesWithSlice state.data cursor.basea cursor.na)
      (by simpa [adjusted, state] using hadjusted.order horder)
      (by simpa [adjusted, state] using
        hadjusted.mainGallopSorted hgeometry hsemantic.leftEntriesPairwise)
      hna (by omega) h.safety.leftWordBound with
    ⟨gallopA, hgallop, hgallopFuel, hpartition⟩
  let aCount := cursor.na - gallopA.index
  have hcountLe : aCount ≤ adjusted.na := by
    dsimp only [aCount, adjusted]
    exact Nat.sub_le _ _
  have hnewNa : cursor.na - aCount = gallopA.index := by
    dsimp only [aCount]
    exact mergeHi_sub_sub_to_index hpartition.1
  have hboundary : ∀ suffixEntry ∈
      ((mergeHiLeftEntries call).take adjusted.na).drop
        (adjusted.na - aCount),
      lt right.key.value suffixEntry.key.value = true := by
    simpa [adjusted, hnewNa] using
      (hadjusted.gallopRightSuffixBoundary hgeometry right gallopA.index
        hpartition)
  rcases mergeHiMoveABlock_semantic hgeometry horder
      hsemantic.rightEntriesPairwise
      hadjusted aCount hcountLe right hright hboundary with
    ⟨movedA, hmove, hmoved⟩
  have hmovedNa : movedA.na = gallopA.index := by
    rcases mergeHiMoveABlockTraced_safe (mergeHiAllocated call).state call.nb adjusted
        hadjusted.safety aCount hcountLe with
      ⟨movedA', htraced, _hsafe, _hinv, hnaEq, _hnbEq⟩
    have hraw' : mergeHiMoveABlock? adjusted aCount = some movedA' := by
      rw [← erase_mergeHiMoveABlockTraced]
      exact htraced
    rw [hmove] at hraw'
    injection hraw' with heq
    subst movedA'
    exact hnaEq.trans (by simpa [adjusted] using hnewNa)
  have hmovedNb : movedA.nb = cursor.nb := by
    rcases mergeHiMoveABlockTraced_safe (mergeHiAllocated call).state call.nb adjusted
        hadjusted.safety aCount hcountLe with
      ⟨movedA', htraced, _hsafe, _hinv, _hnaEq, hnbEq⟩
    have hraw' : mergeHiMoveABlock? adjusted aCount = some movedA' := by
      rw [← erase_mergeHiMoveABlockTraced]
      exact htraced
    rw [hmove] at hraw'
    injection hraw' with heq
    subst movedA'
    simpa [adjusted] using hnbEq
  have hevalFinish :
      (if movedA.na = 0 then next movedA
      else (mergeHiCopyTempDecr? movedA.state movedA.dest movedA.ssb).bind
        fun copiedB =>
          let afterB : MergeHiCursor (Occurrence alpha) nu :=
            { movedA with
              state := copiedB.state
              dest := copiedB.dst
              ssb := copiedB.src
              nb := movedA.nb - 1 }
          if afterB.nb = 1 then next afterB
          else mergeHiGallopB? afterB aCount next) = some result := by
    by_cases hazero : aCount = 0
    · have hmovedEq : movedA = adjusted := by
        have hm := hmove
        rw [mergeHiMoveABlock?, if_pos hazero] at hm
        exact Option.some.inj hm.symm
      subst movedA
      simpa [mergeHiGallopRound_equation, minGallop, state, adjusted,
        hright, mergeHiBindOptionAcross, hgallop, hgallopFuel, aCount,
        hazero] using heval
    · have hm := hmove
      rw [mergeHiMoveABlock?, if_neg hazero] at hm
      rcases Option.bind_eq_some_iff.mp hm with
        ⟨movedState, hmain, hmovedEq⟩
      unfold mainDataMemmove? at hmain
      rcases Option.bind_eq_some_iff.mp hmain with
        ⟨data, hdata, hstateEq⟩
      injection hstateEq with hstateEq
      subst movedState
      injection hmovedEq with hmovedEq
      subst movedA
      have hevalMove := heval
      simp only [mergeHiGallopRound_equation, minGallop, state, adjusted,
        hright, bind, Option.bind, mergeHiBindOptionAcross, hgallop,
        hgallopFuel, Bool.false_eq_true, if_false, aCount, hazero,
        mergeDataMemmove_eq] at hevalMove
      rcases Option.bind_eq_some_iff.mp hevalMove with
        ⟨data', hdata', hfinish⟩
      have hdataEq : data' = data := by
        have hdataCursor : cursor.state.data.memmove?
            (cursor.dest - Int.ofNat (cursor.na - gallopA.index) + 1)
            (cursor.ssa - Int.ofNat (cursor.na - gallopA.index) + 1)
            (cursor.na - gallopA.index) = some data := by
          simpa [adjusted, state, aCount] using hdata
        exact Option.some.inj (hdata'.symm.trans hdataCursor)
      subst data'
      simpa [minGallop, state, adjusted, aCount, bind, Option.bind]
        using hfinish
  by_cases hmovedZero : movedA.na = 0
  · rw [if_pos hmovedZero] at hevalFinish
    exact hnext movedA result hmoved hevalFinish hresultFuel
  · rw [if_neg hmovedZero] at hevalFinish
    have hmovedPositive : 0 < movedA.na := Nat.pos_of_ne_zero hmovedZero
    rcases hmoved.activeLeft_snoc hgeometry hmovedPositive with
      ⟨left, hleft, hleftSnoc⟩
    have hleftMem : left ∈
        ((mergeHiLeftEntries call).take cursor.na).take gallopA.index := by
      have hmem : left ∈ (mergeHiLeftEntries call).take movedA.na := by
        rw [hleftSnoc]
        simp
      rw [List.take_take, Nat.min_eq_left hpartition.1]
      simpa [hmovedNa] using hmem
    have hcompareOriginal := hadjusted.gallopRightPrefixBoundary hgeometry
      right gallopA.index hpartition left hleftMem
    rcases hmoved.activeRight_snoc hgeometry with
      ⟨right', hright', hrightSnoc'⟩
    have hrightEq : right' = right := by
      rw [hmovedNb] at hrightSnoc'
      have htail := List.append_cancel_left
        (hrightSnoc'.symm.trans (by simpa [adjusted] using hrightSnoc))
      simpa using htail
    subst right'
    rcases mergeHiCopyB_semantic hgeometry horder
        hsemantic.leftEntriesPairwise
        hmoved hmovedPositive (by simpa [hmovedNb] using hnb) left right hleft
        hright' hcompareOriginal with
      ⟨copiedB, hcopyB, hafterB⟩
    rw [hcopyB] at hevalFinish
    let afterB : MergeHiCursor (Occurrence alpha) nu :=
      { movedA with
        state := copiedB.state
        dest := copiedB.dst
        ssb := copiedB.src
        nb := movedA.nb - 1 }
    change (if afterB.nb = 1 then next afterB
      else mergeHiGallopB? afterB aCount next) = some result at hevalFinish
    by_cases hafterOne : afterB.nb = 1
    · rw [if_pos hafterOne] at hevalFinish
      exact hnext afterB result hafterB hevalFinish hresultFuel
    · rw [if_neg hafterOne] at hevalFinish
      have hafterMore : 1 < afterB.nb := by
        change 1 < movedA.nb - 1
        have hne : movedA.nb - 1 ≠ 1 := by
          simpa [afterB] using hafterOne
        rw [hmovedNb] at hne
        rw [hmovedNb]
        omega
      exact mergeHiGallopB_semantic hgeometry horder hsemantic hafterB
        (by simpa [afterB] using hmovedPositive) hafterMore aCount hnext
        hresultFuel hevalFinish

/-! ### Complete raw phase loop -/

/-- Every successful, non-fuel-exhausted result of the actual raw phase loop
realizes the exact stable target and whole-range frame. -/
theorem mergeHiLoop_semantic
    {lt : BoolComparator alpha}
    {pre : MergeState (Occurrence alpha) nu} {scanned i : Nat}
    {call : MergeAtCall (Occurrence alpha) nu}
    (hgeometry : MergeAtSafetyGeometry pre scanned i call)
    (horder : BoolStrictWeakOrder lt)
    (hsemantic : MergeHiSemanticPre lt call)
    {fuel : Nat} {cursor : MergeHiCursor (Occurrence alpha) nu}
    {result : MergeHiResult (Occurrence alpha) nu}
    (h : MergeHiSemanticCursorInvariant lt call cursor)
    (heval : mergeHiLoop? fuel cursor = some result)
    (hresultFuel : result.fuelExhausted = false) :
    MergeHiSemanticResult lt call result := by
  induction fuel generalizing cursor result with
  | zero =>
      by_cases hterminal : cursor.na = 0 ∨ cursor.nb = 0
      · have hna : cursor.na = 0 := by
          rcases hterminal with hna | hnb
          · exact hna
          · exact False.elim (Nat.ne_of_gt h.rightPositive hnb)
        have hsucceed : mergeHiSucceed? cursor = some result := by
          simpa [mergeHiLoop?, hterminal] using heval
        exact mergeHiSucceed_semantic hgeometry h hna hsucceed
      · have hna : 0 < cursor.na := by omega
        by_cases hnbOne : cursor.nb = 1
        · have hcopy : mergeHiCopyA? cursor = some result := by
            simpa [mergeHiLoop?, hterminal, hnbOne, Nat.ne_of_gt hna]
              using heval
          exact mergeHiCopyATail_semantic hgeometry horder
            hsemantic.leftEntriesPairwise h hna hnbOne hcopy
        · have hexhausted : some (mergeHiFuelExhausted cursor) =
              some result := by
            simpa [mergeHiLoop?, hterminal, hnbOne] using heval
          injection hexhausted with hresult
          subst result
          simp [mergeHiFuelExhausted] at hresultFuel
  | succ fuel ih =>
      by_cases hterminal : cursor.na = 0 ∨ cursor.nb = 0
      · have hna : cursor.na = 0 := by
          rcases hterminal with hna | hnb
          · exact hna
          · exact False.elim (Nat.ne_of_gt h.rightPositive hnb)
        have hsucceed : mergeHiSucceed? cursor = some result := by
          simpa [mergeHiLoop?, hterminal] using heval
        exact mergeHiSucceed_semantic hgeometry h hna hsucceed
      · have hna : 0 < cursor.na := by omega
        have hnbPositive : 0 < cursor.nb := h.rightPositive
        by_cases hnbOne : cursor.nb = 1
        · have hcopy : mergeHiCopyA? cursor = some result := by
            simpa [mergeHiLoop?, hterminal, hnbOne, Nat.ne_of_gt hna]
              using heval
          exact mergeHiCopyATail_semantic hgeometry horder
            hsemantic.leftEntriesPairwise h hna hnbOne hcopy
        · have hnb : 1 < cursor.nb := by omega
          cases hphase : cursor.phase with
          | galloping aCount bCount =>
              have hround : mergeHiGallopRound? cursor
                  (mergeHiLoop? fuel) = some result := by
                simpa [mergeHiLoop?, hterminal, hnbOne, hphase] using heval
              apply mergeHiGallopRound_semantic hgeometry horder hsemantic h
                hna hnb
              · intro nextCursor nextResult hnextInv hnextEval hnextFuel
                exact ih hnextInv hnextEval hnextFuel
              · exact hresultFuel
              · exact hround
          | straight aCount bCount =>
              rcases h.activeRight_snoc hgeometry with
                ⟨right, hright, _hrightSnoc⟩
              rcases h.activeLeft_snoc hgeometry hna with
                ⟨left, hleft, _hleftSnoc⟩
              by_cases hcompareRaw :
                  cursor.state.key_compare right.key left.key = true
              · have hcompare : lt right.key.value left.key.value = true := by
                  simpa [h.comparator, occurrenceComparator] using hcompareRaw
                rcases mergeHiCopyA_semantic hgeometry horder
                    hsemantic.rightEntriesPairwise h hna left right hleft hright
                    hcompare with ⟨copied, hcopy, hcopied⟩
                let nextCount := aCount + 1
                let next : MergeHiCursor (Occurrence alpha) nu :=
                  { cursor with
                    state := copied.state
                    dest := copied.dst
                    ssa := copied.src
                    na := cursor.na - 1
                    phase :=
                      if mergeHiCountAtLeast nextCount cursor.minGallop then
                        .galloping nextCount 0
                      else
                        .straight nextCount 0
                    minGallop :=
                      if mergeHiCountAtLeast nextCount cursor.minGallop then
                        cursor.minGallop + 1
                      else
                        cursor.minGallop }
                have hnextInv : MergeHiSemanticCursorInvariant lt call next := by
                  by_cases hcross :
                      mergeHiCountAtLeast nextCount cursor.minGallop = true
                  · simpa [next, nextCount, hcross] using
                      hcopied.setControl (cursor.minGallop + 1)
                        (.galloping nextCount 0)
                  · have hcrossFalse :
                        mergeHiCountAtLeast nextCount cursor.minGallop =
                          false := Bool.eq_false_of_not_eq_true hcross
                    simpa [next, nextCount, hcrossFalse] using
                      hcopied.setControl cursor.minGallop
                        (.straight nextCount 0)
                have hnextEval : mergeHiLoop? fuel next = some result := by
                  have hcursorPhase :
                      { cursor with phase := .straight aCount bCount } =
                        cursor := by
                    cases cursor
                    simp_all
                  have hstep := mergeHiLoop_straight_copyA_equation fuel
                    cursor aCount bCount right left hterminal hnbOne hright
                    hleft hcompareRaw
                  rw [hcursorPhase] at hstep
                  rw [hstep] at heval
                  rw [hcopy] at heval
                  simpa [next, nextCount] using heval
                exact ih hnextInv hnextEval hresultFuel
              · have hcompareRawFalse :
                    cursor.state.key_compare right.key left.key = false :=
                  Bool.eq_false_of_not_eq_true hcompareRaw
                have hcompare : lt right.key.value left.key.value = false := by
                  simpa [h.comparator, occurrenceComparator] using
                    hcompareRawFalse
                rcases mergeHiCopyB_semantic hgeometry horder
                    hsemantic.leftEntriesPairwise h hna hnb left right hleft
                      hright
                    hcompare with ⟨copied, hcopy, hcopied⟩
                let nextCount := bCount + 1
                let next : MergeHiCursor (Occurrence alpha) nu :=
                  { cursor with
                    state := copied.state
                    dest := copied.dst
                    ssb := copied.src
                    nb := cursor.nb - 1
                    phase :=
                      if mergeHiCountAtLeast nextCount cursor.minGallop then
                        .galloping 0 nextCount
                      else
                        .straight 0 nextCount
                    minGallop :=
                      if mergeHiCountAtLeast nextCount cursor.minGallop then
                        cursor.minGallop + 1
                      else
                        cursor.minGallop }
                have hnextInv : MergeHiSemanticCursorInvariant lt call next := by
                  by_cases hcross :
                      mergeHiCountAtLeast nextCount cursor.minGallop = true
                  · simpa [next, nextCount, hcross] using
                      hcopied.setControl (cursor.minGallop + 1)
                        (.galloping 0 nextCount)
                  · have hcrossFalse :
                        mergeHiCountAtLeast nextCount cursor.minGallop =
                          false := Bool.eq_false_of_not_eq_true hcross
                    simpa [next, nextCount, hcrossFalse] using
                      hcopied.setControl cursor.minGallop
                        (.straight 0 nextCount)
                have hnextEval : mergeHiLoop? fuel next = some result := by
                  have hcursorPhase :
                      { cursor with phase := .straight aCount bCount } =
                        cursor := by
                    cases cursor
                    simp_all
                  have hstep := mergeHiLoop_straight_copyB_equation fuel
                    cursor aCount bCount right left hterminal hnbOne hright
                    hleft hcompareRawFalse
                  rw [hcursorPhase] at hstep
                  rw [hstep] at heval
                  rw [hcopy] at heval
                  simpa [next, nextCount] using heval
                exact ih hnextInv hnextEval hresultFuel

/-- The actual raw `merge_hi` entry evaluator produces a functionally correct
result from the call-site safety facts and semantic endpoint/sortedness
precondition.  No raw-correctness premise is assumed. -/
theorem mergeHi_raw_correct
    {lt : BoolComparator alpha} (horder : BoolStrictWeakOrder lt)
    (pre : MergeState (Occurrence alpha) nu) (scanned i : Nat)
    (call : MergeAtCall (Occurrence alpha) nu)
    (hlayout : PendingLayout pre scanned)
    (hmax : pre.listlen.toNat ≤ PY_LIST_MAX)
    (hprepare : prepareMergeAt? pre i = some (.mergeHi call))
    (hInv : TempStorageInv pre.a pre.alloced)
    (hLive : pre.a.Live)
    (hMode : SortSlice.ValuesModeInvariant pre.a.hasValues pre.data)
    (hcomparator : call.state.key_compare = occurrenceComparator lt)
    (hsemantic : MergeHiSemanticPre lt call) :
    ∃ result, MergeHiRawCorrectnessPost lt call result := by
  rcases mergeHi_prepare pre scanned i call hlayout hmax hprepare hInv hLive
      hMode with ⟨copied, forced, hprepared⟩
  rcases mergeHi_safe pre scanned i call hlayout hmax hprepare hInv hLive
      hMode with ⟨result, hsafety⟩
  have hraw := hsafety.rawResultEq
  have hguard :
      0 < call.na ∧ 0 < call.nb ∧
        call.na ≤ PY_SSIZE_T_MAX ∧ call.nb ≤ PY_SSIZE_T_MAX ∧
        call.ssa + Int.ofNat call.na = call.ssb :=
    ⟨hprepared.geometry.leftPositive, hprepared.geometry.rightPositive,
      hprepared.geometry.leftWordBound, hprepared.geometry.rightWordBound,
      hprepared.geometry.adjacent⟩
  have hloop : mergeHiLoop? (call.na + call.nb)
      (mergeHiInitialCursor call forced) = some result := by
    unfold mergeHi? at hraw
    rw [if_pos hguard] at hraw
    change (match (mergeHiAllocated call).outcome with
      | .guardRejected => some
          { state := (mergeHiAllocated call).state
            returnCode := -1
            fuelExhausted := false }
      | .reused | .grown => do
          let state ← mergeHiMemcpyDataToTemp? .initialDataToTemp rfl
            call.nb (mergeHiAllocated call).state 0 call.ssb
          let copied ← mergeHiCopyDataDecr? state
            (call.ssb + Int.ofNat (call.nb - 1))
            (call.ssa + Int.ofNat (call.na - 1))
          mergeHiLoop? (call.na + call.nb)
            (mergeHiInitialCursor call copied)) = some result at hraw
    rcases hprepared.allocation.outcome with houtcome | houtcome
    · rw [houtcome, hprepared.initialCopyRaw] at hraw
      simp only [bind, Option.bind] at hraw
      rw [hprepared.forcedRaw] at hraw
      exact hraw
    · rw [houtcome, hprepared.initialCopyRaw] at hraw
      simp only [bind, Option.bind] at hraw
      rw [hprepared.forcedRaw] at hraw
      exact hraw
  have hinitial := hprepared.semanticInitial horder hcomparator hsemantic
  have hresult := mergeHiLoop_semantic hprepared.geometry horder hsemantic
    hinitial hloop hsafety.resultFuel
  exact ⟨result,
    { resultEq := hsafety.rawResultEq
      exactRange := hresult.1
      frame := hresult.2 }⟩

/-- Exact composition point between the independent raw functional proof and
the reviewed traced safety proof.  Both certificates name the same successful
`mergeHi?` result; `MergeHiSafetyPost.exactErasure` is what rules out a
decorative trace or a second execution. -/
theorem mergeHi_safe_join_raw_correctness
    {lt : BoolComparator alpha} (horder : BoolStrictWeakOrder lt)
    (canonical : List (Occurrence alpha))
    (pre : MergeState (Occurrence alpha) nu) (scanned i : Nat)
    (call : MergeAtCall (Occurrence alpha) nu)
    (hlayout : PendingLayout pre scanned)
    (hmax : pre.listlen.toNat ≤ PY_LIST_MAX)
    (hprepare : prepareMergeAt? pre i = some (.mergeHi call))
    (hInv : TempStorageInv pre.a pre.alloced)
    (hLive : pre.a.Live)
    (hMode : SortSlice.ValuesModeInvariant pre.a.hasValues pre.data)
    (hsemantic : MergeHiSemanticPre lt call)
    (hstable : StableOccurrencePermutation lt canonical
      ((sortSliceRangeKeys call.state.data call.ssa.toNat call.na).toList ++
        (sortSliceRangeKeys call.state.data call.ssb.toNat call.nb).toList))
    (hraw : ∃ rawResult,
      MergeHiRawCorrectnessPost lt call rawResult) :
    ∃ result, MergeHiCorrectnessPost lt canonical pre scanned i call result := by
  rcases hraw with ⟨rawResult, hraw⟩
  rcases mergeHi_safe pre scanned i call hlayout hmax hprepare hInv hLive hMode
      with ⟨result, hsafety⟩
  have hsame := hsafety.rawResultEq
  rw [hraw.resultEq] at hsame
  injection hsame with hresult
  subst rawResult
  exact ⟨result, mergeHiCorrectnessPost_of_exactRange horder canonical
    hsafety hsemantic hstable hraw.exactRange hraw.frame⟩

/-- End-to-end functional correctness of the actual traced `merge_hi` call.

The shared semantic precondition records explicit nonemptiness, the two runs
under the public `Sorted` predicate, and both strict trimming endpoints needed
by the reverse evaluator.  Comparator binding and canonical stability remain
identical explicit premises of both merge-direction theorems. -/
theorem mergeHi_correct
    {lt : BoolComparator alpha} (horder : BoolStrictWeakOrder lt)
    (canonical : List (Occurrence alpha))
    (pre : MergeState (Occurrence alpha) nu) (scanned i : Nat)
    (call : MergeAtCall (Occurrence alpha) nu)
    (hlayout : PendingLayout pre scanned)
    (hmax : pre.listlen.toNat ≤ PY_LIST_MAX)
    (hprepare : prepareMergeAt? pre i = some (.mergeHi call))
    (hInv : TempStorageInv pre.a pre.alloced)
    (hLive : pre.a.Live)
    (hMode : SortSlice.ValuesModeInvariant pre.a.hasValues pre.data)
    (hcomparator : call.state.key_compare = occurrenceComparator lt)
    (hstable : StableOccurrencePermutation lt canonical
      ((sortSliceRangeKeys call.state.data call.ssa.toNat call.na).toList ++
        (sortSliceRangeKeys call.state.data call.ssb.toNat call.nb).toList))
    (hsemantic : MergeHiSemanticPre lt call) :
    ∃ result, MergeHiCorrectnessPost lt canonical pre scanned i call result := by
  apply mergeHi_safe_join_raw_correctness horder canonical pre scanned i call
    hlayout hmax hprepare hInv hLive hMode hsemantic hstable
  exact mergeHi_raw_correct horder pre scanned i call hlayout hmax hprepare
    hInv hLive hMode hcomparator hsemantic

/-! ## Executable exact-target regression -/

private def mergeHiCorrectnessNatLt : BoolComparator Nat :=
  fun left right => decide (left < right)

private def mergeHiCorrectnessEntry (value origin payload : Nat) :
    SortSliceEntry (Occurrence Nat) Nat :=
  { key := { value := value, origin := origin }, value := some payload }

/-- A keyed fixture with one cell on each side of the affected range.  The
equal `4` occurrences straddle the two runs, so the expected stable merge also
checks the reverse-fill tie direction and whole-entry payload pairing. -/
private def mergeHiCorrectnessRegressionState :
    MergeState (Occurrence Nat) Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 6
    basekeys := 0
    data :=
      { entries :=
          #[mergeHiCorrectnessEntry 99 0 990,
            mergeHiCorrectnessEntry 4 1 40,
            mergeHiCorrectnessEntry 5 2 50,
            mergeHiCorrectnessEntry 1 3 11,
            mergeHiCorrectnessEntry 4 4 41,
            mergeHiCorrectnessEntry 100 5 1000] }
    a :=
      { cells := Array.replicate 2 none
        backing := .inline
        hasValues := true }
    alloced := 2
    pending := #[]
    key_compare := occurrenceComparator mergeHiCorrectnessNatLt
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

/-- The concrete regression fixture has honest, live inline temporary storage:
its physical cell count exactly matches `alloced`. -/
theorem mergeHi_correctness_regression_tempStorageInv :
    TempStorageInv mergeHiCorrectnessRegressionState.a
      mergeHiCorrectnessRegressionState.alloced := by
  simp only [mergeHiCorrectnessRegressionState, TempStorageInv,
    Array.size_replicate, TempStorage.multiplier, if_pos]
  change 2 = (BitVec.ofNat 64 2).toNat ∧
    2 * (BitVec.ofNat 64 2).toNat ≤ MERGESTATE_TEMP_SIZE
  norm_num [BitVec.toNat_ofNat, MERGESTATE_TEMP_SIZE]

private def mergeHiCorrectnessRegressionExpectedState :
    MergeState (Occurrence Nat) Nat :=
  { mergeHiCorrectnessRegressionState with
    data :=
      { entries :=
          #[mergeHiCorrectnessEntry 99 0 990,
            mergeHiCorrectnessEntry 1 3 11,
            mergeHiCorrectnessEntry 4 1 40,
            mergeHiCorrectnessEntry 4 4 41,
            mergeHiCorrectnessEntry 5 2 50,
            mergeHiCorrectnessEntry 100 5 1000] }
    a :=
      { cells :=
          #[some (mergeHiCorrectnessEntry 1 3 11),
            some (mergeHiCorrectnessEntry 4 4 41)]
        backing := .inline
        hasValues := true } }

private def mergeHiCorrectnessRegressionExpectedResult :
    MergeHiResult (Occurrence Nat) Nat :=
  { state := mergeHiCorrectnessRegressionExpectedState
    returnCode := 0
    fuelExhausted := false }

/-- Kernel-reduced pin that the real raw evaluator reaches the concrete stable
fixture result; the public range theorem below separately checks its semantic
interpretation. -/
theorem mergeHi_correctness_regression_evaluator :
    mergeHi? mergeHiCorrectnessRegressionState 1 3 2 2 =
      some mergeHiCorrectnessRegressionExpectedResult := by
  rfl

/-- Anti-vacuity regression for the central functional claim: the real raw
evaluator produces exactly the left-biased whole-entry merge, keeps the left
equal-key occurrence before the right one, preserves their distinct payloads,
and leaves both neighboring cells unchanged. -/
theorem mergeHi_exact_stable_range_and_frame_regression :
    (mergeHi? mergeHiCorrectnessRegressionState 1 3 2 2).map
        (fun result =>
          ((sortSliceRangeEntries result.state.data 1 4).toList,
            result.state.data.entries[0]?, result.state.data.entries[5]?)) =
      some
        (stableEntryMerge mergeHiCorrectnessNatLt
            (sortSliceRangeEntries mergeHiCorrectnessRegressionState.data
              1 2).toList
            (sortSliceRangeEntries mergeHiCorrectnessRegressionState.data
              3 2).toList,
          some (mergeHiCorrectnessEntry 99 0 990),
          some (mergeHiCorrectnessEntry 100 5 1000)) := by
  rw [mergeHi_correctness_regression_evaluator]
  norm_num [mergeHiCorrectnessRegressionExpectedResult,
    mergeHiCorrectnessRegressionExpectedState,
    mergeHiCorrectnessRegressionState, mergeHiCorrectnessEntry,
    mergeHiCorrectnessNatLt, sortSliceRangeEntries, stableEntryMerge,
    stableEntryLE, stableOccurrenceLE]

end CPythonListsort
