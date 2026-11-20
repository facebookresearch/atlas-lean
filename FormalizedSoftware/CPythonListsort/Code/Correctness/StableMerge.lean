/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.Order
import Code.Correctness.DescendingRunInvariant
import Code.Transcription.SortSlice
import Mathlib.Data.List.Sort

/-!
# Pure stable-merge specification

`merge_lo` and `merge_hi` implement the same mathematical merge while moving
in opposite physical directions.  This file fixes that shared target before
either machine proof reasons about cursors or temporary storage.

The Boolean merge relation selects the left occurrence unless the right value
is strictly smaller.  Comparator-equivalent values therefore select the left
occurrence, exactly matching CPython's stability rule.  Payload-carrying entries
are merged by their occurrence-tagged keys, so every payload remains paired
with its original key occurrence.
-/

namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-- Stable non-strict merge comparison on occurrence-tagged keys: choose the
left key precisely when the right key is not strictly before it. -/
def stableOccurrenceLE (lt : BoolComparator alpha)
    (left right : Occurrence alpha) : Bool :=
  !(lt right.value left.value)

/-- Whole-entry lift of `stableOccurrenceLE`.  The decision inspects only keys,
while `List.merge` moves the complete key/payload entry. -/
def stableEntryLE (lt : BoolComparator alpha)
    (left right : SortSliceEntry (Occurrence alpha) nu) : Bool :=
  stableOccurrenceLE lt left.key right.key

/-- The mathematical stable merge of two occurrence sequences. -/
def stableOccurrenceMerge (lt : BoolComparator alpha)
    (left right : List (Occurrence alpha)) : List (Occurrence alpha) :=
  List.merge left right (stableOccurrenceLE lt)

/-- The mathematical stable merge of two whole-entry sequences. -/
def stableEntryMerge (lt : BoolComparator alpha)
    (left right : List (SortSliceEntry (Occurrence alpha) nu)) :
    List (SortSliceEntry (Occurrence alpha) nu) :=
  List.merge left right (stableEntryLE lt)

@[simp]
theorem stableOccurrenceLE_eq_true
    (lt : BoolComparator alpha) (left right : Occurrence alpha) :
    stableOccurrenceLE lt left right = true ↔
      lt right.value left.value = false := by
  simp [stableOccurrenceLE]

@[simp]
theorem stableEntryLE_eq_true
    (lt : BoolComparator alpha)
    (left right : SortSliceEntry (Occurrence alpha) nu) :
    stableEntryLE lt left right = true ↔
      lt right.key.value left.key.value = false := by
  simp [stableEntryLE]

/-- Projecting keys after whole-entry merge gives exactly the shared occurrence
merge.  This is the bridge from payload-preserving machine proofs to the public
sortedness and stability specifications. -/
theorem stableEntryMerge_keys
    (lt : BoolComparator alpha)
    (left right : List (SortSliceEntry (Occurrence alpha) nu)) :
    (stableEntryMerge lt left right).map SortSliceEntry.key =
      stableOccurrenceMerge lt (left.map SortSliceEntry.key)
        (right.map SortSliceEntry.key) := by
  unfold stableEntryMerge stableOccurrenceMerge
  apply List.map_merge
  intro a _ b _
  rfl

/-- A whole-entry stable merge contains exactly the two input entry lists. -/
theorem stableEntryMerge_perm_append
    (lt : BoolComparator alpha)
    (left right : List (SortSliceEntry (Occurrence alpha) nu)) :
    (stableEntryMerge lt left right).Perm (left ++ right) := by
  exact List.merge_perm_append (stableEntryLE lt)

/-- An occurrence stable merge contains exactly the two input occurrence
lists. -/
theorem stableOccurrenceMerge_perm_append
    (lt : BoolComparator alpha)
    (left right : List (Occurrence alpha)) :
    (stableOccurrenceMerge lt left right).Perm (left ++ right) := by
  exact List.merge_perm_append (stableOccurrenceLE lt)

private theorem stableOccurrenceLE_trans
    {lt : BoolComparator alpha} (horder : BoolStrictWeakOrder lt)
    (a b c : Occurrence alpha)
    (hab : stableOccurrenceLE lt a b = true)
    (hbc : stableOccurrenceLE lt b c = true) :
    stableOccurrenceLE lt a c = true := by
  rw [stableOccurrenceLE_eq_true] at hab hbc ⊢
  exact horder.false_trans hab hbc

set_option linter.flexible false in
private theorem stableOccurrenceLE_total
    {lt : BoolComparator alpha} (horder : BoolStrictWeakOrder lt)
    (a b : Occurrence alpha) :
    stableOccurrenceLE lt a b || stableOccurrenceLE lt b a := by
  simp only [stableOccurrenceLE]
  cases hab : lt b.value a.value <;> cases hba : lt a.value b.value <;>
    simp_all
  exact False.elim (horder.irrefl a.value
    (horder.trans a.value b.value a.value hba hab))

private theorem sortedRelation_pairwise_merge
    {lt : BoolComparator alpha} (horder : BoolStrictWeakOrder lt)
    (left right : List (Occurrence alpha))
    (hleft : left.Pairwise (DescendingRunSpec.SortedRelation lt))
    (hright : right.Pairwise (DescendingRunSpec.SortedRelation lt)) :
    (stableOccurrenceMerge lt left right).Pairwise
      (DescendingRunSpec.SortedRelation lt) := by
  have hleft' : left.Pairwise
      (fun a b => stableOccurrenceLE lt a b = true) := by
    change left.Pairwise (fun a b => lt b.value a.value = false) at hleft
    simpa using hleft
  have hright' : right.Pairwise
      (fun a b => stableOccurrenceLE lt a b = true) := by
    change right.Pairwise (fun a b => lt b.value a.value = false) at hright
    simpa using hright
  have hmerged := List.pairwise_merge
    (stableOccurrenceLE_trans horder)
    (stableOccurrenceLE_total horder) left right hleft' hright'
  change (stableOccurrenceMerge lt left right).Pairwise
    (fun a b => lt b.value a.value = false)
  simpa [stableOccurrenceMerge] using hmerged

private theorem pairwise_stable_merge
    {lt : BoolComparator alpha} (horder : BoolStrictWeakOrder lt) :
    ∀ (left right : List (Occurrence alpha)),
      left.Pairwise (DescendingRunSpec.SortedRelation lt) →
      right.Pairwise (DescendingRunSpec.SortedRelation lt) →
      (left ++ right).Pairwise (DescendingRunSpec.StableRelation lt) →
      (stableOccurrenceMerge lt left right).Pairwise
        (DescendingRunSpec.StableRelation lt)
  | [], right, _, _, hstable => by
      simpa [stableOccurrenceMerge] using hstable
  | left, [], _, _, hstable => by
      simpa [stableOccurrenceMerge] using hstable
  | a :: left, b :: right, hleftSorted, hrightSorted, hstable => by
      rw [stableOccurrenceMerge, List.cons_merge_cons]
      by_cases hchoose : stableOccurrenceLE lt a b = true
      · rw [if_pos hchoose]
        apply List.Pairwise.cons
        · intro x hx
          rw [List.mem_merge] at hx
          have hparts := List.pairwise_append.mp hstable
          rcases hx with hx | hx
          · exact List.rel_of_pairwise_cons hparts.1 hx
          · exact hparts.2.2 a (by simp) x hx
        · have hparts := List.pairwise_append.mp hstable
          apply pairwise_stable_merge horder left (b :: right)
          · exact hleftSorted.tail
          · exact hrightSorted
          · apply List.pairwise_append.mpr
            exact ⟨hparts.1.tail, hparts.2.1,
              fun x hx y hy => hparts.2.2 x (by simp [hx]) y hy⟩
      · rw [if_neg hchoose]
        apply List.Pairwise.cons
        · intro x hx
          rw [List.mem_merge] at hx
          have hparts := List.pairwise_append.mp hstable
          rcases hx with hx | hx
          · intro hequiv
            have hba : lt b.value a.value = true := by
              simpa [stableOccurrenceLE] using hchoose
            have hxa : lt x.value a.value = false := by
              simp only [List.mem_cons] at hx
              rcases hx with hxa | hx
              · subst x
                exact Bool.eq_false_iff.mpr (horder.irrefl a.value)
              · exact List.rel_of_pairwise_cons hleftSorted hx
            have hbx := horder.strict_of_strict_of_not_reverse hba hxa
            exact Bool.noConfusion (hequiv.1.symm.trans hbx)
          · exact List.rel_of_pairwise_cons hparts.2.1 hx
        · have hparts := List.pairwise_append.mp hstable
          apply pairwise_stable_merge horder (a :: left) right
          · exact hleftSorted
          · exact hrightSorted.tail
          · apply List.pairwise_append.mpr
            exact ⟨hparts.1, hparts.2.1.tail,
              fun x hx y hy => hparts.2.2 x hx y (by simp [hy])⟩
termination_by left right => left.length + right.length

/-- Dually, a right-run suffix whose entries are never strictly before any
remaining left entry is already the final stable block.  Comparator-equivalent
right entries satisfy this premise and correctly remain after all equivalent
left entries. -/
theorem stableEntryMerge_append_right_block
    (lt : BoolComparator alpha)
    (suffix : List (SortSliceEntry (Occurrence alpha) nu)) :
    ∀ (left right : List (SortSliceEntry (Occurrence alpha) nu)),
      (∀ leftEntry ∈ left, ∀ suffixEntry ∈ suffix,
        lt suffixEntry.key.value leftEntry.key.value = false) →
      stableEntryMerge lt left (right ++ suffix) =
        stableEntryMerge lt left right ++ suffix
  | [], right, _ => by simp [stableEntryMerge]
  | leftHead :: left, [], hafter => by
      cases suffix with
      | nil => simp [stableEntryMerge]
      | cons suffixHead suffixTail =>
          have hnotStrict :
              lt suffixHead.key.value leftHead.key.value = false :=
            hafter leftHead (by simp) suffixHead (by simp)
          have htail :
              ∀ leftEntry ∈ left,
                ∀ suffixEntry ∈ suffixHead :: suffixTail,
                  lt suffixEntry.key.value leftEntry.key.value = false := by
            intro leftEntry hleft suffixEntry hsuffix
            exact hafter leftEntry (by simp [hleft]) suffixEntry hsuffix
          simp only [List.nil_append]
          unfold stableEntryMerge
          rw [List.cons_merge_cons]
          have hchoose : stableEntryLE lt leftHead suffixHead = true := by
            simp [stableEntryLE, stableOccurrenceLE, hnotStrict]
          rw [if_pos hchoose]
          have ih := stableEntryMerge_append_right_block lt
            (suffixHead :: suffixTail) left [] htail
          simpa [stableEntryMerge] using congrArg (List.cons leftHead) ih
  | leftHead :: left, rightHead :: right, hafter => by
      have hleft :
          ∀ leftEntry ∈ left, ∀ suffixEntry ∈ suffix,
            lt suffixEntry.key.value leftEntry.key.value = false := by
        intro leftEntry hmem suffixEntry hsuffix
        exact hafter leftEntry (by simp [hmem]) suffixEntry hsuffix
      have hright :
          ∀ leftEntry ∈ leftHead :: left, ∀ suffixEntry ∈ suffix,
            lt suffixEntry.key.value leftEntry.key.value = false := hafter
      simp only [List.cons_append]
      unfold stableEntryMerge
      rw [List.cons_merge_cons, List.cons_merge_cons]
      by_cases hchoose : stableEntryLE lt leftHead rightHead = true
      · simp only [hchoose, ↓reduceIte, List.cons_append]
        have ih := stableEntryMerge_append_right_block lt suffix left
          (rightHead :: right) hleft
        simpa [stableEntryMerge] using congrArg (List.cons leftHead) ih
      · simp only [hchoose]
        have ih := stableEntryMerge_append_right_block lt suffix
          (leftHead :: left) right hright
        simpa [stableEntryMerge] using congrArg (List.cons rightHead) ih
termination_by left right => left.length + right.length

/-- Pure stable merge correctness.  The input stability premise is the exact
shared occurrence predicate on the concatenated adjacent runs; the output uses
that same predicate and canonical sequence. -/
theorem stableOccurrenceMerge_correct
    {lt : BoolComparator alpha} (horder : BoolStrictWeakOrder lt)
    (canonical left right : List (Occurrence alpha))
    (hleft : left.Pairwise (DescendingRunSpec.SortedRelation lt))
    (hright : right.Pairwise (DescendingRunSpec.SortedRelation lt))
    (hstable : StableOccurrencePermutation lt canonical (left ++ right)) :
    (stableOccurrenceMerge lt left right).Pairwise
        (DescendingRunSpec.SortedRelation lt) ∧
      StableOccurrencePermutation lt canonical
        (stableOccurrenceMerge lt left right) := by
  refine ⟨sortedRelation_pairwise_merge horder left right hleft hright, ?_⟩
  refine ⟨(stableOccurrenceMerge_perm_append lt left right).trans hstable.1, ?_⟩
  exact pairwise_stable_merge horder left right hleft hright hstable.2

/-- Whole-entry form of pure stable merge correctness.  It simultaneously
exports sorted keys, the shared occurrence-stability predicate, and a
permutation of complete key/payload entries. -/
theorem stableEntryMerge_correct
    {lt : BoolComparator alpha} (horder : BoolStrictWeakOrder lt)
    (canonical : List (Occurrence alpha))
    (left right : List (SortSliceEntry (Occurrence alpha) nu))
    (hleft : (left.map SortSliceEntry.key).Pairwise
      (DescendingRunSpec.SortedRelation lt))
    (hright : (right.map SortSliceEntry.key).Pairwise
      (DescendingRunSpec.SortedRelation lt))
    (hstable : StableOccurrencePermutation lt canonical
      (left.map SortSliceEntry.key ++ right.map SortSliceEntry.key)) :
    ((stableEntryMerge lt left right).map SortSliceEntry.key).Pairwise
        (DescendingRunSpec.SortedRelation lt) ∧
      StableOccurrencePermutation lt canonical
        ((stableEntryMerge lt left right).map SortSliceEntry.key) ∧
      (stableEntryMerge lt left right).Perm (left ++ right) := by
  rw [stableEntryMerge_keys]
  rcases stableOccurrenceMerge_correct horder canonical
      (left.map SortSliceEntry.key) (right.map SortSliceEntry.key)
      hleft hright hstable with ⟨hsorted, hstableOut⟩
  exact ⟨hsorted, hstableOut, stableEntryMerge_perm_append lt left right⟩

/-! ## Suffix decomposition for the backward implementation -/

/-- A block whose every entry is strictly after every right-run entry can be
peeled from the end of the left input and appended unchanged after the merge.
The statement is deliberately whole-entry and does not require decidable
equality, so `merge_hi` can apply it directly to galloped payload blocks. -/
theorem stableEntryMerge_append_left_block
    (lt : BoolComparator alpha)
    (suffix : List (SortSliceEntry (Occurrence alpha) nu)) :
    ∀ (left right : List (SortSliceEntry (Occurrence alpha) nu)),
      (∀ rightEntry ∈ right, ∀ suffixEntry ∈ suffix,
        lt rightEntry.key.value suffixEntry.key.value = true) →
      stableEntryMerge lt (left ++ suffix) right =
        stableEntryMerge lt left right ++ suffix
  | [], [], _ => by simp [stableEntryMerge]
  | [], rightHead :: right, hafter => by
      cases suffix with
      | nil => simp [stableEntryMerge]
      | cons suffixHead suffixTail =>
          have hstrict :
              lt rightHead.key.value suffixHead.key.value = true :=
            hafter rightHead (by simp) suffixHead (by simp)
          have htail :
              ∀ rightEntry ∈ right,
                ∀ suffixEntry ∈ suffixHead :: suffixTail,
                  lt rightEntry.key.value suffixEntry.key.value = true := by
            intro rightEntry hright suffixEntry hsuffix
            exact hafter rightEntry (by simp [hright]) suffixEntry hsuffix
          simp only [List.nil_append]
          unfold stableEntryMerge
          rw [List.cons_merge_cons]
          have hnot :
              ¬stableEntryLE lt suffixHead rightHead = true := by
            simp [stableEntryLE, stableOccurrenceLE, hstrict]
          rw [if_neg hnot]
          have ih := stableEntryMerge_append_left_block lt
            (suffixHead :: suffixTail) [] right htail
          simpa [stableEntryMerge] using congrArg (List.cons rightHead) ih
  | leftHead :: left, [], _ => by simp [stableEntryMerge]
  | leftHead :: left, rightHead :: right, hafter => by
      have hleft :
          ∀ rightEntry ∈ rightHead :: right, ∀ suffixEntry ∈ suffix,
            lt rightEntry.key.value suffixEntry.key.value = true := hafter
      have hright :
          ∀ rightEntry ∈ right, ∀ suffixEntry ∈ suffix,
            lt rightEntry.key.value suffixEntry.key.value = true := by
        intro rightEntry hmem suffixEntry hsuffix
        exact hafter rightEntry (by simp [hmem]) suffixEntry hsuffix
      simp only [List.cons_append]
      unfold stableEntryMerge
      rw [List.cons_merge_cons, List.cons_merge_cons]
      by_cases hchoose : stableEntryLE lt leftHead rightHead = true
      · simp only [hchoose, ↓reduceIte, List.cons_append]
        have ih := stableEntryMerge_append_left_block lt suffix left
          (rightHead :: right) hleft
        simpa [stableEntryMerge] using congrArg (List.cons leftHead) ih
      · simp only [hchoose]
        have ih := stableEntryMerge_append_left_block lt suffix
          (leftHead :: left) right hright
        simpa [stableEntryMerge] using congrArg (List.cons rightHead) ih
termination_by left right => left.length + right.length

/-- One-cell form of `stableEntryMerge_append_left_block`, used by the
ordinary backward A branch. -/
theorem stableEntryMerge_snoc_left_of_all_right_lt
    (lt : BoolComparator alpha)
    (left right : List (SortSliceEntry (Occurrence alpha) nu))
    (lastLeft : SortSliceEntry (Occurrence alpha) nu)
    (hafter : ∀ rightEntry ∈ right,
      lt rightEntry.key.value lastLeft.key.value = true) :
    stableEntryMerge lt (left ++ [lastLeft]) right =
      stableEntryMerge lt left right ++ [lastLeft] := by
  apply stableEntryMerge_append_left_block lt [lastLeft] left right
  intro rightEntry hright suffixEntry hsuffix
  simp only [List.mem_singleton] at hsuffix
  subst suffixEntry
  exact hafter rightEntry hright

/-- One-cell form of `stableEntryMerge_append_right_block`, used by the
ordinary backward B/equality branch. -/
theorem stableEntryMerge_snoc_right_of_all_not_lt
    (lt : BoolComparator alpha)
    (left right : List (SortSliceEntry (Occurrence alpha) nu))
    (lastRight : SortSliceEntry (Occurrence alpha) nu)
    (hafter : ∀ leftEntry ∈ left,
      lt lastRight.key.value leftEntry.key.value = false) :
    stableEntryMerge lt left (right ++ [lastRight]) =
      stableEntryMerge lt left right ++ [lastRight] := by
  apply stableEntryMerge_append_right_block lt [lastRight] left right
  intro leftEntry hleft suffixEntry hsuffix
  simp only [List.mem_singleton] at hsuffix
  subst suffixEntry
  exact hafter leftEntry hleft

/-- Lift a strict comparison from the final element of a sorted right run to
every entry of that run.  This packages the exact order algebra needed by an
A-suffix gallop in the backward merge. -/
theorem all_right_lt_suffix_of_pairwise_of_last_lt
    {lt : BoolComparator alpha} (horder : BoolStrictWeakOrder lt)
    (right suffix : List (SortSliceEntry (Occurrence alpha) nu))
    (hrightNe : right ≠ [])
    (hright : right.Pairwise (fun earlier later =>
      lt later.key.value earlier.key.value = false))
    (hboundary : ∀ suffixEntry ∈ suffix,
      lt (right.getLast hrightNe).key.value suffixEntry.key.value = true) :
    ∀ rightEntry ∈ right, ∀ suffixEntry ∈ suffix,
      lt rightEntry.key.value suffixEntry.key.value = true := by
  intro rightEntry hrightMem suffixEntry hsuffix
  have hlastNotBefore :
      lt (right.getLast hrightNe).key.value rightEntry.key.value = false := by
    apply hright.rel_getLast_of_rel_getLast_getLast hrightMem
    exact Bool.eq_false_iff.mpr
      (horder.irrefl (right.getLast hrightNe).key.value)
  exact horder.strict_of_not_reverse_of_strict hlastNotBefore
    (hboundary suffixEntry hsuffix)

/-- Lift a non-strict comparison against the final element of a sorted left
run to every earlier left entry.  Comparator-equivalent right suffix entries
therefore remain after all equivalent left entries. -/
theorem all_suffix_not_lt_left_of_pairwise_of_not_lt_last
    {lt : BoolComparator alpha} (horder : BoolStrictWeakOrder lt)
    (left suffix : List (SortSliceEntry (Occurrence alpha) nu))
    (hleftNe : left ≠ [])
    (hleft : left.Pairwise (fun earlier later =>
      lt later.key.value earlier.key.value = false))
    (hboundary : ∀ suffixEntry ∈ suffix,
      lt suffixEntry.key.value (left.getLast hleftNe).key.value = false) :
    ∀ leftEntry ∈ left, ∀ suffixEntry ∈ suffix,
      lt suffixEntry.key.value leftEntry.key.value = false := by
  intro leftEntry hleftMem suffixEntry hsuffix
  have hlastNotBefore :
      lt (left.getLast hleftNe).key.value leftEntry.key.value = false := by
    apply hleft.rel_getLast_of_rel_getLast_getLast hleftMem
    exact Bool.eq_false_iff.mpr
      (horder.irrefl (left.getLast hleftNe).key.value)
  apply Bool.eq_false_iff.mpr
  intro hsuffixLeft
  have hsuffixLast := horder.strict_of_strict_of_not_reverse hsuffixLeft
    hlastNotBefore
  have hnot :
      ¬lt suffixEntry.key.value (left.getLast hleftNe).key.value = true := by
    simp [hboundary suffixEntry hsuffix]
  exact hnot hsuffixLast

/-! ## Tie-direction and payload regressions -/

private def decadeLt (left right : Nat) : Bool :=
  decide (left / 10 < right / 10)

private def stableMergeLeftEquivalentEntry :
    SortSliceEntry (Occurrence Nat) Nat :=
  { key := { value := 11, origin := 3 }, value := some 110 }

private def stableMergeRightEquivalentEntry :
    SortSliceEntry (Occurrence Nat) Nat :=
  { key := { value := 19, origin := 8 }, value := some 190 }

/-- Anti-vacuity regression for the actual stability notion: the values are
unequal but comparator-equivalent.  The shared merge still selects the left
occurrence first and carries both payloads with their keys. -/
theorem stableEntryMerge_equivalent_unequal_left_first_regression :
    stableMergeLeftEquivalentEntry.key.value ≠
        stableMergeRightEquivalentEntry.key.value ∧
      ComparatorEquivalent decadeLt
        stableMergeLeftEquivalentEntry.key.value
        stableMergeRightEquivalentEntry.key.value ∧
      stableEntryMerge decadeLt [stableMergeLeftEquivalentEntry]
          [stableMergeRightEquivalentEntry] =
        [stableMergeLeftEquivalentEntry, stableMergeRightEquivalentEntry] := by
  constructor
  · decide
  constructor
  · norm_num [ComparatorEquivalent, decadeLt,
      stableMergeLeftEquivalentEntry, stableMergeRightEquivalentEntry]
  · simp [stableEntryMerge, stableEntryLE, stableOccurrenceLE, decadeLt,
      stableMergeLeftEquivalentEntry, stableMergeRightEquivalentEntry]

private def stableMergeLargerEntry : SortSliceEntry (Occurrence Nat) Nat :=
  { key := { value := 21, origin := 1 }, value := some 210 }

private def stableMergeSmallerEntry : SortSliceEntry (Occurrence Nat) Nat :=
  { key := { value := 11, origin := 7 }, value := some 110 }

/-- A genuinely smaller right head takes the other branch, distinguishing the
stable-equality rule from an implementation that always selects the left. -/
theorem stableEntryMerge_strict_right_first_regression :
    stableEntryMerge decadeLt [stableMergeLargerEntry]
        [stableMergeSmallerEntry] =
      [stableMergeSmallerEntry, stableMergeLargerEntry] := by
  simp [stableEntryMerge, stableEntryLE, stableOccurrenceLE, decadeLt,
    stableMergeLargerEntry, stableMergeSmallerEntry]

end CPythonListsort
