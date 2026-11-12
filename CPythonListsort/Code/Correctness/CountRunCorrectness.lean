/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.CountRunSafety
import Code.Assembly.Order
import Code.Correctness.ReverseSliceCorrectness
import Code.Correctness.SortSliceRange
import Code.Correctness.DescendingRunNormalization
import Code.Correctness.DescendingRunInvariant
import Code.Correctness.ReverseRangeSupport
import Code.Correctness.ScanRemainder

/-!
# Functional correctness of `count_run`

This file proves that the actual bounded `countRun?` transcription returns a
nonempty sorted run, preserves whole key/payload entries, and preserves the
origin order of comparator-equivalent occurrences.  The public theorem is
tied to `countRunTraced?` through the reviewed `countRun_safe` exact-erasure
certificate; no second run detector is substituted for the transcribed one.

The descending case follows CPython's two-level reversal literally.  Equal
blocks are reversed as the scan discovers them, the final equal block is
reversed at the boundary, and then the complete descending prefix is
reversed.  Thus the temporary order inside equal blocks is not exposed by the
public postcondition.
-/

namespace CPythonListsort

universe u v w x

variable {alpha : Type u} {nu : Type v}
variable {beta : Type w} {rho : Type x}

/-- The input-side condition needed for occurrence stability: within the
remaining source range, comparator-equivalent occurrences already appear in
increasing origin order.  The permutation half is deliberately the reflexive
one, so this is the shared `StableOccurrencePermutation` predicate rather
than a weaker local surrogate. -/
def CountRunCanonicalRange (lt : BoolComparator alpha)
    (slice : SortSlice (Occurrence alpha) nu) (base count : Nat) : Prop :=
  let canonical := (sortSliceRangeKeys slice base count).toList
  StableOccurrencePermutation lt canonical canonical

/-- Absolute-origin canonical segments are stable relative to themselves,
independently of the comparator: list order is strictly increasing origin
order before any sorting operation runs. -/
theorem canonicalOccurrenceSegment_countRunCanonical
    (lt : BoolComparator alpha) (input : Array alpha)
    (base count : Nat) :
    StableOccurrencePermutation lt
      (canonicalOccurrenceSegment input base count)
      (canonicalOccurrenceSegment input base count) := by
  refine ⟨List.Perm.refl _, ?_⟩
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij _
  simp [canonicalOccurrenceSegment, tagOccurrences] at hi hj ⊢
  omega

/-- The top-level unscanned-suffix invariant discharges the canonical-origin
premise of `countRun_correct` at the exact call range.  Thus callers do not
assume occurrence stability independently of the scan induction. -/
theorem ScanRemainderMatches.countRunCanonicalRange
    {lt : BoolComparator alpha} {input : Array alpha}
    {state : MergeState (Occurrence alpha) nu} {scanned : Nat}
    (h : ScanRemainderMatches input state scanned) :
    CountRunCanonicalRange lt state.data (state.basekeys + scanned)
      (state.listlen.toNat - scanned) := by
  unfold CountRunCanonicalRange
  rw [h.keys_eq]
  exact canonicalOccurrenceSegment_countRunCanonical lt input
    (state.basekeys + scanned) (state.listlen.toNat - scanned)

/-- Whole-entry unscanned agreement supplies the same canonical-origin
premise through its exact key-projection bridge. -/
theorem ScanRemainderEntriesMatch.countRunCanonicalRange
    {lt : BoolComparator alpha} {source : SortSlice alpha nu}
    {state : MergeState (Occurrence alpha) nu} {scanned : Nat}
    (h : ScanRemainderEntriesMatch source state scanned) :
    CountRunCanonicalRange lt state.data (state.basekeys + scanned)
      (state.listlen.toNat - scanned) :=
  h.toScanRemainderMatches.countRunCanonicalRange

/-- Public semantic packet for one successful invocation of `count_run`.

`entryPermutation` mentions whole key/payload entries.  `stable` separately
mentions the occurrence-carrying key projection.  `frame` uses the shared
range-frame vocabulary consumed by run-formation correctness. -/
structure CountRunCorrectnessPost
    (lt : BoolComparator alpha)
    (state : MergeState (Occurrence alpha) nu)
    (before : SortSlice (Occurrence alpha) nu)
    (base : Int) (nremaining : Nat)
    (result : CountRunResult (Occurrence alpha) nu) : Prop where
  safety : CountRunSafetyPost state before base nremaining result
  lengthBounds : 1 <= result.length ∧ result.length <= nremaining
  minimumLength : nremaining = 1 ∨ 2 ≤ result.length
  sorted :
    Sorted (occurrenceComparator lt)
      (sortSliceRangeKeys result.slice base.toNat result.length)
  stable :
    StableOccurrencePermutation lt
      (sortSliceRangeKeys before base.toNat result.length).toList
      (sortSliceRangeKeys result.slice base.toNat result.length).toList
  entryPermutation :
    (sortSliceRangeEntries result.slice base.toNat result.length).toList.Perm
      (sortSliceRangeEntries before base.toNat result.length).toList
  frame :
    SortSlice.EqualOutsideRange before result.slice base.toNat result.length

/-- The functional part of `CountRunCorrectnessPost`, separated internally so
it can be established from the raw evaluator before the traced safety witness
is identified through exact erasure. -/
private structure CountRunSemanticPost
    (lt : BoolComparator alpha)
    (before : SortSlice (Occurrence alpha) nu)
    (start nremaining : Nat)
    (result : CountRunResult (Occurrence alpha) nu) : Prop where
  fuel : result.fuelExhausted = false
  lengthBounds : 1 ≤ result.length ∧ result.length ≤ nremaining
  minimumLength : nremaining = 1 ∨ 2 ≤ result.length
  sorted :
    Sorted (occurrenceComparator lt)
      (sortSliceRangeKeys result.slice start result.length)
  stable :
    StableOccurrencePermutation lt
      (sortSliceRangeKeys before start result.length).toList
      (sortSliceRangeKeys result.slice start result.length).toList
  entryPermutation :
    (sortSliceRangeEntries result.slice start result.length).toList.Perm
      (sortSliceRangeEntries before start result.length).toList
  frame :
    SortSlice.EqualOutsideRange before result.slice start result.length

private theorem occurrenceComparator_false_trans
    {lt : BoolComparator alpha} (horder : BoolStrictWeakOrder lt)
    {a b c : Occurrence alpha}
    (hab : occurrenceComparator lt b a = false)
    (hbc : occurrenceComparator lt c b = false) :
    occurrenceComparator lt c a = false :=
  horder.false_trans hab hbc

private theorem pairwise_append_singleton_of_last
    {R : beta -> beta -> Prop} {xs : List beta} {x : beta}
    (htrans : forall {a b c}, R a b -> R b c -> R a c)
    (hrefl : forall a, R a a)
    (hxs : xs.Pairwise R) (hne : xs ≠ [])
    (hlast : R (xs.getLast hne) x) :
    (xs ++ [x]).Pairwise R := by
  rw [List.pairwise_append]
  refine ⟨hxs, by simp, ?_⟩
  intro a ha b hb
  simp only [List.mem_singleton] at hb
  subst b
  exact htrans
    (hxs.rel_getLast_of_rel_getLast_getLast ha (hrefl _)) hlast

private theorem sortSliceRangeEntries_succ
    (slice : SortSlice beta rho) (start count : Nat)
    (hstop : start + (count + 1) <= slice.entries.size) :
    (sortSliceRangeEntries slice start (count + 1)).toList =
      (sortSliceRangeEntries slice start count).toList ++
        [slice.entries[start + count]] := by
  rw [sortSliceRangeEntries_toList, sortSliceRangeEntries_toList]
  have hindex : count < (slice.entries.toList.drop start).length := by
    simp
    omega
  symm
  simpa [List.getElem_drop] using
    List.take_concat_get' (slice.entries.toList.drop start) count hindex

private theorem sortSliceRangeKeys_succ
    (slice : SortSlice beta rho) (start count : Nat)
    (hstop : start + (count + 1) <= slice.entries.size) :
    (sortSliceRangeKeys slice start (count + 1)).toList =
      (sortSliceRangeKeys slice start count).toList ++
        [slice.entries[start + count].key] := by
  simp only [sortSliceRangeKeys_toList]
  rw [show ((slice.entries.toList.drop start).take (count + 1)).map
      SortSliceEntry.key =
      (((slice.entries.toList.drop start).take count) ++
        [slice.entries[start + count]]).map SortSliceEntry.key by
    rw [← sortSliceRangeEntries_toList, sortSliceRangeEntries_succ slice start count hstop]
    rw [sortSliceRangeEntries_toList]]
  simp

@[simp]
private theorem sortSlice_read_nat
    (slice : SortSlice beta rho) (index : Nat)
    (hindex : index < slice.entries.size) :
    slice.read? (Int.ofNat index) = some slice.entries[index] := by
  simp [SortSlice.read?, Array.getElem?_eq_getElem hindex]

private structure AscendingCorrectnessPost
    (lt : BoolComparator alpha)
    (slice : SortSlice (Occurrence alpha) nu)
    (start n nremaining : Nat)
    (result : AscendingScanResult) : Prop where
  fuel : result.fuelExhausted = false
  lengthBounds : n ≤ result.length ∧ result.length ≤ nremaining
  sorted :
    Sorted (occurrenceComparator lt)
      (sortSliceRangeKeys slice start result.length)
  stoppedByDecrease :
    result.length < nremaining ->
      ∃ previous next,
        slice.read? (Int.ofNat start + Int.ofNat (result.length - 1)) =
            some previous ∧
          slice.read? (Int.ofNat start + Int.ofNat result.length) =
            some next ∧
          occurrenceComparator lt next.key previous.key = true

private theorem ascendingScan_correct
    (lt : BoolComparator alpha) (horder : BoolStrictWeakOrder lt)
    (slice : SortSlice (Occurrence alpha) nu)
    (start nremaining n fuel : Nat)
    (hstop : start + nremaining ≤ slice.entries.size)
    (hnpos : 0 < n) (hnle : n ≤ nremaining)
    (hfuel : nremaining - n ≤ fuel)
    (hsorted :
      Sorted (occurrenceComparator lt)
        (sortSliceRangeKeys slice start n)) :
    ∃ result,
      ascendingScan? fuel (occurrenceComparator lt) slice
          (Int.ofNat start) nremaining n = some result ∧
        AscendingCorrectnessPost lt slice start n nremaining result := by
  induction fuel generalizing n with
  | zero =>
      have hnremaining : nremaining ≤ n := by omega
      have hn : n = nremaining := by omega
      let result : AscendingScanResult :=
        { length := n, fuelExhausted := decide (n < nremaining) }
      refine ⟨result, ?_, ?_⟩
      · simp [ascendingScan?, result]
      · refine
          { fuel := by simp [result, hn]
            lengthBounds := by simp [result, hn]
            sorted := by simpa [result] using hsorted
            stoppedByDecrease := ?_ }
        simp [result, hn]
  | succ fuel ih =>
      by_cases hactive : n < nremaining
      · have hprevious : start + (n - 1) < slice.entries.size := by omega
        have hnext : start + n < slice.entries.size := by omega
        let previous := slice.entries[start + (n - 1)]
        let next := slice.entries[start + n]
        have hpreviousRead :
            slice.read? (Int.ofNat start + Int.ofNat (n - 1)) =
              some previous := by
          simpa using
            sortSlice_read_nat slice (start + (n - 1)) hprevious
        have hnextRead :
            slice.read? (Int.ofNat start + Int.ofNat n) = some next := by
          simpa using sortSlice_read_nat slice (start + n) hnext
        by_cases hdecrease :
            occurrenceComparator lt next.key previous.key = true
        · let result : AscendingScanResult :=
            { length := n, fuelExhausted := false }
          refine ⟨result, ?_, ?_⟩
          · simp only [ascendingScan?, hactive, if_pos]
            rw [hpreviousRead, hnextRead]
            simp [countRunBindOptionAcross, iflt, hdecrease, result]
          · refine
              { fuel := rfl
                lengthBounds := ⟨le_rfl, hnle⟩
                sorted := hsorted
                stoppedByDecrease := ?_ }
            intro _
            exact ⟨previous, next, by simpa [result] using hpreviousRead,
              by simpa [result] using hnextRead,
              by simpa [result] using hdecrease⟩
        · have hrelation :
              occurrenceComparator lt next.key previous.key = false := by
            exact Bool.eq_false_iff.mpr hdecrease
          have hrangeSucc : start + (n + 1) ≤ slice.entries.size := by omega
          have hkeysSucc := sortSliceRangeKeys_succ slice start n hrangeSucc
          have hkeysSize :
              (sortSliceRangeKeys slice start n).toList.length = n := by
            simpa using
              sortSliceRangeKeys_size slice start n (by omega)
          have hkeysNonempty :
              (sortSliceRangeKeys slice start n).toList ≠ [] := by
            intro hempty
            rw [hempty] at hkeysSize
            simp at hkeysSize
            omega
          have hlast :
              (sortSliceRangeKeys slice start n).toList.getLast hkeysNonempty =
                previous.key := by
            have hcurrent := sortSliceRangeKeys_succ slice start (n - 1)
              (by omega : start + (n - 1 + 1) ≤ slice.entries.size)
            have hn : n - 1 + 1 = n := by omega
            have hcurrent' :
                (sortSliceRangeKeys slice start n).toList =
                  (sortSliceRangeKeys slice start (n - 1)).toList ++
                    [slice.entries[start + (n - 1)].key] := by
              simpa only [hn] using hcurrent
            have hlastOption :
                (sortSliceRangeKeys slice start n).toList.getLast? =
                  some previous.key := by
              rw [hcurrent']
              simp [previous]
            rw [List.getLast?_eq_getLast_of_ne_nil hkeysNonempty] at hlastOption
            exact Option.some.inj hlastOption
          have hrefl : ∀ x : Occurrence alpha,
              occurrenceComparator lt x x = false := by
            intro x
            exact Bool.eq_false_iff.mpr (horder.irrefl x.value)
          have hsortedSucc :
              Sorted (occurrenceComparator lt)
                (sortSliceRangeKeys slice start (n + 1)) := by
            unfold Sorted at hsorted ⊢
            rw [hkeysSucc]
            apply pairwise_append_singleton_of_last
              (R := fun earlier later : Occurrence alpha =>
                occurrenceComparator lt later earlier = false)
              (fun hab hbc => occurrenceComparator_false_trans horder hab hbc)
              hrefl hsorted hkeysNonempty
            rw [hlast]
            exact hrelation
          have hfuel' : nremaining - (n + 1) ≤ fuel := by omega
          rcases ih (n + 1) (by omega) (by omega) hfuel' hsortedSucc with
            ⟨result, hresult, hpost⟩
          refine ⟨result, ?_, ?_⟩
          · simp only [ascendingScan?, hactive, if_pos]
            rw [hpreviousRead, hnextRead]
            simp only [countRunBindOptionAcross, iflt, hdecrease]
            exact hresult
          · exact
              { fuel := hpost.fuel
                lengthBounds := ⟨le_trans (by omega) hpost.lengthBounds.1,
                  hpost.lengthBounds.2⟩
                sorted := hpost.sorted
                stoppedByDecrease := hpost.stoppedByDecrease }
      · have hnremaining : nremaining ≤ n := Nat.le_of_not_gt hactive
        have hn : n = nremaining := by omega
        let result : AscendingScanResult :=
          { length := n, fuelExhausted := false }
        refine ⟨result, ?_, ?_⟩
        · simp [ascendingScan?, hactive, result]
        · refine
            { fuel := rfl
              lengthBounds := by simp [result, hn]
              sorted := by simpa [result] using hsorted
              stoppedByDecrease := ?_ }
          simp [result, hn]

private theorem List.take_add_eq (xs : List beta) (first second : Nat) :
    xs.take (first + second) =
      xs.take first ++ (xs.drop first).take second := by
  induction first generalizing xs with
  | zero => simp
  | succ first ih =>
      cases xs with
      | nil => simp
      | cons x xs =>
          simpa only [Nat.succ_add, List.take_succ_cons, List.drop_succ_cons,
            List.cons_append] using congrArg (List.cons x) (ih xs)

private theorem sortSliceRangeEntries_add
    (slice : SortSlice beta rho) (start first second : Nat) :
    (sortSliceRangeEntries slice start (first + second)).toList =
      (sortSliceRangeEntries slice start first).toList ++
        (sortSliceRangeEntries slice (start + first) second).toList := by
  simp only [sortSliceRangeEntries_toList]
  rw [List.take_add_eq]
  rw [List.drop_drop]

private theorem reverseRange_suffix_rangeEntries
    (slice : SortSlice beta rho) (start count tail : Nat)
    (htail : tail ≤ count)
    (hstop : start + count ≤ slice.entries.size) :
    (sortSliceRangeEntries
        ({ entries := ReverseRangeSpec.reverseRangeEntries slice.entries
            (start + count - tail) (start + count) } : SortSlice beta rho)
        start count).toList =
      DescendingRunSpec.reverseSuffix
        (sortSliceRangeEntries slice start count).toList tail := by
  let prefixCount := count - tail
  have hsplit : prefixCount + tail = count := by
    simp [prefixCount, Nat.sub_add_cancel htail]
  have hreverseStart : start + count - tail = start + prefixCount := by
    simp [prefixCount]
    omega
  let after : SortSlice beta rho :=
    { entries := ReverseRangeSpec.reverseRangeEntries slice.entries
        (start + prefixCount) (start + prefixCount + tail) }
  have hlocalStop : start + prefixCount + tail ≤ slice.entries.size := by
    omega
  have hframe := ReverseRangeSpec.equalOutsideRange_reverseRange slice
    (start + prefixCount) tail hlocalStop
  have hprefix :
      sortSliceRangeEntries after start prefixCount =
        sortSliceRangeEntries slice start prefixCount := by
    exact (hframe.entries_eq_of_disjoint start prefixCount (Or.inl (by omega))).symm
  have hsuffix :
      sortSliceRangeEntries after (start + prefixCount) tail =
        (sortSliceRangeEntries slice (start + prefixCount) tail).reverse := by
    exact ReverseRangeSpec.sortSliceRangeEntries_reverseRange_self slice
      (start + prefixCount) tail hlocalStop
  have houterBefore := sortSliceRangeEntries_add slice start prefixCount tail
  have houterAfter := sortSliceRangeEntries_add after start prefixCount tail
  have hafterSize : after.entries.size = slice.entries.size := by
    exact (ReverseRangeSpec.size_reverseRange slice.entries
      (start + prefixCount) (start + prefixCount + tail)
      (by omega) hlocalStop)
  rw [hsplit] at houterBefore houterAfter
  have hselectedSize :
      (sortSliceRangeEntries slice start count).toList.length = count := by
    simpa using sortSliceRangeEntries_size slice start count hstop
  have hsuffixLength :
      (sortSliceRangeEntries slice (start + prefixCount) tail).toList.length =
        tail := by
    simpa using sortSliceRangeEntries_size slice (start + prefixCount) tail
      hlocalStop
  rw [hreverseStart]
  have hend : start + count = start + prefixCount + tail := by omega
  rw [hend]
  change (sortSliceRangeEntries after start count).toList = _
  rw [houterAfter, hprefix, hsuffix]
  rw [houterBefore]
  have hprefixLength :
      (sortSliceRangeEntries slice start prefixCount).toList.length =
        prefixCount := by
    simpa using sortSliceRangeEntries_size slice start prefixCount (by omega)
  simp [DescendingRunSpec.reverseSuffix, hprefixLength, hsuffixLength,
    prefixCount, htail]

private theorem SortSlice.EqualOutsideRange.widen_count
    {before after : SortSlice beta rho} {start small large : Nat}
    (hframe : SortSlice.EqualOutsideRange before after start small)
    (hle : small ≤ large) :
    SortSlice.EqualOutsideRange before after start large := by
  refine ⟨hframe.size_eq, ?_⟩
  intro otherStart otherCount hdisjoint
  apply hframe.entries_eq_of_disjoint otherStart otherCount
  rcases hdisjoint with hbefore | hafter
  · exact Or.inl hbefore
  · exact Or.inr (by omega)

private theorem equalOutsideRange_reverse_inside
    (slice : SortSlice beta rho) (start count offset subcount : Nat)
    (hoffset : offset + subcount ≤ count)
    (hstop : start + count ≤ slice.entries.size) :
    SortSlice.EqualOutsideRange slice
      ({ entries := ReverseRangeSpec.reverseRangeEntries slice.entries
          (start + offset) (start + offset + subcount) } : SortSlice beta rho)
      start count := by
  have hlocalStop : start + offset + subcount ≤ slice.entries.size := by omega
  have hlocal := ReverseRangeSpec.equalOutsideRange_reverseRange slice
    (start + offset) subcount hlocalStop
  refine ⟨hlocal.size_eq, ?_⟩
  intro otherStart otherCount hdisjoint
  apply hlocal.entries_eq_of_disjoint otherStart otherCount
  rcases hdisjoint with hbefore | hafter
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

private theorem DescendingRunSpec.reverseSuffix_one_of_ne_nil
    (xs : List beta) (hne : xs ≠ []) :
    DescendingRunSpec.reverseSuffix xs 1 = xs := by
  unfold DescendingRunSpec.reverseSuffix
  rw [List.drop_length_sub_one hne]
  simp only [List.reverse_singleton]
  have hlast := List.dropLast_append_getLast hne
  simpa only [List.dropLast_eq_take] using hlast

private structure ReverseLastEqualCorrectnessPost
    (before : SortSlice beta rho) (start n neq : Nat)
    (result : ReverseEqualResult beta rho) : Prop where
  resultEq :
    reverseLastEqual? before (Int.ofNat start) n neq = some result
  fuel : result.fuelExhausted = false
  entries :
    (sortSliceRangeEntries result.slice start n).toList =
      DescendingRunSpec.reverseSuffix
        (sortSliceRangeEntries before start n).toList (neq + 1)
  keys :
    (sortSliceRangeKeys result.slice start n).toList =
      DescendingRunSpec.reverseSuffix
        (sortSliceRangeKeys before start n).toList (neq + 1)
  frame : SortSlice.EqualOutsideRange before result.slice start n

private theorem reverseLastEqual_correct
    (slice : SortSlice beta rho) (start n neq : Nat)
    (htail : neq + 1 ≤ n)
    (hstop : start + n ≤ slice.entries.size) :
    ∃ result,
      ReverseLastEqualCorrectnessPost slice start n neq result := by
  by_cases hzero : neq = 0
  · subst neq
    let result : ReverseEqualResult beta rho :=
      { slice := slice, fuelExhausted := false }
    refine ⟨result, ?_, rfl, ?_, ?_, SortSlice.EqualOutsideRange.refl _ _ _⟩
    · simp [reverseLastEqual?, result]
    · simp only [result]
      symm
      simpa only [Nat.zero_add] using
        DescendingRunSpec.reverseSuffix_one_of_ne_nil
          (sortSliceRangeEntries slice start n).toList (by
            have hsize := sortSliceRangeEntries_size slice start n hstop
            have hlength :
                (sortSliceRangeEntries slice start n).toList.length = n := by
              simpa using hsize
            intro hempty
            rw [hempty] at hlength
            simp at hlength
            omega)
    · simp only [result]
      symm
      simpa only [Nat.zero_add] using
        DescendingRunSpec.reverseSuffix_one_of_ne_nil
          (sortSliceRangeKeys slice start n).toList (by
            have hsize := sortSliceRangeKeys_size slice start n hstop
            have hlength :
                (sortSliceRangeKeys slice start n).toList.length = n := by
              simpa using hsize
            intro hempty
            rw [hempty] at hlength
            simp at hlength
            omega)
  · have hneqPos : 0 < neq := Nat.pos_of_ne_zero hzero
    have htailPos : 0 < neq + 1 := by omega
    have hreverseStart :
        Int.ofNat start + Int.ofNat n - Int.ofNat (neq + 1) =
          Int.ofNat (start + n - (neq + 1)) := by
      simp only [Int.ofNat_eq_natCast]
      omega
    have hlocalRange : SortSlice.RangeInBounds slice
        (Int.ofNat (start + n - (neq + 1))) (neq + 1) := by
      constructor
      · exact Int.natCast_nonneg _
      · simp only [Int.ofNat_eq_natCast]
        omega
    rcases sortsliceReverse_correct slice
        (Int.ofNat (start + n - (neq + 1))) (neq + 1) hlocalRange with
      ⟨reversed, hreversed, hfuel, hentries⟩
    let result : ReverseEqualResult beta rho :=
      { slice := reversed.slice, fuelExhausted := reversed.fuelExhausted }
    have hsliceEq : reversed.slice =
        ({ entries := ReverseRangeSpec.reverseRangeEntries slice.entries
            (start + n - (neq + 1)) (start + n) } : SortSlice beta rho) := by
      have hentries' := hentries
      change reversed.slice.entries =
        ReverseRangeSpec.reverseRangeEntries slice.entries
          (start + n - (neq + 1))
          (start + n - (neq + 1) + (neq + 1)) at hentries'
      have hend : start + n - (neq + 1) + (neq + 1) = start + n := by
        omega
      rw [hend] at hentries'
      apply congrArg SortSlice.mk
      exact hentries'
    have hselectedEntries :
        (sortSliceRangeEntries reversed.slice start n).toList =
          DescendingRunSpec.reverseSuffix
            (sortSliceRangeEntries slice start n).toList (neq + 1) := by
      rw [hsliceEq]
      exact reverseRange_suffix_rangeEntries slice start n (neq + 1)
        htail hstop
    have hselectedKeys :
        (sortSliceRangeKeys reversed.slice start n).toList =
            DescendingRunSpec.reverseSuffix
            (sortSliceRangeKeys slice start n).toList (neq + 1) := by
      simp only [sortSliceRangeKeys, Array.toList_map]
      rw [hselectedEntries]
      simp [DescendingRunSpec.reverseSuffix]
    have hframe : SortSlice.EqualOutsideRange slice reversed.slice start n := by
      have hstartEq : start + n - (neq + 1) =
          start + (n - (neq + 1)) := by omega
      let mathematical : SortSlice beta rho :=
        { entries := ReverseRangeSpec.reverseRangeEntries slice.entries
            (start + n - (neq + 1)) (start + n) }
      have hmathematical :
          SortSlice.EqualOutsideRange slice mathematical start n := by
        have hinside := equalOutsideRange_reverse_inside slice start n
          (n - (neq + 1)) (neq + 1) (by omega) hstop
        change SortSlice.EqualOutsideRange slice
          ({ entries := ReverseRangeSpec.reverseRangeEntries slice.entries
              (start + n - (neq + 1)) (start + n) } : SortSlice beta rho)
          start n
        convert hinside using 1
        rw [hstartEq]
        congr 2
        omega
      have hequal :
          SortSlice.EqualOutsideRange mathematical reversed.slice start n :=
        SortSlice.EqualOutsideRange.of_eq hsliceEq.symm start n
      exact hmathematical.trans hequal
    refine ⟨result, ?_, ?_, ?_, ?_, ?_⟩
    · unfold reverseLastEqual?
      rw [if_neg hzero]
      simp only [hreverseStart]
      rw [hreversed]
      rfl
    · exact hfuel
    · exact hselectedEntries
    · exact hselectedKeys
    · exact hframe

private theorem sortSliceRangeEntries_one
    (slice : SortSlice beta rho) (index : Nat)
    (hindex : index < slice.entries.size) :
    sortSliceRangeEntries slice index 1 = #[slice.entries[index]] := by
  apply Array.toList_inj.mp
  rw [sortSliceRangeEntries_toList]
  have hdrop := List.drop_eq_getElem_cons
    (l := slice.entries.toList) (i := index) (by simpa using hindex)
  rw [hdrop]
  simp

private theorem SortSlice.EqualOutsideRange.next_entry
    {before after : SortSlice beta rho} {start count : Nat}
    (hframe : SortSlice.EqualOutsideRange before after start count)
    (hindex : start + count < before.entries.size) :
    after.entries[start + count]'(by simpa [hframe.size_eq] using hindex) =
      before.entries[start + count] := by
  have hrange := hframe.entries_eq_of_disjoint (start + count) 1
    (Or.inr le_rfl)
  rw [sortSliceRangeEntries_one before (start + count) hindex] at hrange
  have hindexAfter : start + count < after.entries.size := by
    simpa [hframe.size_eq] using hindex
  rw [sortSliceRangeEntries_one after (start + count) hindexAfter] at hrange
  simpa using congrArg Array.toList hrange.symm

private theorem sortSliceRangeEntries_prefix
    (slice : SortSlice beta rho) (start prefixCount whole : Nat)
    (hle : prefixCount ≤ whole) :
    (sortSliceRangeEntries slice start prefixCount).toList =
      (sortSliceRangeEntries slice start whole).toList.take prefixCount := by
  simp only [sortSliceRangeEntries_toList]
  rw [List.take_take]
  simp [Nat.min_eq_left hle]

private theorem sortSliceRangeKeys_prefix
    (slice : SortSlice beta rho) (start prefixCount whole : Nat)
    (hle : prefixCount ≤ whole) :
    (sortSliceRangeKeys slice start prefixCount).toList =
      (sortSliceRangeKeys slice start whole).toList.take prefixCount := by
  simp only [sortSliceRangeKeys_toList, ← List.map_take]
  congr 1
  rw [List.take_take]
  simp [Nat.min_eq_left hle]

private theorem canonicalRange_pairwise_prefix
    {lt : BoolComparator alpha}
    {slice : SortSlice (Occurrence alpha) nu} {start prefixCount whole : Nat}
    (hcanonical : CountRunCanonicalRange lt slice start whole)
    (hle : prefixCount ≤ whole) :
    (sortSliceRangeKeys slice start prefixCount).toList.Pairwise
      (fun earlier later =>
        ComparatorEquivalent lt earlier.value later.value ->
          earlier.origin < later.origin) := by
  have hpair := hcanonical.2
  rw [sortSliceRangeKeys_prefix slice start prefixCount whole hle]
  exact hpair.take

private theorem canonicalRange_next_origin
    {lt : BoolComparator alpha}
    {slice : SortSlice (Occurrence alpha) nu} {start n whole : Nat}
    (hcanonical : CountRunCanonicalRange lt slice start whole)
    (hn : n < whole)
    (hstop : start + whole ≤ slice.entries.size) :
    let next := slice.entries[start + n].key
    ∀ y ∈ (sortSliceRangeKeys slice start n).toList,
      ComparatorEquivalent lt y.value next.value -> y.origin < next.origin := by
  dsimp only
  have hprefixPair := canonicalRange_pairwise_prefix hcanonical
    (show n + 1 ≤ whole by omega)
  have hsucc := sortSliceRangeKeys_succ slice start n (by omega)
  rw [hsucc] at hprefixPair
  rw [List.pairwise_append] at hprefixPair
  intro y hy hequiv
  exact hprefixPair.2.2 y hy _ (by simp) hequiv

private structure DescendingMachineInvariant
    (lt : BoolComparator alpha)
    (source current : SortSlice (Occurrence alpha) nu)
    (start n neq : Nat) : Prop where
  frame : SortSlice.EqualOutsideRange source current start n
  keys :
    DescendingRunSpec.Invariant lt
      (sortSliceRangeKeys source start n).toList
      (sortSliceRangeKeys current start n).toList (neq + 1)
  entries :
    (DescendingRunSpec.normalize
      (sortSliceRangeEntries current start n).toList (neq + 1)).Perm
        (sortSliceRangeEntries source start n).toList

private theorem sortSliceRangeKeys_getLast
    (slice : SortSlice beta rho) (start n : Nat)
    (hn : 0 < n) (hstop : start + n ≤ slice.entries.size)
    (hne : (sortSliceRangeKeys slice start n).toList ≠ []) :
    (sortSliceRangeKeys slice start n).toList.getLast hne =
      slice.entries[start + (n - 1)].key := by
  have hcurrent := sortSliceRangeKeys_succ slice start (n - 1)
    (by omega : start + (n - 1 + 1) ≤ slice.entries.size)
  have hnEq : n - 1 + 1 = n := by omega
  have hcurrent' :
      (sortSliceRangeKeys slice start n).toList =
        (sortSliceRangeKeys slice start (n - 1)).toList ++
          [slice.entries[start + (n - 1)].key] := by
    simpa only [hnEq] using hcurrent
  have hlastOption :
      (sortSliceRangeKeys slice start n).toList.getLast? =
        some slice.entries[start + (n - 1)].key := by
    rw [hcurrent']
    simp
  rw [List.getLast?_eq_getLast_of_ne_nil hne] at hlastOption
  exact Option.some.inj hlastOption

private structure DescendingScanCorrectnessPost
    (lt : BoolComparator alpha)
    (source : SortSlice (Occurrence alpha) nu)
    (start n nremaining neq : Nat)
    (result : DescendingScanResult (Occurrence alpha) nu) : Prop where
  fuel : result.fuelExhausted = false
  lengthBounds : n ≤ result.length ∧ result.length ≤ nremaining
  invariant :
    DescendingMachineInvariant lt source result.slice start result.length
      result.equalTail

private theorem descendingScan_correct
    (lt : BoolComparator alpha) (horder : BoolStrictWeakOrder lt)
    (source current : SortSlice (Occurrence alpha) nu)
    (start nremaining n neq fuel : Nat)
    (hstop : start + nremaining ≤ source.entries.size)
    (hnpos : 0 < n) (hnle : n ≤ nremaining)
    (hfuel : nremaining - n ≤ fuel)
    (hcanonical : CountRunCanonicalRange lt source start nremaining)
    (hinv : DescendingMachineInvariant lt source current start n neq) :
    ∃ result,
      descendingScan? fuel (occurrenceComparator lt) current
          (Int.ofNat start) nremaining n neq = some result ∧
        DescendingScanCorrectnessPost lt source start n nremaining neq result := by
  induction fuel generalizing current n neq with
  | zero =>
      have hnremaining : nremaining ≤ n := by omega
      have hn : n = nremaining := by omega
      let result : DescendingScanResult (Occurrence alpha) nu :=
        { slice := current
          length := n
          equalTail := neq
          fuelExhausted := decide (n < nremaining) }
      refine ⟨result, ?_, ?_⟩
      · simp [descendingScan?, result]
      · exact
          { fuel := by simp [result, hn]
            lengthBounds := by simp [result, hn]
            invariant := by simpa [result] using hinv }
  | succ fuel ih =>
      by_cases hactive : n < nremaining
      · have hcurrentSize : current.entries.size = source.entries.size :=
          hinv.frame.size_eq.symm
        have hpreviousIndex : start + (n - 1) < current.entries.size := by
          rw [hcurrentSize]
          omega
        have hnextSourceIndex : start + n < source.entries.size := by omega
        have hnextCurrentIndex : start + n < current.entries.size := by
          rw [hcurrentSize]
          exact hnextSourceIndex
        let previous := current.entries[start + (n - 1)]
        let next := source.entries[start + n]
        have hnextEntry :
            current.entries[start + n]'hnextCurrentIndex = next := by
          exact hinv.frame.next_entry hnextSourceIndex
        have hpreviousRead :
            current.read? (Int.ofNat start + Int.ofNat (n - 1)) =
              some previous := by
          simpa [previous] using
            sortSlice_read_nat current (start + (n - 1)) hpreviousIndex
        have hnextRead :
            current.read? (Int.ofNat start + Int.ofNat n) = some next := by
          have hread := sortSlice_read_nat current (start + n) hnextCurrentIndex
          simpa [next, hnextEntry] using hread
        have hcurrentStop : start + nremaining ≤ current.entries.size := by
          rw [hcurrentSize]
          exact hstop
        have hlast :
            (sortSliceRangeKeys current start n).toList.getLast
                hinv.keys.current_ne = previous.key := by
          simpa [previous] using sortSliceRangeKeys_getLast current start n
            hnpos (by omega) hinv.keys.current_ne
        have hsourceKeysSucc :=
          sortSliceRangeKeys_succ source start n (by omega)
        have hsourceEntriesSucc :=
          sortSliceRangeEntries_succ source start n (by omega)
        have hcurrentKeysSucc :=
          sortSliceRangeKeys_succ current start n (by omega)
        have hcurrentEntriesSucc :=
          sortSliceRangeEntries_succ current start n (by omega)
        have hnextKeyEq : current.entries[start + n].key = next.key := by
          exact congrArg SortSliceEntry.key hnextEntry
        have hnextWholeEq : current.entries[start + n] = next := hnextEntry
        rw [hnextKeyEq] at hcurrentKeysSucc
        rw [hnextWholeEq] at hcurrentEntriesSucc
        by_cases hstrict :
            iflt (occurrenceComparator lt) next.key previous.key = true
        · have htail : neq + 1 ≤ n := by
            have hlength := sortSliceRangeKeys_size current start n (by omega)
            have hlength' :
                (sortSliceRangeKeys current start n).toList.length = n := by
              simpa using hlength
            exact hinv.keys.tail_le.trans_eq hlength'
          rcases reverseLastEqual_correct current start n neq htail (by omega) with
            ⟨reversed, hreversed⟩
          have hrevSize : reversed.slice.entries.size = current.entries.size :=
            hreversed.frame.size_eq.symm
          have hrevNextIndex : start + n < reversed.slice.entries.size := by
            rw [hrevSize]
            exact hnextCurrentIndex
          have hrevNextEntry :
              reversed.slice.entries[start + n]'hrevNextIndex = next := by
            calc
              reversed.slice.entries[start + n]'hrevNextIndex =
                  current.entries[start + n] :=
                hreversed.frame.next_entry hnextCurrentIndex
              _ = next := hnextEntry
          have hrevKeysSucc :=
            sortSliceRangeKeys_succ reversed.slice start n (by omega)
          have hrevEntriesSucc :=
            sortSliceRangeEntries_succ reversed.slice start n (by omega)
          have hrevNextKeyEq : reversed.slice.entries[start + n].key = next.key :=
            congrArg SortSliceEntry.key hrevNextEntry
          have hrevNextWholeEq : reversed.slice.entries[start + n] = next :=
            hrevNextEntry
          rw [hrevNextKeyEq, hreversed.keys] at hrevKeysSucc
          rw [hrevNextWholeEq, hreversed.entries] at hrevEntriesSucc
          have hstrictPivot :
              lt next.key.value
                ((sortSliceRangeKeys current start n).toList.getLast
                  hinv.keys.current_ne).value = true := by
            have hstrictValue : lt next.key.value previous.key.value = true := by
              simpa [occurrenceComparator] using hstrict
            rw [hlast]
            exact hstrictValue
          have hkeysExtended :=
            hinv.keys.extend_strict horder next.key hstrictPivot
          have hentriesExtended :=
            DescendingRunSpec.normalize_after_strict_perm
              (sortSliceRangeEntries current start n).toList
              (sortSliceRangeEntries source start n).toList next (neq + 1)
              hinv.entries
          have hnextInv : DescendingMachineInvariant lt source reversed.slice
              start (n + 1) 0 := by
            refine
              { frame := ?_
                keys := ?_
                entries := ?_ }
            · exact (hinv.frame.trans hreversed.frame).widen_count (by omega)
            · rw [hsourceKeysSucc, hrevKeysSucc]
              simpa using hkeysExtended
            · rw [hsourceEntriesSucc, hrevEntriesSucc]
              simpa using hentriesExtended
          have hfuel' : nremaining - (n + 1) ≤ fuel := by omega
          rcases ih reversed.slice (n + 1) 0 (by omega) (by omega) hfuel'
              hnextInv with ⟨result, hresult, hpost⟩
          refine ⟨result, ?_, ?_⟩
          · simp only [descendingScan?, hactive, if_pos]
            rw [hpreviousRead]
            rw [hnextRead]
            simp only [bind, Option.bind]
            rw [if_pos hstrict, hreversed.resultEq]
            simp only
            rw [hreversed.fuel]
            simp only [Bool.false_eq_true, if_false]
            exact hresult
          · exact
              { fuel := hpost.fuel
                lengthBounds := ⟨le_trans (by omega) hpost.lengthBounds.1,
                  hpost.lengthBounds.2⟩
                invariant := hpost.invariant }
        · have hnextNotPrevious :
              occurrenceComparator lt next.key previous.key = false :=
            by simpa [iflt] using Bool.eq_false_iff.mpr hstrict
          by_cases hascending :
              iflt (occurrenceComparator lt) previous.key next.key = true
          · let result : DescendingScanResult (Occurrence alpha) nu :=
              { slice := current
                length := n
                equalTail := neq
                fuelExhausted := false }
            refine ⟨result, ?_, ?_⟩
            · simp only [descendingScan?, hactive, if_pos]
              rw [hpreviousRead, hnextRead]
              have hpreviousNext :
                  occurrenceComparator lt previous.key next.key = true := by
                simpa [iflt] using hascending
              simp [hnextNotPrevious, hpreviousNext, result]
            · exact
                { fuel := rfl
                  lengthBounds := ⟨le_rfl, hnle⟩
                  invariant := by simpa [result] using hinv }
          · have hpreviousNotNext :
                occurrenceComparator lt previous.key next.key = false :=
              by simpa [iflt] using Bool.eq_false_iff.mpr hascending
            have hequivalent : ComparatorEquivalent lt next.key.value
                ((sortSliceRangeKeys current start n).toList.getLast
                  hinv.keys.current_ne).value := by
              constructor
              · have hvalue : lt next.key.value previous.key.value = false := by
                  simpa [occurrenceComparator] using hnextNotPrevious
                rw [hlast]
                exact hvalue
              · have hvalue : lt previous.key.value next.key.value = false := by
                  simpa [occurrenceComparator] using hpreviousNotNext
                rw [hlast]
                exact hvalue
            have horigin := canonicalRange_next_origin hcanonical hactive hstop
            have hkeysExtended := hinv.keys.extend_equivalent horder next.key
              hequivalent horigin
            have hentriesExtended :=
              DescendingRunSpec.normalize_append_equivalent_perm
                (sortSliceRangeEntries current start n).toList
                (sortSliceRangeEntries source start n).toList next (neq + 1)
                (by
                  have hlength := sortSliceRangeEntries_size current start n
                    (by omega)
                  have hlength' :
                      (sortSliceRangeKeys current start n).toList.length = n := by
                    simpa using
                      sortSliceRangeKeys_size current start n (by omega)
                  have hentryLength :
                      (sortSliceRangeEntries current start n).toList.length = n := by
                    simpa using hlength
                  exact (hinv.keys.tail_le.trans_eq hlength').trans_eq
                    hentryLength.symm)
                hinv.entries
            have hnextInv : DescendingMachineInvariant lt source current
                start (n + 1) (neq + 1) := by
              refine
                { frame := hinv.frame.widen_count (by omega)
                  keys := ?_
                  entries := ?_ }
              · rw [hsourceKeysSucc, hcurrentKeysSucc]
                simpa using hkeysExtended
              · rw [hsourceEntriesSucc, hcurrentEntriesSucc]
                simpa using hentriesExtended
            have hfuel' : nremaining - (n + 1) ≤ fuel := by omega
            rcases ih current (n + 1) (neq + 1) (by omega) (by omega)
                hfuel' hnextInv with ⟨result, hresult, hpost⟩
            refine ⟨result, ?_, ?_⟩
            · simp only [descendingScan?, hactive, if_pos]
              rw [hpreviousRead]
              rw [hnextRead]
              simp only [bind, Option.bind]
              rw [if_neg (by exact Bool.eq_false_iff.mp hnextNotPrevious)]
              rw [if_neg (by exact Bool.eq_false_iff.mp hpreviousNotNext)]
              exact hresult
            · exact
                { fuel := hpost.fuel
                  lengthBounds := ⟨le_trans (by omega) hpost.lengthBounds.1,
                    hpost.lengthBounds.2⟩
                  invariant := hpost.invariant }
      · have hnremaining : nremaining ≤ n := Nat.le_of_not_gt hactive
        have hn : n = nremaining := by omega
        let result : DescendingScanResult (Occurrence alpha) nu :=
          { slice := current
            length := n
            equalTail := neq
            fuelExhausted := false }
        refine ⟨result, ?_, ?_⟩
        · simp [descendingScan?, hactive, result]
        · exact
            { fuel := rfl
              lengthBounds := by simp [result, hn]
              invariant := by simpa [result] using hinv }

private structure ExactReverseRangePost
    (before : SortSlice beta rho) (start count : Nat)
    (result : ReverseSliceResult beta rho) : Prop where
  resultEq :
    sortsliceReverse? before (Int.ofNat start) count = some result
  fuel : result.fuelExhausted = false
  entries :
    (sortSliceRangeEntries result.slice start count).toList =
      (sortSliceRangeEntries before start count).toList.reverse
  keys :
    (sortSliceRangeKeys result.slice start count).toList =
      (sortSliceRangeKeys before start count).toList.reverse
  frame : SortSlice.EqualOutsideRange before result.slice start count

private theorem exactReverseRange_correct
    (slice : SortSlice beta rho) (start count : Nat)
    (hstop : start + count ≤ slice.entries.size) :
    ∃ result, ExactReverseRangePost slice start count result := by
  have hrange : SortSlice.RangeInBounds slice (Int.ofNat start) count := by
    constructor
    · exact Int.natCast_nonneg _
    · simp only [Int.ofNat_eq_natCast]
      omega
  rcases sortsliceReverse_correct slice (Int.ofNat start) count hrange with
    ⟨result, hresult, hfuel, hentries⟩
  let mathematical : SortSlice beta rho :=
    { entries := ReverseRangeSpec.reverseRangeEntries slice.entries
        start (start + count) }
  have hsliceEq : result.slice = mathematical := by
    apply congrArg SortSlice.mk
    simpa [mathematical] using hentries
  have hentryRange :
      (sortSliceRangeEntries result.slice start count).toList =
        (sortSliceRangeEntries slice start count).toList.reverse := by
    simpa [hsliceEq, mathematical] using congrArg Array.toList
      (ReverseRangeSpec.sortSliceRangeEntries_reverseRange_self
        slice start count hstop)
  have hkeyRange :
      (sortSliceRangeKeys result.slice start count).toList =
        (sortSliceRangeKeys slice start count).toList.reverse := by
    simpa [hsliceEq, mathematical] using congrArg Array.toList
      (ReverseRangeSpec.sortSliceRangeKeys_reverseRange_self
        slice start count hstop)
  have hmathematicalFrame :
      SortSlice.EqualOutsideRange slice mathematical start count := by
    simpa [mathematical] using
      ReverseRangeSpec.equalOutsideRange_reverseRange slice start count hstop
  have hresultFrame :
      SortSlice.EqualOutsideRange mathematical result.slice start count :=
    SortSlice.EqualOutsideRange.of_eq hsliceEq.symm start count
  exact ⟨result,
    { resultEq := hresult
      fuel := hfuel
      entries := hentryRange
      keys := hkeyRange
      frame := hmathematicalFrame.trans hresultFrame }⟩

private theorem finishDescending_correct
    (lt : BoolComparator alpha) (horder : BoolStrictWeakOrder lt)
    (state : MergeState (Occurrence alpha) nu)
    (hcompare : state.key_compare = occurrenceComparator lt)
    (source current : SortSlice (Occurrence alpha) nu)
    (start nremaining n : Nat)
    (hstop : start + nremaining ≤ source.entries.size)
    (hnpos : 0 < n) (hnTwo : 2 ≤ n) (hnle : n ≤ nremaining)
    (hcanonical : CountRunCanonicalRange lt source start nremaining)
    (hinv : DescendingMachineInvariant lt source current start n 0) :
    ∃ result,
      finishDescending? state current (Int.ofNat start) nremaining n =
          some result ∧
        CountRunSemanticPost lt source start nremaining result := by
  rcases descendingScan_correct lt horder source current start nremaining n 0
      nremaining hstop hnpos hnle (by omega) hcanonical hinv with
    ⟨descending, hdescending, hdescendingPost⟩
  have hdescendingState :
      descendingScan? nremaining state.key_compare current (Int.ofNat start)
          nremaining n 0 = some descending := by
    rw [hcompare]
    exact hdescending
  have hdescendingStop :
      start + descending.length ≤ descending.slice.entries.size := by
    rw [← hdescendingPost.invariant.frame.size_eq]
    have hlengthUpper := hdescendingPost.lengthBounds.2
    omega
  have htailBound : descending.equalTail + 1 ≤ descending.length := by
    have hkeysLength :
        (sortSliceRangeKeys descending.slice start descending.length).toList.length =
          descending.length := by
      simpa using sortSliceRangeKeys_size descending.slice start
        descending.length hdescendingStop
    rw [← hkeysLength]
    exact hdescendingPost.invariant.keys.tail_le
  rcases reverseLastEqual_correct descending.slice start descending.length
      descending.equalTail htailBound
      hdescendingStop with ⟨tailReversed, htail⟩
  have htailStop :
      start + descending.length ≤ tailReversed.slice.entries.size := by
    rw [← htail.frame.size_eq]
    exact hdescendingStop
  rcases exactReverseRange_correct tailReversed.slice start descending.length
      htailStop with ⟨wholeReversed, hwhole⟩
  have hwholeKeys :
      (sortSliceRangeKeys wholeReversed.slice start descending.length).toList =
        DescendingRunSpec.normalize
          (sortSliceRangeKeys descending.slice start descending.length).toList
          (descending.equalTail + 1) := by
    rw [hwhole.keys, htail.keys]
    exact (DescendingRunSpec.normalize_eq_reverse_reverseSuffix
      (sortSliceRangeKeys descending.slice start descending.length).toList
      (descending.equalTail + 1)).symm
  have hwholeEntries :
      (sortSliceRangeEntries wholeReversed.slice start descending.length).toList =
        DescendingRunSpec.normalize
          (sortSliceRangeEntries descending.slice start descending.length).toList
          (descending.equalTail + 1) := by
    rw [hwhole.entries, htail.entries]
    exact (DescendingRunSpec.normalize_eq_reverse_reverseSuffix
      (sortSliceRangeEntries descending.slice start descending.length).toList
      (descending.equalTail + 1)).symm
  have hprefixSorted :
      Sorted (occurrenceComparator lt)
        (sortSliceRangeKeys wholeReversed.slice start descending.length) := by
    unfold Sorted
    rw [hwholeKeys]
    exact hdescendingPost.invariant.keys.sorted
  have hsourceWholePrefixFrame :
      SortSlice.EqualOutsideRange source wholeReversed.slice start
        descending.length :=
    hdescendingPost.invariant.frame.trans
      (htail.frame.trans hwhole.frame)
  have hwholeStop :
      start + nremaining ≤ wholeReversed.slice.entries.size := by
    rw [← hsourceWholePrefixFrame.size_eq]
    exact hstop
  have hdescendingPos : 0 < descending.length :=
    lt_of_lt_of_le hnpos hdescendingPost.lengthBounds.1
  rcases ascendingScan_correct lt horder wholeReversed.slice start nremaining
      descending.length nremaining hwholeStop
      hdescendingPos
      hdescendingPost.lengthBounds.2 (by omega) hprefixSorted with
    ⟨extended, hextended, hextendedPost⟩
  have hextendedState :
      ascendingScan? nremaining state.key_compare wholeReversed.slice
          (Int.ofNat start) nremaining descending.length = some extended := by
    rw [hcompare]
    exact hextended
  let result : CountRunResult (Occurrence alpha) nu :=
    { slice := wholeReversed.slice
      length := extended.length
      fuelExhausted := extended.fuelExhausted }
  have hresultEq :
      finishDescending? state current (Int.ofNat start) nremaining n =
          some result := by
    unfold finishDescending?
    rw [hdescendingState]
    simp only [bind, Option.bind]
    rw [hdescendingPost.fuel]
    simp only [Bool.false_eq_true, if_false]
    rw [htail.resultEq]
    simp only
    rw [htail.fuel]
    simp only [Bool.false_eq_true, if_false]
    rw [hwhole.resultEq]
    simp only
    rw [hwhole.fuel]
    simp only [Bool.false_eq_true, if_false]
    rw [hextendedState]
    rfl
  have hprefixStable :
      StableOccurrencePermutation lt
        (sortSliceRangeKeys source start descending.length).toList
        (sortSliceRangeKeys wholeReversed.slice start descending.length).toList := by
    rw [hwholeKeys]
    exact hdescendingPost.invariant.keys.stable
  have hprefixEntryPermutation :
      (sortSliceRangeEntries wholeReversed.slice start descending.length).toList.Perm
        (sortSliceRangeEntries source start descending.length).toList := by
    rw [hwholeEntries]
    exact hdescendingPost.invariant.entries
  let extra := extended.length - descending.length
  have hlengthSplit : descending.length + extra = extended.length := by
    dsimp only [extra]
    have hle := hextendedPost.lengthBounds.1
    omega
  have hsuffixEntries :
      sortSliceRangeEntries source (start + descending.length) extra =
        sortSliceRangeEntries wholeReversed.slice
          (start + descending.length) extra := by
    apply hsourceWholePrefixFrame.entries_eq_of_disjoint
    exact Or.inr le_rfl
  have hsuffixKeys :
      sortSliceRangeKeys source (start + descending.length) extra =
        sortSliceRangeKeys wholeReversed.slice
          (start + descending.length) extra := by
    apply hsourceWholePrefixFrame.keys_eq_of_disjoint
    exact Or.inr le_rfl
  have hsourceEntriesSplit := sortSliceRangeEntries_add source start
    descending.length extra
  have hwholeEntriesSplit := sortSliceRangeEntries_add wholeReversed.slice start
    descending.length extra
  have hsourceKeysSplit :
      (sortSliceRangeKeys source start extended.length).toList =
        (sortSliceRangeKeys source start descending.length).toList ++
          (sortSliceRangeKeys source (start + descending.length) extra).toList := by
    simp only [sortSliceRangeKeys_toList, ← List.map_append,
      ← sortSliceRangeEntries_toList]
    simpa [hlengthSplit] using congrArg (List.map SortSliceEntry.key)
      hsourceEntriesSplit
  have hwholeKeysSplit :
      (sortSliceRangeKeys wholeReversed.slice start extended.length).toList =
        (sortSliceRangeKeys wholeReversed.slice start descending.length).toList ++
          (sortSliceRangeKeys wholeReversed.slice
            (start + descending.length) extra).toList := by
    simp only [sortSliceRangeKeys_toList, ← List.map_append,
      ← sortSliceRangeEntries_toList]
    simpa [hlengthSplit] using congrArg (List.map SortSliceEntry.key)
      hwholeEntriesSplit
  have hentryPermutation :
      (sortSliceRangeEntries wholeReversed.slice start extended.length).toList.Perm
        (sortSliceRangeEntries source start extended.length).toList := by
    rw [hlengthSplit] at hsourceEntriesSplit hwholeEntriesSplit
    rw [hsourceEntriesSplit, hwholeEntriesSplit]
    rw [← congrArg Array.toList hsuffixEntries]
    exact hprefixEntryPermutation.append_right _
  have hcanonicalExtended :
      (sortSliceRangeKeys source start extended.length).toList.Pairwise
        (DescendingRunSpec.StableRelation lt) := by
    exact canonicalRange_pairwise_prefix hcanonical
      hextendedPost.lengthBounds.2
  have hstable :
      StableOccurrencePermutation lt
        (sortSliceRangeKeys source start extended.length).toList
        (sortSliceRangeKeys wholeReversed.slice start extended.length).toList := by
    rw [hsourceKeysSplit, hwholeKeysSplit]
    rw [← congrArg Array.toList hsuffixKeys]
    have hcanonicalSplit :
        ((sortSliceRangeKeys source start descending.length).toList ++
          (sortSliceRangeKeys source
            (start + descending.length) extra).toList).Pairwise
          (DescendingRunSpec.StableRelation lt) := by
      rw [← hsourceKeysSplit]
      exact hcanonicalExtended
    exact DescendingRunSpec.stableOccurrencePermutation_append_untouched_suffix
      hprefixStable hcanonicalSplit
  refine ⟨result, hresultEq, ?_⟩
  exact
    { fuel := by simpa [result] using hextendedPost.fuel
      lengthBounds := by
        have hdescPos : 1 ≤ descending.length := hdescendingPos
        simpa [result] using
          ⟨le_trans hdescPos
            hextendedPost.lengthBounds.1,
            hextendedPost.lengthBounds.2⟩
      minimumLength := by
        right
        simpa [result] using
          le_trans hnTwo
            (le_trans hdescendingPost.lengthBounds.1
              hextendedPost.lengthBounds.1)
      sorted := by simpa [result] using hextendedPost.sorted
      stable := by simpa [result] using hstable
      entryPermutation := by simpa [result] using hentryPermutation
      frame := by
        simpa [result] using hsourceWholePrefixFrame.widen_count
          hextendedPost.lengthBounds.1 }

private theorem sortSliceRangeKeys_head
    (slice : SortSlice beta rho) (start count : Nat)
    (hcount : 0 < count) (hstop : start + count ≤ slice.entries.size)
    (hne : (sortSliceRangeKeys slice start count).toList ≠ []) :
    (sortSliceRangeKeys slice start count).toList.head hne =
      slice.entries[start].key := by
  rw [List.head_eq_getElem_zero hne]
  simp [sortSliceRangeKeys, sortSliceRangeEntries]

private theorem sorted_equivalent_block
    (lt : BoolComparator alpha) (horder : BoolStrictWeakOrder lt)
    (xs : List (Occurrence alpha)) (hne : xs ≠ [])
    (hsorted : xs.Pairwise (DescendingRunSpec.SortedRelation lt))
    (hendpoints : lt (xs.head hne).value (xs.getLast hne).value = false) :
    ∀ x ∈ xs,
      ComparatorEquivalent lt x.value (xs.getLast hne).value := by
  intro x hx
  have hrefl : ∀ y : Occurrence alpha,
      DescendingRunSpec.SortedRelation lt y y := by
    intro y
    exact Bool.eq_false_iff.mpr (horder.irrefl y.value)
  have hlastBeforeX : lt (xs.getLast hne).value x.value = false :=
    hsorted.rel_getLast_of_rel_getLast_getLast hx (hrefl _)
  have hxBeforeHead : lt x.value (xs.head hne).value = false :=
    hsorted.rel_head_of_rel_head_head hx (hrefl _)
  have hxBeforeLast : lt x.value (xs.getLast hne).value = false := by
    apply Bool.eq_false_iff.mpr
    intro hxLast
    have hxHead := horder.strict_of_strict_of_not_reverse hxLast hendpoints
    exact (Bool.eq_false_iff.mp hxBeforeHead) hxHead
  exact ⟨hxBeforeLast, hlastBeforeX⟩

private theorem sourceResult_semantic
    (lt : BoolComparator alpha)
    (source : SortSlice (Occurrence alpha) nu)
    (start nremaining length : Nat)
    (hpositive : 1 ≤ length) (hlength : length ≤ nremaining)
    (hminimum : nremaining = 1 ∨ 2 ≤ length)
    (hsorted :
      Sorted (occurrenceComparator lt)
        (sortSliceRangeKeys source start length))
    (hcanonical : CountRunCanonicalRange lt source start nremaining) :
    CountRunSemanticPost lt source start nremaining
      { slice := source, length := length, fuelExhausted := false } := by
  have hstablePair :
      (sortSliceRangeKeys source start length).toList.Pairwise
        (DescendingRunSpec.StableRelation lt) :=
    canonicalRange_pairwise_prefix hcanonical hlength
  exact
    { fuel := rfl
      lengthBounds := ⟨hpositive, hlength⟩
      minimumLength := hminimum
      sorted := hsorted
      stable := ⟨List.Perm.refl _, by
        unfold DescendingRunSpec.StableRelation at hstablePair
        exact hstablePair⟩
      entryPermutation := List.Perm.refl _
      frame := SortSlice.EqualOutsideRange.refl source start length }

private theorem shortDescendingInvariant
    (lt : BoolComparator alpha) (horder : BoolStrictWeakOrder lt)
    (source : SortSlice (Occurrence alpha) nu) (start nremaining : Nat)
    (hstop : start + nremaining ≤ source.entries.size)
    (hnremaining : 2 ≤ nremaining)
    (hstrict :
      lt source.entries[start + 1].key.value
        source.entries[start].key.value = true) :
    DescendingMachineInvariant lt source source start 2 0 := by
  let first := source.entries[start].key
  let next := source.entries[start + 1].key
  have hkeysOne :
      (sortSliceRangeKeys source start 1).toList = [first] := by
    have hsucc := sortSliceRangeKeys_succ source start 0 (by omega)
    simpa [first] using hsucc
  have hentriesOne :
      (sortSliceRangeEntries source start 1).toList =
        [source.entries[start]] := by
    have hsucc := sortSliceRangeEntries_succ source start 0 (by omega)
    simpa using hsucc
  have hkeysTwo := sortSliceRangeKeys_succ source start 1 (by omega)
  have hentriesTwo := sortSliceRangeEntries_succ source start 1 (by omega)
  have hstableOne : [first].Pairwise (DescendingRunSpec.StableRelation lt) := by
    simp
  have hbaseKeys :
      DescendingRunSpec.Invariant lt [first] [first] 1 := by
    exact DescendingRunSpec.Invariant.of_equivalent_block
      (lt := lt) (current := [first]) (by simp) (by simp) hstableOne (by
        intro x hx
        simp only [List.mem_singleton] at hx
        subst x
        exact horder.comparatorEquivalent_equivalence.refl first.value)
  have hstrict' : lt next.value first.value = true := by
    simpa [first, next] using hstrict
  have hkeysExtended := hbaseKeys.extend_strict horder next hstrict'
  have hkeySuffix : DescendingRunSpec.reverseSuffix [first] 1 = [first] := by
    exact DescendingRunSpec.reverseSuffix_one_of_ne_nil [first] (by simp)
  have hkeys :
      DescendingRunSpec.Invariant lt
        (sortSliceRangeKeys source start 2).toList
        (sortSliceRangeKeys source start 2).toList 1 := by
    rw [hkeysOne] at hkeysTwo
    rw [hkeysTwo]
    change DescendingRunSpec.Invariant lt ([first] ++ [next])
      ([first] ++ [next]) 1
    simpa only [hkeySuffix] using hkeysExtended
  have hentryNormalize :
      DescendingRunSpec.normalize [source.entries[start]] 1 =
        [source.entries[start]] := by
    simpa using DescendingRunSpec.normalize_full [source.entries[start]]
  have hentriesExtended :=
    DescendingRunSpec.normalize_after_strict_perm
      [source.entries[start]] [source.entries[start]]
      source.entries[start + 1] 1 (by
        rw [hentryNormalize])
  have hentrySuffix :
      DescendingRunSpec.reverseSuffix [source.entries[start]] 1 =
        [source.entries[start]] := by
    exact DescendingRunSpec.reverseSuffix_one_of_ne_nil _ (by simp)
  have hentries :
      (DescendingRunSpec.normalize
        (sortSliceRangeEntries source start 2).toList 1).Perm
          (sortSliceRangeEntries source start 2).toList := by
    rw [hentriesTwo]
    simpa [hentriesOne, hentrySuffix] using hentriesExtended
  exact
    { frame := SortSlice.EqualOutsideRange.refl source start 2
      keys := hkeys
      entries := hentries }

private theorem longDescendingInvariant
    (lt : BoolComparator alpha) (horder : BoolStrictWeakOrder lt)
    (source : SortSlice (Occurrence alpha) nu) (start nremaining n : Nat)
    (hstop : start + nremaining ≤ source.entries.size)
    (hnlong : 1 < n) (hnlt : n < nremaining)
    (hcanonical : CountRunCanonicalRange lt source start nremaining)
    (hsorted :
      Sorted (occurrenceComparator lt)
        (sortSliceRangeKeys source start n))
    (hendpoints :
      lt source.entries[start].key.value
        source.entries[start + (n - 1)].key.value = false)
    (hstrictNext :
      lt source.entries[start + n].key.value
        source.entries[start + (n - 1)].key.value = true)
    (reversed : ReverseSliceResult (Occurrence alpha) nu)
    (hreverse : ExactReverseRangePost source start n reversed) :
    DescendingMachineInvariant lt source reversed.slice start (n + 1) 0 := by
  let canonicalKeys := (sortSliceRangeKeys source start n).toList
  let canonicalEntries := (sortSliceRangeEntries source start n).toList
  let nextKey := source.entries[start + n].key
  let nextEntry := source.entries[start + n]
  have hkeyLength : canonicalKeys.length = n := by
    dsimp only [canonicalKeys]
    simpa using sortSliceRangeKeys_size source start n (by omega)
  have hentryLength : canonicalEntries.length = n := by
    dsimp only [canonicalEntries]
    simpa using sortSliceRangeEntries_size source start n (by omega)
  have hkeyNe : canonicalKeys ≠ [] := by
    intro hempty
    rw [hempty] at hkeyLength
    simp at hkeyLength
    omega
  have hhead : canonicalKeys.head hkeyNe = source.entries[start].key := by
    exact sortSliceRangeKeys_head source start n (by omega) (by omega) hkeyNe
  have hlast :
      canonicalKeys.getLast hkeyNe =
        source.entries[start + (n - 1)].key := by
    exact sortSliceRangeKeys_getLast source start n (by omega) (by omega) hkeyNe
  have hsortedList :
      canonicalKeys.Pairwise (DescendingRunSpec.SortedRelation lt) := by
    exact hsorted
  have hallEquivalent :
      ∀ x ∈ canonicalKeys,
        ComparatorEquivalent lt x.value (canonicalKeys.getLast hkeyNe).value := by
    apply sorted_equivalent_block lt horder canonicalKeys hkeyNe hsortedList
    rw [hhead, hlast]
    exact hendpoints
  have hstableCanonical :
      canonicalKeys.Pairwise (DescendingRunSpec.StableRelation lt) :=
    canonicalRange_pairwise_prefix hcanonical (by omega)
  have hbaseKeys :
      DescendingRunSpec.Invariant lt canonicalKeys canonicalKeys n := by
    have hbase := DescendingRunSpec.Invariant.of_equivalent_block hkeyNe
      hsortedList hstableCanonical hallEquivalent
    simpa [hkeyLength] using hbase
  have hstrict :
      lt nextKey.value (canonicalKeys.getLast hbaseKeys.current_ne).value = true := by
    rw [hlast]
    simpa [nextKey] using hstrictNext
  have hkeysExtended := hbaseKeys.extend_strict horder nextKey hstrict
  have hnextIndexSource : start + n < source.entries.size := by omega
  have hnextIndexReversed : start + n < reversed.slice.entries.size := by
    rw [← hreverse.frame.size_eq]
    exact hnextIndexSource
  have hnextEntryReversed :
      reversed.slice.entries[start + n]'hnextIndexReversed = nextEntry := by
    exact hreverse.frame.next_entry hnextIndexSource
  have hnextKeyReversed :
      (reversed.slice.entries[start + n]'hnextIndexReversed).key = nextKey := by
    exact congrArg SortSliceEntry.key hnextEntryReversed
  have hreversedKeysSucc := sortSliceRangeKeys_succ reversed.slice start n
    (by
      rw [← hreverse.frame.size_eq]
      omega)
  have hreversedEntriesSucc := sortSliceRangeEntries_succ reversed.slice start n
    (by
      rw [← hreverse.frame.size_eq]
      omega)
  rw [hnextKeyReversed, hreverse.keys] at hreversedKeysSucc
  rw [hnextEntryReversed, hreverse.entries] at hreversedEntriesSucc
  have hsourceKeysSucc := sortSliceRangeKeys_succ source start n (by omega)
  have hsourceEntriesSucc := sortSliceRangeEntries_succ source start n (by omega)
  have hreverseSuffixKeys :
      DescendingRunSpec.reverseSuffix canonicalKeys n = canonicalKeys.reverse := by
    simp [DescendingRunSpec.reverseSuffix, hkeyLength]
  have hkeys :
      DescendingRunSpec.Invariant lt
        (sortSliceRangeKeys source start (n + 1)).toList
        (sortSliceRangeKeys reversed.slice start (n + 1)).toList 1 := by
    rw [hsourceKeysSucc, hreversedKeysSucc]
    change DescendingRunSpec.Invariant lt (canonicalKeys ++ [nextKey])
      (canonicalKeys.reverse ++ [nextKey]) 1
    rw [← hreverseSuffixKeys]
    exact hkeysExtended
  have hbaseEntryPermutation :
      (DescendingRunSpec.normalize canonicalEntries n).Perm canonicalEntries := by
    rw [← hentryLength]
    rw [DescendingRunSpec.normalize_full]
  have hentriesExtended :=
    DescendingRunSpec.normalize_after_strict_perm canonicalEntries
      canonicalEntries nextEntry n hbaseEntryPermutation
  have hreverseSuffixEntries :
      DescendingRunSpec.reverseSuffix canonicalEntries n =
        canonicalEntries.reverse := by
    simp [DescendingRunSpec.reverseSuffix, hentryLength]
  have hentries :
      (DescendingRunSpec.normalize
        (sortSliceRangeEntries reversed.slice start (n + 1)).toList 1).Perm
          (sortSliceRangeEntries source start (n + 1)).toList := by
    rw [hsourceEntriesSucc, hreversedEntriesSucc]
    simpa [canonicalEntries, nextEntry, hreverseSuffixEntries] using
      hentriesExtended
  exact
    { frame := hreverse.frame.widen_count (by omega)
      keys := hkeys
      entries := hentries }

private theorem countRun_raw_correct
    (lt : BoolComparator alpha) (horder : BoolStrictWeakOrder lt)
    (state : MergeState (Occurrence alpha) nu)
    (hcompare : state.key_compare = occurrenceComparator lt)
    (source : SortSlice (Occurrence alpha) nu)
    (start nremaining : Nat)
    (hstop : start + nremaining ≤ source.entries.size)
    (hpositive : 0 < nremaining)
    (hsizeRepresentable : nremaining ≤ PY_SSIZE_T_MAX)
    (hcanonical : CountRunCanonicalRange lt source start nremaining) :
    ∃ result,
      countRun? state source (Int.ofNat start) nremaining = some result ∧
        CountRunSemanticPost lt source start nremaining result := by
  have hguard : 0 < nremaining ∧ nremaining ≤ PY_SSIZE_T_MAX :=
    ⟨hpositive, hsizeRepresentable⟩
  have hkeysOne :
      (sortSliceRangeKeys source start 1).toList =
        [source.entries[start].key] := by
    have hsucc := sortSliceRangeKeys_succ source start 0 (by omega)
    simpa using hsucc
  have hsortedOne :
      Sorted (occurrenceComparator lt)
        (sortSliceRangeKeys source start 1) := by
    unfold Sorted
    rw [hkeysOne]
    simp
  rcases ascendingScan_correct lt horder source start nremaining 1 nremaining
      hstop (by omega) (by omega) (by omega) hsortedOne with
    ⟨ascending, hascending, hascendingPost⟩
  have hascendingState :
      ascendingScan? nremaining state.key_compare source (Int.ofNat start)
          nremaining 1 = some ascending := by
    rw [hcompare]
    exact hascending
  by_cases hcomplete : ascending.length = nremaining
  · let result : CountRunResult (Occurrence alpha) nu :=
      { slice := source
        length := ascending.length
        fuelExhausted := false }
    have hresult :
        countRun? state source (Int.ofNat start) nremaining = some result := by
      unfold countRun?
      rw [if_pos hguard]
      simp only [countRunBindOptionAcross, hascendingState]
      rw [hascendingPost.fuel]
      simp [hcomplete, result]
    refine ⟨result, hresult, ?_⟩
    simpa [result] using sourceResult_semantic lt source start nremaining
      ascending.length hascendingPost.lengthBounds.1
      hascendingPost.lengthBounds.2 (by
        by_cases hone : nremaining = 1
        · exact Or.inl hone
        · exact Or.inr (by omega)) hascendingPost.sorted hcanonical
  · by_cases hlong : 1 < ascending.length
    · have hlengthLt : ascending.length < nremaining := by
        have hupper := hascendingPost.lengthBounds.2
        omega
      have hfirstIndex : start < source.entries.size := by omega
      have hlastIndex : start + (ascending.length - 1) < source.entries.size := by
        omega
      let first := source.entries[start]
      let last := source.entries[start + (ascending.length - 1)]
      have hfirstRead : source.read? (Int.ofNat start) = some first := by
        simpa [first] using sortSlice_read_nat source start hfirstIndex
      have hlastRead :
          source.read?
              (Int.ofNat start + Int.ofNat (ascending.length - 1)) =
            some last := by
        simpa [last] using sortSlice_read_nat source
          (start + (ascending.length - 1)) hlastIndex
      by_cases hincreasing :
          iflt state.key_compare first.key last.key = true
      · let result : CountRunResult (Occurrence alpha) nu :=
          { slice := source
            length := ascending.length
            fuelExhausted := false }
        have hresult :
            countRun? state source (Int.ofNat start) nremaining =
              some result := by
          unfold countRun?
          rw [if_pos hguard]
          simp only [countRunBindOptionAcross, hascendingState]
          rw [hascendingPost.fuel]
          simp only [Bool.false_eq_true, if_false]
          rw [if_neg hcomplete, if_pos hlong]
          rw [hfirstRead, hlastRead]
          simp only [bind, Option.bind]
          rw [if_pos hincreasing]
        refine ⟨result, hresult, ?_⟩
        simpa [result] using sourceResult_semantic lt source start nremaining
          ascending.length hascendingPost.lengthBounds.1
          hascendingPost.lengthBounds.2 (Or.inr (by omega))
          hascendingPost.sorted hcanonical
      · have hincreasingFalse :
            state.key_compare first.key last.key = false := by
          exact Bool.eq_false_iff.mpr (by simpa [iflt] using hincreasing)
        have hendpoints :
            lt source.entries[start].key.value
              source.entries[start + (ascending.length - 1)].key.value =
                false := by
          rw [hcompare] at hincreasingFalse
          simpa [first, last, occurrenceComparator] using hincreasingFalse
        rcases hascendingPost.stoppedByDecrease hlengthLt with
          ⟨previous, next, hpreviousRead, hnextRead, hdecrease⟩
        have hpreviousExact :
            source.read?
                (Int.ofNat start + Int.ofNat (ascending.length - 1)) =
              some source.entries[start + (ascending.length - 1)] := by
          simpa using sortSlice_read_nat source
            (start + (ascending.length - 1)) hlastIndex
        have hnextIndex : start + ascending.length < source.entries.size := by
          omega
        have hnextExact :
            source.read? (Int.ofNat start + Int.ofNat ascending.length) =
              some source.entries[start + ascending.length] := by
          simpa using sortSlice_read_nat source (start + ascending.length)
            hnextIndex
        rw [hpreviousExact] at hpreviousRead
        rw [hnextExact] at hnextRead
        have hpreviousEq :
            previous = source.entries[start + (ascending.length - 1)] :=
          Option.some.inj hpreviousRead.symm
        have hnextEq : next = source.entries[start + ascending.length] :=
          Option.some.inj hnextRead.symm
        have hstrictNext :
            lt source.entries[start + ascending.length].key.value
              source.entries[start + (ascending.length - 1)].key.value = true := by
          rw [← hnextEq, ← hpreviousEq]
          simpa [occurrenceComparator] using hdecrease
        rcases exactReverseRange_correct source start ascending.length
            (by omega) with ⟨reversed, hreverse⟩
        have hinvariant := longDescendingInvariant lt horder source start
          nremaining ascending.length hstop hlong hlengthLt hcanonical
          hascendingPost.sorted hendpoints hstrictNext reversed hreverse
        rcases finishDescending_correct lt horder state hcompare source
            reversed.slice start nremaining (ascending.length + 1) hstop
            (by omega) (by omega) (by omega) hcanonical hinvariant with
          ⟨result, hfinish, hpost⟩
        refine ⟨result, ?_, hpost⟩
        unfold countRun?
        rw [if_pos hguard]
        simp only [countRunBindOptionAcross, hascendingState]
        rw [hascendingPost.fuel]
        simp only [Bool.false_eq_true, if_false]
        rw [if_neg hcomplete, if_pos hlong]
        rw [hfirstRead, hlastRead]
        simp only [bind, Option.bind]
        rw [if_neg hincreasing, hreverse.resultEq]
        simp only
        rw [hreverse.fuel]
        simp only [Bool.false_eq_true, if_false]
        exact hfinish
    · have hascendingOne : ascending.length = 1 := by
        have hlower := hascendingPost.lengthBounds.1
        omega
      have hnremainingTwo : 2 ≤ nremaining := by
        have hupper := hascendingPost.lengthBounds.2
        omega
      have hlengthLt : ascending.length < nremaining := by omega
      rcases hascendingPost.stoppedByDecrease hlengthLt with
        ⟨previous, next, hpreviousRead, hnextRead, hdecrease⟩
      have hfirstIndex : start < source.entries.size := by omega
      have hnextIndex : start + 1 < source.entries.size := by omega
      have hpreviousExact :
          source.read? (Int.ofNat start) = some source.entries[start] := by
        simpa using sortSlice_read_nat source start hfirstIndex
      have hnextExact :
          source.read? (Int.ofNat start + Int.ofNat 1) =
            some source.entries[start + 1] := by
        simpa using sortSlice_read_nat source (start + 1) hnextIndex
      have hpreviousRead' :
          source.read? (start : Int) = some previous := by
        simpa [hascendingOne] using hpreviousRead
      have hnextRead' :
          source.read? ((start : Int) + 1) = some next := by
        simpa [hascendingOne] using hnextRead
      have hpreviousExact' :
          source.read? (start : Int) = some source.entries[start] := by
        simpa using hpreviousExact
      have hnextExact' :
          source.read? ((start : Int) + 1) =
            some source.entries[start + 1] := by
        simpa using hnextExact
      rw [hpreviousExact'] at hpreviousRead'
      rw [hnextExact'] at hnextRead'
      have hpreviousEq : previous = source.entries[start] :=
        Option.some.inj hpreviousRead'.symm
      have hnextEq : next = source.entries[start + 1] :=
        Option.some.inj hnextRead'.symm
      have hstrict :
          lt source.entries[start + 1].key.value
            source.entries[start].key.value = true := by
        rw [← hnextEq, ← hpreviousEq]
        simpa [occurrenceComparator] using hdecrease
      have hinvariant := shortDescendingInvariant lt horder source start
        nremaining hstop hnremainingTwo hstrict
      rcases finishDescending_correct lt horder state hcompare source source
          start nremaining 2 hstop (by omega) (by omega) hnremainingTwo hcanonical
          hinvariant with ⟨result, hfinish, hpost⟩
      refine ⟨result, ?_, hpost⟩
      unfold countRun?
      rw [if_pos hguard]
      simp only [countRunBindOptionAcross, hascendingState]
      rw [hascendingPost.fuel]
      simp only [Bool.false_eq_true, if_false]
      rw [if_neg hcomplete, if_neg hlong]
      simpa [hascendingOne] using hfinish

/-- The actual traced `count_run` evaluator returns a nonempty sorted natural
run, and its length is at least two unless exactly one input element remains.
Whole entries are permuted only within the returned range, and tagged
comparator-equivalent keys retain their canonical origin order.

The strict-weak-order and canonical-origin hypotheses are correctness-only:
the safety certificate remains the arbitrary-comparator `countRun_safe`
certificate, and exact erasure identifies both statements with one execution. -/
theorem countRun_correct
    (lt : BoolComparator alpha) (horder : BoolStrictWeakOrder lt)
    (state : MergeState (Occurrence alpha) nu)
    (before : SortSlice (Occurrence alpha) nu)
    (base : Int) (nremaining : Nat)
    (hcompare : state.key_compare = occurrenceComparator lt)
    (hrange : SortSlice.RangeInBounds before base nremaining)
    (hpositive : 0 < nremaining)
    (hsizeRepresentable : nremaining ≤ PY_SSIZE_T_MAX)
    (hMode : SortSlice.ValuesModeInvariant state.a.hasValues before)
    (hcanonical :
      CountRunCanonicalRange lt before base.toNat nremaining) :
    ∃ result, CountRunCorrectnessPost lt state before base nremaining result := by
  have hbaseEq : Int.ofNat base.toNat = base :=
    Int.toNat_of_nonneg hrange.1
  have hstop : base.toNat + nremaining ≤ before.entries.size := by
    apply Int.ofNat_le.mp
    calc
      Int.ofNat (base.toNat + nremaining) =
          Int.ofNat base.toNat + Int.ofNat nremaining := by simp
      _ = base + Int.ofNat nremaining := by rw [hbaseEq]
      _ ≤ Int.ofNat before.entries.size := hrange.2
  rcases countRun_raw_correct lt horder state hcompare before base.toNat
      nremaining hstop hpositive hsizeRepresentable hcanonical with
    ⟨rawResult, hrawResultNat, hsemantic⟩
  have hrawResult : countRun? state before base nremaining = some rawResult := by
    rw [← hbaseEq]
    exact hrawResultNat
  rcases countRun_safe state before base nremaining hrange hpositive
      hsizeRepresentable hMode with ⟨safeResult, hsafety⟩
  have hsafeRaw : countRun? state before base nremaining = some safeResult := by
    have hresult := hsafety.resultEq
    change (countRunTraced? state before base nremaining).erase =
      some safeResult at hresult
    rw [hsafety.exactErasure] at hresult
    exact hresult
  rw [hrawResult] at hsafeRaw
  have hresultEq : rawResult = safeResult := Option.some.inj hsafeRaw
  subst safeResult
  refine ⟨rawResult, ?_⟩
  exact
    { safety := hsafety
      lengthBounds := hsemantic.lengthBounds
      minimumLength := hsemantic.minimumLength
      sorted := hsemantic.sorted
      stable := hsemantic.stable
      entryPermutation := hsemantic.entryPermutation
      frame := by simpa [hbaseEq] using hsemantic.frame }

/-! ## Concrete semantic regressions -/

private def countRunCorrectnessOccurrence (value origin : Nat) :
    Occurrence Nat :=
  { value := value, origin := origin }

private def countRunCorrectnessEntry (value origin payload : Nat) :
    SortSliceEntry (Occurrence Nat) Nat :=
  { key := countRunCorrectnessOccurrence value origin
    value := some payload }

private def countRunCorrectnessState
    (slice : SortSlice (Occurrence Nat) Nat) :
    MergeState (Occurrence Nat) Nat :=
  { min_gallop := MIN_GALLOP
    listlen := slice.entries.size
    basekeys := 0
    data := slice
    a := { cells := #[], backing := .inline, hasValues := true }
    alloced := 0
    pending := #[]
    key_compare := occurrenceComparator fun left right => decide (left < right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

private def countRunCorrectnessTaggedEqualSlice :
    SortSlice (Occurrence Nat) Nat :=
  { entries :=
      #[countRunCorrectnessEntry 3 0 30,
        countRunCorrectnessEntry 2 1 20,
        countRunCorrectnessEntry 2 2 21,
        countRunCorrectnessEntry 1 3 10] }

/-- The two equal `2` occurrences survive the descending double reversal in
origin order `1,2`, rather than being exposed in the temporary reversed order. -/
theorem countRun_correct_tagged_equal_block_regression :
    (countRunTraced?
      (countRunCorrectnessState countRunCorrectnessTaggedEqualSlice)
      countRunCorrectnessTaggedEqualSlice 0 4).result.map
        (fun result =>
          (result.length, result.fuelExhausted, result.slice.entries)) =
      some
        (4, false,
          #[countRunCorrectnessEntry 1 3 10,
            countRunCorrectnessEntry 2 1 20,
            countRunCorrectnessEntry 2 2 21,
            countRunCorrectnessEntry 3 0 30]) := by
  decide

private def countRunCorrectnessAllEqualSlice :
    SortSlice (Occurrence Nat) Nat :=
  { entries :=
      #[countRunCorrectnessEntry 2 0 20,
        countRunCorrectnessEntry 2 1 21,
        countRunCorrectnessEntry 2 2 22] }

/-- A fully equivalent run is accepted by the ascending scan and remains in
its canonical origin order. -/
theorem countRun_correct_all_equal_regression :
    (countRunTraced?
      (countRunCorrectnessState countRunCorrectnessAllEqualSlice)
      countRunCorrectnessAllEqualSlice 0 3).result.map
        (fun result =>
          (result.length, result.fuelExhausted, result.slice.entries)) =
      some (3, false, countRunCorrectnessAllEqualSlice.entries) := by
  decide

private def countRunCorrectnessExtensionSlice :
    SortSlice (Occurrence Nat) Nat :=
  { entries :=
      #[countRunCorrectnessEntry 3 0 30,
        countRunCorrectnessEntry 2 1 20,
        countRunCorrectnessEntry 1 2 10,
        countRunCorrectnessEntry 3 3 31,
        countRunCorrectnessEntry 4 4 40,
        countRunCorrectnessEntry 5 5 50,
        countRunCorrectnessEntry 0 6 0] }

/-- After normalizing `3,2,1`, the actual final ascending scan extends through
`3,4,5`; the two equivalent `3` occurrences remain in origin order. -/
theorem countRun_correct_descending_then_ascending_regression :
    (countRunTraced?
      (countRunCorrectnessState countRunCorrectnessExtensionSlice)
      countRunCorrectnessExtensionSlice 0 7).result.map
        (fun result =>
          (result.length, result.fuelExhausted, result.slice.entries)) =
      some
        (6, false,
          #[countRunCorrectnessEntry 1 2 10,
            countRunCorrectnessEntry 2 1 20,
            countRunCorrectnessEntry 3 0 30,
            countRunCorrectnessEntry 3 3 31,
            countRunCorrectnessEntry 4 4 40,
            countRunCorrectnessEntry 5 5 50,
            countRunCorrectnessEntry 0 6 0]) := by
  decide

private def countRunCorrectnessNonzeroBaseSlice :
    SortSlice (Occurrence Nat) Nat :=
  { entries :=
      #[countRunCorrectnessEntry 99 0 990,
        countRunCorrectnessEntry 3 1 30,
        countRunCorrectnessEntry 2 2 20,
        countRunCorrectnessEntry 1 3 10,
        countRunCorrectnessEntry 77 4 770] }

/-- With base one, both sentinels are untouched while exactly the selected
three-entry descending range is normalized. -/
theorem countRun_correct_nonzero_base_frame_regression :
    (countRunTraced?
      (countRunCorrectnessState countRunCorrectnessNonzeroBaseSlice)
      countRunCorrectnessNonzeroBaseSlice 1 3).result.map
        (fun result =>
          (result.length, result.fuelExhausted, result.slice.entries)) =
      some
        (3, false,
          #[countRunCorrectnessEntry 99 0 990,
            countRunCorrectnessEntry 1 3 10,
            countRunCorrectnessEntry 2 2 20,
            countRunCorrectnessEntry 3 1 30,
            countRunCorrectnessEntry 77 4 770]) := by
  decide

end CPythonListsort
