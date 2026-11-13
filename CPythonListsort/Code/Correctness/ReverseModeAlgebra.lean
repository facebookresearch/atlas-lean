/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Correctness.OriginRelabelEquivariance

/-!
# Order and stability algebra for reverse mode

These lemmas contain no evaluator reasoning.  They formalize the mathematical
effect of CPython's reverse-before / stable-forward-sort / reverse-after
pattern once evaluator equivariance has supplied the mirrored pre-finish
result.
-/

namespace CPythonListsort

universe u

/-- The argument-swapped comparator requested by `reverse = true`. -/
def swappedComparator (lt : BoolComparator α) : BoolComparator α :=
  fun left right => lt right left

/-- Comparator selected by the public `reverse` flag. -/
def requestedComparator (lt : BoolComparator α) (reverse : Bool) :
    BoolComparator α :=
  if reverse then swappedComparator lt else lt

@[simp]
theorem requestedComparator_false (lt : BoolComparator α) :
    requestedComparator lt false = lt := by
  rfl

@[simp]
theorem requestedComparator_true (lt : BoolComparator α) :
    requestedComparator lt true = swappedComparator lt := by
  rfl

/-- Lifting a swapped comparator to carried occurrences is definitionally the
same operation as swapping the lifted comparator. -/
@[simp]
theorem occurrenceComparator_swapped (lt : BoolComparator α) :
    occurrenceComparator (swappedComparator lt) =
      swappedComparator (occurrenceComparator lt) := by
  rfl

/-- Strict weak orders are closed under argument swapping. -/
theorem BoolStrictWeakOrder.swapped
    {lt : BoolComparator α} (h : BoolStrictWeakOrder lt) :
    BoolStrictWeakOrder (swappedComparator lt) := by
  refine
    { toIsStrictWeakOrder :=
        { toIsStrictOrder :=
            { toIrrefl := ⟨fun value => h.irrefl value⟩
              toIsTrans :=
                ⟨fun first second third hfirstSecond hsecondThird =>
                  h.trans third second first hsecondThird hfirstSecond⟩ }
          incomp_trans := ?_ } }
  intro first second third hfirstSecond hsecondThird
  have hfirstSecond' :
      ¬lt first second = true ∧ ¬lt second first = true := by
    simpa [swappedComparator, and_comm] using hfirstSecond
  have hsecondThird' :
      ¬lt second third = true ∧ ¬lt third second = true := by
    simpa [swappedComparator, and_comm] using hsecondThird
  have hfirstThird := h.incomp_trans first second third
    hfirstSecond' hsecondThird'
  simpa [swappedComparator, and_comm] using hfirstThird

/-- Either public direction selected by the Boolean mode is again a strict
weak order. -/
theorem BoolStrictWeakOrder.requestedComparator
    {lt : BoolComparator α} (h : BoolStrictWeakOrder lt) (reverse : Bool) :
    BoolStrictWeakOrder (requestedComparator lt reverse) := by
  cases reverse
  · simpa using h
  · simpa using h.swapped

/-- Comparator equivalence is unchanged when the comparator arguments are
swapped. -/
theorem comparatorEquivalent_swapped (lt : BoolComparator α) (left right : α) :
    ComparatorEquivalent (swappedComparator lt) left right ↔
      ComparatorEquivalent lt left right := by
  simp [ComparatorEquivalent, swappedComparator, and_comm]

/-- Reversing a forward-sorted array produces an array sorted by the swapped
comparator. -/
theorem Sorted.reverse_swapped
    {lt : BoolComparator α} {values : Array α}
    (h : Sorted lt values) :
    Sorted (swappedComparator lt) values.reverse := by
  rw [Sorted, Array.toList_reverse, List.pairwise_reverse]
  simpa [Sorted, swappedComparator] using h

/-- Inside the admitted origin interval, mirroring strictly reverses origin
order. -/
theorem mirrorOrigin_lt_mirrorOrigin
    {size earlier later : Nat} (hearlier : earlier < later)
    (hlater : later < size) :
    mirrorOrigin size later < mirrorOrigin size earlier := by
  rw [mirrorOrigin_of_lt size later hlater,
    mirrorOrigin_of_lt size earlier (hearlier.trans hlater)]
  omega

/-- On the live origin interval, mirroring reverses strict order exactly. -/
theorem mirrorOrigin_lt_mirrorOrigin_iff
    {size left right : Nat} (hleft : left < size) (hright : right < size) :
    mirrorOrigin size left < mirrorOrigin size right ↔ right < left := by
  rw [mirrorOrigin_of_lt size left hleft,
    mirrorOrigin_of_lt size right hright]
  omega

/-- A sequence with descending origins inside each comparator-equivalence
class.  This is the natural intermediate stability contract after origin
mirroring but before CPython's final whole-array reversal. -/
def ReverseStableOccurrencePermutation (lt : BoolComparator α)
    (canonical output : List (Occurrence α)) : Prop :=
  output.Perm canonical ∧
    output.Pairwise fun earlier later =>
      ComparatorEquivalent lt earlier.value later.value →
        later.origin < earlier.origin

namespace ReverseStableOccurrencePermutation

/-- Reversing the output turns reverse stability into ordinary stability for
the argument-swapped comparator; the canonical sequence is used only through
permutation and therefore remains unchanged. -/
theorem reverse
    {lt : BoolComparator α} {canonical output : List (Occurrence α)}
    (h : ReverseStableOccurrencePermutation lt canonical output) :
    StableOccurrencePermutation (swappedComparator lt) canonical
      output.reverse := by
  constructor
  · exact output.reverse_perm.trans h.1
  · rw [List.pairwise_reverse]
    apply h.2.imp
    intro earlier later hstable hequivalent
    rw [comparatorEquivalent_swapped] at hequivalent
    exact hstable ⟨hequivalent.2, hequivalent.1⟩

end ReverseStableOccurrencePermutation

/-- Mirroring every in-range origin changes ordinary occurrence stability into
reverse occurrence stability, without changing the sequence order. -/
theorem StableOccurrencePermutation.mirror
    {lt : BoolComparator α} {size : Nat}
    {canonical output : List (Occurrence α)}
    (h : StableOccurrencePermutation lt canonical output)
    (hCanonicalOrigins : ∀ occurrence ∈ canonical, occurrence.origin < size) :
    ReverseStableOccurrencePermutation lt
      (canonical.map (mirrorOccurrence size))
      (output.map (mirrorOccurrence size)) := by
  constructor
  · exact h.1.map (mirrorOccurrence size)
  · have hmirrored : output.Pairwise fun earlier later =>
        ComparatorEquivalent lt
            (mirrorOccurrence size earlier).value
            (mirrorOccurrence size later).value →
          (mirrorOccurrence size later).origin <
            (mirrorOccurrence size earlier).origin := by
      apply h.2.imp_of_mem
      intro earlier later _ hlater hstable hequivalent
      exact mirrorOrigin_lt_mirrorOrigin (hstable hequivalent)
        (hCanonicalOrigins later (h.1.mem_iff.mp hlater))
    exact hmirrored.map (mirrorOccurrence size) (fun _ _ relation => relation)

/-- Mirroring carried origins is invisible to sortedness; reversing the
mirrored array therefore yields sortedness for the swapped value comparator. -/
theorem Sorted.mirror_reverse_swapped
    {lt : BoolComparator α} {size : Nat}
    {entries : Array (Occurrence α)}
    (h : Sorted (occurrenceComparator lt) entries) :
    Sorted (occurrenceComparator (swappedComparator lt))
      (entries.map (mirrorOccurrence size)).reverse := by
  have hmirrored :
      Sorted (occurrenceComparator lt)
        (entries.map (mirrorOccurrence size)) := by
    rw [Sorted, Array.toList_map]
    exact h.map (mirrorOccurrence size) (by
      intro earlier later hrelation
      exact hrelation)
  simpa only [occurrenceComparator_swapped] using hmirrored.reverse_swapped

/-- Occurrence-level sortedness is exactly sortedness of the visible value
projection, because the lifted comparator never observes origins. -/
theorem sorted_occurrenceComparator_iff_values
    (lt : BoolComparator α) (entries : Array (Occurrence α)) :
    Sorted (occurrenceComparator lt) entries ↔
      Sorted lt (entries.map Occurrence.value) := by
  unfold Sorted
  rw [Array.toList_map, List.pairwise_map]
  rfl

/-- Forward-facing projection of occurrence sortedness to public values. -/
theorem Sorted.values
    {lt : BoolComparator α} {entries : Array (Occurrence α)}
    (h : Sorted (occurrenceComparator lt) entries) :
    Sorted lt (entries.map Occurrence.value) :=
  (sorted_occurrenceComparator_iff_values lt entries).mp h

/-- Public stability always carries the ordinary value-permutation fact. -/
theorem Stable.values_perm
    {lt : BoolComparator α} {xs : Array α} {ys : TaggedOutput α}
    (h : Stable lt xs ys) :
    ys.values.toList.Perm xs.toList := by
  have htagValues :
      (tagOccurrences xs).toList.map Occurrence.value = xs.toList := by
    simpa [TaggedOutput.fromInput, TaggedOutput.values, Array.toList_map] using
      congrArg Array.toList (TaggedOutput.values_fromInput xs)
  unfold TaggedOutput.values
  rw [Array.toList_map]
  rw [← htagValues]
  exact h.1.map Occurrence.value

namespace SortSlice

/-- Reverse the physical paired-entry array, keeping each key attached to its
optional payload. -/
def reverseEntries (slice : SortSlice κ ν) : SortSlice κ ν :=
  { entries := slice.entries.reverse }

@[simp]
theorem reverseEntries_entries (slice : SortSlice κ ν) :
    slice.reverseEntries.entries = slice.entries.reverse := by
  rfl

@[simp]
theorem reverseEntries_size (slice : SortSlice κ ν) :
    slice.reverseEntries.entries.size = slice.entries.size := by
  simp [reverseEntries]

@[simp]
theorem reverseEntries_reverseEntries (slice : SortSlice κ ν) :
    slice.reverseEntries.reverseEntries = slice := by
  cases slice
  simp [reverseEntries]

/-- Reversal cannot change keyed/unkeyed payload representation mode. -/
theorem ValuesModeInvariant.reverseEntries
    {hasKeyfunc : Bool} {slice : SortSlice κ ν}
    (h : ValuesModeInvariant hasKeyfunc slice) :
    ValuesModeInvariant hasKeyfunc slice.reverseEntries := by
  intro index hindex
  have hindex' : index < slice.entries.size := by
    simpa [reverseEntries] using hindex
  have hsource : slice.entries.size - 1 - index < slice.entries.size := by
    omega
  simpa [reverseEntries] using
    h (slice.entries.size - 1 - index) hsource

end SortSlice

namespace ListSortInput

/-- A validated top-level input with its complete paired-entry array reversed. -/
def reverseEntries (input : ListSortInput κ ν) : ListSortInput κ ν where
  slice := input.slice.reverseEntries
  hasKeyfunc := input.hasKeyfunc
  valuesMode := input.valuesMode.reverseEntries

@[simp]
theorem reverseEntries_slice (input : ListSortInput κ ν) :
    input.reverseEntries.slice = input.slice.reverseEntries := by
  rfl

@[simp]
theorem reverseEntries_hasKeyfunc (input : ListSortInput κ ν) :
    input.reverseEntries.hasKeyfunc = input.hasKeyfunc := by
  rfl

/-- The reversed validated input exposes its retained representation proof. -/
theorem reverseEntries_valuesMode (input : ListSortInput κ ν) :
    SortSlice.ValuesModeInvariant input.hasKeyfunc
      input.reverseEntries.slice :=
  input.reverseEntries.valuesMode

@[simp]
theorem reverseEntries_reverseEntries (input : ListSortInput κ ν) :
    input.reverseEntries.reverseEntries = input := by
  cases input
  simp [reverseEntries, SortSlice.reverseEntries]

end ListSortInput

/-- Canonical occurrence tagging records the exact source index. -/
@[simp]
theorem tagOccurrences_getElem_origin (xs : Array α) (index : Nat)
    (hindex : index < (tagOccurrences xs).size) :
    (tagOccurrences xs)[index].origin = index := by
  simp [tagOccurrences]

/-- Every canonical occurrence origin lies in the source array. -/
theorem tagOccurrences_origin_lt_size
    {xs : Array α} {occurrence : Occurrence α}
    (hoccurrence : occurrence ∈ (tagOccurrences xs).toList) :
    occurrence.origin < xs.size := by
  rcases List.mem_iff_getElem.mp hoccurrence with
    ⟨index, hindex, hoccurrenceEq⟩
  rw [← hoccurrenceEq]
  simp only [Array.getElem_toList]
  rw [tagOccurrences_getElem_origin]
  simpa [tagOccurrences] using hindex

/-- Tagging an already reversed source and then mirroring its new indices is
exactly the original tagged sequence in reverse order. -/
theorem tagOccurrences_reverse_map_mirror (xs : Array α) :
    (tagOccurrences xs.reverse).map (mirrorOccurrence xs.size) =
      (tagOccurrences xs).reverse := by
  apply Array.ext <;>
    simp [tagOccurrences, mirrorOccurrence, mirrorOrigin]
  omega

/-- Whole-entry form of `tagOccurrences_reverse_map_mirror`: optional payloads
stay attached while the key origins are mirrored. -/
theorem tagSortSliceOccurrences_reverseEntries_map_mirror
    (source : SortSlice κ ν) :
    mirrorSortSlice source.entries.size
        (tagSortSliceOccurrences source.reverseEntries) =
      (tagSortSliceOccurrences source).reverseEntries := by
  cases source with
  | mk entries =>
      simp only [SortSlice.reverseEntries, tagSortSliceOccurrences,
        mirrorSortSlice]
      congr 1
      apply Array.ext <;>
        simp [mirrorSortSliceEntry, mirrorOccurrence, mirrorOrigin]
      omega

/-- Origin mirroring commutes exactly with physical whole-entry reversal. -/
theorem mirrorSortSlice_reverseEntries (size : Nat)
    (slice : SortSlice (Occurrence κ) ν) :
    mirrorSortSlice size slice.reverseEntries =
      (mirrorSortSlice size slice).reverseEntries := by
  cases slice with
  | mk entries =>
      simp [mirrorSortSlice, SortSlice.reverseEntries, Array.map_reverse]

/-- Validated-input specialization of the exact tag/mirror/reverse identity. -/
theorem ListSortInput.mirror_withOccurrenceKeys_reverseEntries
    (input : ListSortInput κ ν) :
    mirrorSortSlice input.slice.entries.size
        input.reverseEntries.withOccurrenceKeys.slice =
      input.withOccurrenceKeys.slice.reverseEntries := by
  exact tagSortSliceOccurrences_reverseEntries_map_mirror input.slice

/-- A whole-entry snapshot against the physically reversed source transports
back to the original source after origin mirroring. -/
theorem EntrySnapshotPermutation.mirror_reversedSource
    {source : SortSlice κ ν}
    {current : SortSlice (Occurrence κ) ν}
    (h : EntrySnapshotPermutation source.reverseEntries current) :
    EntrySnapshotPermutation source
      (mirrorSortSlice source.entries.size current) := by
  have hmapped := h.map (mirrorSortSliceEntry source.entries.size)
  have hmapped' :
      (mirrorSortSlice source.entries.size current).entries.toList.Perm
        (mirrorSortSlice source.entries.size
          (tagSortSliceOccurrences source.reverseEntries)).entries.toList := by
    simpa [EntrySnapshotPermutation, mirrorSortSlice,
      Array.toList_map] using hmapped
  rw [tagSortSliceOccurrences_reverseEntries_map_mirror] at hmapped'
  unfold EntrySnapshotPermutation
  exact hmapped'.trans (by
    simp [SortSlice.reverseEntries])

/-- A stable result for the physically reversed source becomes reverse-stable
against the original source once its carried origins are mirrored. -/
theorem stable_reversedSource_mirror
    {lt : BoolComparator α} {xs : Array α}
    {output : List (Occurrence α)}
    (h : StableOccurrencePermutation lt
      (tagOccurrences xs.reverse).toList output) :
    ReverseStableOccurrencePermutation lt (tagOccurrences xs).toList
      (output.map (mirrorOccurrence xs.size)) := by
  have hOrigins :
      ∀ occurrence ∈ (tagOccurrences xs.reverse).toList,
        occurrence.origin < xs.size := by
    intro occurrence hoccurrence
    simpa using tagOccurrences_origin_lt_size hoccurrence
  have hmirrored := h.mirror hOrigins
  have hCanonical :
      (tagOccurrences xs.reverse).toList.map (mirrorOccurrence xs.size) =
        (tagOccurrences xs).toList.reverse := by
    simpa [Array.toList_map] using
      congrArg Array.toList (tagOccurrences_reverse_map_mirror xs)
  constructor
  · have hperm := hmirrored.1
    rw [hCanonical] at hperm
    exact hperm.trans (tagOccurrences xs).toList.reverse_perm
  · exact hmirrored.2

/-- CPython's final whole-array reversal turns the mirrored intermediate
result into an ordinary stable result for the requested swapped comparator. -/
theorem stable_reversedSource_mirror_reverse
    {lt : BoolComparator α} {xs : Array α}
    {output : List (Occurrence α)}
    (h : StableOccurrencePermutation lt
      (tagOccurrences xs.reverse).toList output) :
    StableOccurrencePermutation (swappedComparator lt)
      (tagOccurrences xs).toList
      (output.map (mirrorOccurrence xs.size)).reverse := by
  exact (stable_reversedSource_mirror h).reverse

/-- Mirroring every carried origin and then reversing the sequence turns
forward occurrence stability into stability for the swapped comparator.

`canonicalFinal` names the desired original canonical sequence.  Reverse-mode
assembly supplies its equality with the mirrored/reversed canonical sequence
created from the physically reversed source. -/
theorem StableOccurrencePermutation.mirror_reverse
    {lt : BoolComparator α} {size : Nat}
    {canonical output canonicalFinal : List (Occurrence α)}
    (h : StableOccurrencePermutation lt canonical output)
    (hCanonicalOrigins : ∀ occurrence ∈ canonical, occurrence.origin < size)
    (hCanonicalFinal :
      (canonical.map (mirrorOccurrence size)).reverse = canonicalFinal) :
    StableOccurrencePermutation (swappedComparator lt) canonicalFinal
      ((output.map (mirrorOccurrence size)).reverse) := by
  constructor
  · have hmap := h.1.map (mirrorOccurrence size)
    have hreverseOutput :=
      List.reverse_perm (output.map (mirrorOccurrence size))
    have hreverseCanonical :=
      (List.reverse_perm (canonical.map (mirrorOccurrence size))).symm
    rw [← hCanonicalFinal]
    exact hreverseOutput.trans (hmap.trans hreverseCanonical)
  · rw [List.pairwise_reverse]
    have hmirrored : output.Pairwise fun earlier later =>
        ComparatorEquivalent (swappedComparator lt)
            (mirrorOccurrence size later).value
            (mirrorOccurrence size earlier).value →
          (mirrorOccurrence size later).origin <
            (mirrorOccurrence size earlier).origin := by
      apply h.2.imp_of_mem
      intro earlier later hearlier hlater hstable hequivalent
      rw [comparatorEquivalent_swapped] at hequivalent
      have hequivalent' :
          ComparatorEquivalent lt earlier.value later.value :=
        ⟨hequivalent.2, hequivalent.1⟩
      have horigin : earlier.origin < later.origin := hstable hequivalent'
      exact mirrorOrigin_lt_mirrorOrigin horigin
        (hCanonicalOrigins later (h.1.mem_iff.mp hlater))
    exact hmirrored.map (mirrorOccurrence size) (fun _ _ relation => relation)

end CPythonListsort
