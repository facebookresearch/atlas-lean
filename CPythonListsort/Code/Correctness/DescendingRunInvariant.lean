/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.Order
import Code.Correctness.DescendingRunNormalization

/-!
# Stable-order invariant for `count_run`'s descending phase

This file contains only pure list/order algebra.  The executable count-run
proof instantiates it with the range read from the transcribed machine.
-/

namespace CPythonListsort

universe u

namespace DescendingRunSpec

/-- Pairwise relation corresponding to ascending `Sorted` order on occurrence
lists: a later occurrence must not compare strictly before an earlier one. -/
def SortedRelation (lt : BoolComparator α) :
    Occurrence α → Occurrence α → Prop :=
  fun earlier later => occurrenceComparator lt later earlier = false

/-- Pairwise occurrence-stability relation shared with
`StableOccurrencePermutation`. -/
def StableRelation (lt : BoolComparator α) :
    Occurrence α → Occurrence α → Prop :=
  fun earlier later =>
    ComparatorEquivalent lt earlier.value later.value →
      earlier.origin < later.origin

@[simp]
private theorem normalize_length (xs : List α) (tailLength : Nat) :
    (normalize xs tailLength).length = xs.length := by
  simp [normalize]

private theorem pairwise_insert_middle
    {R : α → α → Prop} {pre suf : List α} {x : α}
    (hpair : (pre ++ suf).Pairwise R)
    (hleft : ∀ a ∈ pre, R a x)
    (hright : ∀ b ∈ suf, R x b) :
    (pre ++ [x] ++ suf).Pairwise R := by
  have hparts := List.pairwise_append.mp hpair
  apply List.pairwise_append.mpr
  refine ⟨?_, hparts.2.1, ?_⟩
  · apply List.pairwise_append.mpr
    refine ⟨hparts.1, List.pairwise_singleton R x, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst b
    exact hleft a ha
  · intro a ha b hb
    rw [List.mem_append] at ha
    rcases ha with ha | ha
    · exact hparts.2.2 a ha b hb
    · simp only [List.mem_singleton] at ha
      subst a
      exact hright b hb

/-- When the final equivalence block is the whole nonempty scanned prefix,
normalization leaves that prefix unchanged. -/
@[simp]
theorem normalize_full (xs : List α) :
    normalize xs xs.length = xs := by
  simp [normalize]

/-- Appending an untouched suffix preserves stability when the canonical whole
sequence already supplies the prefix-to-suffix origin ordering. -/
theorem stableOccurrencePermutation_append_untouched_suffix
    {lt : BoolComparator α}
    {canonicalPrefix outputPrefix suffix : List (Occurrence α)}
    (hprefix : StableOccurrencePermutation lt canonicalPrefix outputPrefix)
    (hcanonical : (canonicalPrefix ++ suffix).Pairwise
      (StableRelation lt)) :
    StableOccurrencePermutation lt (canonicalPrefix ++ suffix)
      (outputPrefix ++ suffix) := by
  refine ⟨hprefix.1.append_right suffix, ?_⟩
  have hparts := List.pairwise_append.mp hcanonical
  apply List.pairwise_append.mpr
  refine ⟨hprefix.2, hparts.2.1, ?_⟩
  intro a ha b hb
  exact hparts.2.2 a (hprefix.1.mem_iff.mp ha) b hb

/-- Moving a newly appended element to any insertion point preserves the
permutation of the extended canonical sequence. -/
theorem normalize_append_equivalent_perm
    (current canonical : List α) (x : α) (tailLength : Nat)
    (htail : tailLength ≤ current.length)
    (hperm : (normalize current tailLength).Perm canonical) :
    (normalize (current ++ [x]) (tailLength + 1)).Perm
      (canonical ++ [x]) := by
  rw [normalize_append_equivalent current x tailLength htail]
  have hswap :
      ([x] ++ (normalize current tailLength).drop tailLength).Perm
        ((normalize current tailLength).drop tailLength ++ [x]) :=
    List.perm_append_comm
  have hinsert :
      ((normalize current tailLength).take tailLength ++ [x] ++
          (normalize current tailLength).drop tailLength).Perm
        (normalize current tailLength ++ [x]) := by
    have hmove := hswap.append_left
      ((normalize current tailLength).take tailLength)
    simpa only [← List.append_assoc, List.take_append_drop] using hmove
  exact hinsert.trans (hperm.append_right [x])

/-- The strict-smaller branch prepends the new normalized element while the
canonical sequence appends it; those sequences are permutations. -/
theorem normalize_after_strict_perm
    (current canonical : List α) (x : α) (tailLength : Nat)
    (hperm : (normalize current tailLength).Perm canonical) :
    (normalize (reverseSuffix current tailLength ++ [x]) 1).Perm
      (canonical ++ [x]) := by
  rw [normalize_after_strict]
  have hswap :
      ([x] ++ normalize current tailLength).Perm
        (normalize current tailLength ++ [x]) :=
    List.perm_append_comm
  exact hswap.trans (hperm.append_right [x])

/-- The semantic state carried through `count_run`'s descending scan.

`normalize current tailLength` is the stable ascending sequence that would be
obtained by closing the current equality block and reversing the whole scanned
prefix. -/
structure Invariant (lt : BoolComparator α)
    (canonical current : List (Occurrence α)) (tailLength : Nat) : Prop where
  current_ne : current ≠ []
  tail_pos : 0 < tailLength
  tail_le : tailLength ≤ current.length
  sorted : (normalize current tailLength).Pairwise (SortedRelation lt)
  stable : StableOccurrencePermutation lt canonical
    (normalize current tailLength)
  tail_equiv :
    ∀ x ∈ (normalize current tailLength).take tailLength,
      ComparatorEquivalent lt x.value (current.getLast current_ne).value
  rest_greater :
    ∀ x ∈ (normalize current tailLength).drop tailLength,
      lt (current.getLast current_ne).value x.value = true

private theorem strict_reverse_false
    {lt : BoolComparator α} (horder : BoolStrictWeakOrder lt)
    {a b : α} (hab : lt a b = true) : lt b a = false := by
  apply Bool.eq_false_iff.mpr
  intro hba
  exact horder.irrefl a (horder.trans a b a hab hba)

private theorem strict_of_equivalent_left
    {lt : BoolComparator α} (horder : BoolStrictWeakOrder lt)
    {a a' b : α} (hequiv : ComparatorEquivalent lt a a')
    (hstrict : lt a' b = true) : lt a b = true := by
  by_contra hnot
  have hab : lt a b = false := Bool.eq_false_iff.mpr hnot
  by_cases hba : lt b a = true
  · have hnotA'A : ¬lt a' a = true := by simp [hequiv.2]
    exact False.elim (hnotA'A (horder.trans a' b a hstrict hba))
  · have hbaFalse : lt b a = false := Bool.eq_false_iff.mpr hba
    have hincompA'A : ¬lt a' a = true ∧ ¬lt a a' = true := by
      simp [hequiv.1, hequiv.2]
    have hincompAB : ¬lt a b = true ∧ ¬lt b a = true := by
      simp [hab, hbaFalse]
    exact (horder.incomp_trans a' a b hincompA'A hincompAB).1 hstrict

private theorem strict_of_equivalent_right
    {lt : BoolComparator α} (horder : BoolStrictWeakOrder lt)
    {a b b' : α} (hstrict : lt a b = true)
    (hequiv : ComparatorEquivalent lt b b') : lt a b' = true := by
  by_contra hnot
  have hab' : lt a b' = false := Bool.eq_false_iff.mpr hnot
  by_cases hb'a : lt b' a = true
  · have hnotB'B : ¬lt b' b = true := by simp [hequiv.2]
    exact False.elim (hnotB'B (horder.trans b' a b hb'a hstrict))
  · have hb'aFalse : lt b' a = false := Bool.eq_false_iff.mpr hb'a
    have hincompAB' : ¬lt a b' = true ∧ ¬lt b' a = true := by
      simp [hab', hb'aFalse]
    have hincompB'B : ¬lt b' b = true ∧ ¬lt b b' = true := by
      simp [hequiv.1, hequiv.2]
    exact (horder.incomp_trans a b' b hincompAB' hincompB'B).1 hstrict

namespace Invariant

/-- A nonempty already-sorted stable equivalence block initializes the
descending invariant with the complete list as its final block. -/
theorem of_equivalent_block
    {lt : BoolComparator α} {current : List (Occurrence α)}
    (hne : current ≠ [])
    (hsorted : current.Pairwise (SortedRelation lt))
    (hstable : current.Pairwise (StableRelation lt))
    (hall : ∀ x ∈ current,
      ComparatorEquivalent lt x.value (current.getLast hne).value) :
    Invariant lt current current current.length := by
  refine
    { current_ne := hne
      tail_pos := List.length_pos_of_ne_nil hne
      tail_le := le_rfl
      sorted := by simpa using hsorted
      stable := ⟨by simp, by
        unfold StableRelation at hstable
        simpa only [normalize_full] using hstable⟩
      tail_equiv := ?_
      rest_greater := ?_ }
  · intro x hx
    simpa using hall x (by simpa using hx)
  · intro x hx
    simp at hx

/-- Every single occurrence inhabits the descending-run invariant.  This is
the public seed consumed by the first successful `count_run` read. -/
theorem singleton
    {lt : BoolComparator α} (horder : BoolStrictWeakOrder lt)
    (x : Occurrence α) : Invariant lt [x] [x] 1 := by
  refine of_equivalent_block (by simp) (by simp) (by simp) ?_
  intro y hy
  simp only [List.mem_singleton] at hy
  subst y
  exact horder.comparatorEquivalent_equivalence.refl x.value

/-- Extending the final comparator-equivalence block preserves the semantic
descending-run invariant.  The origin premise is exactly the stability fact
needed for the newly appended occurrence against the canonical prefix. -/
theorem extend_equivalent
    {lt : BoolComparator α} (horder : BoolStrictWeakOrder lt)
    {canonical current : List (Occurrence α)} {tailLength : Nat}
    (h : Invariant lt canonical current tailLength)
    (x : Occurrence α)
    (hequivalent : ComparatorEquivalent lt x.value
      (current.getLast h.current_ne).value)
    (horigin : ∀ y ∈ canonical,
      ComparatorEquivalent lt y.value x.value → y.origin < x.origin) :
    Invariant lt (canonical ++ [x]) (current ++ [x])
      (tailLength + 1) := by
  let normalized := normalize current tailLength
  let pre := normalized.take tailLength
  let suf := normalized.drop tailLength
  have hsplit : pre ++ suf = normalized := by
    change normalized.take tailLength ++ normalized.drop tailLength = normalized
    exact List.take_append_drop tailLength normalized
  have hsortedSplit : (pre ++ suf).Pairwise (SortedRelation lt) := by
    rw [hsplit]
    exact h.sorted
  have hstableSplit : (pre ++ suf).Pairwise (StableRelation lt) := by
    rw [hsplit]
    exact h.stable.2
  have hequivRel := horder.comparatorEquivalent_equivalence
  have hxRest : ∀ y ∈ suf, lt x.value y.value = true := by
    intro y hy
    exact strict_of_equivalent_left horder hequivalent
      (h.rest_greater y (by simpa [suf] using hy))
  have hsortedNew : (pre ++ [x] ++ suf).Pairwise (SortedRelation lt) := by
    apply pairwise_insert_middle hsortedSplit
    · intro y hy
      have hyEquiv := h.tail_equiv y (by simpa [pre] using hy)
      have hxy : ComparatorEquivalent lt x.value y.value :=
        hequivRel.trans hequivalent (hequivRel.symm hyEquiv)
      exact hxy.1
    · intro y hy
      exact strict_reverse_false horder (hxRest y hy)
  have hstableNew : (pre ++ [x] ++ suf).Pairwise (StableRelation lt) := by
    apply pairwise_insert_middle hstableSplit
    · intro y hy _
      apply horigin y
      · apply h.stable.1.mem_iff.mp
        exact List.mem_of_mem_take (by simpa [pre] using hy)
      · exact hequivRel.trans
          (h.tail_equiv y (by simpa [pre] using hy))
          (hequivRel.symm hequivalent)
    · intro y hy hxy
      have htrue := hxRest y hy
      simp [hxy.1] at htrue
  have hnorm :
      normalize (current ++ [x]) (tailLength + 1) = pre ++ [x] ++ suf := by
    simpa [pre, suf, normalized] using
      normalize_append_equivalent current x tailLength h.tail_le
  have hpreLength : pre.length = tailLength := by
    simp [pre, normalized, h.tail_le]
  have hprefixLength : (pre ++ [x]).length = tailLength + 1 := by
    simp [hpreLength]
  have htake :
      (pre ++ [x] ++ suf).take (tailLength + 1) = pre ++ [x] := by
    rw [← hprefixLength]
    exact List.take_left
  have hdrop :
      (pre ++ [x] ++ suf).drop (tailLength + 1) = suf := by
    rw [← hprefixLength]
    exact List.drop_left
  refine
    { current_ne := by simp
      tail_pos := by omega
      tail_le := by
        simpa only [List.length_append, List.length_singleton] using
          Nat.add_le_add_right h.tail_le 1
      sorted := ?_
      stable := ?_
      tail_equiv := ?_
      rest_greater := ?_ }
  · rw [hnorm]
    exact hsortedNew
  · constructor
    · exact normalize_append_equivalent_perm current canonical x tailLength
        h.tail_le h.stable.1
    · rw [hnorm]
      exact hstableNew
  · intro y hy
    rw [hnorm, htake] at hy
    rw [List.getLast_append_singleton]
    rw [List.mem_append] at hy
    rcases hy with hy | hy
    · exact hequivRel.trans
        (h.tail_equiv y (by simpa [pre] using hy))
        (hequivRel.symm hequivalent)
    · simp only [List.mem_singleton] at hy
      subst y
      exact hequivRel.refl x.value
  · intro y hy
    rw [hnorm, hdrop] at hy
    rw [List.getLast_append_singleton]
    exact hxRest y hy

/-- Appending a strictly smaller occurrence closes and reverses the previous
equivalence block, then starts a singleton final block. -/
theorem extend_strict
    {lt : BoolComparator α} (horder : BoolStrictWeakOrder lt)
    {canonical current : List (Occurrence α)} {tailLength : Nat}
    (h : Invariant lt canonical current tailLength)
    (x : Occurrence α)
    (hstrict : lt x.value (current.getLast h.current_ne).value = true) :
    Invariant lt (canonical ++ [x])
      (reverseSuffix current tailLength ++ [x]) 1 := by
  let normalized := normalize current tailLength
  have hequivRel := horder.comparatorEquivalent_equivalence
  have hxAll : ∀ y ∈ normalized, lt x.value y.value = true := by
    intro y hy
    have hySplit :
        y ∈ normalized.take tailLength ∨
          y ∈ normalized.drop tailLength := by
      rw [← List.mem_append]
      simpa only [List.take_append_drop] using hy
    rcases hySplit with hy | hy
    · exact strict_of_equivalent_right horder hstrict
        (hequivRel.symm
          (h.tail_equiv y (by simpa [normalized] using hy)))
    · exact horder.trans x.value (current.getLast h.current_ne).value
        y.value hstrict
        (h.rest_greater y (by simpa [normalized] using hy))
  have hnorm :
      normalize (reverseSuffix current tailLength ++ [x]) 1 =
        x :: normalized := by
    simpa [normalized] using normalize_after_strict current x tailLength
  refine
    { current_ne := by simp
      tail_pos := by omega
      tail_le := by simp
      sorted := ?_
      stable := ?_
      tail_equiv := ?_
      rest_greater := ?_ }
  · rw [hnorm]
    apply List.pairwise_cons.mpr
    refine ⟨?_, h.sorted⟩
    intro y hy
    exact strict_reverse_false horder (hxAll y (by simpa [normalized] using hy))
  · constructor
    · exact normalize_after_strict_perm current canonical x tailLength
        h.stable.1
    · rw [hnorm]
      apply List.pairwise_cons.mpr
      refine ⟨?_, h.stable.2⟩
      intro y hy hxy
      have htrue := hxAll y (by simpa [normalized] using hy)
      simp [hxy.1] at htrue
  · intro y hy
    rw [hnorm] at hy
    change y ∈ [x] at hy
    rw [List.mem_singleton] at hy
    subst y
    rw [List.getLast_append_singleton]
    exact hequivRel.refl x.value
  · intro y hy
    rw [hnorm] at hy
    change y ∈ normalized at hy
    rw [List.getLast_append_singleton]
    exact hxAll y (by simpa [normalized] using hy)

end Invariant

/-! ## Inhabited regression -/

private def descendingInvariantRegressionLt : BoolComparator Nat :=
  fun left right => decide (left < right)

private theorem descendingInvariantRegressionOrder :
    BoolStrictWeakOrder descendingInvariantRegressionLt := by
  constructor
  let hstrict : IsStrictOrder Nat
      (fun left right => descendingInvariantRegressionLt left right = true) :=
    { irrefl := by simp [descendingInvariantRegressionLt]
      trans := by
        intro a b c hab hbc
        simp [descendingInvariantRegressionLt] at hab hbc ⊢
        omega }
  exact @IsStrictWeakOrder.mk Nat
    (fun left right => descendingInvariantRegressionLt left right = true)
    hstrict (by
      intro a b c hab hbc
      simp [descendingInvariantRegressionLt] at hab hbc ⊢
      omega)

private def descendingInvariantThree : Occurrence Nat :=
  { value := 3, origin := 0 }

private def descendingInvariantTwoOne : Occurrence Nat :=
  { value := 2, origin := 1 }

private def descendingInvariantTwoTwo : Occurrence Nat :=
  { value := 2, origin := 2 }

/-- Concrete strict-then-equivalent regression: the descending scan
`[3@0, 2@1, 2@2]` has an inhabited invariant, and normalization produces the
stable ascending sequence `[2@1, 2@2, 3@0]`.  The proof exercises both public
extension theorems rather than unfolding `Invariant` directly. -/
theorem descendingRunInvariant_strict_equivalent_regression :
    Invariant descendingInvariantRegressionLt
        [descendingInvariantThree, descendingInvariantTwoOne,
          descendingInvariantTwoTwo]
        [descendingInvariantThree, descendingInvariantTwoOne,
          descendingInvariantTwoTwo] 2 ∧
      normalize
        [descendingInvariantThree, descendingInvariantTwoOne,
          descendingInvariantTwoTwo] 2 =
        [descendingInvariantTwoOne, descendingInvariantTwoTwo,
          descendingInvariantThree] := by
  have hseed := Invariant.singleton descendingInvariantRegressionOrder
    descendingInvariantThree
  have hstrict := hseed.extend_strict descendingInvariantRegressionOrder
    descendingInvariantTwoOne (by
      norm_num [descendingInvariantRegressionLt,
        descendingInvariantThree, descendingInvariantTwoOne])
  have hequivalent :
      ComparatorEquivalent descendingInvariantRegressionLt
        descendingInvariantTwoTwo.value
        ((reverseSuffix [descendingInvariantThree] 1 ++
          [descendingInvariantTwoOne]).getLast (by simp)).value := by
    norm_num [ComparatorEquivalent, descendingInvariantRegressionLt,
      reverseSuffix, descendingInvariantThree, descendingInvariantTwoOne,
      descendingInvariantTwoTwo]
  have horigin :
      ∀ y ∈ [descendingInvariantThree, descendingInvariantTwoOne],
        ComparatorEquivalent descendingInvariantRegressionLt y.value
          descendingInvariantTwoTwo.value →
          y.origin < descendingInvariantTwoTwo.origin := by
    intro y hy hequiv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · norm_num [ComparatorEquivalent, descendingInvariantRegressionLt,
        descendingInvariantThree, descendingInvariantTwoTwo] at hequiv
    · norm_num [descendingInvariantTwoOne, descendingInvariantTwoTwo]
  have hextended := hstrict.extend_equivalent
    descendingInvariantRegressionOrder descendingInvariantTwoTwo
    hequivalent horigin
  constructor
  · simpa [reverseSuffix] using hextended
  · norm_num [normalize, descendingInvariantThree,
      descendingInvariantTwoOne, descendingInvariantTwoTwo]

end DescendingRunSpec

end CPythonListsort
