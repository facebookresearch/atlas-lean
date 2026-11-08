/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.StringMatching.Basic
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Algebra.Group.Nat.Defs

import Batteries.Data.List.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.List.Range

/-!
# Naive all-occurrence string matching

`naiveMatches` checks every possible alignment, comparing symbols from left to right and stopping
an alignment at its first mismatch. It returns all matching zero-based shifts in increasing order,
including overlapping matches. The empty pattern matches at every boundary; a pattern longer than
the text has no matches.

The cost counts exactly one unit for each executed symbol comparison, including a failed
comparison. List operations, allocation, arithmetic, control flow, and output construction are
free in this model. It is a comparison count, not a machine running-time bound.

The algorithm follows NAIVE-STRING-MATCHER in Cormen, Leiserson, Rivest, and Stein,
*Introduction to Algorithms*, fourth edition, Section 32.1, p. 960. Lists replace character arrays
and the returned list records the printed shifts. The interface generalizes the finite alphabet
to any symbol type with lawful Boolean equality, and extends the source's `m ≤ n` domain by
returning no matches when `m > n`. The exact bound `(n - m + 1) * m` is attained by repeated-symbol
inputs; taking `m = n / 2` gives the source's quadratic worst-case family.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.TimeM

universe u

variable {α : Type u}

@[no_expose]
private def timedPrefix [BEq α] : List α → List α → TimeM Nat Bool
  | [], _ => pure true
  | _ :: _, [] => pure false
  | x :: xs, y :: ys => do
      ✓
      if x == y then timedPrefix xs ys else pure false

@[no_expose]
private def timedScan [BEq α] (pattern : List α) :
    List (List α) → Nat → TimeM Nat (List Nat)
  | [], _ => pure []
  | suffix :: suffixes, offset => do
      let matched ← timedPrefix pattern suffix
      let remaining ← timedScan pattern suffixes (offset + 1)
      pure (if matched then offset :: remaining else remaining)

/-- All matching zero-based shifts, charging one unit for each executed symbol comparison. -/
public def naiveMatches [BEq α] (pattern text : List α) : TimeM Nat (List Nat) :=
  if pattern.length ≤ text.length then
    timedScan pattern (text.tails.take (text.length - pattern.length + 1)) 0
  else
    pure []

@[expose] public section

private lemma timedPrefix_ret [BEq α] (pattern text : List α) :
    (timedPrefix pattern text).ret = pattern.isPrefixOf text := by
  induction pattern generalizing text with
  | nil => simp [timedPrefix]
  | cons x xs ih =>
      cases text with
      | nil => simp [timedPrefix]
      | cons y ys =>
          cases h : x == y <;> simp [timedPrefix, List.isPrefixOf, h, ih]

private lemma timedPrefix_time_eq [BEq α] (pattern text : List α)
    (hlen : pattern.length ≤ text.length) :
    (timedPrefix pattern text).time =
      min pattern.length ((pattern.zip text).findIdx (fun pair => !(pair.1 == pair.2)) + 1) := by
  induction pattern generalizing text with
  | nil => simp [timedPrefix]
  | cons x xs ih =>
      cases text with
      | nil => simp at hlen
      | cons y ys =>
          have htail : xs.length ≤ ys.length := by simpa using hlen
          cases h : x == y with
          | false => simp [timedPrefix, h, List.findIdx_cons]
          | true =>
              simp only [timedPrefix, h, ↓reduceIte, time_bind, time_tick,
                List.zip_cons_cons, List.findIdx_cons, Bool.not_true, Bool.false_eq_true,
                List.length_cons, ↓reduceIte]
              rw [ih ys htail]
              omega

private lemma timedScan_ret [BEq α] (pattern : List α) (suffixes : List (List α))
    (offset : Nat) :
    (timedScan pattern suffixes offset).ret = suffixes.findIdxs pattern.isPrefixOf offset := by
  induction suffixes generalizing offset with
  | nil => rfl
  | cons suffix suffixes ih =>
      simp [timedScan, timedPrefix_ret, List.findIdxs_cons, ih]

private lemma timedScan_time [BEq α] (pattern : List α) (suffixes : List (List α))
    (offset : Nat) :
    (timedScan pattern suffixes offset).time =
      (suffixes.map fun suffix => (timedPrefix pattern suffix).time).sum := by
  induction suffixes generalizing offset with
  | nil => rfl
  | cons suffix suffixes ih => simp [timedScan, ih]

private lemma candidate_length (pattern text : List α)
    (hlen : pattern.length ≤ text.length) :
    (text.tails.take (text.length - pattern.length + 1)).length =
      text.length - pattern.length + 1 := by
  simp only [List.length_take, List.length_tails]
  omega

private lemma candidate_get (pattern text : List α) (offset : Nat)
    (h : offset < (text.tails.take (text.length - pattern.length + 1)).length) :
    (text.tails.take (text.length - pattern.length + 1))[offset] = text.drop offset := by
  simp

private lemma candidate_length_le (pattern text suffix : List α)
    (hlen : pattern.length ≤ text.length)
    (hsuffix : suffix ∈ text.tails.take (text.length - pattern.length + 1)) :
    pattern.length ≤ suffix.length := by
  obtain ⟨offset, hoffset, rfl⟩ := List.mem_iff_getElem.mp hsuffix
  rw [candidate_get]
  rw [candidate_length pattern text hlen] at hoffset
  simp only [List.length_drop]
  omega

/-- Erasing cost gives the canonical index filter on the candidate suffixes. -/
theorem naiveMatches_ret [BEq α] (pattern text : List α) :
    (naiveMatches pattern text).ret =
      if pattern.length ≤ text.length then
        (text.tails.take (text.length - pattern.length + 1)).findIdxs pattern.isPrefixOf
      else [] := by
  by_cases hlen : pattern.length ≤ text.length
  · simp [naiveMatches, hlen, timedScan_ret]
  · simp [naiveMatches, hlen]

/-- An offset is reported exactly when the pattern matches there, including empty patterns. -/
theorem mem_naiveMatches_iff [BEq α] [LawfulBEq α] (pattern text : List α) (offset : Nat) :
    offset ∈ (naiveMatches pattern text).ret ↔
      Cslib.Algorithms.Lean.StringMatching.MatchAt pattern text offset := by
  rw [naiveMatches_ret]
  by_cases hlen : pattern.length ≤ text.length
  · simp only [hlen, ↓reduceIte, List.mem_findIdxs_iff_exists_getElem_pos]
    constructor
    · rintro ⟨hoffset, hprefix⟩
      rw [candidate_get] at hprefix
      rw [candidate_length pattern text hlen] at hoffset
      exact ⟨by omega, List.isPrefixOf_iff_prefix.mp hprefix⟩
    · rintro ⟨hoffset, hprefix⟩
      have hprefixLength := hprefix.length_le
      simp only [List.length_drop] at hprefixLength
      have hcandidate : offset <
          (text.tails.take (text.length - pattern.length + 1)).length := by
        rw [candidate_length pattern text hlen]
        omega
      refine ⟨hcandidate, ?_⟩
      rw [candidate_get]
      exact List.isPrefixOf_iff_prefix.mpr hprefix
  · simp only [hlen, ↓reduceIte, List.not_mem_nil, false_iff]
    rintro ⟨hoffset, hprefix⟩
    have hprefixLength := hprefix.length_le
    simp only [List.length_drop] at hprefixLength
    omega

/-- Reported offsets are strictly increasing, so each occurrence is reported only once. -/
theorem naiveMatches_pairwise [BEq α] (pattern text : List α) :
    (naiveMatches pattern text).ret.Pairwise (· < ·) := by
  rw [naiveMatches_ret]
  split
  · exact List.pairwise_findIdxs
  · exact List.Pairwise.nil

/-- The exact sum of left-to-right comparison counts at every candidate alignment. -/
theorem naiveMatches_time_eq [BEq α] (pattern text : List α) :
    (naiveMatches pattern text).time =
      if pattern.length ≤ text.length then
        ((text.tails.take (text.length - pattern.length + 1)).map fun suffix =>
          min pattern.length
            ((pattern.zip suffix).findIdx (fun pair => !(pair.1 == pair.2)) + 1)).sum
      else 0 := by
  by_cases hlen : pattern.length ≤ text.length
  · simp only [naiveMatches, hlen, ↓reduceIte, timedScan_time]
    congr 1
    apply List.map_congr_left
    intro suffix hsuffix
    exact timedPrefix_time_eq pattern suffix (candidate_length_le pattern text suffix hlen hsuffix)
  · simp [naiveMatches, hlen]

/-- At most `m` comparisons per alignment, and no comparisons when the pattern is too long. -/
theorem naiveMatches_time_le [BEq α] (pattern text : List α) :
    (naiveMatches pattern text).time ≤
      if pattern.length ≤ text.length then
        (text.length - pattern.length + 1) * pattern.length
      else 0 := by
  rw [naiveMatches_time_eq]
  split
  · next hlen =>
      have hbound := List.sum_le_length_nsmul
        ((text.tails.take (text.length - pattern.length + 1)).map fun suffix =>
          min pattern.length ((pattern.zip suffix).findIdx
            (fun pair => !(pair.1 == pair.2)) + 1)) pattern.length (by
          intro value hvalue
          obtain ⟨suffix, _, rfl⟩ := List.mem_map.mp hvalue
          exact Nat.min_le_left _ _)
      simpa using hbound
  · exact Nat.le_refl 0

private lemma timedPrefix_replicate [BEq α] [ReflBEq α] (x : α) (m n : Nat) (hlen : m ≤ n) :
    timedPrefix (List.replicate m x) (List.replicate n x) = ⟨true, m⟩ := by
  induction m generalizing n with
  | zero => rfl
  | succ m ih =>
      cases n with
      | zero => omega
      | succ n =>
          have htail : m ≤ n := by omega
          apply TimeM.ext
          · simp [List.replicate_succ, timedPrefix, ih n htail]
          · simp [List.replicate_succ, timedPrefix, ih n htail, Nat.add_comm]

private lemma findIdxs_all_true {β : Type u} (p : β → Bool) (xs : List β) (offset : Nat)
    (hall : ∀ x ∈ xs, p x = true) : xs.findIdxs p offset = List.range' offset xs.length := by
  induction xs generalizing offset with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.findIdxs_cons, hall x (by simp), ↓reduceIte,
        List.length_cons, List.range'_succ]
      congr 1
      exact ih (offset + 1) (fun y hy => hall y (by simp [hy]))

private lemma candidate_replicate [BEq α] [ReflBEq α] (x : α) (m n : Nat) (hlen : m ≤ n)
    (suffix : List α)
    (hsuffix : suffix ∈
      (List.replicate n x).tails.take ((List.replicate n x).length -
        (List.replicate m x).length + 1)) :
    timedPrefix (List.replicate m x) suffix = ⟨true, m⟩ := by
  obtain ⟨offset, hoffset, rfl⟩ := List.mem_iff_getElem.mp hsuffix
  rw [candidate_get, List.drop_replicate]
  have hlen' : (List.replicate m x).length ≤ (List.replicate n x).length := by
    simpa using hlen
  rw [candidate_length _ _ hlen'] at hoffset
  simp only [List.length_replicate] at hoffset
  exact timedPrefix_replicate x m (n - offset) (by omega)

/-- On repeated-symbol inputs every possible alignment is reported, including overlaps. -/
theorem naiveMatches_ret_replicate [BEq α] [ReflBEq α] (x : α) (m n : Nat) (hlen : m ≤ n) :
    (naiveMatches (List.replicate m x) (List.replicate n x)).ret = List.range (n - m + 1) := by
  rw [naiveMatches_ret]
  have hlen' : (List.replicate m x).length ≤ (List.replicate n x).length := by simpa using hlen
  simp only [hlen', ↓reduceIte]
  rw [findIdxs_all_true]
  · simp [List.range_eq_range']
  · intro suffix hsuffix
    rw [← timedPrefix_ret]
    exact congrArg TimeM.ret (candidate_replicate x m n hlen suffix hsuffix)

/-- Repeated-symbol inputs attain the comparison upper bound exactly. -/
theorem naiveMatches_time_replicate [BEq α] [ReflBEq α] (x : α) (m n : Nat) (hlen : m ≤ n) :
    (naiveMatches (List.replicate m x) (List.replicate n x)).time = (n - m + 1) * m := by
  have hlen' : (List.replicate m x).length ≤ (List.replicate n x).length := by simpa using hlen
  simp only [naiveMatches, hlen', ↓reduceIte, timedScan_time]
  have hsum := List.sum_eq_length_nsmul
    (((List.replicate n x).tails.take ((List.replicate n x).length -
      (List.replicate m x).length + 1)).map fun suffix =>
        (timedPrefix (List.replicate m x) suffix).time) m (by
      intro value hvalue
      obtain ⟨suffix, hsuffix, rfl⟩ := List.mem_map.mp hvalue
      exact congrArg TimeM.time (candidate_replicate x m n hlen suffix hsuffix))
  simpa using hsum

/-- The empty pattern matches every text boundary without any symbol comparisons. -/
@[simp]
theorem naiveMatches_nil_pattern [BEq α] (text : List α) :
    naiveMatches [] text = ⟨List.range (text.length + 1), 0⟩ := by
  apply TimeM.ext
  · rw [naiveMatches_ret]
    simp only [List.length_nil, Nat.zero_le, ↓reduceIte, Nat.sub_zero]
    rw [findIdxs_all_true]
    · simp [List.range_eq_range']
    · intro suffix _
      simp
  · rw [naiveMatches_time_eq]
    simp

/-- A pattern longer than the text has no candidates and performs no symbol comparisons. -/
@[simp]
theorem naiveMatches_of_length_lt [BEq α] (pattern text : List α)
    (hlen : text.length < pattern.length) : naiveMatches pattern text = pure [] := by
  simp [naiveMatches, Nat.not_le.mpr hlen]

end

end Cslib.Algorithms.Lean.TimeM
