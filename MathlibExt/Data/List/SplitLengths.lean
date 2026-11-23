/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Modified for Atlas by Meta Platforms, Inc. and affiliates: reused Mathlib's canonical
`List.splitLengths`, generalized the source results, and added importing-client tests.
-/

module

public import Mathlib.Data.List.SplitLengths

/-! # Lookup and reconstruction for lists split at specified lengths

Adapted from `eth/proof/machines/StepMachines/Prog/Chunks.lean`,
`eth/proof/machines/StepMachines/Math/CodeMore.lean`, and
`eth/proof/networks/Value/Words.lean` in
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.
-/

@[expose] public section

namespace List

/-- A valid indexed chunk begins after the total length of the preceding chunks. -/
theorem getD_splitLengths {α : Type*} (xs : List α) (lengths : List ℕ) (fallback : List α)
    {i : ℕ} (hi : i < lengths.length) :
    (lengths.splitLengths xs).getD i fallback =
      (xs.drop (lengths.take i).sum).take lengths[i] := by
  induction lengths generalizing xs i with
  | nil => simp at hi
  | cons n lengths ih =>
    cases i with
    | zero => simp
    | succ i =>
      rw [splitLengths_cons, getD_cons_succ,
        ih (xs := xs.drop n) (by simpa using hi)]
      simp only [take_succ_cons, sum_cons, getElem_cons_succ, drop_drop]

/-- Looking up a named chunk uses the first occurrence of its name. -/
theorem getD_splitLengths_map {ι α : Type*} [BEq ι] [LawfulBEq ι]
    (length : ι → ℕ) (names : List ι) (xs fallback : List α) {i : ι} (hi : i ∈ names) :
    ((names.map length).splitLengths xs).getD (names.idxOf i) fallback =
      (xs.drop ((names.map length).take (names.idxOf i)).sum).take (length i) := by
  have hidx : names.idxOf i < names.length := idxOf_lt_length_of_mem hi
  rw [getD_splitLengths xs (names.map length) fallback (by simpa)]
  rw [getElem_map, getElem_idxOf hidx]

/-- Splitting at a repeated width recovers the corresponding uniform chunk. -/
theorem getD_splitLengths_replicate {α : Type*} (width count i : ℕ)
    (xs fallback : List α) (hi : i < count) :
    ((List.replicate count width).splitLengths xs).getD i fallback =
      (xs.drop (i * width)).take width := by
  rw [getD_splitLengths xs (List.replicate count width) fallback (by simpa)]
  simp [take_replicate, Nat.min_eq_left hi.le]

/-- Lists of the same uniform-block length are equal when every block extract agrees. -/
theorem eq_of_extract_mul_eq {α : Type*} (width count : ℕ) (xs ys : List α)
    (hxs : xs.length = count * width) (hys : ys.length = count * width)
    (h : ∀ i < count,
      xs.extract (i * width) (i * width + width) =
        ys.extract (i * width) (i * width + width)) :
    xs = ys := by
  induction count generalizing xs ys with
  | zero => simp_all
  | succ count ih =>
    rw [Nat.succ_mul] at hxs hys
    have htake : xs.take width = ys.take width := by
      simpa [extract_eq_take_drop] using h 0 (by omega)
    have hdrop : xs.drop width = ys.drop width := by
      apply ih
      · rw [length_drop, hxs]
        omega
      · rw [length_drop, hys]
        omega
      · intro i hi
        have hi' := h (i + 1) (by omega)
        simpa [extract_eq_take_drop, drop_drop, Nat.add_mul, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using hi'
    rw [← take_append_drop width xs, htake, hdrop, take_append_drop]

/-- Concatenating `count` lists of length `width` has length `count * width`. -/
theorem length_flatMap_range {α : Type*} (count width : ℕ) (blocks : ℕ → List α)
    (hblocks : ∀ i < count, (blocks i).length = width) :
    ((List.range count).flatMap blocks).length = count * width := by
  induction count with
  | zero => simp
  | succ count ih =>
    rw [range_succ, flatMap_append, length_append,
      ih fun i hi => hblocks i (by omega)]
    simp [hblocks count (by omega), Nat.succ_mul]

private theorem extract_flatMap_getElem {α β : Type*} (width : ℕ) (items : List β)
    (blocks : β → List α) (hblocks : ∀ item ∈ items, (blocks item).length = width)
    {i : ℕ} (hi : i < items.length) :
    (items.flatMap blocks).extract (i * width) (i * width + width) = blocks items[i] := by
  induction items generalizing i with
  | nil => simp at hi
  | cons item items ih =>
    cases i with
    | zero =>
      rw [getElem_cons_zero, flatMap_cons, extract_eq_take_drop]
      simpa using take_left' (hblocks item mem_cons_self)
    | succ i =>
      have hitem : (blocks item).length = width := hblocks item mem_cons_self
      have hstart : (i + 1) * width = (blocks item).length + i * width := by
        rw [hitem, Nat.succ_mul]
        omega
      rw [getElem_cons_succ, flatMap_cons, extract_eq_take_drop,
        Nat.add_sub_cancel_left, hstart, drop_length_add_append]
      simpa [extract_eq_take_drop] using
        ih (fun item hi => hblocks item (mem_cons_of_mem _ hi)) (by simpa using hi)

/-- A uniform-width extract of a concatenated family recovers that family member. -/
theorem extract_flatMap_range {α : Type*} (count width : ℕ) (blocks : ℕ → List α)
    (hblocks : ∀ i < count, (blocks i).length = width) {i : ℕ} (hi : i < count) :
    ((List.range count).flatMap blocks).extract (i * width) (i * width + width) =
      blocks i := by
  have h := extract_flatMap_getElem width (List.range count) blocks
    (fun item hitem => hblocks item (mem_range.mp hitem)) (by simpa using hi)
  simpa only [getElem_range] using h

/-- Every finite family of equal-length lists is realized by their concatenation. -/
theorem exists_length_eq_and_extract_eq {α : Type*} (width count : ℕ)
    (blocks : ℕ → List α) (hblocks : ∀ i < count, (blocks i).length = width) :
    ∃ xs : List α,
      xs.length = count * width ∧
        ∀ i < count, xs.extract (i * width) (i * width + width) = blocks i :=
  ⟨(List.range count).flatMap blocks, length_flatMap_range count width blocks hblocks,
    fun _ hi => extract_flatMap_range count width blocks hblocks hi⟩

end List
