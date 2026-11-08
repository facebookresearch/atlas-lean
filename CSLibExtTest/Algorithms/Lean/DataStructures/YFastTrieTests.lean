/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.YFastTrie

/-!
# Tests for the grouped y-fast trie API

Client examples for empty/singleton inputs, exact and partial chunk
boundaries, membership hits/misses, successor within and across groups,
no-successor cases, and the documented `B = 0` degenerate behavior.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.YFastTrieTests

open Cslib.Algorithms.Lean

/-- Keys are `w = 4` bit numbers, cast from literals. -/
public def k (n : Nat) : Fin (2 ^ 4) := ⟨n % 16, Nat.mod_lt _ (by decide)⟩

public def sample : List (Fin (2 ^ 4)) := [k 1, k 3, k 4, k 7, k 9, k 12]

example : sample.Pairwise (· < ·) := by decide

/-- Empty input: no groups, valid at any bound. -/
example : (GroupedYFastTrie.chunkGroups 2 ([] : List (Fin (2 ^ 4)))).flatten =
    [] :=
  GroupedYFastTrie.flatten_chunkGroups 2 []

example : (GroupedYFastTrie.ofSortedList 2 ([] : List (Fin (2 ^ 4)))).contents =
    ∅ := by
  rw [GroupedYFastTrie.contents_ofSortedList]
  simp

example : (GroupedYFastTrie.ofSortedList 2
    ([] : List (Fin (2 ^ 4)))).Valid :=
  GroupedYFastTrie.valid_ofSortedList (by decide) List.Pairwise.nil

example (x : Fin (2 ^ 4)) :
    (GroupedYFastTrie.empty : GroupedYFastTrie 4 2).member x = false :=
  GroupedYFastTrie.member_empty x

example (x : Fin (2 ^ 4)) :
    (GroupedYFastTrie.empty : GroupedYFastTrie 4 2).successor x = none :=
  GroupedYFastTrie.successor_empty x

/-- Singleton input: one group of length `1 ≤ B`; member hits, miss fails. -/
example : (GroupedYFastTrie.ofSortedList 2 [k 3]).member (k 3) = true := by
  rw [GroupedYFastTrie.member_ofSortedList_iff (by decide) (by decide)]
  simp

example : (GroupedYFastTrie.ofSortedList 2 [k 3]).successor (k 3) = none := by
  have h := GroupedYFastTrie.successor_eq_none_iff
    (GroupedYFastTrie.valid_ofSortedList (w := 4) (B := 2) (by decide)
      (by decide : [k 3].Pairwise (· < ·))) (k 3)
  apply h.mpr
  rw [GroupedYFastTrie.contents_ofSortedList]
  simp [k]

/-- Exact chunk boundary: `6` keys at `B = 3` give two full groups, contents exact. -/
example : (GroupedYFastTrie.chunkGroups 3 sample).flatten = sample :=
  GroupedYFastTrie.flatten_chunkGroups 3 sample

example : (GroupedYFastTrie.ofSortedList 3 sample).contents = sample.toFinset :=
  GroupedYFastTrie.contents_ofSortedList sample

/-- Partial last chunk: every `B = 4` chunk has length at most `4`. -/
example : ∀ g ∈ GroupedYFastTrie.chunkGroups 4 sample, g.length ≤ 4 := by
  intro g hg
  exact (GroupedYFastTrie.chunkGroups_spec (by decide) sample
    (by decide) g hg).2.1

/-- Membership hits in both groups, misses for absent keys. -/
example : (GroupedYFastTrie.ofSortedList 3 sample).member (k 1) = true := by
  rw [GroupedYFastTrie.member_ofSortedList_iff (by decide) (by decide)]
  simp [sample]

example : (GroupedYFastTrie.ofSortedList 3 sample).member (k 12) = true := by
  rw [GroupedYFastTrie.member_ofSortedList_iff (by decide) (by decide)]
  simp [sample]

example : (GroupedYFastTrie.ofSortedList 3 sample).member (k 5) = false := by
  have h := GroupedYFastTrie.member_ofSortedList_iff (w := 4) (B := 3)
    (by decide) (by decide : sample.Pairwise (· < ·)) (k 5)
  have hnot : k 5 ∉ sample := by simp [sample, k]
  exact Bool.eq_false_iff.mpr (fun hm => hnot (h.mp hm))

/-- Successor within a group (`3 → 4`), across groups (`4 → 7` at the
`B = 3` boundary), and no successor above the maximum. -/
example : (GroupedYFastTrie.ofSortedList 3 sample).successor (k 3) =
    some (k 4) := by
  rw [GroupedYFastTrie.successor_ofSortedList_eq_some_iff (by decide)
    (by decide : sample.Pairwise (· < ·))]
  refine ⟨by simp [sample], by decide, ?_⟩
  intro z hz hxz
  simp [sample] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [k]

example : (GroupedYFastTrie.ofSortedList 3 sample).successor (k 4) =
    some (k 7) := by
  rw [GroupedYFastTrie.successor_ofSortedList_eq_some_iff (by decide)
    (by decide : sample.Pairwise (· < ·))]
  refine ⟨by simp [sample], by decide, ?_⟩
  intro z hz hxz
  simp [sample] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [k]

example : (GroupedYFastTrie.ofSortedList 3 sample).successor (k 12) = none := by
  have h := GroupedYFastTrie.successor_eq_none_iff
    (GroupedYFastTrie.valid_ofSortedList (w := 4) (B := 3) (by decide)
      (by decide : sample.Pairwise (· < ·))) (k 12)
  apply h.mpr
  rw [GroupedYFastTrie.contents_ofSortedList]
  intro z hz
  rw [List.mem_toFinset] at hz
  simp [sample] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [k]

/-- The documented `B = 0` behavior: one degenerate group, invalid trie. -/
example : GroupedYFastTrie.chunkGroups 0 sample = [sample] :=
  GroupedYFastTrie.chunkGroups_zero_of_ne (by simp [sample])

example : ¬ (GroupedYFastTrie.ofSortedList 0 sample).Valid :=
  GroupedYFastTrie.not_valid_ofSortedList_zero (by simp [sample])

example : ¬ (GroupedYFastTrie.ofSortedList 0 [k 1]).Valid :=
  GroupedYFastTrie.not_valid_ofSortedList_zero (by simp)

example : (GroupedYFastTrie.ofSortedList 0 sample).contents = sample.toFinset :=
  GroupedYFastTrie.contents_ofSortedList sample

example {t : GroupedYFastTrie 4 3} (hv : t.Valid) (x : Fin (2 ^ 4)) :
    t.member x = true ↔ x ∈ t.contents :=
  GroupedYFastTrie.member_iff hv x

#print axioms GroupedYFastTrie.valid_ofSortedList
#print axioms GroupedYFastTrie.member_ofSortedList_iff
#print axioms GroupedYFastTrie.not_valid_ofSortedList_zero

end Cslib.Algorithms.Lean.YFastTrieTests
