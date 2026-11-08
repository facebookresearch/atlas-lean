/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.SuffixTree
public meta import CSLibExt.Algorithms.Lean.DataStructures.SuffixArray

/-!
# Tests for the suffix-tree API

Client examples for empty patterns and inputs, patterns ending within an
edge and at an edge boundary, duplicate-key precedence in `buildFrom`,
successful and unsuccessful searches, and terminator behavior, through
the public API (including the generic `RadixTrie` prefix-search API now
exported from `RadixTrie.lean`), plus focused guards for the suffix-array
API imported from `SuffixArray.lean` (otherwise only imported
transitively here).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.SuffixTreeTests

open Cslib.Algorithms.Lean

/-- Empty input: one stored key, the terminator alone. -/
example : (SuffixTree.storedKeys ([] : List Nat)).length = 1 :=
  SuffixTree.storedKeys_length _

example : [Option.none] ∈ SuffixTree.storedKeys ([] : List Nat) := by
  rw [SuffixTree.mem_storedKeys_iff]
  exact ⟨0, Nat.zero_le _, rfl⟩

example : (SuffixTree.suffixTree ([] : List Nat)).lookup [Option.none] = some 0 := by
  have h := SuffixTree.lookup_suffix (s := ([] : List Nat)) (i := 0) (Nat.zero_le _)
  simpa [SuffixTree.terminated] using h

/-- Empty pattern: prefix search on a nonempty suffix tree succeeds
(the empty pattern is an infix), via the infix characterization. -/
example : (SuffixTree.suffixTree [1, 2, 1]).hasPrefix
    (([] : List Nat).map Option.some) = true := by
  rw [SuffixTree.hasPrefix_suffixTree_iff_isInfix]
  exact ⟨[], [1, 2, 1], rfl⟩

example : (SuffixTree.suffixTree [1, 2, 1]).hasPrefix ([2, 1].map Option.some) = true :=
  SuffixTree.hasPrefix_suffixTree_iff_isInfix.mpr ⟨[1], [], rfl⟩

example : (SuffixTree.suffixTree [1, 2, 1]).hasPrefix ([2, 2].map Option.some) = false := by
  rw [Bool.eq_false_iff, Ne, SuffixTree.hasPrefix_suffixTree_iff_exists]
  rintro ⟨i, hpre⟩
  have hle : i ≤ 1 := by
    have h2 := hpre.length_le
    simp only [List.length_drop, List.length_cons, List.length_nil] at h2
    omega
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · obtain ⟨t, ht⟩ := hpre
    change [2, 2] ++ t = [1, 2, 1] at ht
    cases t <;> simp at ht
  · obtain ⟨t, ht⟩ := hpre
    change [2, 2] ++ t = [2, 1] at ht
    cases t <;> simp at ht

/-- A pattern ending within an edge: `[2]` stops inside the edge for the
suffix `2, 1, †`; a pattern ending exactly at a suffix/key boundary:
the full stored suffix `[2, 1]` (and with terminator, exact lookup). -/
example : (SuffixTree.suffixTree [1, 2, 1]).hasPrefix ([2].map Option.some) = true :=
  SuffixTree.hasPrefix_suffixTree_iff_isInfix.mpr ⟨[1], [1], rfl⟩

example : (SuffixTree.suffixTree [1, 2, 1]).hasPrefix ([1, 2, 1].map Option.some) =
    true :=
  SuffixTree.hasPrefix_suffixTree_iff_isInfix.mpr ⟨[], [], rfl⟩

/-- A pattern longer than every suffix fails. -/
example : (SuffixTree.suffixTree [1, 2, 1]).hasPrefix ([1, 2, 1, 1].map Option.some) =
    false := by
  rw [Bool.eq_false_iff, Ne, SuffixTree.hasPrefix_suffixTree_iff_exists]
  rintro ⟨i, hpre⟩
  have h2 := hpre.length_le
  simp only [List.length_drop, List.length_cons, List.length_nil] at h2
  omega

example : (SuffixTree.suffixTree [1, 2, 1]).lookup ([1, 2, 1].map Option.some ++ [none]) =
    some 0 := by
  have h := SuffixTree.lookup_suffix (s := [1, 2, 1]) (i := 0) (Nat.zero_le _)
  simpa [SuffixTree.terminated] using h

/-- Terminator behavior: lookup of an unterminated proper suffix does not
return that suffix's index as a stored key — stored keys all end in `none`. -/
example : ∀ k ∈ (SuffixTree.suffixTree [1, 2, 1]).keys,
    k.getLast? = some Option.none := by
  intro k hk
  rw [SuffixTree.mem_suffixTree_keys] at hk
  obtain ⟨i, hi, rfl⟩ := hk
  have h := SuffixTree.terminated_drop [1, 2, 1] hi
  rw [h]
  simp [SuffixTree.terminated]

example : (SuffixTree.storedKeys [1, 2, 1]).length = 4 :=
  SuffixTree.storedKeys_length _

example : (SuffixTree.storedKeys [1, 2, 1]).Nodup :=
  SuffixTree.storedKeys_nodup _

example : RadixTrie.Valid (SuffixTree.suffixTree [1, 2, 1]) :=
  SuffixTree.valid_suffixTree _

/-- Generic radix-trie prefix search, usable without suffix trees. -/
example {t : RadixTrie Nat Nat} (h : RadixTrie.Valid t) (p : List Nat) :
    t.hasPrefix p = true ↔ ∃ k ∈ t.keys, p <+: k :=
  RadixTrie.hasPrefix_eq_true_iff h p

/-- `buildFrom` without duplicate keys looks up the stored value. -/
example : (RadixTrie.buildFrom [([1, 2], 10), ([3], 20)]).lookup [3] = some 20 :=
  RadixTrie.lookup_buildFrom_of_mem (by simp) (by simp)

/-- Duplicate keys in `buildFrom`: the head entry is inserted last, so it
takes precedence; some stored value is always found for a present key. -/
example : ∃ v, (RadixTrie.buildFrom [([1], 10), ([1], 20)]).lookup [1] = some v :=
  RadixTrie.lookup_buildFrom_exists_of_mem (k := [1]) (v := 10) (by simp)

example : (RadixTrie.buildFrom [([1], 10), ([1], 20)] :
    RadixTrie Nat Nat).lookup [1] = some 10 := by
  show ((RadixTrie.buildFrom [([1], 20)]).insert [1] 10).lookup [1] = some 10
  exact RadixTrie.lookup_insert_same _ _ _

example : [1] ∈ (RadixTrie.buildFrom [([1], 10), ([1], 20)] :
    RadixTrie Nat Nat).keys := by
  rw [RadixTrie.mem_keys_buildFrom]
  refine ⟨10, ?_⟩
  simp

example (L : List (List Nat × Nat)) :
    RadixTrie.Valid (RadixTrie.buildFrom L) :=
  RadixTrie.Valid.buildFrom L

example {t : RadixTrie Nat Nat} (h : RadixTrie.Valid t) : t.keys.Nodup :=
  h.keys_nodup

/-! ### Suffix-array API (added by this PR alongside the suffix tree)

Concrete guards pin comparator direction, proper-prefix ordering,
empty/singleton inputs, repeated symbols, and the length-`n - 1` LCP
convention. (`suffixArray` uses well-founded `List.mergeSort`, so outputs
are checked with `#guard` evaluation rather than kernel `decide`.) -/

#guard SuffixArray.suffixArray ([] : List Nat) == []
#guard SuffixArray.suffixArray [5] == [0]
#guard SuffixArray.lcpArray ([] : List Nat) == []
#guard SuffixArray.lcpArray [5] == []
#guard SuffixArray.suffixArray [1, 2, 3] == [0, 1, 2]
#guard SuffixArray.suffixArray [3, 2, 1] == [2, 1, 0]
-- Proper-prefix ordering: [2] < [2, 1, 2], and [1, 2] is smallest.
#guard SuffixArray.suffixArray [2, 1, 2] == [1, 2, 0]
#guard SuffixArray.lcpArray [2, 1, 2] == [0, 1]
-- Repeated symbols ("banana" pattern) and all-equal symbols.
#guard SuffixArray.suffixArray [2, 1, 3, 1, 3, 1] == [5, 3, 1, 0, 4, 2]
#guard SuffixArray.lcpArray [2, 1, 3, 1, 3, 1] == [1, 3, 0, 0, 2]
#guard SuffixArray.suffixArray [1, 1, 1] == [2, 1, 0]
#guard SuffixArray.lcpArray [1, 1, 1] == [1, 2]

example : SuffixArray.lcp [1, 2, 3] [1, 2, 4] = 2 := by decide
example : SuffixArray.lcp ([] : List Nat) [1] = 0 := by decide
example : SuffixArray.lcp [1, 2] [1, 2, 3] = 2 := by decide
example (s : List Nat) :
    (SuffixArray.suffixArray s).Perm (List.range s.length) :=
  SuffixArray.suffixArray_perm s
example (s : List Nat) : (SuffixArray.lcpArray s).length = s.length - 1 :=
  SuffixArray.lcpArray_length s
example (s : List Nat) :
    List.Pairwise (· ≤ ·)
      ((SuffixArray.suffixArray s).map (SuffixArray.suffix s)) :=
  SuffixArray.pairwise_suffix_suffixArray s

#print axioms SuffixArray.suffixArray_perm
#print axioms SuffixArray.lcpArray_length
#print axioms SuffixTree.hasPrefix_suffixTree_iff_isInfix
#print axioms SuffixTree.lookup_suffix
#print axioms RadixTrie.hasPrefix_eq_true_iff
#print axioms RadixTrie.lookup_buildFrom_of_mem

end Cslib.Algorithms.Lean.SuffixTreeTests
