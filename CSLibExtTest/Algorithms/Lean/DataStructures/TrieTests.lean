/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.Trie

@[expose] public section

/-!
# Tests for finite tries

These examples exercise empty keys, replacement, prefix keys, common prefixes, validity, duplicate
child rejection, entry enumeration, and lookup-equivalence under insertion reordering.
-/

namespace Cslib.Algorithms.Lean.TrieTests

open Trie

private def prefixTrie : Trie Nat String :=
  ((Trie.empty.insert [1] "prefix").insert [1, 2] "long").insert [] "root"

private theorem prefixTrie_valid : prefixTrie.Valid :=
  ((Trie.Valid.empty.insert [1] "prefix").insert [1, 2] "long").insert [] "root"

private def sharedPrefixTrie : Trie Nat String :=
  (Trie.empty.insert [1, 2] "left").insert [1, 3] "right"

private theorem sharedPrefixTrie_valid : sharedPrefixTrie.Valid :=
  (Trie.Valid.empty.insert [1, 2] "left").insert [1, 3] "right"

private def orderedEntriesTrie : Trie Nat String :=
  (((Trie.empty.insert [] "root").insert [1] "prefix").insert [1, 2] "nested").insert
    [2] "sibling"

example : (Trie.empty : Trie Nat String).lookup [] = none := by
  simp

example : (Trie.empty.insert [] "root" : Trie Nat String).lookup [] = some "root" := by
  simp

example : ((Trie.empty.insert [1] "old").insert [1] "new" : Trie Nat String).lookup [1] =
    some "new" := by
  simp

example : prefixTrie.lookup [1] = some "prefix" := by
  simp [prefixTrie]

example : prefixTrie.lookup [1, 2] = some "long" := by
  simp [prefixTrie]

example : sharedPrefixTrie.lookup [1, 2] = some "left" := by
  simp [sharedPrefixTrie]

example : sharedPrefixTrie.lookup [1, 3] = some "right" := by
  simp [sharedPrefixTrie]

example : prefixTrie.lookup [9] = none := by
  simp [prefixTrie]

example : ([], "root") ∈ prefixTrie.entries := by
  exact (Trie.lookup_eq_some_iff_mem_entries prefixTrie_valid [] "root").mp (by
    simp [prefixTrie])

example : ([1], "prefix") ∈ prefixTrie.entries := by
  exact (Trie.lookup_eq_some_iff_mem_entries prefixTrie_valid [1] "prefix").mp (by
    simp [prefixTrie])

example : ([1, 2], "long") ∈ prefixTrie.entries := by
  exact (Trie.lookup_eq_some_iff_mem_entries prefixTrie_valid [1, 2] "long").mp (by
    simp [prefixTrie])

example : ([1, 2], "left") ∈ sharedPrefixTrie.entries := by
  exact (Trie.lookup_eq_some_iff_mem_entries sharedPrefixTrie_valid [1, 2] "left").mp (by
    simp [sharedPrefixTrie])

example : ([1, 3], "right") ∈ sharedPrefixTrie.entries := by
  exact (Trie.lookup_eq_some_iff_mem_entries sharedPrefixTrie_valid [1, 3] "right").mp (by
    simp [sharedPrefixTrie])

example : orderedEntriesTrie.entries =
    [([], "root"), ([1], "prefix"), ([1, 2], "nested"), ([2], "sibling")] := by
  decide

example :
    ((Trie.empty.insert [1] "old").insert [1] "new" : Trie Nat String).entries =
      [([1], "new")] := by
  decide

example :
    let child : Trie Nat String := Trie.empty
    ¬Trie.Valid (.node none [(1, child), (1, child)]) := by
  dsimp
  intro h
  have hkeys := h.nodup_child_keys
  simp at hkeys

example :
    Trie.LookupEquiv
      ((Trie.empty.insert [1] "one").insert [2] "two" : Trie Nat String)
      ((Trie.empty.insert [2] "two").insert [1] "one" : Trie Nat String) :=
  Trie.LookupEquiv.insert_comm Trie.empty (by decide) "one" "two"

end Cslib.Algorithms.Lean.TrieTests
