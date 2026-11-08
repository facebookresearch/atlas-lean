/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.RadixTrie
public meta import CSLibExt.Algorithms.Lean.DataStructures.RadixTrie

/-!
# Tests for radix tries

Concrete guards cover the empty key, replacement, key-prefix and label-prefix splits,
divergent splits, and entry enumeration. Invalid-structure examples check that empty
labels, duplicate sibling heads, and uncompressed unary value-free nodes are rejected
by `Valid`. The final commands audit the transitive axioms of the public theorems.
(`insert` is defined by well-founded recursion on the key, so concrete outputs are
checked with `#guard` evaluation rather than kernel `decide`.)
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.RadixTrieTests

open Cslib.Algorithms.Lean Cslib.Algorithms.Lean.RadixTrie

private def t0 : RadixTrie Nat String := RadixTrie.empty

-- Empty trie and empty key.
#guard t0.entries == []
#guard t0.lookup [1] == none
#guard (t0.insert [] "root").entries == [([], "root")]
#guard (t0.insert [] "root").lookup [] == some "root"

-- Single insertion and replacement of the same key.
#guard (t0.insert [1, 2, 3] "a").entries == [([1, 2, 3], "a")]
#guard ((t0.insert [1, 2, 3] "a").insert [1, 2, 3] "z").entries == [([1, 2, 3], "z")]

-- Key-prefix split: inserting [1, 2] above the existing [1, 2, 3] edge.
#guard ((t0.insert [1, 2, 3] "a").insert [1, 2] "b").entries ==
  [([1, 2], "b"), ([1, 2, 3], "a")]
-- Label-prefix split: inserting [1, 2, 3] below the existing [1, 2] value.
#guard ((t0.insert [1, 2] "b").insert [1, 2, 3] "a").entries ==
  [([1, 2], "b"), ([1, 2, 3], "a")]

-- Divergent split: [1, 2, 3] and [1, 4] branch after the common prefix [1].
#guard ((t0.insert [1, 2, 3] "a").insert [1, 4] "c").entries ==
  [([1, 2, 3], "a"), ([1, 4], "c")]
#guard ((t0.insert [1, 2, 3] "a").insert [1, 4] "c").lookup [1, 2, 3] == some "a"
#guard ((t0.insert [1, 2, 3] "a").insert [1, 4] "c").lookup [1, 4] == some "c"
#guard ((t0.insert [1, 2, 3] "a").insert [1, 4] "c").lookup [1] == none
#guard (t0.insert [1, 2, 3] "a").lookup [1, 2] == none

-- Validity of built tries and the public API theorems.
example : Valid (t0 : RadixTrie Nat String) := Valid.empty
example : Valid ((t0.insert [1, 2, 3] "a").insert [1, 4] "c") :=
  Valid.insert (Valid.insert Valid.empty [1, 2, 3] "a") [1, 4] "c"
example (t : RadixTrie Nat String) (k : List Nat) (v : String) :
    (t.insert k v).lookup k = some v := lookup_insert_same t k v
example (t : RadixTrie Nat String) (h : Valid t) (k : List Nat) (v : String) :
    t.lookup k = some v ↔ (k, v) ∈ t.entries := lookup_eq_some_iff_mem_entries h k v

-- Malformed structures are rejected: empty edge label.
example : ¬ Valid (.node none [([], (.node (some "x") [] : RadixTrie Nat String))]) := by
  intro h
  cases h with
  | node hne _ _ _ =>
      exact hne ([], .node (some "x") []) (by simp) rfl

-- Malformed: duplicate sibling first symbols.
example : ¬ Valid (.node none
    [([1], (.node (some "x") [] : RadixTrie Nat String)),
     ([1, 2], .node (some "y") [])]) := by
  intro h
  have hd := Valid.nodup_child_heads h
  simp at hd

-- Malformed: an uncompressed unary value-free chain (the review's example) is not
-- valid; the inner node should have been merged into a single [0, 1] edge.
example : ¬ Valid (.node none
    [([0], (.node none [([1], .node (some "v") [])] : RadixTrie Nat String))]) := by
  intro h
  have hc := Valid.rootCompact_child h
    (e := ([0], (.node none [([1], .node (some "v") [])] : RadixTrie Nat String))) (by simp)
  simp [RootCompact] at hc

-- The compressed form of the same content is valid.
example : Valid (.node none [([0, 1], (.node (some "v") [] : RadixTrie Nat String))]) := by
  apply Valid.node
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    cases he
    simp
  · simp
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    cases he
    exact .node (by simp) (by simp) (by simp) (by simp)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    cases he
    exact rootCompact_some "v" []

end Cslib.Algorithms.Lean.RadixTrieTests

#print axioms Cslib.Algorithms.Lean.RadixTrie.lookup_insert_same
#print axioms Cslib.Algorithms.Lean.RadixTrie.lookup_insert_of_ne
#print axioms Cslib.Algorithms.Lean.RadixTrie.Valid.empty
#print axioms Cslib.Algorithms.Lean.RadixTrie.Valid.insert
#print axioms Cslib.Algorithms.Lean.RadixTrie.Valid.nodup_child_heads
#print axioms Cslib.Algorithms.Lean.RadixTrie.Valid.rootCompact_child
#print axioms Cslib.Algorithms.Lean.RadixTrie.lookup_eq_some_iff_mem_entries
#print axioms Cslib.Algorithms.Lean.RadixTrie.rootCompact_insert_cons
