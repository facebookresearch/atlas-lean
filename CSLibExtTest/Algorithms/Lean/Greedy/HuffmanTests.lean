/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Greedy.Huffman
public meta import CSLibExt.Algorithms.Lean.Greedy.Huffman

public section

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.privateModule false

open MathlibExt.InformationTheory

namespace Cslib.Algorithms.Lean.HuffmanTests

#guard huffman ([] : List (Nat × Nat)) == none

#guard huffman [(7, 0)] == some (.leaf 7 0)

#guard huffman [(1, 2), (1, 3)] == none

private def tied : Option (HuffmanTree Nat) := huffman [(10, 1), (20, 1), (30, 1)]

#guard (tied >>= (·.code? 30)) == some [false]

#guard (tied >>= (·.code? 10)) == some [true, false]

#guard (tied >>= (·.code? 20)) == some [true, true]

private def zeroWeights : Option (HuffmanTree Nat) := huffman [(10, 0), (20, 0), (30, 1)]

#guard (zeroWeights >>= (·.code? 10)) == some [false, false]

#guard (zeroWeights >>= (·.code? 20)) == some [false, true]

#guard (zeroWeights >>= (·.code? 30)) == some [true]

private def populated : Option (HuffmanTree Nat) :=
  huffman [(0, 5), (1, 9), (2, 12), (3, 13), (4, 16), (5, 45)]

#guard (populated >>= fun tree => tree.encode? [5, 0, 4, 2]) ==
  some [false, true, true, false, false, true, true, true, true, false, false]

#guard (populated >>= fun tree => tree.encode? [5, 0, 4, 2] >>= tree.decode?) ==
  some [5, 0, 4, 2]

example {α : Type} [DecidableEq α] {input : List (α × Nat)}
    {tree : HuffmanTree α} (h : huffman input = some tree) :
    tree.weightedLeaves.Perm input :=
  huffman_weightedLeaves_perm h

example {α : Type} [DecidableEq α] {input : List (α × Nat)}
    {tree : HuffmanTree α} (h : huffman input = some tree) :
    IsPrefixFree tree.codeOfLeaf :=
  huffman_prefixFree h

example {α : Type} [DecidableEq α] {tree : HuffmanTree α}
    (message : List tree.LeafSymbol) :
    tree.decode? (message.flatMap fun symbol => tree.codeOfLeaf symbol) =
      some (message.map Subtype.val) :=
  tree.decode_codeOfLeaf message

example {α : Type} [DecidableEq α] (tree : HuffmanTree α)
    (message : List tree.LeafSymbol) :
    (match tree.encode? (message.map Subtype.val) with
      | none => none
      | some bits => tree.decode? bits) =
      some (message.map Subtype.val) :=
  tree.decode_encode_leafSymbols message

example {heap : MinHeap HuffmanPriority} {choice : HuffmanTwoMin}
    (h : extractTwoMin? heap = some choice) :
    (∀ item ∈ heap.elements, choice.first ≤ item) ∧
      (∀ item ∈ choice.second ::ₘ choice.rest.elements, choice.second ≤ item) :=
  extractTwoMin_greedy h

example {α : Type} (left right : HuffmanTree α) :
    (HuffmanTree.fork left right).weightedPathLength =
      left.weightedPathLength + right.weightedPathLength + left.totalWeight + right.totalWeight :=
  HuffmanTree.weightedPathLength_fork left right

end Cslib.Algorithms.Lean.HuffmanTests
