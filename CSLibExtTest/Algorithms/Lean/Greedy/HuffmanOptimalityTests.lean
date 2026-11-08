/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Greedy.HuffmanOptimality
public meta import CSLibExt.Algorithms.Lean.Greedy.HuffmanOptimality

public section

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.privateModule false

namespace Cslib.Algorithms.Lean.HuffmanOptimalityTests

private def worseTree : HuffmanTree Nat :=
  .fork (.fork (.leaf 0 1) (.leaf 2 100)) (.leaf 1 1)

private def optimalTree : Option (HuffmanTree Nat) :=
  huffman [(0, 1), (1, 1), (2, 100)]

private theorem worseTree_admissible :
    worseTree.Admissible [(0, 1), (1, 1), (2, 100)] := by
  change [(0, 1), (2, 100), (1, 1)].Perm [(0, 1), (1, 1), (2, 100)]
  exact List.Perm.cons _ (List.Perm.swap _ _ [])

example : worseTree.Admissible [(0, 1), (1, 1), (2, 100)] :=
  worseTree_admissible

example {tree : HuffmanTree Nat}
    (h : huffman [(0, 1), (1, 1), (2, 100)] = some tree) :
    tree.weightedPathLength ≤ worseTree.weightedPathLength :=
  huffman_optimal h worseTree_admissible

#guard worseTree.weightedPathLength == 203

#guard optimalTree.map HuffmanTree.weightedPathLength == some 104

#guard optimalTree.isSome

private def singletonTree : Option (HuffmanTree Nat) :=
  huffman [(7, 5)]

#guard singletonTree.map HuffmanTree.encodedLength == some 5

#guard singletonTree.map HuffmanTree.weightedPathLength == some 0

example {tree : HuffmanTree Nat}
    (h : huffman [(7, 5)] = some tree) :
    tree.encodedLength ≤ (HuffmanTree.leaf 7 5).encodedLength :=
  huffman_encodedLength_optimal h List.Perm.rfl

example : (huffman [(0, 1), (1, 1), (2, 100)]).isSome :=
  huffman_isSome (by decide) (by decide)

example : (huffman [(7, 5)]).isSome :=
  huffman_isSome (by decide) (by decide)

example : huffman ([] : List (Nat × Nat)) = none :=
  huffman_eq_none_iff.mpr (Or.inl rfl)

example : huffman [(0, 1), (0, 2)] = none :=
  huffman_eq_none_iff.mpr (Or.inr (by decide))

example : (worseTree.weightedLeaves.map
    (fun x => x.2 * ((worseTree.code? x.1).map List.length).getD 0)).sum =
    worseTree.encodedLength :=
  HuffmanTree.encodedLength_eq_sum_codeLengths (by decide)

end Cslib.Algorithms.Lean.HuffmanOptimalityTests
