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

namespace Cslib.Algorithms.Lean.HuffmanLookupTests

private def singletonInput : List (Nat × Nat) := [(7, 5)]

private def singletonForest : List (HuffmanWorkItem Nat) :=
  initialHuffmanForest singletonInput

#guard huffmanLoopWithLookupCount 0 1 (huffmanHeapOfForest singletonForest)
  (initialHuffmanTable singletonInput) == some (.leaf 7 5, 1)

private def fourInput : List (Nat × Nat) :=
  [(10, 1), (20, 1), (30, 2), (40, 3)]

private def fourForest : List (HuffmanWorkItem Nat) :=
  initialHuffmanForest fourInput

#guard (huffmanLoopWithLookupCount 3 4 (huffmanHeapOfForest fourForest)
  (initialHuffmanTable fourInput)).map Prod.snd == some 7

#guard (huffmanLoopWithLookupCount 3 4 (huffmanHeapOfForest fourForest)
  (initialHuffmanTable fourInput)).map Prod.fst ==
    huffmanLoop 3 4 (huffmanHeapOfForest fourForest) (initialHuffmanTable fourInput)

example {α : Type} (fuel nextSerial : Nat) (heap : MinHeap HuffmanPriority)
    (table : Array (Option (HuffmanWorkItem α))) :
    (huffmanLoopWithLookupCount fuel nextSerial heap table).map Prod.fst =
      huffmanLoop fuel nextSerial heap table :=
  huffmanLoopWithLookupCount_map_fst fuel nextSerial heap table

-- API contract: the accumulator form adds its initial count verbatim.
#guard huffmanLoopWithLookupCountAux 0 1 (huffmanHeapOfForest singletonForest)
  (initialHuffmanTable singletonInput) 40 == some (.leaf 7 5, 41)

end Cslib.Algorithms.Lean.HuffmanLookupTests

