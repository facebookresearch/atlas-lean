/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.SkewHeap.Basic
public import CSLibExt.Algorithms.Lean.DataStructures.SkewHeap.PriorityQueue
public import CSLibExt.Algorithms.Lean.DataStructures.SkewHeap.Amortized

/-!
# Skew heaps

Skew heaps (Sleator–Tarjan) are heaps in the sense of §14.1 that
implement mergeable priority queues, and can be viewed as a
self-adjusting form of leftist heaps that attempt to maintain
balance by unconditionally swapping all nodes on the merge path.
Import the submodules separately when only one API is needed:
`SkewHeap.Basic` (carrier, merge, operations),
`SkewHeap.PriorityQueue` (the ADTs and the correctness proof),
`SkewHeap.Amortized` (potential, Lemma 22.1, logarithmic amortized
bounds, Exercise 22.1).

Source: the AFP entries `Skew Heap` and `Amortized Complexity`
and book Ch. 22, as cited in each submodule (`SkewHeap.Basic`,
`SkewHeap.PriorityQueue`, `SkewHeap.Amortized`).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean
namespace SkewHeap


end SkewHeap

end Cslib.Algorithms.Lean
