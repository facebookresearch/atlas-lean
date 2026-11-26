/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.DataStructures.BinaryHeap.BuildHeap
meta import CSLibExt.Algorithms.Lean.DataStructures.BinaryHeap.BuildHeap

/-! # Tests for bottom-up binary heap construction

Concrete runs check the result and the exact counters on boundary inputs, and on the worst
case of a perfect tree, where the swap and comparison bounds are attained. The examples
exercise the public theorems from an importing module.
-/

set_option autoImplicit false

open Cslib.Algorithms.Lean

/-! ### Node heights -/

-- The perfect tree with seven nodes: one node of height two, two of height one.
#guard (List.range 7).map (heapHeight 7) == [2, 1, 1, 0, 0, 0, 0]
#guard (∑ i ∈ Finset.range 7, heapHeight 7 i) == 4
-- A complete but not perfect tree: index `2` of a four-node tree is a leaf, although the
-- remaining-depth measure `Nat.log2 4 - Nat.log2 3` of `TimeM.siftDown_swaps_le` is one.
#guard heapHeight 4 2 == 0
#guard Nat.log2 4 - Nat.log2 3 == 1
-- Indices beyond the tree have height zero.
#guard heapHeight 4 4 == 0 && heapHeight 0 0 == 0
-- The sum of heights is `n` minus the binary digit sum of `n`.
#guard (List.range 40).all fun n =>
  (∑ i ∈ Finset.range n, heapHeight n i) + (Nat.digits 2 n).sum == n

example : heapHeight 7 0 = if heapLeft 0 < 7 then
    max (heapHeight 7 (heapLeft 0)) (heapHeight 7 (heapRight 0)) + 1 else 0 :=
  heapHeight_eq 7 0

example (n i d : Nat) (hi : i < n) : d ≤ heapHeight n i ↔ (i + 1) * 2 ^ d ≤ n :=
  le_heapHeight_iff hi d

/-! ### Concrete runs -/

#guard buildHeap (#[] : Array Nat) == #[]
#guard buildHeap #[5] == #[5]
#guard buildHeap #[2, 1] == #[1, 2]
#guard buildHeap #[1, 2, 3, 4, 5, 6, 7] == #[1, 2, 3, 4, 5, 6, 7]
#guard buildHeap #[7, 6, 5, 4, 3, 2, 1] == #[1, 3, 2, 4, 6, 7, 5]
#guard buildHeap #[3, 1, 3, 2, 1] == #[1, 1, 3, 2, 3]

#guard (TimeM.buildHeap (#[] : Array Nat)).time == (0, 0)
#guard (TimeM.buildHeap #[5]).time == (0, 0)
-- One node with only a left child: one comparison, no child-selection comparison.
#guard (TimeM.buildHeap #[2, 1]).time == (1, 1)
-- Already a heap: two comparisons per internal node and no swaps.
#guard (TimeM.buildHeap #[1, 2, 3, 4, 5, 6, 7]).time == (6, 0)
-- Decreasing input on the perfect tree of height two: `S = 4` swaps and `2 S = 8` comparisons.
#guard (TimeM.buildHeap #[7, 6, 5, 4, 3, 2, 1]).time == (8, 4)
#guard (TimeM.buildHeap #[7, 6, 5, 4, 3, 2, 1]).ret == #[1, 3, 2, 4, 6, 7, 5]

/-! ### Public theorems -/

section
variable {α : Type} [LinearOrder α] (a : Array α)

example : (TimeM.buildHeap a).ret = buildHeap a := TimeM.ret_buildHeap a
example : HeapOrdered (buildHeap a) := buildHeap_ordered a
example : (buildHeap a).Perm a := buildHeap_perm a
example (i : Nat) : (TimeM.siftDown a i).time.2 ≤ heapHeight a.size i :=
  TimeM.siftDown_swaps_le_heapHeight a i
example (i : Nat) : (TimeM.siftDown a i).time.1 ≤ 2 * heapHeight a.size i :=
  TimeM.siftDown_comparisons_le_heapHeight a i

-- The explicit linear bounds: at most `n` swaps and `2 n` comparisons.
example : (TimeM.buildHeap a).time.2 ≤ a.size ∧ (TimeM.buildHeap a).time.1 ≤ 2 * a.size := by
  obtain ⟨-, -, hs, hc, hsum, -⟩ := TimeM.buildHeap_linear a
  omega

-- A perfect tree of height two has height sum `2 ^ 3 - 1 - 3 = 4`.
example (h7 : a.size = 7) : ∑ i ∈ Finset.range a.size, heapHeight a.size i = 4 :=
  (TimeM.buildHeap_linear a).2.2.2.2.2 2 h7
end

#print axioms le_heapHeight_iff
#print axioms heapHeight_eq
#print axioms sum_heapHeight_add_digits_sum
#print axioms buildHeap_perm
#print axioms buildHeap_ordered
#print axioms TimeM.ret_buildHeap
#print axioms TimeM.siftDown_swaps_le_heapHeight
#print axioms TimeM.siftDown_comparisons_le_heapHeight
#print axioms TimeM.buildHeap_linear
