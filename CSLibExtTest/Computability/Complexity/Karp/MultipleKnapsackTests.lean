/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.MultipleKnapsack

/-! # Tests for the MULTIPLE KNAPSACK definitions, reduction map and certificate check -/

open MetaMathlibExt.Complexity.NPComplete.MultipleKnapsack
open MetaMathlibExt.BitstringEncoding Cslib.Complexity.Karp

/-! ### Feasibility -/

-- Two knapsacks of capacity 2 and 1; items (weight, value) (2, 3) and (1, 1). Packing both
-- items, one per knapsack, reaches value 4.
example : MultipleKnapsackFeasible ([(2, 3), (1, 1)], [2, 1], 4) :=
  ⟨[0, 1], rfl, by decide, by decide, by decide⟩

-- With only the first knapsack the value 4 is out of reach.
example : ¬ MultipleKnapsackFeasible ([(2, 3), (1, 1)], [2], 4) := by
  rw [feasible_iff_exists_loopCheck]
  rintro ⟨w, hw, h⟩
  simp only [List.length_cons, List.length_nil] at hw
  rcases w with _ | ⟨a, _ | ⟨b, _ | ⟨c, w⟩⟩⟩ <;> simp at hw <;>
    revert h <;> (try cases a) <;> (try cases b) <;> decide

-- Assignment `m` (here `1`) leaves an item out: a zero target is always met.
example : MultipleKnapsackFeasible ([(5, 5)], [1], 0) :=
  ⟨[1], rfl, by decide, by decide, by decide⟩

example : ¬ MultipleKnapsackFeasible noInstance := not_feasible_noInstance

/-! ### The SUBSET-SUM reduction -/

example : fromSubsetSum [2, 3] 5 = ([(2, 2), (3, 3)], [5], 5) := rfl

example : MultipleKnapsackFeasible (fromSubsetSum [2, 3] 5) :=
  (fromSubsetSum_feasible _ _).2 ⟨[2, 3], List.Sublist.refl _, rfl⟩

example : ¬ MultipleKnapsackFeasible (fromSubsetSum [2, 2] 3) := by
  rw [fromSubsetSum_feasible]
  rintro ⟨l, hl, hs⟩
  have : l = [] ∨ l = [2] ∨ l = [2, 2] := by
    rcases hl with _ | ⟨_, hl⟩ | ⟨_, hl⟩ <;>
      rcases hl with _ | ⟨_, hl⟩ | ⟨_, hl⟩ <;> cases hl <;> simp
  rcases this with rfl | rfl | rfl <;> simp at hs

-- Malformed SUBSET-SUM strings go to the fixed no-instance.
example : reduceFromSubsetSum [] = bitEncode noInstance := by decide
example : reduceFromSubsetSum [true] = bitEncode noInstance := by decide

example : reduceFromSubsetSum (encodeSS [2] 2) = bitEncode (fromSubsetSum [2] 2) := by decide

example : multipleKnapsackDec (reduceFromSubsetSum (encodeSS [2, 3] 5)) = true := by
  rw [← reduceFromSubsetSum_correct, subsetSumDec_encodeSS_eq_true]
  exact ⟨[2, 3], List.Sublist.refl _, rfl⟩

/-! ### The certificate check -/

-- The masks `[1, 0]` and `[0, 1]` put the first item in knapsack 0 and the second in knapsack 1.
example : mkCheck (bitEncode (([(2, 3), (1, 1)], [2, 1], 4) : MultipleKnapsackInstance))
    [true, false, false, true] = true := by decide

-- Both items in knapsack 0 overflow its capacity 2.
example : mkCheck (bitEncode (([(2, 3), (1, 1)], [2, 1], 4) : MultipleKnapsackInstance))
    [true, true, false, false] = false := by decide

-- Overlapping masks count each selected item once in the value.
example : mkCheck (bitEncode (([(1, 3)], [1, 1], 6) : MultipleKnapsackInstance))
    [true, true] = false := by decide

-- An undecodable instance is rejected whatever the certificate.
example : mkCheck [true] [] = false := by decide

-- Missing certificate bits count as false: `[true]` is read as the mask `[true, false]`.
example : mkCheck (bitEncode (([(1, 2), (1, 0)], [1], 2) : MultipleKnapsackInstance))
    [true] = true := by decide

-- Bits after the last mask are ignored: for one item and one knapsack, `[true]` and
-- `[true, true]` both pass.
example : mkCheck (bitEncode (([(1, 2)], [1], 2) : MultipleKnapsackInstance)) [true] = true := by
  decide

example : mkCheck (bitEncode (([(1, 2)], [1], 2) : MultipleKnapsackInstance))
    [true, true] = true := by decide

-- The standalone loop does not need lists of equal lengths: with one flag, the masks have one
-- bit and the weight `5` at position `1` is never selected; with two flags it is.
example : loopCheck [1, 5] [2] 2 [1] [true, true] [true] = true := by decide

example : loopCheck [1, 5] [2] 2 [1] [true, true] [true, true] = false := by decide

example : multipleKnapsackDec
    (bitEncode (([(2, 3), (1, 1)], [2, 1], 4) : MultipleKnapsackInstance)) = true :=
  (multipleKnapsackDec_iff_check _).2 ⟨[true, false, false, true], by decide, by decide⟩

example : multipleKnapsackDec [true] = false := by
  have hd : bitDecode (α := MultipleKnapsackInstance) [true] = none := by decide
  simp [multipleKnapsackDec, hd]

/-! ### Noncanonical inputs -/

-- The capacity field `[false]` is not canonical; the decoder reads it as `2`, so the bitstring
-- decodes to `([], [2], 0)` and is accepted, although it is not the canonical encoding.
example : delimit [] ++ delimit (delimit [false]) ≠
    bitEncode (([], [2], 0) : MultipleKnapsackInstance) := by decide

example : multipleKnapsackDec (delimit [] ++ delimit (delimit [false])) = true := by
  classical
  change decide (MultipleKnapsackFeasible ([], [2], 0)) = true
  rw [decide_eq_true_eq]
  exact ⟨[], rfl, by decide, by decide, by decide⟩
