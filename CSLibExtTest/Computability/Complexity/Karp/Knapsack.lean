/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Complexity.Karp.Knapsack

namespace CSLibExtTest.Computability.Complexity.Karp.Knapsack

open MetaMathlibExt.BitstringEncoding MetaMathlibExt.Complexity.NPComplete.Knapsack

private theorem accepts_encoding (i : KnapsackInstance) :
    knapsackDec (bitEncode i) = true ↔ KnapsackFeasible i := by
  simp [knapsackDec]

-- Equal item pairs represent two occurrences that can be selected together.
example : knapsackDec (bitEncode (([(2, 3), (2, 3)], 4, 6) : KnapsackInstance)) = true := by
  rw [accepts_encoding]
  exact ⟨[(2, 3), (2, 3)], List.Sublist.refl _, by decide, by decide⟩

-- The value threshold can be met only by exceeding the capacity.
example : knapsackDec (bitEncode (([(2, 3)], 1, 3) : KnapsackInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨chosen, h, hw, hv⟩
  rcases List.sublist_singleton.mp h with rfl | rfl
  · exact (by decide : ¬3 ≤ 0) hv
  · exact (by decide : ¬2 ≤ 1) hw

-- The empty selection meets a zero target.
example : knapsackDec (bitEncode (([], 0, 0) : KnapsackInstance)) = true := by
  rw [accepts_encoding]
  exact ⟨[], List.Sublist.slnil, by decide, by decide⟩

-- A noncanonical natural payload is accepted if the canonical decoder accepts it.
example : knapsackDec [false, true, false, false] = true := by
  have hd : bitDecode (α := KnapsackInstance) [false, true, false, false] =
      some ([], 2, 0) := by decide
  simp only [knapsackDec, hd, decide_eq_true_eq]
  exact ⟨[], List.Sublist.slnil, by decide, by decide⟩

-- An incomplete outer frame is a no-instance.
example : knapsackDec [true] = false := rfl

end CSLibExtTest.Computability.Complexity.Karp.Knapsack
