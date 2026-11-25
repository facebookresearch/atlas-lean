/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.BasePhiRepresentations

/-!
# Tests for natural base phi expansions
-/

namespace MetaMathlibExt

-- The two initial counts use different Bergman words: 1 and 10.01.
example : naturalExpansionCount 1 = 1 ∧ naturalExpansionCount 2 = 2 :=
  naturalExpansionCount_fib 0

-- Both families have acquired copies of the repeating block at this index.
example : naturalExpansionCount 8 = 5 ∧ naturalExpansionCount 13 = 13 :=
  naturalExpansionCount_fib 2

-- The leftmost digit of 10.01 can be flipped to give a second natural expansion of 2.
example : ({0, -1, -2} : Finset ℤ) ∈ naturalExpansions 2 :=
  ⟨zero_neg_one_neg_two_mem_knottExpansions, {1, -2}, isBergmanExpansion_one_neg_two,
    by rw [basePhiValue_one_neg_two]; norm_num, by decide⟩

-- The Knott condition excludes an expansion that ends in 011.
example : ({-1, -2} : Finset ℤ) ∉ naturalExpansions 1 :=
  fun h => not_satisfiesKnottCondition_neg_one_neg_two h.1.2

end MetaMathlibExt
