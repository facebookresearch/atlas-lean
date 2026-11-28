/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.BasePhiRepresentations

/-!
# Tests for base phi expansions
-/

open scoped goldenRatio

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

-- Zero has no occupied positions and needs no flips.
example : Relation.ReflTransGen IsGoldenMeanFlip ∅ ∅ :=
  reflTransGen_isGoldenMeanFlip_of_isBergmanExpansion 0
    (by simp [IsBergmanExpansion]) (by norm_num [basePhiValue_empty])
    (by norm_num [basePhiValue_empty])

-- The three adjacent occupied positions in 1.11 require choosing the highest pair to carry.
example : Relation.ReflTransGen IsGoldenMeanFlip {1, -2} {0, -1, -2} :=
  reflTransGen_isGoldenMeanFlip_of_isBergmanExpansion 2 isBergmanExpansion_one_neg_two
    (by norm_num [basePhiValue_one_neg_two]) (by norm_num [basePhiValue_zero_neg_one_neg_two])

-- This expansion of 2 has two more occupied positions than the Bergman expansion.
example : Relation.ReflTransGen IsGoldenMeanFlip {1, -2} {0, -1, -3, -4} := by
  apply reflTransGen_isGoldenMeanFlip_of_isBergmanExpansion 2 isBergmanExpansion_one_neg_two
    (by norm_num [basePhiValue_one_neg_two])
  have hcarry : φ ^ (-3 : ℤ) + φ ^ (-4 : ℤ) = φ ^ (-2 : ℤ) := calc
    _ = φ ^ (-4 : ℤ) * (φ + 1) := by
      rw [show (-3 : ℤ) = -4 + 1 by decide, zpow_add_one₀ Real.goldenRatio_ne_zero]
      ring
    _ = φ ^ (-4 : ℤ) * φ ^ (2 : ℤ) := by rw [zpow_ofNat, Real.goldenRatio_sq]
    _ = _ := by rw [show (-2 : ℤ) = -4 + 2 by decide, zpow_add₀ Real.goldenRatio_ne_zero]
  change basePhiValue {0, -1, -3, -4} = (2 : ℝ)
  rw [← basePhiValue_zero_neg_one_neg_two]
  unfold basePhiValue
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_pair (by decide),
    Finset.sum_insert (by decide), Finset.sum_pair (by decide), hcarry]

-- The expansion 10.01 has value 2: its leading digit contributes at most 2, and its value
-- is strictly below the contribution of a digit at the next position.
example : φ ^ (1 : ℤ) ≤ (2 : ℝ) ∧ (2 : ℝ) < φ ^ (2 : ℤ) := by
  rw [← basePhiValue_one_neg_two]
  refine ⟨BasePhiRepresentations.value_pow_le_of_mem (by decide), ?_⟩
  apply BasePhiRepresentations.bergman_value_lt isBergmanExpansion_one_neg_two
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  omega

-- Any Bergman expansion of 2 has exactly the two occupied positions of 10.01.
example {S : Finset ℤ} (hS : IsBergmanExpansion S) (hval : basePhiValue S = 2) :
    S = {1, -2} :=
  BasePhiRepresentations.bergman_eq_of_value_eq hS isBergmanExpansion_one_neg_two
    (hval.trans basePhiValue_one_neg_two.symm)

-- The contribution of the two fractional digits in .11 is exactly one.
example : φ ^ (-1 : ℤ) + φ ^ (-2 : ℤ) = 1 := by
  simpa only [show (-1 : ℤ) - 1 = -2 by decide, neg_add_cancel, zpow_zero]
    using BasePhiRepresentations.pow_add_prev (-1)

end MetaMathlibExt
