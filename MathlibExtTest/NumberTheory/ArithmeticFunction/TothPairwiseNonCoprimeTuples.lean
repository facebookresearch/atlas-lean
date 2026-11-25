/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.TothPairwiseNonCoprimeTuples

open Finset MetaMathlibExt

-- Only (0, 1) and (1, 2) are coprime in this tuple.
example : coprimePairCount ![0, 1, 2] = 2 := by decide

-- At r = 1, the two singleton contributions cancel the double-edge contribution.
example :
    (∑ j ∈ Icc 1 3, (-1 : ℤ) ^ (j - 1) * (j.choose 1 : ℤ) *
      ∑ E ∈ (univ.filter fun e : Fin 3 × Fin 3 => e.1 < e.2).powersetCard j,
        (coprimalityIndicator E ![0, 1, 2] : ℤ)) = 0 := by decide

-- At r = 0, even the all-zero tuple contributes one via the empty graph.
example :
    (∑ j ∈ Icc 0 1, (-1 : ℤ) ^ j *
      ∑ E ∈ (univ.filter fun e : Fin 2 × Fin 2 => e.1 < e.2).powersetCard j,
        (coprimalityIndicator E ![0, 0] : ℤ)) = 1 := by
  have h : coprimePairCount ![0, 0] = 0 := by decide
  simpa [h] using (exactly_coprime_pairs_inclusion_exclusion (by decide) 0 ![0, 0]).symm

-- Asking for two coprime pairs in a two-component tuple gives an empty sum.
example (n : Fin 2 → ℕ) : coprimePairCount n ≠ 2 := by
  have h := exactly_coprime_pairs_inclusion_exclusion (by decide) 2 n
  simpa using h

-- At the exact threshold, the only contributing edge set consists of both good pairs.
example :
    (∑ j ∈ Icc 2 3, (-1 : ℤ) ^ (j - 2) * ((j - 1).choose (2 - 1) : ℤ) *
      ∑ E ∈ (univ.filter fun e : Fin 3 × Fin 3 => e.1 < e.2).powersetCard j,
        (coprimalityIndicator E ![0, 1, 2] : ℤ)) = 1 := by
  have h : coprimePairCount ![0, 1, 2] = 2 := by decide
  simpa [h] using (at_least_coprime_pairs_inclusion_exclusion (by decide) 2 (by decide)
    ![0, 1, 2]).symm

-- At threshold one, the two singleton contributions and the negative double-edge term sum to one.
example :
    (∑ j ∈ Icc 1 3, (-1 : ℤ) ^ (j - 1) * ((j - 1).choose (1 - 1) : ℤ) *
      ∑ E ∈ (univ.filter fun e : Fin 3 × Fin 3 => e.1 < e.2).powersetCard j,
        (coprimalityIndicator E ![0, 1, 2] : ℤ)) = 1 := by
  decide

-- Above the total number of available pairs, the empty sum forces a false threshold.
example (n : Fin 2 → ℕ) : ¬ 2 ≤ coprimePairCount n := by
  have h := at_least_coprime_pairs_inclusion_exclusion (by decide) 2 (by decide) n
  simpa using h
