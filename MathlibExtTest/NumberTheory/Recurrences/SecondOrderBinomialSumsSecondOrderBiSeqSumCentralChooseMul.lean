/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.SecondOrderBinomialSumsSecondOrderBiSeqSumCentralChooseMul

/-!
# Tests for two-sided central-binomial product sums

Concrete negative shifts and a squared-sequence corollary use the four product identities.
-/

namespace MathlibExtTest.NumberTheory.Recurrences.SecondOrderBinomialSumsSecondOrderBiSeqSumCentralChooseMul

open MetaMathlibExt

example (n : ℕ) (hn : 0 < n) :
    (∑ k ∈ Finset.Icc (-(n : ℤ)) n, ((2 * n).choose (n + k).toNat : ℤ) *
      secondOrderBiSeq 1 0 1 k * secondOrderBiSeq 1 0 1 k) = 2 * 5 ^ (n - 1) := by
  simpa [mul_comm] using (secondOrderBiSeq_sum_central_choose_mul 1 n hn 0 0).1

example :
    (∑ k ∈ Finset.Icc (-2 : ℤ) 2, ((4 : ℕ).choose (2 + k).toNat : ℤ) *
      secondOrderBiSeq (-1) 2 (-1) (k - 3) * secondOrderBiSeq (-1) 2 (-1) (k + 2)) = 25 := by
  simpa [sub_eq_add_neg, (secondOrderBiSeq_small (-1) 2 (-1)).2.2.2] using
    (secondOrderBiSeq_sum_central_choose_mul (-1) 2 (by decide) (-3) 2).2.1

example :
    (∑ k ∈ Finset.Icc (-1 : ℤ) 1, ((2 : ℕ).choose (1 + k).toNat : ℤ) *
      secondOrderBiSeq 0 0 1 (k - 2) * secondOrderBiSeq 0 2 0 (k + 1)) = 4 := by
  simpa [sub_eq_add_neg, (secondOrderBiSeq_small 0 0 1).2.2.2] using
    (secondOrderBiSeq_sum_central_choose_mul 0 1 (by decide) (-2) 1).2.2.1

example :
    (∑ k ∈ Finset.Icc (-1 : ℤ) 1, ((2 : ℕ).choose (1 + k).toNat : ℤ) *
      secondOrderBiSeq 0 2 0 (k + 1) * secondOrderBiSeq 0 0 1 (k - 2)) = 4 := by
  simpa [sub_eq_add_neg, (secondOrderBiSeq_small 0 0 1).2.2.2] using
    (secondOrderBiSeq_sum_central_choose_mul 0 1 (by decide) 1 (-2)).2.2.2

end MathlibExtTest.NumberTheory.Recurrences.SecondOrderBinomialSumsSecondOrderBiSeqSumCentralChooseMul
