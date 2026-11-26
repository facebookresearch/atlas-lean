/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.Enumerative.HypersequenceMatrixProduct

/-! # Tests for the product of Parisse's hypersequence matrices -/

open MetaMathlibExt

-- The first nonconstant row can also be checked directly against the defining sum.
example :
    ∑ i ∈ Finset.range 2, (hyperseqB 4 1 i : ℂ) * alternatingBinomialPowerSum i 1 1 5 = 1 := by
  norm_num [Finset.sum_range_succ, (hyperseqB_one 4).1, (hyperseqB_one 4).2,
    alternatingBinomialPowerSum, Nat.choose]

-- A nonzero shift on the diagonal gives 3!, not just the Kronecker delta.
example :
    ∑ i ∈ Finset.range 4, (hyperseqB 2 3 i : ℂ) * alternatingBinomialPowerSum i 3 1 3 = 6 := by
  have h := sum_hyperseqB_mul_hyperseqC 2 3 3
  norm_num [Nat.factorial] at h
  exact h

-- Below the diagonal there are no surviving falling-factorial terms.
example :
    ∑ i ∈ Finset.range 4, (hyperseqB 0 3 i : ℂ) * alternatingBinomialPowerSum i 2 1 1 = 0 := by
  simpa using sum_hyperseqB_mul_hyperseqC 0 3 2

-- Above the diagonal the terms cancel, including when the row is zero.
example :
    ∑ i ∈ Finset.range 1, (hyperseqB 0 0 i : ℂ) * alternatingBinomialPowerSum i 2 1 1 = 0 := by
  simpa using sum_hyperseqB_mul_hyperseqC 0 0 2

example :
    ∑ i ∈ Finset.range 1, (hyperseqB 0 0 i : ℂ) * alternatingBinomialPowerSum i 0 1 1 = 1 := by
  simpa using sum_hyperseqB_mul_hyperseqC 0 0 0
