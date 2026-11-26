/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PartitionConvolutionModThree

open MetaMathlibExt PowerSeries

-- The constant coefficient comes from the empty partition in both factors.
example : (∑ x ∈ Finset.antidiagonal 0,
    (Fintype.card (Nat.Partition x.1) : ℤ) * (Fintype.card (Nat.Partition x.2) : ℤ))
    ≡ 1 [ZMOD 3] := by
  apply (partition_convolution_two_modEq_three 0).trans
  have h₀ := coeff_pentagonalSeries_pentagonal ℤ 0
  norm_num [pentagonal_def] at h₀
  simp [h₀]

-- At degree five the two Euler coefficients are +1 and -1.
example : (∑ x ∈ Finset.antidiagonal 5,
    (Fintype.card (Nat.Partition x.1) : ℤ) * (Fintype.card (Nat.Partition x.2) : ℤ))
    ≡ 0 [ZMOD 3] := by
  have h₅ := coeff_pentagonalSeries_pentagonal ℤ 2
  have h₂ := coeff_pentagonalSeries_pentagonal ℤ (-1)
  apply (partition_convolution_two_modEq_three 5).trans
  norm_num [pentagonal_def, Int.coe_negOnePow] at h₅ h₂
  norm_num [Finset.sum_range_succ, h₅, h₂]
