/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.FibStepConvolution

namespace MathlibExt.Combinatorics.Enumerative.FibStepConvolutionWanted

-- At zero the subtracted boundary term has index 0 by natural subtraction.
example : 2 * ∑ j ∈ Finset.range 1, (-1 : ℤ) ^ j * fibStep 3 j = 0 := by
  rw [two_mul_sum_neg_one_pow_trib (n := 0)]
  decide

-- The first nonzero sum contains the term -T₁.
example : 2 * ∑ j ∈ Finset.range 2, (-1 : ℤ) ^ j * fibStep 3 j = -2 := by
  rw [two_mul_sum_neg_one_pow_trib (n := 1)]
  decide

-- Later even and odd endpoints have opposite signs and nonzero lower boundary terms.
example : 2 * ∑ j ∈ Finset.range 5, (-1 : ℤ) ^ j * fibStep 3 j = 4 := by
  rw [two_mul_sum_neg_one_pow_trib (n := 4)]
  decide

example : 2 * ∑ j ∈ Finset.range 6, (-1 : ℤ) ^ j * fibStep 3 j = -10 := by
  rw [two_mul_sum_neg_one_pow_trib (n := 5)]
  decide

end MathlibExt.Combinatorics.Enumerative.FibStepConvolutionWanted
