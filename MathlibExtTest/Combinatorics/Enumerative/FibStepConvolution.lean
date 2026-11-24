/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.FibStepConvolution

namespace MathlibExt.Combinatorics.Enumerative.FibStepConvolutionWanted

-- The fourth-order window initially extends past index zero.
example : fibStepSeq 4 5 = [0, 1, 1, 2, 4, 8] := by decide

-- At index zero both sequences contribute their initial zero.
example : ∑ j ∈ Finset.range 1, fibStep 2 j * fibStep 3 (0 - j) = 0 := by
  rw [sum_fib_mul_trib 0]
  decide

-- At index five the shifted difference is 24 - 13.
example : ∑ j ∈ Finset.range 6, fibStep 2 j * fibStep 3 (5 - j) = 11 := by
  rw [sum_fib_mul_trib 5]
  decide

-- At the lower endpoint the shifted convolution has just one summand.
example : ∑ j ∈ Finset.range 2, fibStep 2 j * (fibStep 3 (1 - j) - fibStep 4 (1 - j)) = 0 := by
  rw [sum_fib_mul_sub_eq 1 (by decide)]
  decide

-- The first nonzero convolution detects both the sign and the one-place shift.
example : ∑ j ∈ Finset.range 7, fibStep 2 j * (fibStep 3 (6 - j) - fibStep 4 (6 - j)) = -1 := by
  rw [sum_fib_mul_sub_eq 6 (by decide)]
  decide

-- For the next three orders, the shifted sum again starts at index zero.
example : ∑ j ∈ Finset.range 2, fibStep 3 j * (fibStep 4 (1 - j) - fibStep 5 (1 - j)) = 0 := by
  rw [sum_trib_mul_sub_eq 1 (by decide)]
  decide

-- The tetranacci and pentanacci terms first differ at index six.
example : ∑ j ∈ Finset.range 8, fibStep 3 j * (fibStep 4 (7 - j) - fibStep 5 (7 - j)) = -1 := by
  rw [sum_trib_mul_sub_eq 7 (by decide)]
  decide

-- At the lower bound the term three places back is the initial zero.
example : 5 * ∑ j ∈ Finset.range 4, fibStep 6 j * fibStep 2 (3 - j) = 10 := by
  rw [five_mul_sum_fibStep6_mul_fib 3 (by decide)]
  decide

-- At index nine the convolution first uses the six-step value at index eight with nonzero weight.
example : 5 * ∑ j ∈ Finset.range 10, fibStep 6 j * fibStep 2 (9 - j) = 1105 := by
  rw [five_mul_sum_fibStep6_mul_fib 9 (by decide)]
  decide

end MathlibExt.Combinatorics.Enumerative.FibStepConvolutionWanted
