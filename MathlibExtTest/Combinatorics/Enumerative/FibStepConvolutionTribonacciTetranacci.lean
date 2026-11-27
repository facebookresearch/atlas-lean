/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.FibStepConvolutionTribonacciTetranacci

namespace MathlibExt.Combinatorics.Enumerative.FibStepConvolutionWanted

-- The zero-index convolution has just the initial zero term.
example : ∑ j ∈ Finset.range 1, fibStep 3 j * fibStep 4 (0 - j) = 0 := by
  rw [sum_trib_mul_tetra 0]
  decide

-- The first nonzero convolution detects the sign and three-place shift.
example : ∑ j ∈ Finset.range 3, fibStep 3 j * fibStep 4 (2 - j) = 1 := by
  rw [sum_trib_mul_tetra 2]
  decide

-- At index six the convolution uses distinct tribonacci and tetranacci values.
example : ∑ j ∈ Finset.range 7, fibStep 3 j * fibStep 4 (6 - j) = 27 := by
  rw [sum_trib_mul_tetra 6]
  decide

end MathlibExt.Combinatorics.Enumerative.FibStepConvolutionWanted
