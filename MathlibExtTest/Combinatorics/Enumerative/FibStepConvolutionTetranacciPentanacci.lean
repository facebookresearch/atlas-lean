/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.FibStepConvolutionTetranacciPentanacci

/-! # Tests for the tetranacci–pentanacci convolution -/

open MathlibExt.Combinatorics.Enumerative.FibStepConvolutionWanted

-- The convolution is zero at the lower endpoint.
example : (∑ j ∈ Finset.range (0 + 1), fibStep 4 j * fibStep 5 (0 - j)) = 0 := by
  rw [sum_tetra_mul_penta 0]
  decide

-- At n = 4 the three interior terms contribute 2, 1 and 2.
example : (∑ j ∈ Finset.range (4 + 1), fibStep 4 j * fibStep 5 (4 - j)) = 5 := by
  rw [sum_tetra_mul_penta 4]
  decide
