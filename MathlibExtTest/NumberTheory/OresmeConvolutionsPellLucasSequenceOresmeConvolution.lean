/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.OresmeConvolutionsPellLucasSequenceOresmeConvolution
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Tests for the Pell–Lucas–Oresme convolution

The closed form gives the convolution at indices zero, one, and four.
-/

namespace MathlibExtTest.NumberTheory.OresmeConvolutionsPellLucasSequenceOresmeConvolution

open MetaMathlibExt

example : ∑ k ∈ Finset.range 1,
    (pellLucasSequence k : ℚ) * (((0 - k : ℕ) : ℚ) / 2 ^ (0 - k)) = 0 := by
  rw [pellLucasSequence_oresme_convolution 0]
  norm_num

example : ∑ k ∈ Finset.range 2,
    (pellLucasSequence k : ℚ) * (((1 - k : ℕ) : ℚ) / 2 ^ (1 - k)) = 1 / 2 := by
  rw [pellLucasSequence_oresme_convolution 1]
  norm_num [pellLucasSequence_succ_succ]

example : ∑ k ∈ Finset.range 5,
    (pellLucasSequence k : ℚ) * (((4 - k : ℕ) : ℚ) / 2 ^ (4 - k)) = 45 / 8 := by
  rw [pellLucasSequence_oresme_convolution 4]
  norm_num [pellLucasSequence_succ_succ]

end MathlibExtTest.NumberTheory.OresmeConvolutionsPellLucasSequenceOresmeConvolution
