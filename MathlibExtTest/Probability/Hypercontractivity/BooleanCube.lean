/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Hypercontractivity.BooleanCube

open BooleanCube StatMech.Probability

-- Both exponents exceed two and the noise is at the sharp threshold.
example {n : ℕ} (f : BoolCube n → ℝ) :
    bnt_qnorm 9 (boolNoiseOp (1 / 2) f) ≤ bnt_qnorm 3 f := by
  apply hypercontractivity_theorem (f := f) (by norm_num) (by norm_num) (by norm_num)
  apply Real.le_sqrt_of_sq_le
  norm_num

-- The endpoint convention in the statement makes zero noise admissible at p = q = 1.
example {n : ℕ} (f : BoolCube n → ℝ) :
    bnt_qnorm 1 (boolNoiseOp 0 f) ≤ bnt_qnorm 1 f := by
  apply hypercontractivity_theorem <;> norm_num
