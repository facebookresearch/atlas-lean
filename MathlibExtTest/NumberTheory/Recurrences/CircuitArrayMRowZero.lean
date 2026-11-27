/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.CircuitArrayMRowZero
import Mathlib.Tactic.NormNum

/-!
# Tests for row zero of the multivariable circuit array
-/

open MetaMathlibExt

-- The first column is the boundary value itself.
example : circuitArrayM 0 1 = circuitVar 1 := by
  rw [circuitArrayM_row_zero 1 le_rfl]
  norm_num

-- Two further reductions give the same variable with denominator `81`.
example : circuitArrayM 0 3 = (80 + circuitVar 1) / 81 := by
  rw [circuitArrayM_row_zero 3 (by decide)]
  norm_num
