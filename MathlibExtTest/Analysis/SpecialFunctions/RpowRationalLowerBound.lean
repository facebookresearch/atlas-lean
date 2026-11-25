/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.RpowRationalLowerBound
import Mathlib.Tactic.NormNum

/-!
# Boundary cases for the rational lower bound
-/

open MetaMathlibExt

-- At the least admissible degree the bound specializes to one for the square root.
example {x : ℝ} (hx : 0 < x) : (2 + 3 * x) / (2 + x) < √(1 + 2 * x) := by
  have h := one_add_mul_rpow_inv_gt (m := 2) (by decide) hx
  norm_num [Real.sqrt_eq_rpow] at h ⊢
  exact h

-- At zero the two sides agree for every degree.
example (m : ℕ) :
    (2 + ((m : ℝ) + 1) * 0) / (2 + (m - 1) * 0) = (1 + m * (0 : ℝ)) ^ (1 / (m : ℝ)) := by
  norm_num

-- At degree one the two sides agree for every argument.
example (x : ℝ) :
    (2 + ((1 : ℝ) + 1) * x) / (2 + (1 - 1) * x) = (1 + 1 * x) ^ (1 / (1 : ℝ)) := by
  norm_num
  ring
