/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Polynomial.ArithmeticProgressionRootPower
import Mathlib.Tactic.NormNum

/-!
# Boundary cases for the arithmetic-progression root identity
-/

open MetaMathlibExt Polynomial

-- For the root of X + 3, the difference a - d in the denominator is negative.
example (z : ℂ) (hz : z + 3 = 0) : z ^ 2 = (5 * z - 3) / (z + 1) := by
  have h := arithProgPoly_root_pow_eq 1 1 2 (by decide) z (Or.inl (by
    norm_num [Finset.sum_range_succ, map_ofNat]
    exact hz))
  norm_num at h
  exact h

-- When both m and a vanish the polynomial is zero, so every complex z is a root.
example (d : ℕ) (hd : 0 < d) (z : ℂ) : z = d * z / d := by
  simpa using arithProgPoly_root_pow_eq 0 0 d hd z (Or.inl (by simp))

-- The constant polynomial 1 admits z = 1 through the second disjunct.
example (d : ℕ) (hd : 0 < d) : (1 : ℂ) = (1 + d - 1) / (1 - (1 - d)) := by
  simpa using arithProgPoly_root_pow_eq 0 1 d hd 1 (Or.inr rfl)
