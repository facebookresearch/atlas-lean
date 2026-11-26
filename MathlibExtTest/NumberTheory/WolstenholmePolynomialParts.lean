/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.WolstenholmePolynomialParts
import Mathlib.Tactic.NormNum

/-! # Tests for divisibility of Wolstenholme's polynomial parts -/

open MetaMathlibExt Polynomial

-- At n = 0 the roots coincide. For m = 2 the first polynomial takes value 1 at k = 1.
example : ∃ Q : ℚ[X], 1 = (-1 / 2 : ℚ) * Q.eval 1 := by
  obtain ⟨Q, hQ⟩ := (exists_polynomial_part_eq_mul_half_mul 2 0).1
  refine ⟨Q, ?_⟩
  convert hQ 1 using 1
  · decide +kernel
  · norm_num

-- The second formula uses the binomial coefficient of order zero when j > m.
example : ∃ Q : ℚ[X], -2 = -(Q.eval 1) := by
  obtain ⟨Q, hQ⟩ := (exists_polynomial_part_eq_mul_half_mul 0 (-1)).2 2 1 (by decide) (by decide)
  refine ⟨Q, ?_⟩
  have h : -2 = (-1 : ℚ) * Q.eval 1 := by
    convert hQ 1 using 1 <;>
      norm_num [Finset.prod_range_succ, Ring.choose_zero_right, Nat.factorial]
  simpa only [neg_one_mul] using h
