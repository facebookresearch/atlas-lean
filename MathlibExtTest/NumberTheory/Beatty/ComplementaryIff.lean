/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Beatty.ComplementaryIff
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Tests for Beatty's theorem and its converse -/

namespace MathlibExtTest.NumberTheory.Beatty.ComplementaryIff

open MetaMathlibExt Set

-- The slopes `√2` and `2 + √2` give a partition of the positive integers.
example : Disjoint {beattySeq (Real.sqrt 2) k | k > 0} {beattySeq (2 + Real.sqrt 2) k | k > 0} ∧
    {beattySeq (Real.sqrt 2) k | k > 0} ∪ {beattySeq (2 + Real.sqrt 2) k | k > 0} =
      {n : ℤ | 0 < n} := by
  have h : 0 < Real.sqrt 2 := by positivity
  refine (beatty_complementary_iff_irrational_inv_add_inv h (by positivity)).2
    ⟨irrational_sqrt_two, ?_⟩
  field_simp
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

-- The rational slopes `2, 2` have reciprocal sum one, but cannot give a partition.
example : ¬ (Disjoint {beattySeq (2 : ℝ) k | k > 0} {beattySeq (2 : ℝ) k | k > 0} ∧
    {beattySeq (2 : ℝ) k | k > 0} ∪ {beattySeq (2 : ℝ) k | k > 0} = {n : ℤ | 0 < n}) := by
  intro h
  have hirr := ((beatty_complementary_iff_irrational_inv_add_inv
    (α := 2) (β := 2) (by norm_num) (by norm_num)).1 h).1
  exact hirr ⟨(2 : ℚ), by norm_num⟩

end MathlibExtTest.NumberTheory.Beatty.ComplementaryIff
