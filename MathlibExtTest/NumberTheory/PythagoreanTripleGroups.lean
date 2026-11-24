/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PythagoreanTripleGroups

/-! # Tests for Amato's product of rational Pythagorean triples -/

open MetaMathlibExt

-- The second coordinate can vanish when multiplying signed rational triples.
example :
    pythagoreanTripleMul ((-3 / 5, 4 / 5, -1) : ℚ × ℚ × ℚ) (3, 4, 5) =
      (-9 / 5, 0, -9 / 5) := by
  norm_num [pythagoreanTripleMul]

example :
    pythagoreanTripleMul (-3 / 5, 4 / 5, -1) (3, 4, 5) ∈ ratPythagoreanTriples := by
  refine pythagoreanTripleMul_mem_ratPythagoreanTriples _ _ ?_
    three_four_five_mem_ratPythagoreanTriples
  exact ⟨by norm_num, by norm_num⟩

-- The first coordinate must be nonzero even when the Pythagorean equation holds.
example : ((0, -1, 1) : ℚ × ℚ × ℚ) ∉ ratPythagoreanTriples := by
  intro h
  exact h.1 rfl
