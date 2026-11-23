/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.TrinomialUpperHalf
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open MetaMathlibExt

-- Row zero includes the central term even at weight zero.
example : ∑ k ∈ Finset.range (0 + 1),
    (trinomialCoefficient 0 (0 - k) : ℂ) * (0 : ℂ) ^ (0 + k) = 1 := by
  rw [sum_trinomialCoefficient_upper_half]
  norm_num [trinomialCoefficient_zero_zero]

-- Row one has a single term in the correction sum.
example (w : ℂ) : ∑ k ∈ Finset.range (1 + 1),
    (trinomialCoefficient 1 (1 - k) : ℂ) * w ^ (1 + k) = w + w ^ 2 := by
  rw [sum_trinomialCoefficient_upper_half]
  simp [trinomialCoefficient_zero_zero, trinomialCoefficient_one_one]
  ring

-- At weight one the correction vanishes in every row.
example (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (trinomialCoefficient n (n - k) : ℂ) =
      (3 : ℂ) ^ n / 2 + (trinomialCoefficient n n : ℂ) / 2 := by
  have h := sum_trinomialCoefficient_upper_half n 1
  norm_num at h
  exact h
