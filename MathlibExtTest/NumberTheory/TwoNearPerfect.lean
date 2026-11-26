/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TwoNearPerfect
import Mathlib.Tactic.NormNum

namespace MathlibExtTest.NumberTheory.TwoNearPerfect

-- At `a = k = 1` the discriminant is `9 = 3 ^ 2`, so the theorem applies.
example : (1 : ℕ) = 1 ∧ (1 : ℕ) = 1 :=
  MetaMathlibExt.eq_one_of_isSquare_discriminant (a := 1) (k := 1)
    (ha := by decide) (hak := by decide) (hD := ⟨3, by norm_num⟩)

-- At `a = 1` and `k = 2` the discriminant cannot be a square.
example : ¬ IsSquare ((2 : ℤ) ^ (2 * 2 + 2) + 2 ^ (2 + 2) - 2 ^ (1 + 2) - 7) := by
  intro h
  have hka := MetaMathlibExt.eq_one_of_isSquare_discriminant (a := 1) (k := 2)
    (ha := by decide) (hak := by decide) (hD := h)
  norm_num at hka

end MathlibExtTest.NumberTheory.TwoNearPerfect
