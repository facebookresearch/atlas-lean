/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.MahlerPopkenComplexity

namespace MathlibExt.NumberTheory.MahlerPopkenComplexityWanted

-- With positive leaves there is no expression for zero.
example : mahlerPopkenComplexity 2 0 = 0 := by
  have he (e : MahlerPopkenExpr 2) : e.eval ≠ 0 := e.eval_pos.ne'
  simp [mahlerPopkenComplexity, he]

-- One has neither a nontrivial divisor nor a split into positive summands.
example (m : ℕ) : mahlerPopkenRecursionValue m 1 = 0 := by
  simp [mahlerPopkenRecursionValue]

-- At the lower endpoint, a single leaf realizes the minimum.
example : mahlerPopkenComplexity 2 1 = 1 := by
  exact le_antisymm (mahlerPopkenComplexity_min_le (.leaf 0) rfl)
    (mahlerPopkenComplexity_pos (by decide) (by decide))

-- The logarithmic bound is sharp at eight, represented by (2 + 2) * 2.
example : mahlerPopkenComplexity 2 8 = 3 := by
  let two : MahlerPopkenExpr 2 := .leaf 1
  apply le_antisymm (mahlerPopkenComplexity_min_le (.mul (.add two two) two) rfl)
  have h := logb_two_le_mahlerPopkenComplexity_two 8 (by decide)
  rw [show ((8 : ℕ) : ℝ) = 2 ^ 3 by norm_num, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num), mul_one] at h
  exact_mod_cast h

end MathlibExt.NumberTheory.MahlerPopkenComplexityWanted
