/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.GDifferenceBasisScaling

/-! # Tests for scaling interval difference bases -/

open MetaMathlibExt

-- At the endpoint n = 2² · 1, scale a basis with two representations of 1.
example : diffBasisNumber 2 4 ≤ 9 := by
  have h : diffBasisNumber 2 1 ≤ 3 := by
    apply Nat.sInf_le
    refine ⟨{0, 1, 2}, by decide, fun x hx => ?_⟩
    have hx' : x = 1 := by simpa using hx
    subst x
    decide
  exact (diffBasisNumber_le_succ_mul 2 2 4 1 (by decide) (by decide)).trans
    (Nat.mul_le_mul_left 3 h)

-- When v = 0 the empty basis witnesses the value on both sides, even for positive g.
example (g : ℕ) : diffBasisNumber g 0 = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply Nat.sInf_le
  exact ⟨∅, rfl, by simp⟩
