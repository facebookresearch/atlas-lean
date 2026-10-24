/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.AbsoluteValue.Nonarchimedean
public import MathlibExt.Analysis.AbsoluteValue.FiniteField

import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

open AbsoluteValue

variable {K : Type*} [Field K]

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The iff applies to an arbitrary absolute value. -/
public theorem test_iff (v : AbsoluteValue K ℝ) :
    IsNonarchimedean v ↔ ∀ n : ℕ, v (n : K) ≤ 1 :=
  v.isNonarchimedean_iff_natCast_le_one

/-- The positive-`n` form of the iff applies to an arbitrary absolute value. -/
public theorem test_iff_of_pos (v : AbsoluteValue K ℝ) :
    IsNonarchimedean v ↔ ∀ n : ℕ, 0 < n → v (n : K) ≤ 1 :=
  v.isNonarchimedean_iff_natCast_le_one_of_pos

/-- The usual absolute value on `ℝ` is not nonarchimedean, witnessed by
`v 2 = 2 > 1`. -/
public theorem test_abs_not_nonarchimedean :
    ¬ IsNonarchimedean (AbsoluteValue.abs : AbsoluteValue ℝ ℝ) := by
  rw [AbsoluteValue.isNonarchimedean_iff_natCast_le_one]
  push Not
  exact ⟨2, by simp [AbsoluteValue.abs_apply]⟩

/-- The binomial-expansion bound at `n = 0` is `v (x + y) ^ 0 ≤ 1`. -/
public theorem test_add_pow_zero (v : AbsoluteValue K ℝ)
    (hv : ∀ n : ℕ, v (n : K) ≤ 1) (x y : K) :
    v (x + y) ^ 0 ≤ (↑(0 : ℕ) + 1) * (max (v x) (v y)) ^ 0 :=
  v.add_pow_le_mul_max_pow_of_natCast_le_one hv x y 0

/-- On `ZMod 5`, every absolute value is nonarchimedean via the
`n = 0` and positive-`n` forms agreeing: the forward direction of the iff
recovers the nat-cast bound from positive characteristic. -/
public theorem test_zmod5_natCast_le_one (v : AbsoluteValue (ZMod 5) ℝ)
    (n : ℕ) : v (n : ZMod 5) ≤ 1 :=
  (v.isNonarchimedean_iff_natCast_le_one.mp
    (AbsoluteValue.isNonarchimedean_of_charP (K := ZMod 5) (p := 5) v)) n

end
