/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.JCoefficientBound

@[expose] public section

open ModularCurve

/-- Source consumer with the original binders. -/
private theorem exactSource (n : ℕ) : (1 : ℚ) ≤ jq.coeff (n : ℤ) :=
  ModularCurve.one_le_coeff_jq n

/-- The bound at the first nonnegative indices, and nonvanishing there. -/
example : (1 : ℚ) ≤ jq.coeff (0 : ℤ) ∧ jq.coeff (0 : ℤ) ≠ 0 :=
  ⟨ModularCurve.one_le_coeff_jq 0, ModularCurve.coeff_jq_ne_zero 0⟩

/-- Below the pole the coefficients vanish, so the nonnegative-index
hypothesis matters: at `-2` the coefficient is `0`, not at least `1`. -/
example : jq.coeff (-2 : ℤ) = 0 :=
  ModularCurve.coeff_jq_of_lt (by norm_num)
