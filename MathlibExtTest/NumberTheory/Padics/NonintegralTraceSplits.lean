/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Padics.NonintegralTraceSplits

/-!
# Tests for the splitting of $x^2 - sx + 1$ for a nonintegral $p$-adic trace
-/

set_option autoImplicit false

@[expose] public section

namespace NonintegralTraceSplitsTest

open Polynomial

/-- For $s = 1/3 \in \mathbb{Q}_3$, the polynomial $x^2 - x/3 + 1$ has two distinct roots in
$\mathbb{Q}_3$, of norms $3$ and $1/3$. -/
example : ∃ r₁ r₂ : ℚ_[3], (X ^ 2 - C (3⁻¹ : ℚ_[3]) * X + 1 : ℚ_[3][X]) = (X - C r₁) * (X - C r₂) ∧
    r₁ ≠ r₂ ∧ ‖r₁‖ = 3 ∧ ‖r₂‖ = 3⁻¹ := by
  have h : ‖(3⁻¹ : ℚ_[3])‖ = 3 := by
    have := Padic.norm_p (p := 3)
    push_cast at this
    rw [norm_inv, this, inv_inv]
  obtain ⟨r₁, r₂, hf, hne, h₁, h₂⟩ := Padic.exists_eq_mul_X_sub_C_of_one_lt_norm (by
    rw [h]; norm_num)
  exact ⟨r₁, r₂, hf, hne, h₁.trans h, h₂.trans (by rw [h])⟩

end NonintegralTraceSplitsTest
