/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.DualNumberDeformation

@[expose] public section

open TrivSqZeroExt

-- Consumer with the original binders.
example {k : Type} [Field k] (W : WeierstrassCurve.Affine k) (hΔ : W.Δ ≠ 0)
    (x₀ y₀ : k) (h₀ : W.Equation x₀ y₀) :
    ∃ v : k × k, v ≠ 0 ∧
      ∀ x y : DualNumber k, x.fst = x₀ → y.fst = y₀ →
        ((W.map (algebraMap k (DualNumber k))).Equation x y ↔
          ∃ c : k, x.snd = c * v.1 ∧ y.snd = c * v.2) :=
  W.exists_ne_zero_forall_equation_dualNumber_iff hΔ x₀ y₀ h₀

-- The nonzero-discriminant hypothesis matters: over the singular curve
-- `y² = x³` (discriminant `0`), the cusp point `(0, 0)` satisfies the equation
-- but both gradient components vanish, so no such nonzero direction exists
-- with the stated one-dimensional description at that point via this theorem.
example : WeierstrassCurve.Affine.Equation (⟨0, 0, 0, 0, 0⟩ : WeierstrassCurve.Affine ℚ) 0 0 := by
  rw [WeierstrassCurve.Affine.equation_iff']
  norm_num
