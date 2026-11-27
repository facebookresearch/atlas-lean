/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.RealizeEqDiv

@[expose] public section

open UpperHalfPlane

-- Consumer with the original binders.
example (N : ℕ) {k : ℤ}
    (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k) (x : LaurentSeries ℂ)
    (hx : x * ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
      ((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ))
    (τ : ℍ) (hτ : (h : ℍ → ℂ) τ ≠ 0) :
    ModularCurve.realize N x τ = (g : ℍ → ℂ) τ / (h : ℍ → ℂ) τ :=
  ModularCurve.realize_eq_div N g h x hx τ hτ

-- Boundary: without a representing pair the realization is `0` by definition.
-- The nonvanishing hypothesis cannot be dropped: division is totalized, so
-- `g τ / h τ = 0` whenever `h τ = 0`, while `realize N x τ` need not be `0`,
-- since another representation may have a nonvanishing denominator at `τ`.
example (N : ℕ) (x : LaurentSeries ℂ) (τ : ℍ)
    (hnex : ¬ ∃ p : (k : ℤ) × (ModularForm (CongruenceSubgroup.Gamma0 N) k ×
          ModularForm (CongruenceSubgroup.Gamma0 N) k),
        (p.2.2 : ℍ → ℂ) τ ≠ 0 ∧
          x * ((qExpansion 1 (p.2.2 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
            ((qExpansion 1 (p.2.1 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) :
    ModularCurve.realize N x τ = 0 := by
  classical
  simp only [ModularCurve.realize, dite_eq_right hnex]
