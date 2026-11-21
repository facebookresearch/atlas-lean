/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.TateCurve

@[expose] public section

open TateCurve

/-- Consumer exercising the coefficient formulas with the original binders. -/
theorem exactSource_coeff (n : ℕ) :
    PowerSeries.coeff n tateA4 = -∑ d ∈ n.divisors, (5 * (d : ℤ) ^ 3) ∧
      PowerSeries.coeff n tateA6 = -∑ d ∈ n.divisors, tateB d :=
  ⟨coeff_tateA4 n, coeff_tateA6 n⟩

/-- The Tate curve over `ℤ⟦q⟧` has the stated Weierstrass coefficients. -/
example : tatePowerSeries.a₁ = 1 ∧ tatePowerSeries.a₄ = tateA4 ∧
    tatePowerSeries.a₆ = tateA6 :=
  ⟨rfl, rfl, rfl⟩

/-- The Tate curve becomes elliptic after mapping to Laurent series. -/
example (K : Type*) [CommRing K] : (tateLaurent K).IsElliptic :=
  inferInstance

/-- Boundary coefficients of the origin coordinate series. -/
example (K : Type*) [CommRing K] :
    (tateOriginX K).coeff (-2) = 1 ∧ (tateOriginY K).coeff (-3) = -1 :=
  ⟨coeff_tateOriginX_neg_two K, coeff_tateOriginY_neg_three K⟩

example : PowerSeries.coeff 1 tateA4 = -5 ∧ PowerSeries.coeff 1 tateA6 = -1 :=
  ⟨coeff_one_tateA4, coeff_one_tateA6⟩
