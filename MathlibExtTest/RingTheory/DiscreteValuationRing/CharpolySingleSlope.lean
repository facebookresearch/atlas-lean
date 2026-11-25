/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.DiscreteValuationRing.CharpolySingleSlope

@[expose] public section

open IsLocalRing Polynomial

universe u

-- Exact-source consumer, with the original binders.
private theorem exactSource
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (O : Type u) [CommRing O] [IsDomain O] [Algebra W O] [Module.Free W O]
    [Module.Finite W O] (a : O) :
    (LinearMap.mulLeft W a).charpoly.Monic ∧
    (LinearMap.mulLeft W a).charpoly.natDegree = Module.finrank W O ∧
    (∀ i : ℕ, i ≤ Module.finrank W O →
      ((Module.finrank W O - i : ℕ) : ℕ∞) *
        IsDiscreteValuationRing.addVal W (Algebra.norm W a) ≤
        (Module.finrank W O : ℕ∞) * IsDiscreteValuationRing.addVal W
          ((LinearMap.mulLeft W a).charpoly.coeff i)) ∧
    ((Module.finrank W O : ℕ∞) * IsDiscreteValuationRing.addVal W (Algebra.norm W a) =
      (Module.finrank W O : ℕ∞) * IsDiscreteValuationRing.addVal W
        ((LinearMap.mulLeft W a).charpoly.coeff 0)) :=
  IsDiscreteValuationRing.charpoly_mulLeft_single_slope_of_isAdicComplete O a

-- Boundary: for `a = 0` in a rank-one free algebra, the characteristic
-- polynomial is `X`, so the constant coefficient has infinite valuation
-- while the norm is `0`.
example {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W] :
    (LinearMap.mulLeft W (0 : W)).charpoly = Polynomial.X := by
  have h : LinearMap.mulLeft W (0 : W) = 0 := by
    ext x
    simp [LinearMap.mulLeft]
  rw [h]
  simp
