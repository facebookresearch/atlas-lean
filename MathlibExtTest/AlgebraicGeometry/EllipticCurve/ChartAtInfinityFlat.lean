/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.ChartAtInfinityFlat
public import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Tests for the freeness and finite presentation of the chart at infinity

Examples on the curve `y² + y = x³ - x` over `ℤ` and over the `5`-adic integers.
-/

@[expose] public section

namespace WeierstrassCurve.ChartAtInfinityFlatTest

open scoped TensorProduct

/-- The curve `y² + y = x³ - x` over `ℤ`. -/
abbrev E : WeierstrassCurve ℤ := { a₁ := 0, a₂ := 0, a₃ := 1, a₄ := -1, a₆ := 0 }

instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- The same curve over the discrete valuation ring `ℤ_[5]`. -/
noncomputable abbrev E₅ : WeierstrassCurve ℤ_[5] := E.baseChange ℤ_[5]

example : Module.Free ℤ E.CoordinateRingAtInfinity := inferInstance

example : Module.Flat ℤ E.CoordinateRingAtInfinity := E.flat_coordinateRingAtInfinity

example : Algebra.FinitePresentation ℤ E.CoordinateRingAtInfinity := inferInstance

/-- The page's setting: a Weierstrass cubic over a discrete valuation ring. -/
example : IsDiscreteValuationRing ℤ_[5] := inferInstance

example : Module.Flat ℤ_[5] E₅.CoordinateRingAtInfinity := inferInstance

example : Algebra.FinitePresentation ℤ_[5] E₅.CoordinateRingAtInfinity := inferInstance

/-- Both charts of the projective cubic over `ℤ_[5]` are flat and finitely presented; the chart
`Z ≠ 0` by Mathlib. -/
example : Module.Flat ℤ_[5] E₅.toAffine.CoordinateRing ∧
    Algebra.FinitePresentation ℤ_[5] E₅.toAffine.CoordinateRing := ⟨inferInstance, inferInstance⟩

/-- The fibre of the chart at infinity over `ZMod 5`. -/
noncomputable example :
    ZMod 5 ⊗[ℤ] E.CoordinateRingAtInfinity ≃ₐ[ZMod 5]
      (E.baseChange (ZMod 5)).CoordinateRingAtInfinity :=
  E.tensorCoordinateRingAtInfinityEquiv (ZMod 5)

example : E.monicPolynomialAtInfinity.Monic := E.monic_monicPolynomialAtInfinity

#check @WeierstrassCurve.monicPolynomialAtInfinity
#check @WeierstrassCurve.finSuccEquiv_polynomialAtInfinity
#check @WeierstrassCurve.monic_monicPolynomialAtInfinity
#check @WeierstrassCurve.coordinateRingAtInfinityEquivAdjoinRoot
#check @WeierstrassCurve.instFreeCoordinateRingAtInfinity
#check @WeierstrassCurve.flat_coordinateRingAtInfinity
#check @WeierstrassCurve.instFinitePresentationCoordinateRingAtInfinity
#check @WeierstrassCurve.baseChange_polynomialAtInfinity
#check @WeierstrassCurve.tensorCoordinateRingAtInfinityEquiv
#check @WeierstrassCurve.tensorCoordinateRingAtInfinityEquiv_tmul_zAtInfinity
#check @WeierstrassCurve.tensorCoordinateRingAtInfinityEquiv_tmul_wAtInfinity

end WeierstrassCurve.ChartAtInfinityFlatTest
