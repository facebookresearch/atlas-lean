/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.LocalRingAtInfinity

/-!
# Tests for the local ring at the point at infinity of a Weierstrass cubic

Examples on the curve `y² + y = x³ - x` over `ℚ`.
-/

@[expose] public section

namespace WeierstrassCurve.LocalRingAtInfinityTest

open IsLocalRing

/-- The curve `y² + y = x³ - x` over `ℚ`. -/
noncomputable abbrev E : WeierstrassCurve ℚ := { a₁ := 0, a₂ := 0, a₃ := 1, a₄ := -1, a₆ := 0 }

example : IsDomain E.CoordinateRingAtInfinity := inferInstance

example : IsDiscreteValuationRing E.LocalRingAtInfinity := inferInstance

example : Irreducible (algebraMap _ E.LocalRingAtInfinity E.zAtInfinity) :=
  E.irreducible_zAtInfinity

example : maximalIdeal E.LocalRingAtInfinity =
    Ideal.span {algebraMap _ E.LocalRingAtInfinity E.zAtInfinity} :=
  E.maximalIdeal_localRingAtInfinity

example : E.maximalIdealAtInfinity = Ideal.span {E.zAtInfinity, E.wAtInfinity} :=
  E.maximalIdealAtInfinity_eq_span

example : IsDiscreteValuationRing.addVal E.LocalRingAtInfinity
    (algebraMap _ _ E.wAtInfinity) = 3 :=
  E.addVal_wAtInfinity

/-- For this curve `u = 1 + w + z w`, so `w (1 + w + z w) = z³` in `B_E`. -/
example : E.wAtInfinity * (1 + E.wAtInfinity + E.zAtInfinity * E.wAtInfinity) =
    E.zAtInfinity ^ 3 := by
  have h := E.wAtInfinity_mul_unitAtInfinity
  simp only [unitAtInfinity, map_zero, map_one, map_neg, zero_mul, add_zero, sub_zero,
    one_mul] at h
  linear_combination h

example : IsFractionRing E.CoordinateRingAtInfinity E.toAffine.FunctionField := inferInstance

example : IsFractionRing E.LocalRingAtInfinity E.toAffine.FunctionField := inferInstance

example : E.valuationAtInfinity (algebraMap _ E.toAffine.FunctionField E.affineX) =
    WithZero.exp 2 :=
  E.valuationAtInfinity_affineX

example : E.valuationAtInfinity (algebraMap _ E.toAffine.FunctionField E.affineY) =
    WithZero.exp 3 :=
  E.valuationAtInfinity_affineY

/-- `x` is not regular at infinity on `E`. -/
example : algebraMap _ E.toAffine.FunctionField E.affineX ∉
    Set.range (algebraMap E.LocalRingAtInfinity E.toAffine.FunctionField) := by
  rintro ⟨o, ho⟩
  have h := IsDedekindDomain.HeightOneSpectrum.valuation_le_one
    (K := E.toAffine.FunctionField) E.placeAtInfinity o
  change E.valuationAtInfinity (algebraMap _ _ o) ≤ 1 at h
  rw [ho, E.valuationAtInfinity_affineX, ← WithZero.exp_zero,
    WithZero.exp_le_exp] at h
  norm_num at h

/-- A function on the affine chart of `E` that is regular at infinity is constant. -/
example (f : E.toAffine.CoordinateRing)
    (hf : algebraMap _ E.toAffine.FunctionField f ∈
      Set.range (algebraMap E.LocalRingAtInfinity E.toAffine.FunctionField)) :
    ∃ c : ℚ, f = algebraMap ℚ _ c :=
  E.exists_eq_algebraMap_of_mem_range f hf

end WeierstrassCurve.LocalRingAtInfinityTest
