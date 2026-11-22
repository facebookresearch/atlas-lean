/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import MathlibExt.NumberTheory.NumberField.DiscriminantIdeal
public import MathlibExt.RingTheory.DedekindDomain.DiscriminantTower

@[expose] public section

attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

namespace DiscriminantTowerTest

open Ideal NumberField

/-- The discriminant tower formula in the tower `ℤ ⊆ ℤ ⊆ 𝓞 ℚ`. -/
theorem discriminantIdeal_tower_int_rat :
    Ideal.discriminantIdeal ℤ (𝓞 ℚ) =
      (Ideal.discriminantIdeal ℤ ℤ) ^
          Module.finrank (FractionRing ℤ) (FractionRing (𝓞 ℚ)) *
        Ideal.spanNorm ℤ (Ideal.discriminantIdeal ℤ (𝓞 ℚ)) :=
  Ideal.discriminantIdeal_tower ℤ ℤ (𝓞 ℚ)

/-- The discriminant ideal of `ℤ / ℤ` has absolute norm `1`, since
`discr ℚ = 1`. -/
theorem absNorm_discriminantIdeal_rat :
    Ideal.absNorm (Ideal.discriminantIdeal ℤ (𝓞 ℚ)) = 1 := by
  rw [Ideal.absNorm_discriminantIdeal, Rat.numberField_discr]
  rfl

/-- Deriving the usual absolute-discriminant tower identity for number
fields from the ideal-theoretic tower formula. -/
theorem natAbs_discr_tower
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [Module.Finite (𝓞 K) (𝓞 L)]
    [Module.IsTorsionFree (𝓞 K) (𝓞 L)] :
    (NumberField.discr L).natAbs =
      Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) *
        (NumberField.discr K).natAbs ^ Module.finrank K L := by
  have h := Ideal.discriminantIdeal_tower ℤ (𝓞 K) (𝓞 L)
  have habs := congrArg Ideal.absNorm h
  rw [Ideal.absNorm_discriminantIdeal] at habs
  simp only [map_mul, map_pow, Ideal.discriminantIdeal_eq_spanNorm,
    Ideal.spanNorm_eq, Ideal.absNorm_relNorm] at habs
  have hfin : Module.finrank (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) =
      Module.finrank K L := by
    rw [IsFractionRing.finrank_eq (𝓞 K) (FractionRing (𝓞 K)) (𝓞 L)
      (FractionRing (𝓞 L)),
      IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L]
  rw [hfin, NumberField.absNorm_differentIdeal K (𝓞 K), mul_comm] at habs
  exact habs

#print axioms Ideal.discriminantIdeal_tower
#print axioms Ideal.absNorm_discriminantIdeal
#print axioms DiscriminantTowerTest.natAbs_discr_tower

end DiscriminantTowerTest
