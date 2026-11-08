/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.Ideal.Norm.RelNorm

/-!
# Discriminant ideal of a Dedekind extension, and its tower formula

For a Dedekind extension `B / A`, the discriminant ideal `D_{B / A}` is the
norm of the different ideal `𝒟_{B / A}`. This file defines it and proves its
tower formula: for a tower `A ⊆ B ⊆ C` of Dedekind domains with separable
fraction fields,
`D_{C / A} = D_{B / A} ^ [Frac C : Frac B] * N_{B / A} (D_{C / B})`.

This is the second half of Proposition 12.28 of ATLAS `NumberTheoryI`;
the first half (transitivity of the different ideal) is Mathlib's
`differentIdeal_eq_differentIdeal_mul_differentIdeal`.

## Main definitions

* `Ideal.discriminantIdeal`: the discriminant ideal of a Dedekind extension.

## Main results

* `Ideal.discriminantIdeal_tower`: the discriminant tower formula.
-/

@[expose] public section

attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

namespace Ideal

/-- The discriminant ideal `D_{B / A}` of a Dedekind extension `B / A`,
defined as the norm of the different ideal. -/
noncomputable def discriminantIdeal (A B : Type*) [CommRing A]
    [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Module.Finite A B] [Module.IsTorsionFree A B] : Ideal A :=
  Ideal.spanNorm A (differentIdeal A B)

/-- The discriminant ideal is the norm of the different ideal, by definition. -/
theorem discriminantIdeal_eq_spanNorm (A B : Type*) [CommRing A]
    [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Module.Finite A B] [Module.IsTorsionFree A B] :
    discriminantIdeal A B = Ideal.spanNorm A (differentIdeal A B) :=
  rfl

/-- The discriminant tower formula: for a tower `A ⊆ B ⊆ C` of Dedekind
domains with separable fraction fields, the discriminant ideal of `C / A`
is the discriminant ideal of `B / A` raised to `[Frac C : Frac B]`, times
the norm of the discriminant ideal of `C / B`. -/
theorem discriminantIdeal_tower (A B C : Type*) [CommRing A]
    [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B] [CommRing C]
    [IsDedekindDomain C] [Algebra A B] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C] [Module.Finite A B] [Module.Finite A C]
    [Module.Finite B C] [Module.IsTorsionFree A B]
    [Module.IsTorsionFree A C] [Module.IsTorsionFree B C]
    [Algebra.IsSeparable (FractionRing A) (FractionRing C)] :
    discriminantIdeal A C =
      (discriminantIdeal A B) ^
          Module.finrank (FractionRing B) (FractionRing C) *
        Ideal.spanNorm A (discriminantIdeal B C) := by
  have hfin : Module.finrank (FractionRing B) (FractionRing C) =
      Module.finrank B C :=
    IsFractionRing.finrank_eq B (FractionRing B) C (FractionRing C)
  unfold discriminantIdeal
  rw [Ideal.spanNorm_eq A (differentIdeal A C),
    differentIdeal_eq_differentIdeal_mul_differentIdeal A B C,
    map_mul, mul_comm]
  congr 1
  · rw [← Ideal.relNorm_relNorm A B
      (Ideal.map (algebraMap B C) (differentIdeal A B)),
      Ideal.relNorm_algebraMap C (differentIdeal A B), hfin, map_pow,
      Ideal.spanNorm_eq]
  · rw [← Ideal.spanNorm_eq A (differentIdeal B C), Ideal.spanNorm_spanNorm]

end Ideal
