/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.DedekindDomain.LengthQuotientRamificationInertia

@[expose] public section

open IsLocalRing

namespace MathlibExtTest.RingTheory.DedekindDomain.LengthQuotientRamificationInertia

/-- Consumer with the original binders. -/
theorem exactSource
    {C : Type*} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    (K : Type*) [Field K] [Algebra C K] [IsFractionRing C K]
    {D : Type*} [CommRing D] [IsDomain D] [IsLocalRing D] [IsNoetherianRing D]
    [Algebra C D]
    (hDmax : ∀ c : C, algebraMap C D c ∈ maximalIdeal D ↔ c ∈ maximalIdeal C)
    (hDres : ∀ d : D, ∃ c : C, d - algebraMap C D c ∈ maximalIdeal D)
    (hDdim : Ring.DimensionLEOne D) (hDnf : maximalIdeal D ≠ ⊥)
    (κ : Type*) [Field κ] [Algebra D κ] [IsFractionRing D κ] [Algebra C κ]
    [IsScalarTower C D κ] [Algebra K κ] [IsScalarTower C K κ]
    [FiniteDimensional K κ] [Algebra.IsSeparable K κ] :
    {B : ValuationSubring κ | ∀ d : D, algebraMap D κ d ∈ B}.Finite ∧
    Module.length D (D ⧸ (maximalIdeal C).map (algebraMap C D)) =
      ∑ᶠ B : {B : ValuationSubring κ // (∀ c : C, algebraMap C κ c ∈ B) ∧
          (∀ d : D, algebraMap D κ d ∈ B) ∧
          ∀ c : C, algebraMap C κ c ∈ B.nonunits ↔ c ∈ maximalIdeal C},
        ((letI : Algebra C ↥B.1 := ((algebraMap C κ).codRestrict B.1 B.2.1).toAlgebra
          (maximalIdeal C).ramificationIdx' (maximalIdeal ↥B.1) *
            (maximalIdeal C).inertiaDeg' (maximalIdeal ↥B.1) : ℕ) : ℕ∞) :=
  IsLocalRing.length_quotient_map_maximalIdeal_eq_finsum_ramificationIdx_mul_inertiaDeg
    K hDmax hDres hDdim κ

/-- Higher-universe consumer: the rings may live in a higher universe. -/
theorem exactSource_universe.{u, v, w}
    {C : Type u} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    (K : Type v) [Field K] [Algebra C K] [IsFractionRing C K]
    {D : Type w} [CommRing D] [IsDomain D] [IsLocalRing D] [IsNoetherianRing D]
    [Algebra C D]
    (hDmax : ∀ c : C, algebraMap C D c ∈ maximalIdeal D ↔ c ∈ maximalIdeal C)
    (hDres : ∀ d : D, ∃ c : C, d - algebraMap C D c ∈ maximalIdeal D)
    (hDdim : Ring.DimensionLEOne D) (hDnf : maximalIdeal D ≠ ⊥)
    (κ : Type w) [Field κ] [Algebra D κ] [IsFractionRing D κ] [Algebra C κ]
    [IsScalarTower C D κ] [Algebra K κ] [IsScalarTower C K κ]
    [FiniteDimensional K κ] [Algebra.IsSeparable K κ] :
    {B : ValuationSubring κ | ∀ d : D, algebraMap D κ d ∈ B}.Finite ∧
    Module.length D (D ⧸ (maximalIdeal C).map (algebraMap C D)) =
      ∑ᶠ B : {B : ValuationSubring κ // (∀ c : C, algebraMap C κ c ∈ B) ∧
          (∀ d : D, algebraMap D κ d ∈ B) ∧
          ∀ c : C, algebraMap C κ c ∈ B.nonunits ↔ c ∈ maximalIdeal C},
        ((letI : Algebra C ↥B.1 := ((algebraMap C κ).codRestrict B.1 B.2.1).toAlgebra
          (maximalIdeal C).ramificationIdx' (maximalIdeal ↥B.1) *
            (maximalIdeal C).inertiaDeg' (maximalIdeal ↥B.1) : ℕ) : ℕ∞) :=
  IsLocalRing.length_quotient_map_maximalIdeal_eq_finsum_ramificationIdx_mul_inertiaDeg
    K hDmax hDres hDdim κ

/-- Boundary check: a field has bottom maximal ideal. In the theorem this
case cannot arise from the remaining hypotheses, since the image of a
uniformizer of `C` is a nonzero element of the maximal ideal of `D`. -/
example {D : Type*} [Field D] [IsLocalRing D] : maximalIdeal D = ⊥ :=
  IsLocalRing.maximalIdeal_eq_bot

end MathlibExtTest.RingTheory.DedekindDomain.LengthQuotientRamificationInertia
