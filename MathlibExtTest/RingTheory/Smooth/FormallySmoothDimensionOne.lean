/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Smooth.FormallySmoothDimensionOne

@[expose] public section

universe u v

open IsLocalRing in
/-- Source-shaped consumer with the original binders. -/
private theorem exactSource {k : Type*} [Field k] {R : Type*} [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.FormallySmooth k R] [Algebra.FinitePresentation k R]
    (hdim : Ring.KrullDimLE 1 R) (𝔫 : Ideal R) [𝔫.IsMaximal] (hne : 𝔫 ≠ ⊥)
    (hrat : Function.Surjective ((Ideal.Quotient.mk 𝔫).comp (algebraMap k R))) :
    ∃ _ : IsDomain (Localization.AtPrime 𝔫),
      IsDiscreteValuationRing (Localization.AtPrime 𝔫) :=
  Algebra.FormallySmooth.isDiscreteValuationRing_localizationAtPrime_of_krullDimLE_one
    hdim 𝔫 hne hrat

/-- Higher-universe consumer. -/
example {k : Type (u+1)} [Field k] {R : Type (v+1)} [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.FormallySmooth k R] [Algebra.FinitePresentation k R]
    (hdim : Ring.KrullDimLE 1 R) (𝔫 : Ideal R) [𝔫.IsMaximal] (hne : 𝔫 ≠ ⊥)
    (hrat : Function.Surjective ((Ideal.Quotient.mk 𝔫).comp (algebraMap k R))) :
    ∃ _ : IsDomain (Localization.AtPrime 𝔫),
      IsDiscreteValuationRing (Localization.AtPrime 𝔫) :=
  Algebra.FormallySmooth.isDiscreteValuationRing_localizationAtPrime_of_krullDimLE_one
    hdim 𝔫 hne hrat
