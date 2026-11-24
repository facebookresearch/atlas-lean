/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Valuation.GaloisConjugacy

@[expose] public section

set_option autoImplicit false

open IsLocalRing

/-- Exact-source consumer, using the original binders verbatim. -/
example {E K : Type*} [Field E] [Field K] [Algebra E K] [FiniteDimensional E K]
    [IsGalois E K] (V : ValuationSubring E) [IsDiscreteValuationRing ↥V]
    (B B' : ValuationSubring K)
    (hB : ∀ x : E, algebraMap E K x ∈ B ↔ x ∈ V)
    (hB' : ∀ x : E, algebraMap E K x ∈ B' ↔ x ∈ V) :
    ∃ σ : K ≃ₐ[E] K, B' = B.comap σ.toAlgHom.toRingHom :=
  ValuationSubring.exists_algEquiv_comap_eq_of_isGalois V B B' hB hB'

/-- The same consumer in a higher universe. -/
example {E K : Type 1} [Field E] [Field K] [Algebra E K] [FiniteDimensional E K]
    [IsGalois E K] (V : ValuationSubring E) [IsDiscreteValuationRing ↥V]
    (B B' : ValuationSubring K)
    (hB : ∀ x : E, algebraMap E K x ∈ B ↔ x ∈ V)
    (hB' : ∀ x : E, algebraMap E K x ∈ B' ↔ x ∈ V) :
    ∃ σ : K ≃ₐ[E] K, B' = B.comap σ.toAlgHom.toRingHom :=
  ValuationSubring.exists_algEquiv_comap_eq_of_isGalois V B B' hB hB'

/-- Boundary case: when the two valuation subrings already agree, the
identity automorphism is a conjugator. -/
example {E K : Type*} [Field E] [Field K] [Algebra E K] [FiniteDimensional E K]
    [IsGalois E K] (V : ValuationSubring E) [IsDiscreteValuationRing ↥V]
    (B : ValuationSubring K)
    (hB : ∀ x : E, algebraMap E K x ∈ B ↔ x ∈ V) :
    ∃ σ : K ≃ₐ[E] K, B = B.comap σ.toAlgHom.toRingHom :=
  ValuationSubring.exists_algEquiv_comap_eq_of_isGalois V B B hB hB
