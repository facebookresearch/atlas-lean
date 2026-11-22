/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Ideal.CotangentLength

@[expose] public section

set_option autoImplicit false

/-- Exact-source consumer, using the original binders verbatim. -/
example {𝒪 : Type*} {R : Type*} {T : Type*} [CommRing 𝒪] [IsDomain 𝒪]
    [IsPrincipalIdealRing 𝒪] [CommRing R] [Algebra 𝒪 R] [CommRing T] [Algebra 𝒪 T]
    (φ : R →ₐ[𝒪] T) (hφ : Function.Surjective φ) (πR : R →ₐ[𝒪] 𝒪) (πT : T →ₐ[𝒪] 𝒪)
    (hπ : πT.comp φ = πR) (hfg : (RingHom.ker πR).FG) :
    Module.length 𝒪 (𝒪 ⧸ (RingHom.ker πT).annihilator.map πT) ≤
      Module.length 𝒪 (RingHom.ker πR).Cotangent :=
  AlgHom.length_quotient_congruenceIdeal_le_length_cotangent φ hφ πR πT hπ hfg

/-- The same consumer in higher universes. -/
example {𝒪 : Type 1} {R : Type 2} {T : Type 3} [CommRing 𝒪] [IsDomain 𝒪]
    [IsPrincipalIdealRing 𝒪] [CommRing R] [Algebra 𝒪 R] [CommRing T] [Algebra 𝒪 T]
    (φ : R →ₐ[𝒪] T) (hφ : Function.Surjective φ) (πR : R →ₐ[𝒪] 𝒪) (πT : T →ₐ[𝒪] 𝒪)
    (hπ : πT.comp φ = πR) (hfg : (RingHom.ker πR).FG) :
    Module.length 𝒪 (𝒪 ⧸ (RingHom.ker πT).annihilator.map πT) ≤
      Module.length 𝒪 (RingHom.ker πR).Cotangent :=
  AlgHom.length_quotient_congruenceIdeal_le_length_cotangent φ hφ πR πT hπ hfg

/-- Boundary case: identity augmentations have zero cotangent length. -/
example : Module.length ℤ (ℤ ⧸ (RingHom.ker (AlgHom.id ℤ ℤ)).annihilator.map
      (AlgHom.id ℤ ℤ)) ≤
    Module.length ℤ (RingHom.ker (AlgHom.id ℤ ℤ)).Cotangent :=
  AlgHom.length_quotient_congruenceIdeal_le_length_cotangent (AlgHom.id ℤ ℤ)
    Function.surjective_id (AlgHom.id ℤ ℤ) (AlgHom.id ℤ ℤ) rfl
    (by exact ⟨∅, by ext x; simp [RingHom.mem_ker]⟩)
