/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.LocalRing.NumericalCriterion

/-- The original statement, with its original binders, follows from the
public theorem. -/
example {𝒪 : Type*} {R : Type*} {T : Type*} [CommRing 𝒪]
    [CommRing R] [Algebra 𝒪 R] [CommRing T] [Algebra 𝒪 T]
    (φ : R →ₐ[𝒪] T) (hφ : Function.Surjective φ) (πR : R →ₐ[𝒪] 𝒪) (πT : T →ₐ[𝒪] 𝒪)
    (hπ : πT.comp φ = πR) :
    Module.length 𝒪 (RingHom.ker πT).Cotangent ≤
        Module.length 𝒪 (RingHom.ker πR).Cotangent ∧
      (RingHom.ker πR).annihilator.map πR ≤ (RingHom.ker πT).annihilator.map πT :=
  AlgHom.length_cotangent_le_and_congruenceIdeal_le_of_surjective φ hφ πR πT hπ

/-- Higher-universe consumer in `Type 1`. -/
example {𝒪 : Type 1} {R : Type 1} {T : Type 1} [CommRing 𝒪]
    [CommRing R] [Algebra 𝒪 R] [CommRing T] [Algebra 𝒪 T]
    (φ : R →ₐ[𝒪] T) (hφ : Function.Surjective φ) (πR : R →ₐ[𝒪] 𝒪) (πT : T →ₐ[𝒪] 𝒪)
    (hπ : πT.comp φ = πR) :
    Module.length 𝒪 (RingHom.ker πT).Cotangent ≤
        Module.length 𝒪 (RingHom.ker πR).Cotangent ∧
      (RingHom.ker πR).annihilator.map πR ≤ (RingHom.ker πT).annihilator.map πT :=
  AlgHom.length_cotangent_le_and_congruenceIdeal_le_of_surjective φ hφ πR πT hπ

/-- With `φ` the identity, both conclusions are equalities/inclusions
that hold trivially; this pins the direction of the statements. -/
example {𝒪 : Type*} {R : Type*} [CommRing 𝒪] [CommRing R] [Algebra 𝒪 R]
    (πR : R →ₐ[𝒪] 𝒪) :
    Module.length 𝒪 (RingHom.ker πR).Cotangent ≤
        Module.length 𝒪 (RingHom.ker πR).Cotangent ∧
      (RingHom.ker πR).annihilator.map πR ≤ (RingHom.ker πR).annihilator.map πR :=
  AlgHom.length_cotangent_le_and_congruenceIdeal_le_of_surjective
    (AlgHom.id 𝒪 R) Function.surjective_id πR πR rfl

/-- The original reduced-algebra statement, with its original binders. -/
example {𝒪 : Type*} {T : Type*} [CommRing 𝒪] [IsDomain 𝒪]
    [CommRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [IsNoetherianRing T] [IsReduced T]
    (πT : T →ₐ[𝒪] 𝒪) :
    (RingHom.ker πT).annihilator.map πT ≠ ⊥ :=
  AlgHom.congruenceIdeal_ne_bot_of_isReduced πT

/-- Higher-universe consumer in `Type 1`. -/
example {𝒪 : Type 1} {T : Type 1} [CommRing 𝒪] [IsDomain 𝒪]
    [CommRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [IsNoetherianRing T] [IsReduced T]
    (πT : T →ₐ[𝒪] 𝒪) :
    (RingHom.ker πT).annihilator.map πT ≠ ⊥ :=
  AlgHom.congruenceIdeal_ne_bot_of_isReduced πT

/-- For `T = 𝒪` with the identity section, the kernel is `⊥`, its
annihilator is `⊤`, and the congruence ideal is `⊤ ≠ ⊥`. -/
example {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsNoetherianRing 𝒪] :
    (RingHom.ker (AlgHom.id 𝒪 𝒪)).annihilator.map (AlgHom.id 𝒪 𝒪) ≠ ⊥ :=
  AlgHom.congruenceIdeal_ne_bot_of_isReduced (AlgHom.id 𝒪 𝒪)
