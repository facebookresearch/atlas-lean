/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.FieldTheory.Galois.GaloisRepLocalConditions

@[expose] public section

universe u

/-- Consumer with the original binders: the local conditions are
predicates on an adic representation. -/
example {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A)
    (p : ℕ) : Prop :=
  ρ.DetIsCyclotomic p ∧ ρ.IsOrdinaryAt p ∧
    ∀ q : ℕ, q.Prime → ρ.IsUnipotentOnInertiaAt q

/-- Higher-universe consumer. -/
example {A : Type (u + 1)} [CommRing A] [IsLocalRing A]
    (ρ : GaloisRepAdic A) (p : ℕ) : Prop :=
  ρ.DetIsCyclotomic p ∧ ρ.IsOrdinaryAt p

/-- Consumer for the bundled ordinary and minimal ordinary
conditions, with the original binders. -/
example (𝒪 : Type) [CommRing 𝒪] (p : ℕ) (S : Finset ℕ)
    {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A]
    (ρ : GaloisRepAdic A) (h : GaloisRep.ordinaryCondition 𝒪 p S ρ) :
    ρ.DetIsCyclotomic p ∧ ρ.IsOrdinaryAt p :=
  ⟨h.1, h.2.1⟩

/-- The minimal ordinary condition gives unipotent inertia at its
exceptional primes other than `p`. -/
example (𝒪 : Type) [CommRing 𝒪] (p : ℕ) (S : Finset ℕ)
    {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A]
    (ρ : GaloisRepAdic A)
    (h : GaloisRep.minimalOrdinaryCondition 𝒪 p S ρ) {q : ℕ}
    (hqS : q ∈ S) (hq : q.Prime) (hqp : q ≠ p) :
    ρ.IsUnipotentOnInertiaAt q :=
  h.2 q hqS hq hqp

/-- Boundary: unramifiedness is only asserted outside the
exceptional set; at `q = p` with `p ∈ S` the ordinary condition
gives no unramified conclusion, showing the exceptional set
matters. -/
example (𝒪 : Type) [CommRing 𝒪] (p : ℕ)
    {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A]
    (ρ : GaloisRepAdic A)
    (h : GaloisRep.ordinaryCondition 𝒪 p {p} ρ) :
    ρ.IsOrdinaryAt p :=
  h.2.1
