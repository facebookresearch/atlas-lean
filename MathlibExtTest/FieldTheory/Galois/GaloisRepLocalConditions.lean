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

/-- Outside the exceptional set `{p}`, the ordinary condition gives
unramifiedness at every prime `q ≠ p`. -/
example (𝒪 : Type) [CommRing 𝒪] (p : ℕ)
    {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A]
    (ρ : GaloisRepAdic A)
    (h : GaloisRep.ordinaryCondition 𝒪 p {p} ρ) {q : ℕ}
    (hq : q.Prime) (hqp : q ≠ p) :
    ρ.IsUnramifiedAt q :=
  h.2.2 q hq (Finset.notMem_singleton.mpr hqp)

/-- Boundary at the exceptional set `{2}`: the ordinary condition
gives unramifiedness at `3 ∉ {2}`, but not at `2 ∈ {2}`, where the
unramified clause would need `2 ∉ {2}`. -/
example (𝒪 : Type) [CommRing 𝒪]
    {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A]
    (ρ : GaloisRepAdic A)
    (h : GaloisRep.ordinaryCondition 𝒪 2 {2} ρ) :
    ρ.IsUnramifiedAt 3 := by
  fail_if_success
    have : ρ.IsUnramifiedAt 2 :=
      h.2.2 2 Nat.prime_two (Finset.mem_singleton_self 2)
  exact h.2.2 3 Nat.prime_three (by decide)

/-- Coefficient ring and target ring in independent universes: both
bundled conditions and their unfolding lemmas apply. -/
example (𝒪 : Type) [CommRing 𝒪] (p : ℕ) (S : Finset ℕ)
    {A : Type 1} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A]
    (ρ : GaloisRepAdic A)
    (h : GaloisRep.minimalOrdinaryCondition 𝒪 p S ρ) :
    GaloisRep.ordinaryCondition 𝒪 p S ρ ∧
      (ρ.DetIsCyclotomic p ∧ ρ.IsOrdinaryAt p ∧
        ∀ q : ℕ, q.Prime → q ∉ S → ρ.IsUnramifiedAt q) :=
  ⟨((GaloisRep.minimalOrdinaryCondition_def 𝒪 p S ρ).mp h).1,
    (GaloisRep.ordinaryCondition_def 𝒪 p S ρ).mp h.1⟩

/-- Coefficient ring in a higher universe than the target ring. -/
example (𝒪 : Type (u + 1)) [CommRing 𝒪] (p : ℕ) (S : Finset ℕ)
    {A : Type u} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A]
    (ρ : GaloisRepAdic A)
    (h : GaloisRep.ordinaryCondition 𝒪 p S ρ)
    (hS : ∀ q ∈ S, q.Prime → q ≠ p → ρ.IsUnipotentOnInertiaAt q) :
    GaloisRep.minimalOrdinaryCondition 𝒪 p S ρ :=
  (GaloisRep.minimalOrdinaryCondition_def 𝒪 p S ρ).mpr ⟨h, hS⟩
