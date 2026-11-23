/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.LocalRing.IsReducedOfDerivation

/-- Exact-source consumer: the original `Type` binders and hypothesis shapes. -/
theorem exactSource (k : Type) [Field k] [CharZero k] (A : Type) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] [Algebra k A]
    (hk : ∀ a : A, ∃ c : k, a - algebraMap k A c ∈ IsLocalRing.maximalIdeal A)
    (hder : ∀ φ : A →ₗ[k] k, (∀ a ∈ (IsLocalRing.maximalIdeal A) ^ 2, φ a = 0) →
      (∀ c : k, φ (algebraMap k A c) = 0) →
      ∃ D : Derivation k A A, ∀ a : A, D a - algebraMap k A (φ a) ∈
        IsLocalRing.maximalIdeal A) :
    IsReduced A :=
  IsLocalRing.isReduced_of_forall_exists_derivation_of_charZero k A hk hder

universe u v

/-- The criterion is universe-polymorphic in both the field and the algebra. -/
example (k : Type u) [Field k] [CharZero k] (A : Type v) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] [Algebra k A]
    (hk : ∀ a : A, ∃ c : k, a - algebraMap k A c ∈ IsLocalRing.maximalIdeal A)
    (hder : ∀ φ : A →ₗ[k] k, (∀ a ∈ (IsLocalRing.maximalIdeal A) ^ 2, φ a = 0) →
      (∀ c : k, φ (algebraMap k A c) = 0) →
      ∃ D : Derivation k A A, ∀ a : A, D a - algebraMap k A (φ a) ∈
        IsLocalRing.maximalIdeal A) :
    IsReduced A :=
  IsLocalRing.isReduced_of_forall_exists_derivation_of_charZero k A hk hder

/-- Boundary case: a field is reduced, and its maximal ideal is trivial, so
the residue-field hypothesis `hk` is automatic there. The dual numbers show
the derivation-lifting hypothesis cannot be dropped in general. -/
example (k : Type) [Field k] [CharZero k] : IsReduced k := inferInstance

example (k : Type) [Field k] : IsLocalRing.maximalIdeal k = ⊥ :=
  IsLocalRing.maximalIdeal_eq_bot
