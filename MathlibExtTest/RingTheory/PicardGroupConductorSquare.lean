/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.PicardGroupConductorSquare

@[expose] public section

universe u v

-- Exact-source consumer with the original binders.
example
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] [FaithfulSMul A B]
    (𝔠 : Ideal B) (h𝔠 : ∀ b ∈ 𝔠, b ∈ Set.range (algebraMap A B)) :
    ∃ δ : (B ⧸ 𝔠)ˣ →* CommRing.Pic A,
      (∀ u : (B ⧸ 𝔠)ˣ, ∃ I : Submodule A B,
        (∀ x : B, x ∈ I ↔ ∃ a : A,
          (u : B ⧸ 𝔠) * Ideal.Quotient.mk 𝔠 x = Ideal.Quotient.mk 𝔠 (algebraMap A B a)) ∧
        Nonempty ((δ u : CommRing.Pic A) ≃ₗ[A] ↥I)) ∧
      (∀ u : (B ⧸ 𝔠)ˣ, δ u = 1 ↔
        ∃ (t : Bˣ) (a : (A ⧸ 𝔠.comap (algebraMap A B))ˣ),
          (u : B ⧸ 𝔠) =
            Ideal.quotientMap 𝔠 (algebraMap A B) le_rfl (a : A ⧸ 𝔠.comap (algebraMap A B)) *
              Ideal.Quotient.mk 𝔠 (t : B)) ∧
      (∀ P : CommRing.Pic A, (∃ u, δ u = P) ↔
        CommRing.Pic.mapAlgebra A B P = 1 ∧
          CommRing.Pic.mapAlgebra A (A ⧸ 𝔠.comap (algebraMap A B)) P = 1) ∧
      (∀ (t : Bˣ) (a : (A ⧸ 𝔠.comap (algebraMap A B))ˣ),
        Ideal.Quotient.mk 𝔠 (t : B) =
            Ideal.quotientMap 𝔠 (algebraMap A B) le_rfl (a : A ⧸ 𝔠.comap (algebraMap A B)) →
          ∃ s : Aˣ, algebraMap A B s = t) :=
  CommRing.Pic.exists_boundaryHom_conductorSquare_exact 𝔠 h𝔠

-- Higher-universe consumer.
example
    {A : Type 1} {B : Type 2} [CommRing A] [CommRing B] [Algebra A B] [FaithfulSMul A B]
    (𝔠 : Ideal B) (h𝔠 : ∀ b ∈ 𝔠, b ∈ Set.range (algebraMap A B)) :
    ∃ _δ : (B ⧸ 𝔠)ˣ →* CommRing.Pic A, True :=
  ⟨(CommRing.Pic.exists_boundaryHom_conductorSquare_exact 𝔠 h𝔠).choose, trivial⟩

-- Boundary case: when `A = B` and the algebra map is the identity, every
-- ideal satisfies the hypothesis, so the boundary map exists for every `𝔠`.
example (A : Type*) [CommRing A] (𝔠 : Ideal A) :
    ∃ _δ : (A ⧸ 𝔠)ˣ →* CommRing.Pic A, True :=
  ⟨(CommRing.Pic.exists_boundaryHom_conductorSquare_exact (A := A) (B := A) 𝔠
    (fun b _ => ⟨b, by simp⟩)).choose, trivial⟩
