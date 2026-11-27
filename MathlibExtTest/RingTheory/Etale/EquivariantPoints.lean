/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Etale.EquivariantPoints

@[expose] public section

set_option autoImplicit false

-- Exact-source consumer, with the original binders.
private theorem exactSource
    {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [IsGalois K Ω]
    {B : Type*} {C : Type*} [CommRing B] [CommRing C] [Algebra K B] [Algebra K C]
    [Algebra.Etale K B] [Algebra.Etale K C]
    (Φ : (C →ₐ[K] Ω) → (B →ₐ[K] Ω))
    (hΦ : ∀ (γ : Ω ≃ₐ[K] Ω) (χ : C →ₐ[K] Ω),
      Φ (γ.toAlgHom.comp χ) = γ.toAlgHom.comp (Φ χ)) :
    ∃! ψ : B →ₐ[K] C, ∀ χ : C →ₐ[K] Ω, χ.comp ψ = Φ χ :=
  Algebra.Etale.existsUnique_algHom_forall_comp_eq_of_equivariant Φ hΦ

-- Higher-universe consumer: the same statement with all types in `Type 1`.
private theorem exactSourceUniverse1
    {K : Type 1} [Field K] {Ω : Type 1} [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [IsGalois K Ω]
    {B : Type 1} {C : Type 1} [CommRing B] [CommRing C] [Algebra K B] [Algebra K C]
    [Algebra.Etale K B] [Algebra.Etale K C]
    (Φ : (C →ₐ[K] Ω) → (B →ₐ[K] Ω))
    (hΦ : ∀ (γ : Ω ≃ₐ[K] Ω) (χ : C →ₐ[K] Ω),
      Φ (γ.toAlgHom.comp χ) = γ.toAlgHom.comp (Φ χ)) :
    ∃! ψ : B →ₐ[K] C, ∀ χ : C →ₐ[K] Ω, χ.comp ψ = Φ χ :=
  Algebra.Etale.existsUnique_algHom_forall_comp_eq_of_equivariant Φ hΦ

-- Boundary: two realizing homomorphisms must agree, so the equivariance
-- hypothesis pins down at most one homomorphism.
example
    {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [IsGalois K Ω]
    {B : Type*} {C : Type*} [CommRing B] [CommRing C] [Algebra K B] [Algebra K C]
    [Algebra.Etale K B] [Algebra.Etale K C]
    (Φ : (C →ₐ[K] Ω) → (B →ₐ[K] Ω))
    (hΦ : ∀ (γ : Ω ≃ₐ[K] Ω) (χ : C →ₐ[K] Ω),
      Φ (γ.toAlgHom.comp χ) = γ.toAlgHom.comp (Φ χ))
    (ψ₁ ψ₂ : B →ₐ[K] C)
    (h₁ : ∀ χ : C →ₐ[K] Ω, χ.comp ψ₁ = Φ χ)
    (h₂ : ∀ χ : C →ₐ[K] Ω, χ.comp ψ₂ = Φ χ) : ψ₁ = ψ₂ := by
  obtain ⟨ψ, -, huniq⟩ := exactSource Φ hΦ
  exact (huniq ψ₁ h₁).trans (huniq ψ₂ h₂).symm
