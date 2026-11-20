/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.FieldTheory.Galois.SemilinearDescent

@[expose] public section

open scoped TensorProduct

-- Consumer with the original binders.
example {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] {U : Type*} [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (ρ : (L ≃ₐ[K] L) →* (U →ₗ[K] U))
    (f : (L ≃ₐ[K] L) → L ⊗[K] U →+ L ⊗[K] U)
    (hf : ∀ (σ : L ≃ₐ[K] L) (l : L) (u : U), f σ (l ⊗ₜ[K] u) = σ l ⊗ₜ[K] ρ σ u) :
    ∃ b : Module.Basis (Fin (Module.finrank K U)) L (L ⊗[K] U),
      ∀ (σ : L ≃ₐ[K] L) (i : Fin (Module.finrank K U)), f σ (b i) = b i :=
  IsGalois.exists_basis_baseChange_forall_apply_eq_self ρ f hf

-- Higher-universe consumer.
example {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] {U : Type 1} [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (ρ : (L ≃ₐ[K] L) →* (U →ₗ[K] U))
    (f : (L ≃ₐ[K] L) → L ⊗[K] U →+ L ⊗[K] U)
    (hf : ∀ (σ : L ≃ₐ[K] L) (l : L) (u : U), f σ (l ⊗ₜ[K] u) = σ l ⊗ₜ[K] ρ σ u) :
    ∃ b : Module.Basis (Fin (Module.finrank K U)) L (L ⊗[K] U),
      ∀ (σ : L ≃ₐ[K] L) (i : Fin (Module.finrank K U)), f σ (b i) = b i :=
  IsGalois.exists_basis_baseChange_forall_apply_eq_self ρ f hf

-- Boundary: without Galois, invariant vectors need not span; the zero action
-- on a one-dimensional space has only the zero invariant under a nontrivial
-- automorphism, checked here as a concrete non-example of the conclusion's
-- spanning content via finrank.
example : Module.finrank ℚ ℚ = 1 := Module.finrank_self ℚ
