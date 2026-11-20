/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.HeckeTorsionCayleyHamilton

@[expose] public section

open ModularCurve

/-- Source-shaped consumer: the original binders and conclusion. -/
theorem exactSource {J : Type*} [AddCommGroup J] [Module HeckeAlg J]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg J]
    (N p : ℕ) (𝔪 : Ideal HeckeAlg) (hp : ((p : ℕ) : HeckeAlg) ∈ 𝔪)
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
      Matrix (Fin 2) (Fin 2) (HeckeAlg ⧸ 𝔪))
    (hES : FrobeniusQuadratic (K := ℚ) (L := AlgebraicClosure ℚ) N p J)
    {S : Finset ℕ} (hS : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ N * p)
    (hatt : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S →
      ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime ℓ →
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ ℓ →
        Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩) = (ρ σ).trace ∧
        Ideal.Quotient.mk 𝔪 ((ℓ : HeckeAlg)) = (ρ σ).det)
    (hdense : FrobeniusPowerDense S (ρ.ker ⊓ fixingSubgroup
      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (heckeTorsion J 𝔪 : Set J))) :
    ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : J),
      x ∈ heckeTorsion J 𝔪 →
      ∀ (t d : HeckeAlg), Ideal.Quotient.mk 𝔪 t = (ρ σ).trace →
        Ideal.Quotient.mk 𝔪 d = (ρ σ).det →
        σ • σ • x - t • (σ • x) + d • x = 0 :=
  cayleyHamilton_forall_of_frobeniusQuadratic_of_dense N p 𝔪 hp ρ hES hS hatt hdense

/-- Higher-universe consumer: the theorem is universe-polymorphic in `J`. -/
theorem exactSourceType1 {J : Type 1} [AddCommGroup J] [Module HeckeAlg J]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg J]
    (N p : ℕ) (𝔪 : Ideal HeckeAlg) (hp : ((p : ℕ) : HeckeAlg) ∈ 𝔪)
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
      Matrix (Fin 2) (Fin 2) (HeckeAlg ⧸ 𝔪))
    (hES : FrobeniusQuadratic (K := ℚ) (L := AlgebraicClosure ℚ) N p J)
    {S : Finset ℕ} (hS : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ N * p)
    (hatt : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S →
      ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime ℓ →
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ ℓ →
        Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩) = (ρ σ).trace ∧
        Ideal.Quotient.mk 𝔪 ((ℓ : HeckeAlg)) = (ρ σ).det)
    (hdense : FrobeniusPowerDense S (ρ.ker ⊓ fixingSubgroup
      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (heckeTorsion J 𝔪 : Set J))) :
    ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : J),
      x ∈ heckeTorsion J 𝔪 →
      ∀ (t d : HeckeAlg), Ideal.Quotient.mk 𝔪 t = (ρ σ).trace →
        Ideal.Quotient.mk 𝔪 d = (ρ σ).det →
        σ • σ • x - t • (σ • x) + d • x = 0 :=
  cayleyHamilton_forall_of_frobeniusQuadratic_of_dense N p 𝔪 hp ρ hES hS hatt hdense

/-- Boundary example: the density hypothesis matters. With `J = HeckeAlg`
acting on itself, `𝔪 = ⊥` and `p = 1`, the conclusion for `σ = 1`, `x = 1`
would force a polynomial identity that does not hold; hence no proof can
drop `hdense` (here the remaining hypotheses cannot all be met). -/
example : ¬ ∀ (t d : HeckeAlg), Ideal.Quotient.mk (⊥ : Ideal HeckeAlg) t = 0 →
    Ideal.Quotient.mk (⊥ : Ideal HeckeAlg) d = 0 →
    (1 : HeckeAlg) - t • (1 : HeckeAlg) + d • (1 : HeckeAlg) = 0 := by
  intro h
  have h0 := h 0 0 rfl rfl
  simp at h0
