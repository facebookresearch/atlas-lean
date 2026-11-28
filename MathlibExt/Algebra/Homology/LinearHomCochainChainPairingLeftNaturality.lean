/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.Algebra.Homology.LinearHomCochainChainPairingLeftTmulNaturality

/-!
# Left-variable naturality of the Hom cochain–chain pairing

Let R be commutative and all coefficients lie in universe u. Let Δ:K₃→K₁⊗K₂ and Δ′:K₃′→K₁′⊗K₂ be
chain diagonals, with f₁:K₁′→K₁ and f₃:K₃′→K₃ satisfying f₃≫Δ=Δ′≫(f₁⊗id). Fix actions
ρ_q:A⊗K₂,q→L_q.

At p,q∈ℕ, precomposing the cochain with f₁,p and pairing against the primed diagonal equals
pushing the chain argument forward by f₃,p+q and pairing against Δ. This is the R-linear
tensor-map square from Hom_R(K₁,p,A)⊗K₃′,p+q to L_q.
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped TensorProduct

universe u

namespace HomologicalComplex

/-- Let R be commutative in universe u, with all modules and nonnegative chain-complex terms in u.
For Δ:K₃→K₁⊗K₂, Δ′:K₃′→K₁′⊗K₂, f₁:K₁′→K₁ and f₃:K₃′→K₃, assume f₃≫Δ=Δ′≫(f₁⊗id_{K₂}). With fixed
ρ_q:A⊗K₂,q→L_q, the pairings satisfy
(precompose(f₁,p)⊗id)≫κ_{Δ′,ρ}^{p,q}=(id⊗f₃,p+q)≫κ_{Δ,ρ}^{p,q}. Precomposition sends φ to
f₁,p≫φ, and the output degree is q. -/
@[reassoc]
theorem linearHomCochainChainPair_naturality_left
    {R : Type u} [CommRing R] {A : ModuleCat.{u} R}
    {K₁ K₁' K₂ K₃ K₃' L : ChainComplex (ModuleCat.{u} R) ℕ}
    (Δ : K₃ ⟶ tensorObj K₁ K₂)
    (Δ' : K₃' ⟶ tensorObj K₁' K₂)
    (f₁ : K₁' ⟶ K₁) (f₃ : K₃' ⟶ K₃)
    (ρ : ∀ q, A ⊗ K₂.X q ⟶ L.X q)
    (hΔ : f₃ ≫ Δ = Δ' ≫ tensorHom f₁ (𝟙 K₂))
    (p q : ℕ) :
    (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).map f₁.op).f p ⊗ₘ
        𝟙 (K₃'.X (p + q))) ≫
      linearHomCochainChainPair R Δ' ρ p q =
    (𝟙 (ModuleCat.of R (K₁.X p ⟶ A)) ⊗ₘ f₃.f (p + q)) ≫
      linearHomCochainChainPair R Δ ρ p q := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro φ x
  have hL : ((((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).map
      f₁.op).f p ⊗ₘ 𝟙 (K₃'.X (p + q))).hom (φ ⊗ₜ[R] x)) =
      (f₁.f p ≫ φ) ⊗ₜ[R] x := by
    simp
    rfl
  have hR : ((𝟙 (ModuleCat.of R (K₁.X p ⟶ A)) ⊗ₘ f₃.f (p + q)).hom
      (φ ⊗ₜ[R] x)) = φ ⊗ₜ[R] (f₃.f (p + q)).hom x := by
    simp
    rfl
  change (linearHomCochainChainPair R Δ' ρ p q).hom
      ((((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).map f₁.op).f p ⊗ₘ
        𝟙 (K₃'.X (p + q))).hom (φ ⊗ₜ[R] x)) =
    (linearHomCochainChainPair R Δ ρ p q).hom
      ((𝟙 (ModuleCat.of R (K₁.X p ⟶ A)) ⊗ₘ f₃.f (p + q)).hom (φ ⊗ₜ[R] x))
  rw [hL, hR]
  exact linearHomCochainChainPair_naturality_left_tmul Δ Δ' f₁ f₃ ρ hΔ p q φ x

end HomologicalComplex

end
