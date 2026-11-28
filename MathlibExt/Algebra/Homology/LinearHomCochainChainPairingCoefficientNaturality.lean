/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
import MathlibExt.Algebra.Homology.LinearHomCochainChainPairing
import MathlibExt.Algebra.Homology.LinearHomCochainComplex

/-!
# Coefficient naturality of degree-lowering Hom cochain pairings

Let R be commutative and all module carriers lie in universe u. Fix a chain diagonal Δ:K₃→K₁⊗K₂.
Coefficient and output maps f_A:A→A′ and f_L:L→L′ compare actions ρ_q:A⊗K₂,q→L_q and
ρ′_q:A′⊗K₂,q→L′_q when ρ_q≫f_L,q=(f_A⊗id)≫ρ′_q.

For a cochain φ:K₁,p→A and chain x∈K₃,p+q, pairing φ≫f_A with x using ρ′ equals applying f_L,q
to the pairing of φ with x using ρ. This is equality of the full R-linear tensor maps, with
output degree q and fixed diagonal input.
-/

open CategoryTheory CategoryTheory.MonoidalCategory HomologicalComplex Opposite

universe u

namespace HomologicalComplex

variable (R : Type u) [CommRing R]

/-- Let R be commutative in universe u, with all modules and nonnegative chain-complex terms in u.
Let Δ:K₃→K₁⊗K₂, f_A:A→A′ and f_L:L→L′, and suppose ρ_q≫f_L,q=(f_A⊗id_{K₂,q})≫ρ′_q for every q.
For p,q∈ℕ, the pairings satisfy
(postcompose(f_A)⊗id_{K₃,p+q})≫κ_{Δ,ρ′}^{p,q}=κ_{Δ,ρ}^{p,q}≫f_L,q. Here postcomposition sends
φ:K₁,p→A to φ≫f_A, and both sides map Hom_R(K₁,p,A)⊗K₃,p+q to L′_q. -/
@[reassoc]
public theorem linearHomCochainChainPair_coefficient_naturality
    {K₁ K₂ K₃ : ChainComplex (ModuleCat.{u} R) ℕ}
    {A A' : ModuleCat.{u} R}
    {L L' : ChainComplex (ModuleCat.{u} R) ℕ}
    [K₁.HasTensor K₂]
    (Δ : K₃ ⟶ tensorObj K₁ K₂)
    (fA : A ⟶ A') (fL : L ⟶ L')
    (ρ : ∀ q, A ⊗ K₂.X q ⟶ L.X q)
    (ρ' : ∀ q, A' ⊗ K₂.X q ⟶ L'.X q)
    (hρ : ∀ q, ρ q ≫ fL.f q = (fA ⊗ₘ 𝟙 _) ≫ ρ' q)
    (p q : ℕ) :
    ((((linearHomCochainComplexBifunctor R (ModuleCat.{u} R)).map fA).app
      (Opposite.op K₁)).f p ⊗ₘ 𝟙 _) ≫
      linearHomCochainChainPair R Δ ρ' p q =
    linearHomCochainChainPair R Δ ρ p q ≫ fL.f q := by
  have hdesc : ∀ φ : K₁.X p ⟶ A,
      linearHomCochainChainPairDesc R ρ' p q (φ ≫ fA) =
        linearHomCochainChainPairDesc R ρ p q φ ≫ fL.f q := by
    intro φ
    apply mapBifunctor.hom_ext
    intro i j hij
    unfold linearHomCochainChainPairDesc
    by_cases hi : i = p
    · subst i
      have hj : j = q := Nat.add_left_cancel hij
      subst j
      simp only [← Category.assoc]
      simp only [ι_mapBifunctorDesc, dite_eq_left]
      simp only [Category.assoc]
      rw [hρ q]
      simp only [← Category.assoc]
      rw [MonoidalCategory.tensorHom_comp_tensorHom]
      simp
    · simp [hi]
  have hcoeff : ∀ φ : K₁.X p ⟶ A,
      ((((linearHomCochainComplexBifunctor R (ModuleCat.{u} R)).map fA).app
        (Opposite.op K₁)).f p).hom φ = (φ ≫ fA) := by
    intro φ
    rfl
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro φ x
  have htmul : ((((linearHomCochainComplexBifunctor R (ModuleCat.{u} R)).map fA).app
      (Opposite.op K₁)).f p ⊗ₘ 𝟙 (K₃.X (p + q))).hom (φ ⊗ₜ[R] x) =
      (φ ≫ fA) ⊗ₜ[R] x := by
    simp [hcoeff φ]
    rfl
  change (linearHomCochainChainPair R Δ ρ' p q).hom
      (((((linearHomCochainComplexBifunctor R (ModuleCat.{u} R)).map fA).app
        (Opposite.op K₁)).f p ⊗ₘ 𝟙 _).hom (φ ⊗ₜ[R] x)) =
    (fL.f q).hom ((linearHomCochainChainPair R Δ ρ p q).hom (φ ⊗ₜ[R] x))
  rw [htmul]
  change (Δ.f (p + q) ≫ linearHomCochainChainPairDesc R ρ' p q (φ ≫ fA)).hom x =
    (fL.f q).hom
      ((Δ.f (p + q) ≫ linearHomCochainChainPairDesc R ρ p q φ).hom x)
  change (linearHomCochainChainPairDesc R ρ' p q (φ ≫ fA)).hom
      ((Δ.f (p + q)).hom x) =
    (fL.f q).hom ((linearHomCochainChainPairDesc R ρ p q φ).hom
      ((Δ.f (p + q)).hom x))
  have hdesc_app : ∀ y,
      (linearHomCochainChainPairDesc R ρ' p q (φ ≫ fA)).hom y =
        (fL.f q).hom ((linearHomCochainChainPairDesc R ρ p q φ).hom y) :=
    fun y => congrArg (fun f : (tensorObj K₁ K₂).X (p + q) ⟶ _ => f.hom y)
      (hdesc φ)
  exact hdesc_app ((Δ.f (p + q)).hom x)

end HomologicalComplex
