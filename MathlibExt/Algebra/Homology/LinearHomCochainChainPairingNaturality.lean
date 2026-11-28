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

public import MathlibExt.Algebra.Homology.LinearHomCochainChainPairing

/-!
# Right-factor, diagonal-input and output naturality of Hom cap pairings

Let R be commutative and all modules lie in universe u. Fix K₁ and the cochain coefficient A.
Maps f₂:K₂→K₂′, f₃:K₃→K₃′ and f_L:L→L′ compare diagonals and actions when f₃≫Δ′=Δ≫(id_{K₁}⊗f₂)
and ρ_q≫f_L,q=(id_A⊗f₂,q)≫ρ′_q.

The pairing followed by f_L,q equals the primed pairing after pushing the degree-p+q chain input
forward by f₃. The cochain φ:K₁,p→A is unchanged. Thus both compatibility diagrams are reflected
in the full pairing map into degree q of L′.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace HomologicalComplex

variable (R : Type u) [CommRing R]
variable (K₁ : ChainComplex (ModuleCat.{u} R) ℕ)
variable (A : ModuleCat.{u} R)

/-- Let R be commutative in universe u, with all modules and nonnegative chain-complex terms in u.
Fix K₁,A, diagonals Δ:K₃→K₁⊗K₂ and Δ′:K₃′→K₁⊗K₂′, and maps f₂:K₂→K₂′, f₃:K₃→K₃′, f_L:L→L′.
Assume f₃≫Δ′=Δ≫(id_{K₁}⊗f₂) and ρ_q≫f_L,q=(id_A⊗f₂,q)≫ρ′_q for every q. Then
κ_{Δ,ρ}^{p,q}≫f_L,q=(id_{Hom_R(K₁,p,A)}⊗f₃,p+q)≫κ_{Δ′,ρ′}^{p,q}. The equality retains both
diagrams and all degree-p+q chain inputs. -/
@[reassoc]
public theorem linearHomCochainChainPair_naturality_right
    {K₂ K₂' K₃ K₃' L L' : ChainComplex (ModuleCat.{u} R) ℕ}
    [K₁.HasTensor K₂] [K₁.HasTensor K₂']
    (Δ : K₃ ⟶ tensorObj K₁ K₂)
    (Δ' : K₃' ⟶ tensorObj K₁ K₂')
    (f₂ : K₂ ⟶ K₂') (f₃ : K₃ ⟶ K₃') (fL : L ⟶ L')
    (ρ : ∀ q, A ⊗ K₂.X q ⟶ L.X q)
    (ρ' : ∀ q, A ⊗ K₂'.X q ⟶ L'.X q)
    (hΔ : f₃ ≫ Δ' = Δ ≫ HomologicalComplex.tensorHom (𝟙 K₁) f₂)
    (hρ : ∀ q, ρ q ≫ fL.f q = (𝟙 A ⊗ₘ f₂.f q) ≫ ρ' q)
    (p q : ℕ) :
    linearHomCochainChainPair R Δ ρ p q ≫ fL.f q =
      (𝟙 _ ⊗ₘ f₃.f (p + q)) ≫ linearHomCochainChainPair R Δ' ρ' p q := by
  have hdiag : f₃.f (p + q) ≫ Δ'.f (p + q) =
      Δ.f (p + q) ≫ (HomologicalComplex.tensorHom (𝟙 K₁) f₂).f (p + q) := by
    have h := congrArg (fun f : K₃ ⟶ HomologicalComplex.tensorObj K₁ K₂' => f.f (p + q)) hΔ
    simpa using h
  have hdesc : ∀ φ : K₁.X p ⟶ A,
      (HomologicalComplex.tensorHom (𝟙 K₁) f₂).f (p + q) ≫
        linearHomCochainChainPairDesc R ρ' p q φ =
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
      simp only [curriedTensor_obj_obj, ComplexShape.π_def, tensorHom_id,
        ι_mapBifunctorMap_assoc, id_f, CategoryTheory.Functor.map_id,
        NatTrans.id_app, curriedTensor_obj_map, ι_mapBifunctorDesc, ↓reduceDIte,
        Category.id_comp]
      rw [hρ q]
      simp only [← Category.assoc]
      rw [MonoidalCategory.whisker_exchange]
      simp
    · simp only [← Category.assoc]
      simp [hi]
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro φ x
  have htmul : (𝟙 (ModuleCat.of R (K₁.X p ⟶ A)) ⊗ₘ f₃.f (p + q)).hom
      (φ ⊗ₜ[R] x) = φ ⊗ₜ[R] (f₃.f (p + q)).hom x := by
    simp
    rfl
  change (fL.f q).hom ((linearHomCochainChainPair R Δ ρ p q).hom (φ ⊗ₜ[R] x)) =
    (linearHomCochainChainPair R Δ' ρ' p q).hom
      ((𝟙 _ ⊗ₘ f₃.f (p + q)).hom (φ ⊗ₜ[R] x))
  rw [htmul, linearHomCochainChainPair_tmul, linearHomCochainChainPair_tmul]
  show (fL.f q).hom ((Δ.f (p + q) ≫ linearHomCochainChainPairDesc R ρ p q φ).hom x) =
    (Δ'.f (p + q) ≫ linearHomCochainChainPairDesc R ρ' p q φ).hom
      ((f₃.f (p + q)).hom x)
  change (fL.f q).hom ((linearHomCochainChainPairDesc R ρ p q φ).hom ((Δ.f (p + q)).hom x)) =
    (linearHomCochainChainPairDesc R ρ' p q φ).hom
      ((Δ'.f (p + q)).hom ((f₃.f (p + q)).hom x))
  have hdiag_app : (Δ'.f (p + q)).hom ((f₃.f (p + q)).hom x) =
      ((HomologicalComplex.tensorHom (𝟙 K₁) f₂).f (p + q)).hom ((Δ.f (p + q)).hom x) :=
    congrArg (fun f : K₃.X (p + q) ⟶ _ => f.hom x) hdiag
  have hdesc_app : ∀ y,
      (linearHomCochainChainPairDesc R ρ' p q φ).hom
        (((HomologicalComplex.tensorHom (𝟙 K₁) f₂).f (p + q)).hom y) =
        (fL.f q).hom ((linearHomCochainChainPairDesc R ρ p q φ).hom y) :=
    fun y => congrArg (fun f : (HomologicalComplex.tensorObj K₁ K₂).X (p + q) ⟶ _ => f.hom y)
      (hdesc φ)
  rw [← hdesc_app, ← hdiag_app]

end HomologicalComplex

end
