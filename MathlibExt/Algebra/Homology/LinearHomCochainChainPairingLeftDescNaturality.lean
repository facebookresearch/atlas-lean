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
# Left-complex naturality of the Hom cochain descriptor

Let R be commutative and all coefficients lie in universe u. For chain complexes K₁,K₁′,K₂,L, a
map f₁:K₁′→K₁ and actions ρ_q:A⊗K₂,q→L_q, the descriptor for φ:K₁,p→A pulls back along
f₁⊗id_{K₂} to the descriptor for f₁,p≫φ.

Both descriptors select the (p,q) summand of total degree p+q. Thus the equation holds before
any chain diagonal is applied and preserves the contravariant left-complex action.
-/

@[expose] public section

open CategoryTheory MonoidalCategory HomologicalComplex

universe u

variable {R : Type u} [CommRing R]
variable {A : ModuleCat.{u} R}
variable {K₁ K₁' K₂ L : ChainComplex (ModuleCat.{u} R) ℕ}

/-- Let R be commutative in universe u, with all modules and nonnegative chain-complex terms in u.
For f₁:K₁′→K₁, actions ρ_q:A⊗K₂,q→L_q, p,q∈ℕ and φ:K₁,p→A, let D_φ:(K₁⊗K₂)_{p+q}→L_q select the
(p,q) summand. Then (f₁⊗id_{K₂})_{p+q}≫D_φ=D_{f₁,p≫φ}, where the right descriptor is on K₁′⊗K₂.
The equality retains the same coefficient action and output degree. -/
theorem HomologicalComplex.linearHomCochainChainPairDesc_naturality_left
    (f₁ : K₁' ⟶ K₁) (ρ : ∀ q, A ⊗ K₂.X q ⟶ L.X q) (p q : ℕ)
    (φ : K₁.X p ⟶ A) :
    (HomologicalComplex.tensorHom f₁ (𝟙 K₂)).f (p + q) ≫
      HomologicalComplex.linearHomCochainChainPairDesc R ρ p q φ =
      HomologicalComplex.linearHomCochainChainPairDesc R ρ p q (f₁.f p ≫ φ) := by
  apply mapBifunctor.hom_ext
  intro i j h
  unfold HomologicalComplex.linearHomCochainChainPairDesc
  by_cases hi : i = p
  · subst i
    have hj : j = q := Nat.add_left_cancel h
    subst j
    simp only [← Category.assoc]
    simp only [ι_mapBifunctorDesc, dite_eq_left]
    simp only [Category.assoc]
    simp only [curriedTensor_obj_obj, ComplexShape.π_def, tensorHom_id,
      ι_mapBifunctorMap_assoc, id_f, curriedTensor_obj_map, ι_mapBifunctorDesc,
      ↓reduceDIte]
    rw [MonoidalCategory.comp_whiskerRight]
    simp
  · simp only [← Category.assoc]
    simp [hi]

end
