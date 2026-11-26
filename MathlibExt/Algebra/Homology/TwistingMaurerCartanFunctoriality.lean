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

public import MathlibExt.Algebra.Homology.TwistingMaurerCartan

/-!
# Functoriality of the Maurer–Cartan equation

Let R be commutative, C,C' dg coalgebras and A,B dg algebras in the same integer cochain module
category. A coalgebra map ψ:C'→C and algebra map φ:A→B send a Maurer–Cartan cochain τ to φ∘τ∘ψ.

The maps are degree zero, commute with the Hom differential, and preserve convolution. Thus
δτ+τ⋆τ=0 is carried to the same equation for the mapped cochain. The bundled map is
contravariant in the coalgebra and covariant in the algebra.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

namespace CochainComplex

variable {R : Type*} [CommRing R]
variable {C A : CochainComplex (ModuleCat R) ℤ}

variable [∀ (X₁ X₂ : GradedObject ℤ (ModuleCat R)), GradedObject.HasTensor X₁ X₂]
variable [∀ (X : ModuleCat R), PreservesColimit (Functor.empty.{0} (ModuleCat R))
  ((curriedTensor (ModuleCat R)).obj X)]
variable [∀ (X : ModuleCat R), PreservesColimit (Functor.empty.{0} (ModuleCat R))
  ((curriedTensor (ModuleCat R)).flip.obj X)]
variable [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
variable [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
variable [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

variable [MonObj A] [ComonObj C]

variable {B : CochainComplex (ModuleCat R) ℤ} [MonObj B]
variable {C' : CochainComplex (ModuleCat R) ℤ} [ComonObj C']

/-- Let R be a commutative ring and C,A ℤ-indexed cochain complexes in a common R-module carrier
category, with C a dg coalgebra and A a dg algebra. Use the monoidal cochain tensor with all
total-degree coproducts, both zero-object and triple-coproduct compatibility conditions, and
fourfold tensor extensionality. A degree-one τ is Maurer–Cartan when δτ+τ⋆τ=0 in degree two. Let
B be a dg algebra and φ:A→B an algebra cochain map. If τ is Maurer–Cartan, φ∘τ is Maurer–Cartan
in Hom¹(C,B). Postcomposition preserves δ and the convolution product. -/
theorem IsMaurerCartan.postcomp {τ : HomComplex.Cochain C A 1}
    (h : IsMaurerCartan τ) (φ : A ⟶ B) [IsMonHom φ] :
    IsMaurerCartan (τ.comp (HomComplex.Cochain.ofHom φ) (add_zero 1)) := by
  unfold IsMaurerCartan at h ⊢
  rw [HomComplex.δ_comp_ofHom, ← conv_postcomp]
  rw [← HomComplex.Cochain.add_comp]
  rw [h, HomComplex.Cochain.zero_comp]

/-- Let R be a commutative ring and C,A ℤ-indexed cochain complexes in a common R-module carrier
category, with C a dg coalgebra and A a dg algebra. Use the monoidal cochain tensor with all
total-degree coproducts, both zero-object and triple-coproduct compatibility conditions, and
fourfold tensor extensionality. A degree-one τ is Maurer–Cartan when δτ+τ⋆τ=0 in degree two. For
a dg coalgebra C' and coalgebra cochain map ψ:C'→C, a Maurer–Cartan τ gives τ∘ψ in Hom¹(C',A)
with the same equation. Precomposition preserves δ and convolution. -/
theorem IsMaurerCartan.precomp {τ : HomComplex.Cochain C A 1}
    (h : IsMaurerCartan τ) (ψ : C' ⟶ C) [IsComonHom ψ] :
    IsMaurerCartan ((HomComplex.Cochain.ofHom ψ).comp τ (zero_add 1)) := by
  unfold IsMaurerCartan at h ⊢
  rw [HomComplex.δ_ofHom_comp, ← conv_precomp]
  rw [← HomComplex.Cochain.comp_add]
  rw [h, HomComplex.Cochain.comp_zero]

/-- Let R be a commutative ring and C,A ℤ-indexed cochain complexes in a common R-module carrier
category, with C a dg coalgebra and A a dg algebra. Use the monoidal cochain tensor with all
total-degree coproducts, both zero-object and triple-coproduct compatibility conditions, and
fourfold tensor extensionality. For coalgebra cochain map ψ:C'→C, algebra cochain map φ:A→B, and
a bundle x with cochain τ, the mapped bundle in MaurerCartan(C',B) has cochain φ∘τ∘ψ and the
transported equation. -/
def MaurerCartan.map (x : MaurerCartan (R := R) (C := C) (A := A))
    (ψ : C' ⟶ C) [IsComonHom ψ] (φ : A ⟶ B) [IsMonHom φ] :
    MaurerCartan (R := R) (C := C') (A := B) where
  tau := (HomComplex.Cochain.ofHom ψ).comp
    (x.tau.comp (HomComplex.Cochain.ofHom φ) (add_zero 1)) (zero_add 1)
  isMC := IsMaurerCartan.precomp (IsMaurerCartan.postcomp x.isMC φ) ψ

/-- Let R be a commutative ring and C,A ℤ-indexed cochain complexes in a common R-module carrier
category, with C a dg coalgebra and A a dg algebra. Use the monoidal cochain tensor with all
total-degree coproducts, both zero-object and triple-coproduct compatibility conditions, and
fourfold tensor extensionality. For x with τ, ψ:C'→C a coalgebra map and φ:A→B an algebra map,
(x.map ψ φ).tau=φ∘τ∘ψ. The two degree-zero maps retain the cochain degree one and introduce no
degree sign. -/
@[simp]
theorem MaurerCartan.map_tau (x : MaurerCartan (R := R) (C := C) (A := A))
    (ψ : C' ⟶ C) [IsComonHom ψ] (φ : A ⟶ B) [IsMonHom φ] :
    (x.map ψ φ).tau = (HomComplex.Cochain.ofHom ψ).comp
      (x.tau.comp (HomComplex.Cochain.ofHom φ) (add_zero 1)) (zero_add 1) :=
  rfl

end CochainComplex
