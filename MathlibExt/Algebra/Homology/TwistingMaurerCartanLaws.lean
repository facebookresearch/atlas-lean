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

public import MathlibExt.Algebra.Homology.TwistingMaurerCartanFunctoriality

/-!
# Identity and composition of Maurer–Cartan transport

For dg coalgebras C and dg algebras A over a commutative ring, a pair ψ:C'→C, φ:A→B transports a
Maurer–Cartan cochain by φ∘τ∘ψ. Identity maps retain the same bundle.

Two transports along C''→C'→C and A→B→B' combine into the coalgebra composite ψ₁≫ψ₂ and algebra
composite φ₂≫φ₁. The degree-zero compositions preserve the same Maurer–Cartan equation.
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

variable {B B' : CochainComplex (ModuleCat R) ℤ} [MonObj B] [MonObj B']
variable {C' C'' : CochainComplex (ModuleCat R) ℤ} [ComonObj C'] [ComonObj C'']

/-- Let R be a commutative ring and C,A ℤ-indexed cochain complexes in a common R-module carrier
category, with C a dg coalgebra and A a dg algebra. Use the monoidal cochain tensor with all
total-degree coproducts, both zero-object and triple-coproduct compatibility conditions, and
fourfold tensor extensionality. For a Maurer–Cartan bundle x in Hom¹(C,A), x.map(id_C,id_A)=x,
with the same underlying cochain and equation. -/
theorem MaurerCartan.map_id (x : MaurerCartan (R := R) (C := C) (A := A)) :
    x.map (𝟙 C) (𝟙 A) = x := by
  apply MaurerCartan.ext
  simp only [MaurerCartan.map_tau, HomComplex.Cochain.comp_id,
    HomComplex.Cochain.id_comp]

/-- Let R be a commutative ring and C,A ℤ-indexed cochain complexes in a common R-module carrier
category, with C a dg coalgebra and A a dg algebra. Use the monoidal cochain tensor with all
total-degree coproducts, both zero-object and triple-coproduct compatibility conditions, and
fourfold tensor extensionality. Let ψ₂:C'→C, ψ₁:C''→C' be coalgebra cochain maps and φ₂:A→B,
φ₁:B→B' algebra cochain maps. Then (x.map ψ₂ φ₂).map ψ₁ φ₁=x.map(ψ₁≫ψ₂)(φ₂≫φ₁). Both bundles
have cochain φ₁∘φ₂∘τ∘ψ₂∘ψ₁. -/
theorem MaurerCartan.map_comp (x : MaurerCartan (R := R) (C := C) (A := A))
    (ψ₂ : C' ⟶ C) [IsComonHom ψ₂] (φ₂ : A ⟶ B) [IsMonHom φ₂]
    (ψ₁ : C'' ⟶ C') [IsComonHom ψ₁] (φ₁ : B ⟶ B') [IsMonHom φ₁] :
    (x.map ψ₂ φ₂).map ψ₁ φ₁ = x.map (ψ₁ ≫ ψ₂) (φ₂ ≫ φ₁) := by
  apply MaurerCartan.ext
  simp only [MaurerCartan.map_tau, HomComplex.Cochain.ofHom_comp,
    HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain,
    HomComplex.Cochain.comp_assoc_of_second_is_zero_cochain]

end CochainComplex
