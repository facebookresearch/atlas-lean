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
public import MathlibExt.RingTheory.DifferentialGraded.TwistingAugmentationFactor

/-!
# Reduced Maurer–Cartan cochains relative to explicit unit maps

Let C be a dg coalgebra and A a dg algebra over a commutative ring in the integer cochain
category. Fix cochain maps η:I→C and ε:A→I, where I is the tensor unit. A Maurer–Cartan bundle
is reduced relative to these maps when its underlying τ satisfies τ∘η=0 and ε∘τ=0.

The zero bundle is reduced for every such pair of maps. For a coalgebra map ψ:C'→C and algebra
map φ:A→B, reducedness is retained under τ↦φ∘τ∘ψ when η'≫ψ=η and φ≫ε'=ε.
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
fourfold tensor extensionality. Let I be the tensor unit. For arbitrary cochain maps η:I→C,
ε:A→I and a Maurer–Cartan bundle x with cochain τ, reducedness is the conjunction τ∘η=0 and
ε∘τ=0 as degree-one cochains. -/
def IsReducedMaurerCartan (η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C)
    (ε : A ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ))
    (x : MaurerCartan (R := R) (C := C) (A := A)) : Prop :=
  IsReducedCochain η ε x.tau

/-- Let R be a commutative ring and C,A ℤ-indexed cochain complexes in a common R-module carrier
category, with C a dg coalgebra and A a dg algebra. Use the monoidal cochain tensor with all
total-degree coproducts, both zero-object and triple-coproduct compatibility conditions, and
fourfold tensor extensionality. Let I be the tensor unit. For any cochain maps η:I→C and ε:A→I,
the zero bundle is reduced relative to them: 0∘η=0 and ε∘0=0. -/
theorem IsReducedMaurerCartan.zero
    (η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C)
    (ε : A ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ)) :
    IsReducedMaurerCartan η ε (MaurerCartan.zero (R := R) (C := C) (A := A)) :=
  IsReducedCochain.zero η ε

/-- Let R be a commutative ring and C,A ℤ-indexed cochain complexes in a common R-module carrier
category, with C a dg coalgebra and A a dg algebra. Use the monoidal cochain tensor with all
total-degree coproducts, both zero-object and triple-coproduct compatibility conditions, and
fourfold tensor extensionality. Let I be the tensor unit and x be reduced in η:I→C,ε:A→I. For
coalgebra map ψ:C'→C, algebra map φ:A→B, and cochain maps η':I→C',ε':B→I satisfying η'≫ψ=η and
φ≫ε'=ε, the mapped bundle x.map ψ φ is reduced in η',ε'. -/
theorem IsReducedMaurerCartan.map {x : MaurerCartan (R := R) (C := C) (A := A)}
    {η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C}
    {ε : A ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ)}
    {η' : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C'}
    {ε' : B ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ)}
    (hx : IsReducedMaurerCartan η ε x)
    (ψ : C' ⟶ C) [IsComonHom ψ] (φ : A ⟶ B) [IsMonHom φ]
    (hψ : η' ≫ ψ = η) (hφ : φ ≫ ε' = ε) :
    IsReducedMaurerCartan η' ε' (x.map ψ φ) := by
  obtain ⟨hleft, hright⟩ := hx
  refine ⟨?_, ?_⟩
  · simp only [MaurerCartan.map_tau]
    rw [← HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain
      (HomComplex.Cochain.ofHom η') (HomComplex.Cochain.ofHom ψ),
      ← HomComplex.Cochain.ofHom_comp, hψ,
      ← HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain
      (HomComplex.Cochain.ofHom η) x.tau,
      hleft, HomComplex.Cochain.zero_comp]
  · simp only [MaurerCartan.map_tau,
      HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain,
      HomComplex.Cochain.comp_assoc_of_second_is_zero_cochain]
    rw [← HomComplex.Cochain.ofHom_comp, hφ, hright,
      HomComplex.Cochain.comp_zero]

end CochainComplex
