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
# Maurer–Cartan functoriality

This file packages the zero-locus functoriality for the graded convolution
product: postcomposition by a monoid morphism and precomposition by a
comonoid morphism preserve the Maurer–Cartan equation, with a bundled
combined map.

## Grading and sign conventions

Cohomological grading throughout, following the Maurer–Cartan base: a twisting
cochain is `τ : Cochain C A 1` with `δ 1 (1 + 1) τ + conv τ τ = 0` in degree
`1 + 1`, where `δ` is the pinned `HomComplex.δ` and `conv` is the graded
convolution `μ ∘ (f ⊗ g) ∘ Δ`. Postcomposition uses `add_zero` transports and
precomposition uses `zero_add` transports, exactly as in the base convolution
definition. No new signs are introduced here.

## Primary source

Standard reference: J.-L. Loday and B. Vallette, *Algebraic Operads*,
Grundlehren 346, Springer, 2012,
<https://doi.org/10.1007/978-3-642-30362-3>. Exact printed-section numbers
and a sign-level match against the printed text were not verified in this
environment, so none is claimed here.

## Declaration inventory

* `CochainComplex.conv_postcomp` and `CochainComplex.conv_precomp` are
  consumed from `TwistingCochain`, where the generic convolution transport
  laws now live; they are not re-proved here.
* `IsMaurerCartan.postcomp`: the Maurer–Cartan predicate is preserved by
  monoid-morphism postcomposition, from the pinned `δ_comp_ofHom` and
  `conv_postcomp`.
* `IsMaurerCartan.precomp`: the Maurer–Cartan predicate is preserved by
  comonoid-morphism precomposition, from the pinned `δ_ofHom_comp` and
  `conv_precomp`.
* `MaurerCartan.map`: bundled combined pre/postcomposition map for bundled
  Maurer–Cartan cochains, with its `map_tau` computation rule.

## Nonclaims

No augmentation vanishing transport, no twisted-differential map, no Hom-complex
map, no free or cofree object, no adjunction, no totalization, no derived or
Koszul result, no operadic result, and no model-categorical result is claimed
here. Only the zero-locus functoriality stated above is proved.

## Import justification

`TwistingMaurerCartan` supplies `IsMaurerCartan` and `MaurerCartan` with the
`add_zero`/`zero_add` degree conventions preserved exactly, and transitively
supplies `conv` with its `conv_postcomp`/`conv_precomp` transport laws from
`TwistingCochain`. No further MathlibExt import is needed.
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

/-- The Maurer–Cartan predicate is preserved by monoid-morphism
postcomposition, from the pinned differential postcomposition rule and
`conv_postcomp`. -/
theorem IsMaurerCartan.postcomp {τ : HomComplex.Cochain C A 1}
    (h : IsMaurerCartan τ) (φ : A ⟶ B) [IsMonHom φ] :
    IsMaurerCartan (τ.comp (HomComplex.Cochain.ofHom φ) (add_zero 1)) := by
  unfold IsMaurerCartan at h ⊢
  rw [HomComplex.δ_comp_ofHom, ← conv_postcomp]
  rw [← HomComplex.Cochain.add_comp]
  rw [h, HomComplex.Cochain.zero_comp]

/-- The Maurer–Cartan predicate is preserved by comonoid-morphism
precomposition, from the pinned differential precomposition rule and
`conv_precomp`. -/
theorem IsMaurerCartan.precomp {τ : HomComplex.Cochain C A 1}
    (h : IsMaurerCartan τ) (ψ : C' ⟶ C) [IsComonHom ψ] :
    IsMaurerCartan ((HomComplex.Cochain.ofHom ψ).comp τ (zero_add 1)) := by
  unfold IsMaurerCartan at h ⊢
  rw [HomComplex.δ_ofHom_comp, ← conv_precomp]
  rw [← HomComplex.Cochain.comp_add]
  rw [h, HomComplex.Cochain.comp_zero]

/-- Bundled combined pre/postcomposition map for Maurer–Cartan cochains:
first postcompose by a monoid morphism, then precompose by a comonoid
morphism. -/
def MaurerCartan.map (x : MaurerCartan (R := R) (C := C) (A := A))
    (ψ : C' ⟶ C) [IsComonHom ψ] (φ : A ⟶ B) [IsMonHom φ] :
    MaurerCartan (R := R) (C := C') (A := B) where
  tau := (HomComplex.Cochain.ofHom ψ).comp
    (x.tau.comp (HomComplex.Cochain.ofHom φ) (add_zero 1)) (zero_add 1)
  isMC := IsMaurerCartan.precomp (IsMaurerCartan.postcomp x.isMC φ) ψ

/-- Underlying cochain of the bundled functoriality map. -/
@[simp]
theorem MaurerCartan.map_tau (x : MaurerCartan (R := R) (C := C) (A := A))
    (ψ : C' ⟶ C) [IsComonHom ψ] (φ : A ⟶ B) [IsMonHom φ] :
    (x.map ψ φ).tau = (HomComplex.Cochain.ofHom ψ).comp
      (x.tau.comp (HomComplex.Cochain.ofHom φ) (add_zero 1)) (zero_add 1) :=
  rfl

end CochainComplex
