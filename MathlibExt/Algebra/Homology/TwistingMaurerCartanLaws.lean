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
# Maurer–Cartan map laws

This file proves the two functor laws for the bundled `CochainComplex.MaurerCartan.map`,
built on `TwistingMaurerCartanFunctoriality`.
Only the identity and composition laws are proved here.

## Grading and sign conventions

Cohomological grading throughout, following the Maurer–Cartan base: the bundled
map first postcomposes by a monoid morphism with `add_zero` transports, then
precomposes by a comonoid morphism with `zero_add` transports, exactly as in
`MaurerCartan.map_tau`. No new signs or transports are introduced here.

## Declaration inventory

* `MaurerCartan.map_id`: mapping along both identity morphisms is the identity,
  from the pinned `Cochain.comp_id` and `Cochain.id_comp`.
* `MaurerCartan.map_comp`: successive maps compose with contravariant
  coalgebra composition `ψ₁ ≫ ψ₂` and covariant algebra composition
  `φ₂ ≫ φ₁`, from the pinned `Cochain.ofHom_comp` and the two
  degree-zero cochain associativity lemmas.

## Nonclaims

No twisted-differential map, no Hom-complex map, no free or cofree object, no
totalization, no adjunction, no derived or Koszul result, no operadic result,
and no model-categorical result is proved here. Only the two functor laws
stated above are proved.

## Import justification

`TwistingMaurerCartanFunctoriality` supplies `MaurerCartan.map` with its
`map_tau` computation rule, `MaurerCartan.ext`, and the preserved-predicate
lemmas that fix the orientation used here. No further MathlibExt import is
needed.
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

/-- Mapping a Maurer–Cartan cochain along both identity morphisms is the
identity, from the pinned cochain identity laws. -/
theorem MaurerCartan.map_id (x : MaurerCartan (R := R) (C := C) (A := A)) :
    x.map (𝟙 C) (𝟙 A) = x := by
  apply MaurerCartan.ext
  simp only [MaurerCartan.map_tau, HomComplex.Cochain.comp_id,
    HomComplex.Cochain.id_comp]

/-- Successive bundled maps compose into one map: coalgebra morphisms compose
contravariantly as `ψ₁ ≫ ψ₂` while algebra morphisms compose covariantly as
`φ₂ ≫ φ₁`, exactly matching the `map_tau` orientation. The proof unfolds both
sides with `map_tau`, splits the morphism cochains with `ofHom_comp`, and
reassociates the degree-zero factors with the pinned cochain associativity
lemmas. -/
theorem MaurerCartan.map_comp (x : MaurerCartan (R := R) (C := C) (A := A))
    (ψ₂ : C' ⟶ C) [IsComonHom ψ₂] (φ₂ : A ⟶ B) [IsMonHom φ₂]
    (ψ₁ : C'' ⟶ C') [IsComonHom ψ₁] (φ₁ : B ⟶ B') [IsMonHom φ₁] :
    (x.map ψ₂ φ₂).map ψ₁ φ₁ = x.map (ψ₁ ≫ ψ₂) (φ₂ ≫ φ₁) := by
  apply MaurerCartan.ext
  simp only [MaurerCartan.map_tau, HomComplex.Cochain.ofHom_comp,
    HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain,
    HomComplex.Cochain.comp_assoc_of_second_is_zero_cochain]

end CochainComplex
