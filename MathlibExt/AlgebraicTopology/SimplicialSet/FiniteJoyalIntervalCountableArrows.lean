/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.NatModel
public import MathlibExt.AlgebraicTopology.SimplicialSet.Countability
public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalAnodyneClass
public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyTestingFibrations
public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyTestingTwoOutOfThree
public import Mathlib.CategoryTheory.MorphismProperty.IsSmall

/-!
# Small countable testing representatives

Natural-number models and the actual value-universe Hom sets give a small
literal family of monic testing equivalences. Every countable testing arrow
is represented by an actual arrow isomorphism with both endpoint components.
The family index need not be countable.

This is the explicit countable-representative construction used with
Cisinski, Lemma 2.4.39 (2026), and Proposition 1.2.15 (2006).
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory
open scoped Simplicial

universe u

namespace SSet.joyalInterval

/-- A small literal family represents every monic testing equivalence
with countable endpoints, retaining both actual endpoint isomorphisms. -/
theorem exists_countable_testing_representatives :
    ∃ (Γ : Type u) (A B : Γ → SSet.{u}) (g : ∀ γ, A γ ⟶ B γ),
      MorphismProperty.IsSmall.{u} (MorphismProperty.ofHoms g) ∧
      (∀ γ, productPrecylinder.testingTrivialCofibrations auxiliaryAnodyneExtensions (g γ) ∧
        Countable (A γ).N ∧ Countable (B γ).N) ∧
      ∀ (X Y : SSet.{u}) (f : X ⟶ Y), Countable X.N → Countable Y.N →
        productPrecylinder.testingTrivialCofibrations auxiliaryAnodyneExtensions f →
        ∃ (γ : Γ) (eX : A γ ≅ X) (eY : B γ ≅ Y), eX.hom ≫ f = g γ ≫ eY.hom := by
  classical
  let T : MorphismProperty SSet.{u} :=
    productPrecylinder.testingTrivialCofibrations auxiliaryAnodyneExtensions
  let : (productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions).RespectsIso := by
    rw [productPrecylinder.testingEquivalences_eq_iInf_isomorphisms auxiliaryAnodyneExtensions]
    infer_instance
  let : T.RespectsIso := by
    change (MorphismProperty.monomorphisms SSet.{u} ⊓
      productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions).RespectsIso
    infer_instance
  let Γ : Type u := Σ M : NatModel, Σ N : NatModel,
    {k : M.toSSet.{u} ⟶ N.toSSet.{u} // T k}
  let A : Γ → SSet.{u} := fun γ => γ.1.toSSet.{u}
  let B : Γ → SSet.{u} := fun γ => γ.2.1.toSSet.{u}
  let g : ∀ γ : Γ, A γ ⟶ B γ := fun γ => γ.2.2.1
  let : Small.{u} Γ := inferInstance
  have hsmall : MorphismProperty.IsSmall.{u} (MorphismProperty.ofHoms g) :=
    MorphismProperty.isSmall_ofHoms g
  refine ⟨Γ, A, B, g, hsmall, ?_, ?_⟩
  · rintro ⟨M, N, k, hk⟩
    exact ⟨hk, M.countable_N_toSSet, N.countable_N_toSSet⟩
  · intro X Y f hX hY hf
    choose cX hcX using fun x ↦ @Countable.exists_injective_nat (X.obj x)
      (@countable_obj_of_countable_N X hX x)
    choose cY hcY using fun x ↦ @Countable.exists_injective_nat (Y.obj x)
      (@countable_obj_of_countable_N Y hY x)
    let M := NatModel.of X cX hcX
    let N := NatModel.of Y cY hcY
    let eX : M.toSSet.{u} ≅ X := NatModel.isoOf X cX hcX
    let eY : N.toSSet.{u} ≅ Y := NatModel.isoOf Y cY hcY
    let k : M.toSSet.{u} ⟶ N.toSSet.{u} := eX.hom ≫ f ≫ eY.inv
    have square : eX.hom ≫ f = k ≫ eY.hom := by
      simp only [k, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    let E : Arrow.mk k ≅ Arrow.mk f := Arrow.isoMk' k f eX eY square
    have hk : T k := (T.arrow_mk_iso_iff E).mpr hf
    exact ⟨⟨M, N, k, hk⟩, eX, eY, square⟩

end SSet.joyalInterval
