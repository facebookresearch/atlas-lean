/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialPresheaf.InnerMapping
public import Lean.Meta.Instances

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalClosed MonoidalCategory Opposite
open scoped MonoidalClosed Simplicial

attribute [local instance] SimplicialPresheaf.scalarEnrichment

run_cmd do
  let env ← Lean.getEnv
  if Lean.Meta.isInstanceCore env ``SimplicialPresheaf.hasEnd then
    throwError "The generic end-existence constructor must remain explicit."
  if Lean.Meta.isInstanceCore env ``SimplicialPresheaf.hasFunctorEnrichedHom then
    throwError "The generic enriched-Hom constructor must remain explicit."

namespace SimplicialPresheaf.InnerMappingTest

variable {D : Type w} [Category.{v} D] [Small.{u} D] [LocallySmall.{u} D]

section OriginalGenericIndex

variable {J : Type w} [Category.{v} J] [Small.{u} J] [LocallySmall.{u} J]

example (F : Jᵒᵖ ⥤ J ⥤ SSet.{u}) : HasEnd F := SimplicialPresheaf.hasEnd F

example (A Z : J ⥤ SSet.{u}) :
    Enriched.FunctorCategory.HasFunctorEnrichedHom SSet.{u} A Z :=
  SimplicialPresheaf.hasFunctorEnrichedHom A Z

end OriginalGenericIndex

example (A Z : SimplicialPresheaf.{u} D) : SSet.{u} := innerHom A Z

example {A B : SimplicialPresheaf.{u} D} (f : A ⟶ B)
    (Z : SimplicialPresheaf.{u} D) (g : B ⟶ Z) :
    (innerHomPre f Z).app (op ⦋0⦌) (innerHomHomEquiv B Z g) =
      innerHomHomEquiv A Z (f ≫ g) := innerHomHomEquiv_precomp f Z g

example (A : SimplicialPresheaf.{u} D) {Z Z' : SimplicialPresheaf.{u} D}
    (g : Z ⟶ Z') (f : A ⟶ Z) :
    (innerHomPost A g).app (op ⦋0⦌) (innerHomHomEquiv A Z f) =
      innerHomHomEquiv A Z' (f ≫ g) := innerHomHomEquiv_postcomp A g f

example {A B Z Z' : SimplicialPresheaf.{u} D} (f : A ⟶ B) (g : B ⟶ Z)
    (h : Z ⟶ Z') :
    (innerHomPost A h).app (op ⦋0⦌)
        ((innerHomPre f Z).app (op ⦋0⦌) (innerHomHomEquiv B Z g)) =
      innerHomHomEquiv A Z' (f ≫ g ≫ h) := by
  simp only [innerHomHomEquiv_precomp, innerHomHomEquiv_postcomp, Category.assoc]

example (A Z : SimplicialPresheaf.{u} D) {d e : Dᵒᵖ} (g : d ⟶ e) :
    innerHomπ A Z d ≫ (ihom (A.obj d)).map (Z.map g) =
      innerHomπ A Z e ≫ (pre (A.map g)).app (Z.obj e) := innerHom_condition A Z g

example (A : SimplicialPresheaf.{u} D) :
    scalarTensor.obj A ⊣ innerHomFunctor.obj (op A) := scalarTensorHomAdjunction A

example (A Z : SimplicialPresheaf.{u} D) (d : Dᵒᵖ) :
    ((scalarTensorHomAdjunction A).counit.app Z).app d = uncurry (innerHomπ A Z d) :=
  scalarTensorHomAdjunction_counit_app A Z d

example (K : SSet.{u}) : scalarTensorFixed (D := D) K ⊣ (scalarCotensor (D := D)).obj (op K) :=
  scalarTensorCotensorAdjunction K

example (K : SSet.{u}) (Z : SimplicialPresheaf.{u} D) {d e : Dᵒᵖ} (g : d ⟶ e) :
    ((scalarCotensor.obj (op K)).obj Z).map g = (ihom K).map (Z.map g) :=
  scalarCotensor_site_map K Z g

example (d : D) (K : SSet.{u}) (Z : SimplicialPresheaf.{u} D) :
    ((discreteYoneda.obj d ⊗ (CategoryTheory.Functor.const Dᵒᵖ).obj K) ⟶ Z) ≃
      (K ⟶ Z.obj (op d)) := discreteYonedaTensorHomEquiv d K Z

example (A Z : SimplicialPresheaf.{u} D) (d : Dᵒᵖ) :
    (exponential A Z).obj d = innerHom (discreteYoneda.obj d.unop ⊗ A) Z := exponential_obj A Z d

example (A : SimplicialPresheaf.{u} D) : tensorLeft A ⊣ exponentialFunctor A := exponentialAdjunction A

example (A Z : SimplicialPresheaf.{u} D) {Δ Δ' : SimplexCategoryᵒᵖ} (δ : Δ ⟶ Δ')
    (x : (innerHom A Z).obj Δ) :
    innerHomSimplexEquiv A Z Δ' ((innerHom A Z).map δ x) =
      (scalarTensor.obj A).map (SSet.stdSimplex.map δ.unop) ≫ innerHomSimplexEquiv A Z Δ x :=
  innerHomSimplexEquiv_operator A Z δ x

example (A Z : SimplicialPresheaf.{u} D) :
    innerHom A Z ≅ innerHom ((smallModelTransport (D := D)).functor.obj A)
      ((smallModelTransport (D := D)).functor.obj Z) := innerHomSmallModelIso A Z

example : SimplicialPresheaf.{u} D ≌ ForgetEnrichment SSet.{u} (SimplicialPresheaf.{u} D) :=
  enrichedCarrierEquivalence

example : SimplicialCategory (ForgetEnrichment SSet.{u} (SimplicialPresheaf.{u} D)) :=
  enrichedCarrierSimplicialCategory

example (f : Arrow (SimplicialPresheaf.{u} D)) :
    let E := enrichedCarrierEquivalence (D := D)
    let F := CategoryTheory.Functor.mapArrowEquivalence E
    (F.unitIso.app f).hom.left ≫ E.inverse.map (E.functor.map f.hom) =
      f.hom ≫ (F.unitIso.app f).hom.right := (enrichedCarrier_arrow_unit f).2.2

example (A : SimplicialPresheaf.{u} (Discrete PEmpty)) :
    tensorLeft A ⊣ exponentialFunctor A := exponentialAdjunction A

end SimplicialPresheaf.InnerMappingTest
