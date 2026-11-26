/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialPresheaf.Basic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v w v' w'

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits MonoidalCategory Opposite

namespace MathlibExtTest.SimplicialPresheaf

variable {D : Type w} [Category.{v} D] {E : Type w'} [Category.{v'} E]

example : SimplicialPresheaf.{u} D = (Dᵒᵖ ⥤ SSet.{u}) := rfl

example {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y) :
    f ≫ 𝟙 Y = f := Category.comp_id f

example (X Y : SimplicialPresheaf.{u} D) (a : Dᵒᵖ) (n : SimplexCategoryᵒᵖ) :
    ((X ⊗ Y).obj a).obj n = ((X.obj a).obj n × (Y.obj a).obj n) :=
  SimplicialPresheaf.product_obj X Y a n

example (X : SimplicialPresheaf.{u} D) (K : SSet.{u})
    (a : Dᵒᵖ) (n : SimplexCategoryᵒᵖ) :
    (((SimplicialPresheaf.scalarTensor.obj X).obj K).obj a).obj n =
      ((X.obj a).obj n × K.obj n) :=
  SimplicialPresheaf.scalarTensor_obj X K a n

example {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y) (K : SSet.{u}) (a : Dᵒᵖ) :
    ((SimplicialPresheaf.scalarTensor.map f).app K).app a = f.app a ▷ K :=
  SimplicialPresheaf.scalarTensor_presheaf_map f K a

example (X : SimplicialPresheaf.{u} D) {K L : SSet.{u}} (g : K ⟶ L) (a : Dᵒᵖ) :
    ((SimplicialPresheaf.scalarTensor.obj X).map g).app a = X.obj a ◁ g :=
  SimplicialPresheaf.scalarTensor_scalar_map X g a

section Representables

variable [LocallySmall.{u} D]

example (d : D) (a : Dᵒᵖ) (n : SimplexCategoryᵒᵖ) :
    (((SimplicialPresheaf.discreteYoneda.{u}.obj d).obj a).obj n) ≃ (a.unop ⟶ d) :=
  SimplicialPresheaf.discreteYonedaObjEquiv d a n

example (d : D) {a b : Dᵒᵖ} (g : a ⟶ b) (n : SimplexCategoryᵒᵖ)
    (h : ((SimplicialPresheaf.discreteYoneda.{u}.obj d).obj a).obj n) :
    SimplicialPresheaf.discreteYonedaObjEquiv d b n
        (((SimplicialPresheaf.discreteYoneda.{u}.obj d).map g).app n h) =
      g.unop ≫ SimplicialPresheaf.discreteYonedaObjEquiv d a n h :=
  SimplicialPresheaf.discreteYoneda_obj_map d g n h

example {d d' : D} (t : d ⟶ d') (a : Dᵒᵖ) (n : SimplexCategoryᵒᵖ)
    (h : ((SimplicialPresheaf.discreteYoneda.{u}.obj d).obj a).obj n) :
    SimplicialPresheaf.discreteYonedaObjEquiv d' a n
        (((SimplicialPresheaf.discreteYoneda.{u}.map t).app a).app n h) =
      SimplicialPresheaf.discreteYonedaObjEquiv d a n h ≫ t :=
  SimplicialPresheaf.discreteYoneda_map_app t a n h

end Representables

example (e : D ≌ E) (X : SimplicialPresheaf.{u} D) :
    (SimplicialPresheaf.transport e).functor.obj X = e.inverse.op ⋙ X :=
  SimplicialPresheaf.transport_functor_obj e X

example (e : D ≌ E) {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y) (a : Eᵒᵖ) :
    ((SimplicialPresheaf.transport e).functor.map f).app a =
      f.app (e.inverse.op.obj a) :=
  SimplicialPresheaf.transport_functor_map_app e f a

example (e : D ≌ E) (X : SimplicialPresheaf.{u} D) (a : Dᵒᵖ) :
    ((SimplicialPresheaf.transport e).unitIso.app X).hom.app a =
      X.map (e.op.unitIso.app a).hom :=
  SimplicialPresheaf.transport_unit_app e X a

example (e : D ≌ E) (X : SimplicialPresheaf.{u} E) (a : Eᵒᵖ) :
    ((SimplicialPresheaf.transport e).counitIso.app X).hom.app a =
      X.map (e.op.counitIso.app a).hom :=
  SimplicialPresheaf.transport_counit_app e X a

example (e : D ≌ E) (f : Arrow (SimplicialPresheaf.{u} D)) :
    let A := Functor.mapArrowEquivalence (SimplicialPresheaf.transport e)
    (A.unitIso.app f).hom.left ≫
        (SimplicialPresheaf.transport e).inverse.map
          ((SimplicialPresheaf.transport e).functor.map f.hom) =
      f.hom ≫ (A.unitIso.app f).hom.right :=
  (SimplicialPresheaf.transport_arrow_unit e f).2.2

example (e : D ≌ E) (f : Arrow (SimplicialPresheaf.{u} E)) :
    let A := Functor.mapArrowEquivalence (SimplicialPresheaf.transport e)
    (A.counitIso.app f).hom.left ≫ f.hom =
      (SimplicialPresheaf.transport e).functor.map
          ((SimplicialPresheaf.transport e).inverse.map f.hom) ≫
        (A.counitIso.app f).hom.right :=
  (SimplicialPresheaf.transport_arrow_counit e f).2.2

example [Small.{u} D] [LocallySmall.{u} D] :
    SimplicialPresheaf.{u} D ≌ SimplicialPresheaf.{u} (SmallModel.{u} D) :=
  SimplicialPresheaf.smallModelTransport

example [LocallySmall.{u} D] :
    letI : Category.{u} (ShrinkHoms D) := inferInstance
    SimplicialPresheaf.{u} D ≌ SimplicialPresheaf.{u} (ShrinkHoms D) :=
  SimplicialPresheaf.homShrinkTransport

example [Small.{u} D] [LocallySmall.{u} D] : LocallySmall.{u} (SimplicialPresheaf.{u} D) :=
  SimplicialPresheaf.locallySmall

example [LocallySmall.{u} D] [LocallySmall.{u} E] (e : D ≌ E) :
    SimplicialPresheaf.discreteYoneda.{u} ⋙ (SimplicialPresheaf.transport e).functor ≅
      e.functor ⋙ SimplicialPresheaf.discreteYoneda.{u} :=
  SimplicialPresheaf.transportDiscreteYoneda e

end MathlibExtTest.SimplicialPresheaf
