/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module
public import MathlibExt.CategoryTheory.Monoidal.RightModuleFreeUnit
public import MathlibExt.CategoryTheory.Enriched.RightModuleFreeEvaluation
public import MathlibExt.CategoryTheory.Enriched.FreeAdjunctionSource

/-!
# Free units through enriched evaluation adjunctions

The original free enriched diagram and stock free-module adjunction identify
the source unit with the regular module. A genuine carrier equivalence and
evaluation comparison then give the entire operator free-unit isomorphism.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory MonoidalCategory Limits
open scoped MonoidalClosed

namespace CategoryTheory.Enriched.RightModuleFreeEvaluation.Unit

universe uV vV uI uJ
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V] {I : Type uI} [EnrichedCategory V I]
  [MonoidalCategory (EnrichedFunctorCat V I)]
  (S : EnrichedFunctorCat V I) [MonObj S]
open EnrichedFunctorCat CategoryTheory.Enriched.RightModuleFreeEvaluation

/-- The composed source free object is the original free-I object under the stock free functor. -/
theorem sourceFreeObjectEq (n : I) (X : V) :
    (Primitive.free S n).obj X =
      (RightModuleFree.functor S).obj (Free.object n X) := rfl

/-- An actual coefficient-unit comparison and the original Day unitor give the regular module. -/
def sourceFreeRegularIso (n : I) (X : V)
    (q : Free.object n X ≅ 𝟙_ (EnrichedFunctorCat V I)) :
    (Primitive.free S n).obj X ≅ RightModuleFree.regularObject S :=
  eqToIso (sourceFreeObjectEq S n X) ≪≫
    (RightModuleFree.functor S).mapIso q ≪≫ RightModuleFree.freeUnitRegularIso S

/-- The entire forward arrow retains the original object identification, free map and unitor. -/
theorem sourceFreeRegularIso_hom (n : I) (X : V)
    (q : Free.object n X ≅ 𝟙_ (EnrichedFunctorCat V I)) :
    (sourceFreeRegularIso S n X q).hom = eqToHom (sourceFreeObjectEq S n X) ≫
      (RightModuleFree.functor S).map q.hom ≫ (RightModuleFree.freeUnitRegularIso S).hom := rfl

/-- The inverse retains the inverse unitor, original inverse free map and object identification. -/
theorem sourceFreeRegularIso_inv (n : I) (X : V)
    (q : Free.object n X ≅ 𝟙_ (EnrichedFunctorCat V I)) :
    (sourceFreeRegularIso S n X q).inv = (RightModuleFree.freeUnitRegularIso S).inv ≫
      (RightModuleFree.functor S).map q.inv ≫ eqToHom (sourceFreeObjectEq S n X).symm :=
  Category.assoc (RightModuleFree.freeUnitRegularIso S).inv
    ((RightModuleFree.functor S).map q.inv) (eqToHom (sourceFreeObjectEq S n X).symm)

variable {J : Type uJ} [EnrichedCategory V J]

/-- The actual source free/evaluation adjunction and carrier comparison recognize the native
unit. -/
def regularUnitOperatorIso
    (e : CommutativeModuleConversion.RightModule S ≌ EnrichedFunctorCat V J)
    (n : I) (a : J)
    (q : Free.object n (𝟙_ V) ≅ 𝟙_ (EnrichedFunctorCat V I))
    (h : e.functor ⋙ EnrichedFunctorCat.evaluation a ≅ Primitive.evaluation S n) :
    e.functor.obj (RightModuleFree.regularObject S) ≅ Free.object a (𝟙_ V) :=
  e.functor.mapIso (sourceFreeRegularIso S n (𝟙_ V) q).symm ≪≫
    (FreeAdjunctionSource.operatorIso e a (Primitive.free S n)
      (Primitive.evaluation S n) (Primitive.adjunction S n) h).app (𝟙_ V)

/-- The whole forward native map uses the inverse source unit and original free comparison. -/
theorem regularUnitOperatorIso_hom
    (e : CommutativeModuleConversion.RightModule S ≌ EnrichedFunctorCat V J)
    (n : I) (a : J)
    (q : Free.object n (𝟙_ V) ≅ 𝟙_ (EnrichedFunctorCat V I))
    (h : e.functor ⋙ EnrichedFunctorCat.evaluation a ≅ Primitive.evaluation S n) :
    (regularUnitOperatorIso S e n a q h).hom =
      e.functor.map (sourceFreeRegularIso S n (𝟙_ V) q).inv ≫
        (FreeAdjunctionSource.operatorIso e a (Primitive.free S n)
          (Primitive.evaluation S n) (Primitive.adjunction S n) h).hom.app (𝟙_ V) := rfl

/-- The whole inverse uses the original inverse free comparison and actual forward source unit. -/
theorem regularUnitOperatorIso_inv
    (e : CommutativeModuleConversion.RightModule S ≌ EnrichedFunctorCat V J)
    (n : I) (a : J)
    (q : Free.object n (𝟙_ V) ≅ 𝟙_ (EnrichedFunctorCat V I))
    (h : e.functor ⋙ EnrichedFunctorCat.evaluation a ≅ Primitive.evaluation S n) :
    (regularUnitOperatorIso S e n a q h).inv =
      (FreeAdjunctionSource.operatorIso e a (Primitive.free S n)
        (Primitive.evaluation S n) (Primitive.adjunction S n) h).inv.app (𝟙_ V) ≫
          e.functor.map (sourceFreeRegularIso S n (𝟙_ V) q).hom := rfl

end CategoryTheory.Enriched.RightModuleFreeEvaluation.Unit
