/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.FreeMappingSource

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uV vV uA uJ uC vC

open CategoryTheory MonoidalCategory Opposite
open scoped MonoidalClosed

namespace FreeMappingSourcePointFunctionTests

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} {J : Type uJ} [EnrichedCategory V J]
  {C : Type uC} [Category.{vC} C]
  (index : A → J) (F : A → C) (U : C ⥤ EnrichedFunctorCat V J)
  (q : ∀ a, U.obj (F a) ≅ EnrichedFunctorCat.Free.object (index a) (𝟙_ V))

open EnrichedFunctorCat.FreeMappingSource

example (a b : A) :
    HEq (fun f : InducedCategory.Hom (F := fun a => op (F a)) a b =>
      (functor index F U q).map f)
        (fun f : InducedCategory.Hom (F := fun a => op (F a)) a b =>
          ForgetEnrichment.homOf V
            (EnrichedFunctorCat.FreeYoneda.evaluateHom (index a) (index b)
              ((q b).inv ≫ U.map f.hom.unop ≫ (q a).hom))) :=
  functor_map_function index F U q a b

example (a b : A) :
    HEq (fun f : InducedCategory.Hom (F := fun a => op (F a)) a b =>
      ForgetEnrichment.homTo V ((functor index F U q).map f))
        (fun f : InducedCategory.Hom (F := fun a => op (F a)) a b =>
          EnrichedFunctorCat.FreeYoneda.evaluateHom (index a) (index b)
            ((q b).inv ≫ U.map f.hom.unop ≫ (q a).hom)) :=
  functor_point_function index F U q a b

example {a b : A} (f : InducedCategory.Hom (F := fun a => op (F a)) a b) :
    HEq ((functor index F U q).map f)
      (ForgetEnrichment.homOf V
        (EnrichedFunctorCat.FreeYoneda.evaluateHom (index a) (index b)
          ((q b).inv ≫ U.map f.hom.unop ≫ (q a).hom))) :=
  functor_map index F U q f

example {a b : A} (f : InducedCategory.Hom (F := fun a => op (F a)) a b) :
    HEq (ForgetEnrichment.homTo V ((functor index F U q).map f))
      (EnrichedFunctorCat.FreeYoneda.evaluateHom (index a) (index b)
        ((q b).inv ≫ U.map f.hom.unop ≫ (q a).hom)) :=
  functor_point index F U q f

example {a b : A} {Z : V}
    (f : InducedCategory.Hom (F := fun a => op (F a)) a b)
    (r : (index a ⟶[V] index b) ⟶ Z) :
    ForgetEnrichment.homTo V ((functor index F U q).map f) ≫
      eqToHom (functor_hom_eq index F U q a b) ≫ r =
        EnrichedFunctorCat.FreeYoneda.evaluateHom (index a) (index b)
          ((q b).inv ≫ U.map f.hom.unop ≫ (q a).hom) ≫ r :=
  functor_point_rebased_assoc index F U q f r

example (a : A) :
    (functor index F U q).map
      (𝟙 (show InducedCategory Cᵒᵖ (fun a => op (F a)) from a)) =
        𝟙 ((functor index F U q).obj a) :=
  (functor index F U q).map_id a

example {a b c : A}
    (f : InducedCategory.Hom (F := fun a => op (F a)) a b)
    (g : InducedCategory.Hom (F := fun a => op (F a)) b c) :
    (functor index F U q).map (f ≫ g) =
      (functor index F U q).map f ≫ (functor index F U q).map g :=
  (functor index F U q).map_comp f g

example (a b : A) :
    (fun f : InducedCategory.Hom (F := fun a => op (F a)) a b =>
      ForgetEnrichment.homTo V ((functor index F U q).map f) ≫
        eqToHom (functor_hom_eq index F U q a b)) =
          (fun f : InducedCategory.Hom (F := fun a => op (F a)) a b =>
            EnrichedFunctorCat.FreeYoneda.evaluateHom (index a) (index b)
              ((q b).inv ≫ U.map f.hom.unop ≫ (q a).hom)) :=
  functor_point_function_rebased index F U q a b

end FreeMappingSourcePointFunctionTests
