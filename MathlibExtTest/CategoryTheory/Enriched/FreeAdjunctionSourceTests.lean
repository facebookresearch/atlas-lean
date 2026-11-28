/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.FreeAdjunctionSource

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uV vV uJ uC vC

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace FreeAdjunctionSourceTests

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {J : Type uJ} [EnrichedCategory V J]
  {C : Type uC} [Category.{vC} C]
  (E : C ≌ EnrichedFunctorCat V J) (a : J)
  (L : V ⥤ C) (R : C ⥤ V) (adj : L ⊣ R)
  (r : E.functor ⋙ EnrichedFunctorCat.evaluation a ≅ R)

open EnrichedFunctorCat.FreeAdjunctionSource

example : EnrichedFunctorCat.Free.functor (V := V) a ⋙ E.inverse ⊣
    E.functor ⋙ EnrichedFunctorCat.evaluation a := transported E a

example : EnrichedFunctorCat.Free.functor (V := V) a ⋙ E.inverse ⊣ R :=
  migrated E a R r

example : L ≅ EnrichedFunctorCat.Free.functor (V := V) a ⋙ E.inverse :=
  comparison E a L R adj r

example : L ⋙ E.functor ≅ EnrichedFunctorCat.Free.functor (V := V) a :=
  operatorIso E a L R adj r

example (X : V) :
    (nativeIso E a).hom.app X =
      E.counitIso.hom.app ((EnrichedFunctorCat.Free.functor a).obj X) :=
  nativeIso_hom_app E a X

example (X : V) :
    (nativeIso E a).inv.app X =
      E.counitIso.inv.app ((EnrichedFunctorCat.Free.functor a).obj X) :=
  nativeIso_inv_app E a X

example (X : V) :
    (nativeIso E a).hom.app X ≫ (nativeIso E a).inv.app X = 𝟙 _ :=
  (nativeIso E a).hom_inv_id_app X

example (X : V) :
    (operatorIso E a L R adj r).inv.app X =
      E.counitIso.inv.app ((EnrichedFunctorCat.Free.functor a).obj X) ≫
        E.functor.map ((comparison E a L R adj r).inv.app X) :=
  operatorIso_inv_app E a L R adj r X

example {X : V} {M : C}
    (f : E.inverse.obj ((EnrichedFunctorCat.Free.functor a).obj X) ⟶ M) :
    adj.homEquiv X M ((comparison E a L R adj r).hom.app X ≫ f) =
      (migrated E a R r).homEquiv X M f :=
  comparison_homEquiv E a L R adj r f

example {X : V} {M : C}
    (f : E.inverse.obj ((EnrichedFunctorCat.Free.functor a).obj X) ⟶ M) :
    (transported E a).homEquiv X M f =
      (EnrichedFunctorCat.Free.adjunction a).homEquiv X (E.functor.obj M)
        (E.counitIso.inv.app ((EnrichedFunctorCat.Free.functor a).obj X) ≫ E.functor.map f) :=
  transported_homEquiv E a f

example {X : V} {M : C} (f : L.obj X ⟶ M) :
    adj.homEquiv X M f ≫ r.inv.app M =
      EnrichedFunctorCat.Free.evaluate a X (E.functor.obj M)
        ((operatorIso E a L R adj r).inv.app X ≫ E.functor.map f) :=
  point E a L R adj r f

example (X : V) :
    (EnrichedFunctorCat.Free.functor a ⋙ E.inverse).map ((migrated E a R r).unit.app X) ≫
      (migrated E a R r).counit.app
        ((EnrichedFunctorCat.Free.functor a ⋙ E.inverse).obj X) = 𝟙 _ :=
  (migrated E a R r).left_triangle_components X

example (M : C) :
    (migrated E a R r).unit.app (R.obj M) ≫
      R.map ((migrated E a R r).counit.app M) = 𝟙 _ :=
  (migrated E a R r).right_triangle_components M

end FreeAdjunctionSourceTests
