/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.FreeEvaluation

set_option autoImplicit false
noncomputable section
universe uA uV vV

namespace MathlibExtTest.EnrichedFreeEvaluation

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]

example (a : A) : EnrichedFunctorCat.Free.functor (V := V) a ⊣ EnrichedFunctorCat.evaluation (V := V) a :=
  EnrichedFunctorCat.Free.adjunction (V := V) a

example (a b : A) (X : V) :
    ((EnrichedFunctorCat.Free.functor a).obj X).toEnrichedFunctor.obj b =
      X ⊗ (a ⟶[V] b) := rfl

example (a b c : A) (X : V) :
    MonoidalClosed.uncurry
        (((EnrichedFunctorCat.Free.functor a).obj X).toEnrichedFunctor.map b c) =
      (α_ X (a ⟶[V] b) (b ⟶[V] c)).hom ≫ X ◁ eComp V a b c :=
  MonoidalClosed.uncurry_curry _

example (a b : A) {X Y : V} (f : X ⟶ Y) :
    EnrichedFunctorCat.component ((EnrichedFunctorCat.Free.functor a).map f) b =
      f ▷ (a ⟶[V] b) := EnrichedFunctorCat.Free.coefficientMap_component a f b

example (a : A) (X : V) (F : EnrichedFunctorCat V A)
    (f : X ⟶ F.toEnrichedFunctor.obj a) :
    EnrichedFunctorCat.Free.evaluate a X F (EnrichedFunctorCat.Free.extend a X F f) = f :=
  EnrichedFunctorCat.Free.evaluate_extend a X F f

example (a : A) (X : V) (F : EnrichedFunctorCat V A)
    (t : (EnrichedFunctorCat.Free.functor a).obj X ⟶ F) :
    EnrichedFunctorCat.Free.extend a X F (EnrichedFunctorCat.Free.evaluate a X F t) = t :=
  EnrichedFunctorCat.Free.extend_evaluate a X F t

example (a b : A) (X : V) (F : EnrichedFunctorCat V A)
    (t : (EnrichedFunctorCat.Free.functor a).obj X ⟶ F) :
    EnrichedFunctorCat.component t b =
      EnrichedFunctorCat.Free.extensionComponent a X F
        (EnrichedFunctorCat.Free.evaluate a X F t) b :=
  EnrichedFunctorCat.Free.reconstruct_component a X F t b

example (a : A) :
    (EnrichedFunctorCat.Free.adjunction (V := V) a).homEquiv = EnrichedFunctorCat.Free.homEquiv (V := V) a :=
  EnrichedFunctorCat.Free.adjunction_homEquiv a

#print axioms EnrichedFunctorCat.Free.object
#print axioms EnrichedFunctorCat.Free.extend
#print axioms EnrichedFunctorCat.Free.reconstruct_component
#print axioms EnrichedFunctorCat.Free.homEquiv
#print axioms EnrichedFunctorCat.Free.functor
#print axioms EnrichedFunctorCat.Free.adjunction

end MathlibExtTest.EnrichedFreeEvaluation
