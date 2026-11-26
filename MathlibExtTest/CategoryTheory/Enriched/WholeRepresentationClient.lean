/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Codex
import MathlibExt.CategoryTheory.Enriched.WholeRepresentationEquivalence
import Batteries.Tactic.Lint

set_option autoImplicit false

noncomputable section

universe uV vV uC

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.WholeRepresentationClient

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C]

example : WholeRepresentation V C ≌ WholeEnrichedFunctor V C := WholeRepresentation.enrichedEquivalence

example (X : WholeRepresentation V C) (x y : C) :
    (WholeRepresentation.toWholeEnrichedFunctors.obj X).functor.map x y =
      MonoidalClosed.curry (X.action x y) := rfl

example (F : WholeEnrichedFunctor V C) (x y : C) :
    (WholeRepresentation.fromWholeEnrichedFunctors.obj F).action x y =
      MonoidalClosed.uncurry (F.functor.map x y) := rfl

example {X Y : WholeRepresentation V C} (f : X ⟶ Y) (x y : C) :
    (WholeRepresentation.toWholeEnrichedFunctors.obj X).functor.map x y ≫
        (ihom (X.obj x)).map (f.app y) =
      (WholeRepresentation.toWholeEnrichedFunctors.obj Y).functor.map x y ≫
        (MonoidalClosed.pre (f.app x)).app (Y.obj y) :=
  (WholeRepresentation.toWholeEnrichedFunctors.map f).naturality x y

example {F G : WholeEnrichedFunctor V C} (f : F ⟶ G) (x y : C) :
    f.app x ▷ (x ⟶[V] y) ≫
        (WholeRepresentation.fromWholeEnrichedFunctors.obj G).action x y =
      (WholeRepresentation.fromWholeEnrichedFunctors.obj F).action x y ≫ f.app y := f.comm x y

example (X : WholeRepresentation V C) :
    WholeRepresentation.ofEnrichedFunctor X.toEnrichedFunctor = X := WholeRepresentation.of_to X

example (F : EnrichedFunctor V C V) :
    (WholeRepresentation.ofEnrichedFunctor F).toEnrichedFunctor = F := WholeRepresentation.to_of F

example (X : WholeRepresentation V C) (x y : C) :
    (WholeRepresentation.enrichedEquivalence.inverse.obj
      (WholeRepresentation.enrichedEquivalence.functor.obj X)).action x y = X.action x y :=
  WholeRepresentation.enrichedEquivalence_action X x y

example (F : WholeEnrichedFunctor V C) (x y : C) :
    (WholeRepresentation.enrichedEquivalence.functor.obj
      (WholeRepresentation.enrichedEquivalence.inverse.obj F)).functor.map x y = F.functor.map x y :=
  WholeRepresentation.enrichedEquivalence_map F x y

example {X Y : WholeRepresentation V C} (f : X ⟶ Y) (x : C) :
    (WholeRepresentation.fromWholeEnrichedFunctors.map
      (WholeRepresentation.toWholeEnrichedFunctors.map f)).app x = f.app x := rfl

example {F G : WholeEnrichedFunctor V C} (f : F ⟶ G) (x : C) :
    (WholeRepresentation.toWholeEnrichedFunctors.map
      (WholeRepresentation.fromWholeEnrichedFunctors.map f)).app x = f.app x := rfl

example (X : WholeRepresentation V C) (x : C) :
    (WholeRepresentation.enrichedUnitIso.hom.app X).app x = 𝟙 (X.obj x) :=
  WholeRepresentation.enrichedUnitIso_hom_app X x

example (X : WholeRepresentation V C) (x : C) :
    (WholeRepresentation.enrichedUnitIso.inv.app X).app x = 𝟙 (X.obj x) :=
  WholeRepresentation.enrichedUnitIso_inv_app X x

example (F : WholeEnrichedFunctor V C) (x : C) :
    (WholeRepresentation.enrichedCounitIso.hom.app F).app x = 𝟙 (F.functor.obj x) :=
  WholeRepresentation.enrichedCounitIso_hom_app F x

example (F : WholeEnrichedFunctor V C) (x : C) :
    (WholeRepresentation.enrichedCounitIso.inv.app F).app x = 𝟙 (F.functor.obj x) :=
  WholeRepresentation.enrichedCounitIso_inv_app F x

end CategoryTheory.WholeRepresentationClient

#lint only unusedArguments in MathlibExt.CategoryTheory.Enriched.WholeRepresentationData
#lint only unusedArguments in MathlibExt.CategoryTheory.Enriched.WholeRepresentationCurry
#lint only unusedArguments in MathlibExt.CategoryTheory.Enriched.WholeRepresentationFunctor
#lint only unusedArguments in MathlibExt.CategoryTheory.Enriched.WholeRepresentationEquivalence

#print axioms CategoryTheory.WholeRepresentation.instCategory
#print axioms CategoryTheory.WholeRepresentation.id_app
#print axioms CategoryTheory.WholeRepresentation.comp_app
#print axioms CategoryTheory.WholeRepresentation.hom_ext
#print axioms CategoryTheory.WholeRepresentation.toEnrichedFunctor
#print axioms CategoryTheory.WholeRepresentation.ofEnrichedFunctor
#print axioms CategoryTheory.WholeRepresentation.toEnrichedFunctor_obj
#print axioms CategoryTheory.WholeRepresentation.toEnrichedFunctor_map
#print axioms CategoryTheory.WholeRepresentation.of_to_action
#print axioms CategoryTheory.WholeRepresentation.to_of_map
#print axioms CategoryTheory.WholeEnrichedFunctor.Hom.comm
#print axioms CategoryTheory.WholeEnrichedFunctor.Hom.ofAction
#print axioms CategoryTheory.WholeEnrichedFunctor.instCategory
#print axioms CategoryTheory.WholeEnrichedFunctor.id_app
#print axioms CategoryTheory.WholeEnrichedFunctor.comp_app
#print axioms CategoryTheory.WholeEnrichedFunctor.hom_ext
#print axioms CategoryTheory.WholeRepresentation.toWholeEnrichedFunctors
#print axioms CategoryTheory.WholeRepresentation.fromWholeEnrichedFunctors
#print axioms CategoryTheory.WholeRepresentation.enrichedUnitIsoApp
#print axioms CategoryTheory.WholeRepresentation.enrichedCounitIsoApp
#print axioms CategoryTheory.WholeRepresentation.enrichedUnitIso
#print axioms CategoryTheory.WholeRepresentation.enrichedCounitIso
#print axioms CategoryTheory.WholeRepresentation.enrichedEquivalence
#print axioms CategoryTheory.WholeRepresentation.toWholeEnrichedFunctors_obj
#print axioms CategoryTheory.WholeRepresentation.fromWholeEnrichedFunctors_obj
#print axioms CategoryTheory.WholeRepresentation.toWholeEnrichedFunctors_map_app
#print axioms CategoryTheory.WholeRepresentation.fromWholeEnrichedFunctors_map_app
#print axioms CategoryTheory.WholeRepresentation.enrichedEquivalence_action
#print axioms CategoryTheory.WholeRepresentation.enrichedEquivalence_map
#print axioms CategoryTheory.WholeRepresentation.of_to
#print axioms CategoryTheory.WholeRepresentation.to_of
#print axioms CategoryTheory.WholeRepresentation.enrichedUnitIso_hom_app
#print axioms CategoryTheory.WholeRepresentation.enrichedUnitIso_inv_app
#print axioms CategoryTheory.WholeRepresentation.enrichedCounitIso_hom_app
#print axioms CategoryTheory.WholeRepresentation.enrichedCounitIso_inv_app
