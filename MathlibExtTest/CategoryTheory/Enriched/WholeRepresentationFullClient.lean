/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Codex
import MathlibExt.CategoryTheory.Enriched.WholeRepresentationFreeComparison
import MathlibExtTest.CategoryTheory.Enriched.WholeRepresentationClient
import Batteries.Tactic.Lint

set_option autoImplicit false

noncomputable section

universe uV vV uC

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.WholeRepresentationFullClient

open WholeRepresentation WholeRepresentation.FreeEvaluation

local notation "eval" => WholeRepresentation.FreeEvaluation.evaluation

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {C : Type uC} [EnrichedCategory V C]

section Monoidal

example (n k : C) (K : V) : (freeObject n K).obj k = K ⊗ (n ⟶[V] k) := freeObject_obj n k K

example (n k l : C) (K : V) :
    (freeObject n K).action k l = (α_ K (n ⟶[V] k) (k ⟶[V] l)).hom ≫ K ◁ eComp V n k l :=
  freeObject_action n k l K

example (n k : C) {K L : V} (h : K ⟶ L) : ((freeAt n).map h).app k = h ▷ (n ⟶[V] k) :=
  freeAt_map_app n k h

example (n : C) (X : WholeRepresentation V C) : (eval n).obj X = X.obj n := evaluation_obj n X

example (n : C) {X Y : WholeRepresentation V C} (f : X ⟶ Y) : (eval n).map f = f.app n :=
  evaluation_map n f

end Monoidal

section Closed

variable [MonoidalClosed V] [BraidedCategory V]

example : WholeRepresentation V C ≌ EnrichedFunctorCat V C := genuineEquivalence

example (X : WholeRepresentation V C) (x y : C) :
    (toGenuineFunctors.obj X).toEnrichedFunctor.map x y = MonoidalClosed.curry (X.action x y) :=
  toGenuineFunctors_map X x y

example (F : EnrichedFunctorCat V C) (x y : C) :
    (fromGenuineFunctors.obj F).action x y = MonoidalClosed.uncurry (F.toEnrichedFunctor.map x y) := rfl

example {X Y : WholeRepresentation V C} (f : X ⟶ Y) (x : C) :
    EnrichedFunctorCat.component (toGenuineFunctors.map f) x = f.app x :=
  toGenuineFunctors_map_component f x

example {F G : EnrichedFunctorCat V C} (f : F ⟶ G) (x : C) :
    (fromGenuineFunctors.map f).app x = EnrichedFunctorCat.component f x := fromGenuineFunctors_map_app f x

example (X : WholeRepresentation V C) : genuineEquivalence.inverse.obj
    (genuineEquivalence.functor.obj X) = X := genuineEquivalence_representation X

example (F : EnrichedFunctorCat V C) : (genuineEquivalence.functor.obj
    (genuineEquivalence.inverse.obj F)).toEnrichedFunctor = F.toEnrichedFunctor :=
  genuineEquivalence_toEnrichedFunctor F

example (X : WholeRepresentation V C) (x : C) : (genuineUnitIso.hom.app X).app x = 𝟙 (X.obj x) :=
  genuineUnitIsoApp_hom_app X x

example (X : WholeRepresentation V C) (x : C) : (genuineUnitIso.inv.app X).app x = 𝟙 (X.obj x) := rfl

example (F : EnrichedFunctorCat V C) (x : C) :
    EnrichedFunctorCat.component (genuineCounitIso.hom.app F) x = 𝟙 (F.toEnrichedFunctor.obj x) :=
  genuineCounitHom_component F x

example (F : EnrichedFunctorCat V C) (x : C) :
    EnrichedFunctorCat.component (genuineCounitIso.inv.app F) x = 𝟙 (F.toEnrichedFunctor.obj x) :=
  genuineCounitInv_component F x

example {X Y : WholeRepresentation V C} (f : X ⟶ Y) (x : C) :
    (fromGenuineFunctors.map (toGenuineFunctors.map f)).app x = f.app x :=
  toGenuineFunctors_map_component f x

example {F G : EnrichedFunctorCat V C} (f : F ⟶ G) (x : C) :
    EnrichedFunctorCat.component (toGenuineFunctors.map (fromGenuineFunctors.map f)) x =
      EnrichedFunctorCat.component f x :=
  (toGenuineFunctors_map_component (fromGenuineFunctors.map f) x).trans (fromGenuineFunctors_map_app f x)

example (n : C) : freeAt (V := V) n ⊣ eval n := adjunction n

example (n k : C) (K : V) (X : WholeRepresentation V C) (h : K ⟶ X.obj n) :
    ((homEquiv n K X).symm h).app k = h ▷ (n ⟶[V] k) ≫ X.action n k := extend_app n k K X h

example (n : C) (K : V) (X : WholeRepresentation V C) (f : freeObject n K ⟶ X) :
    homEquiv n K X f = (ρ_ K).inv ≫ (K ◁ eId V n) ≫ f.app n := rfl

example (n : C) (K : V) (X : WholeRepresentation V C) (h : K ⟶ X.obj n) :
    evaluate n K X (extend n K X h) = h := evaluate_extend n K X h

example (n : C) (K : V) (X : WholeRepresentation V C) (f : freeObject n K ⟶ X) :
    extend n K X (evaluate n K X f) = f := extend_evaluate n K X f

example (n : C) (K : V) : (adjunction (V := V) n).unit.app K = (ρ_ K).inv ≫ (K ◁ eId V n) :=
  adjunction_unit n K

example (n k : C) (X : WholeRepresentation V C) :
    ((adjunction (V := V) n).counit.app X).app k = X.action n k := adjunction_counit_app n k X

example (n : C) (K : V) : (EnrichedFunctorCat.Free.adjunction (V := V) n).unit.app K =
    (adjunction (V := V) n).unit.app K := genuine_unit n K

example (n : C) (X : WholeRepresentation V C) : toGenuineFunctors.map
    ((adjunction (V := V) n).counit.app X) =
      (EnrichedFunctorCat.Free.adjunction (V := V) n).counit.app (genuineObject X) := genuine_counit n X

example (n : C) (K : V) : (freeAt n).map ((adjunction (V := V) n).unit.app K) ≫
    (adjunction (V := V) n).counit.app ((freeAt n).obj K) = 𝟙 ((freeAt n).obj K) := free_triangle n K

example (n : C) (X : WholeRepresentation V C) : (adjunction (V := V) n).unit.app ((eval n).obj X) ≫
    (eval n).map ((adjunction (V := V) n).counit.app X) = 𝟙 ((eval n).obj X) :=
  evaluation_triangle n X

example (n : C) (K : V) (X : WholeRepresentation V C) (f : freeObject n K ⟶ X) :
    (adjunction (V := V) n).homEquiv K X f =
      (EnrichedFunctorCat.Free.adjunction (V := V) n).homEquiv K (genuineObject X) (genuineMap f) :=
  adjunction_hom_genuine n K X f

example (n : C) (K : V) (X : WholeRepresentation V C) (h : K ⟶ X.obj n) :
    genuineMap (((adjunction (V := V) n).homEquiv K X).symm h) =
      ((EnrichedFunctorCat.Free.adjunction (V := V) n).homEquiv K (genuineObject X)).symm h :=
  adjunction_hom_inverse_genuine n K X h

example (n k : C) (K : V) : EnrichedFunctorCat.component ((genuineFreeIso n).hom.app K) k =
    𝟙 (K ⊗ (n ⟶[V] k)) := genuineFreeIso_hom_component n k K

example (n k : C) (K : V) : EnrichedFunctorCat.component ((genuineFreeIso n).inv.app K) k =
    𝟙 (K ⊗ (n ⟶[V] k)) := genuineFreeIso_inv_component n k K

example (n : C) (X : WholeRepresentation V C) : (genuineEvaluationIso n).hom.app X = 𝟙 (X.obj n) :=
  genuineEvaluationIso_hom_app n X

example (n : C) (X : WholeRepresentation V C) : (genuineEvaluationIso n).inv.app X = 𝟙 (X.obj n) :=
  genuineEvaluationIso_inv_app n X

end Closed

end CategoryTheory.WholeRepresentationFullClient

#lint only unusedArguments in MathlibExt.CategoryTheory.Enriched.WholeRepresentationCurry
#lint only unusedArguments in MathlibExt.CategoryTheory.Enriched.WholeRepresentationData
#lint only unusedArguments in MathlibExt.CategoryTheory.Enriched.WholeRepresentationEquivalence
#lint only unusedArguments in MathlibExt.CategoryTheory.Enriched.WholeRepresentationFreeComparison
#lint only unusedArguments in MathlibExt.CategoryTheory.Enriched.WholeRepresentationFreeEvaluation
#lint only unusedArguments in MathlibExt.CategoryTheory.Enriched.WholeRepresentationFreeObject
#lint only unusedArguments in MathlibExt.CategoryTheory.Enriched.WholeRepresentationFunctor
#lint only unusedArguments in MathlibExt.CategoryTheory.Enriched.WholeRepresentationGenuine

#print axioms CategoryTheory.WholeRepresentation.toEnrichedFunctor
#print axioms CategoryTheory.WholeRepresentation.ofEnrichedFunctor
#print axioms CategoryTheory.WholeRepresentation.toEnrichedFunctor_obj
#print axioms CategoryTheory.WholeRepresentation.toEnrichedFunctor_map
#print axioms CategoryTheory.WholeRepresentation.of_to_action
#print axioms CategoryTheory.WholeRepresentation.to_of_map
#print axioms CategoryTheory.WholeRepresentation
#print axioms CategoryTheory.WholeRepresentation.Hom
#print axioms CategoryTheory.WholeRepresentation.instCategory
#print axioms CategoryTheory.WholeRepresentation.id_app
#print axioms CategoryTheory.WholeRepresentation.comp_app
#print axioms CategoryTheory.WholeRepresentation.hom_ext
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
#print axioms CategoryTheory.WholeRepresentation.FreeEvaluation.genuineFreeIso
#print axioms CategoryTheory.WholeRepresentation.FreeEvaluation.genuineEvaluationIso
#print axioms CategoryTheory.WholeRepresentation.FreeEvaluation.genuineFreeIso_hom_component
#print axioms CategoryTheory.WholeRepresentation.FreeEvaluation.genuineFreeIso_inv_component
#print axioms CategoryTheory.WholeRepresentation.FreeEvaluation.genuineEvaluationIso_hom_app
#print axioms CategoryTheory.WholeRepresentation.FreeEvaluation.genuineEvaluationIso_inv_app
#print axioms CategoryTheory.WholeRepresentation.FreeEvaluation.adjunction_unit
#print axioms CategoryTheory.WholeRepresentation.FreeEvaluation.adjunction_counit_app
#print axioms CategoryTheory.WholeRepresentation.FreeEvaluation.genuine_unit
#print axioms CategoryTheory.WholeRepresentation.FreeEvaluation.genuine_counit
#print axioms CategoryTheory.WholeRepresentation.FreeEvaluation.free_triangle
#print axioms CategoryTheory.WholeRepresentation.FreeEvaluation.evaluation_triangle
#print axioms CategoryTheory.WholeRepresentation.FreeEvaluation.adjunction_hom_genuine
#print axioms CategoryTheory.WholeRepresentation.FreeEvaluation.adjunction_hom_inverse_genuine
#print axioms CategoryTheory.WholeRepresentation.FreeEvaluation.freeObject_genuine
#print axioms CategoryTheory.WholeRepresentation.FreeEvaluation.freeMap_genuine
#print axioms CategoryTheory.WholeRepresentation.FreeEvaluation.extend
#print axioms CategoryTheory.WholeRepresentation.FreeEvaluation.extend_app
#print axioms CategoryTheory.WholeRepresentation.FreeEvaluation.extend_genuine
#print axioms CategoryTheory.WholeRepresentation.FreeEvaluation.evaluate
#print axioms CategoryTheory.WholeRepresentation.FreeEvaluation.evaluate_genuine
#print axioms CategoryTheory.WholeRepresentation.FreeEvaluation.evaluate_extend
#print axioms CategoryTheory.WholeRepresentation.FreeEvaluation.extend_evaluate
#print axioms CategoryTheory.WholeRepresentation.FreeEvaluation.homEquiv
#print axioms CategoryTheory.WholeRepresentation.FreeEvaluation.extend_precomp
#print axioms CategoryTheory.WholeRepresentation.FreeEvaluation.evaluate_postcomp
#print axioms CategoryTheory.WholeRepresentation.FreeEvaluation.adjunction
#print axioms CategoryTheory.WholeRepresentation.FreeEvaluation.adjunction_homEquiv
#print axioms CategoryTheory.WholeRepresentation.FreeEvaluation.freeObject
#print axioms CategoryTheory.WholeRepresentation.FreeEvaluation.freeMap
#print axioms CategoryTheory.WholeRepresentation.FreeEvaluation.freeAt
#print axioms CategoryTheory.WholeRepresentation.FreeEvaluation.evaluation
#print axioms CategoryTheory.WholeRepresentation.FreeEvaluation.freeObject_obj
#print axioms CategoryTheory.WholeRepresentation.FreeEvaluation.freeObject_action
#print axioms CategoryTheory.WholeRepresentation.FreeEvaluation.freeAt_map_app
#print axioms CategoryTheory.WholeRepresentation.FreeEvaluation.evaluation_obj
#print axioms CategoryTheory.WholeRepresentation.FreeEvaluation.evaluation_map
#print axioms CategoryTheory.WholeEnrichedFunctor
#print axioms CategoryTheory.WholeEnrichedFunctor.Hom
#print axioms CategoryTheory.WholeEnrichedFunctor.Hom.comm
#print axioms CategoryTheory.WholeEnrichedFunctor.Hom.ofAction
#print axioms CategoryTheory.WholeEnrichedFunctor.instCategory
#print axioms CategoryTheory.WholeEnrichedFunctor.id_app
#print axioms CategoryTheory.WholeEnrichedFunctor.comp_app
#print axioms CategoryTheory.WholeEnrichedFunctor.hom_ext
#print axioms CategoryTheory.WholeRepresentation.genuineObject
#print axioms CategoryTheory.WholeRepresentation.genuineMap
#print axioms CategoryTheory.WholeRepresentation.genuineMap_component
#print axioms CategoryTheory.WholeRepresentation.toGenuineFunctors
#print axioms CategoryTheory.WholeRepresentation.fromGenuineFunctors
#print axioms CategoryTheory.WholeRepresentation.toGenuineFunctors_obj
#print axioms CategoryTheory.WholeRepresentation.toGenuineFunctors_map
#print axioms CategoryTheory.WholeRepresentation.toGenuineFunctors_map_component
#print axioms CategoryTheory.WholeRepresentation.fromGenuineFunctors_map_app
#print axioms CategoryTheory.WholeRepresentation.genuineUnitIsoApp
#print axioms CategoryTheory.WholeRepresentation.genuineCounitHom
#print axioms CategoryTheory.WholeRepresentation.genuineCounitInv
#print axioms CategoryTheory.WholeRepresentation.genuineCounitHom_component
#print axioms CategoryTheory.WholeRepresentation.genuineCounitInv_component
#print axioms CategoryTheory.WholeRepresentation.genuineCounitIsoApp
#print axioms CategoryTheory.WholeRepresentation.genuineUnitIsoApp_hom_app
#print axioms CategoryTheory.WholeRepresentation.genuineCounitIsoApp_hom_component
#print axioms CategoryTheory.WholeRepresentation.genuineUnitIso
#print axioms CategoryTheory.WholeRepresentation.genuineCounitIso
#print axioms CategoryTheory.WholeRepresentation.genuineEquivalence
#print axioms CategoryTheory.WholeRepresentation.genuineEquivalence_toEnrichedFunctor
#print axioms CategoryTheory.WholeRepresentation.genuineEquivalence_representation
