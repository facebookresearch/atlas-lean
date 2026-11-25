/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Authors: Tsutomu Okano <toskua@meta.com>
-/

import MathlibExt.CategoryTheory.Enriched.RightModuleFreeUnit

/-!
# Public clients of the canonical free-unit comparisons

Apply the ordinary monoidal and enriched free-unit interfaces to their original
module objects. The client checks both carrier maps and the whole free-adjunction
transport with the comparison constructors kept irreducible.
-/

set_option autoImplicit false
noncomputable section
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace MathlibExtTest.RightModuleFreeUnitClients.Monoidal

universe uC vC
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
attribute [local irreducible] RightModuleFree.freeUnitRegular
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] (S : C) [MonObj S]

/-- A general monoidal caller obtains the entire regular-module comparison. -/
def selectedUnit (P : C) (e : P ≅ 𝟙_ C) :
    (RightModuleFree.functor S).obj P ≅ RightModuleFree.regularObject S :=
  RightModuleFree.freeUnitRegular S P e

/-- The forward carrier retains the actual coefficient tensor and left unitor. -/
theorem selectedUnit_forward (P : C) (e : P ≅ 𝟙_ C) :
    (selectedUnit S P e).hom.hom = (e.hom ▷ S) ≫ (λ_ S).hom :=
  RightModuleFree.freeUnitRegular_hom S P e

/-- The inverse retains the inverse unitor and coefficient tensor. -/
theorem selectedUnit_inverse (P : C) (e : P ≅ 𝟙_ C) :
    (selectedUnit S P e).inv.hom = (λ_ S).inv ≫ (e.inv ▷ S) :=
  RightModuleFree.freeUnitRegular_inv S P e

end MathlibExtTest.RightModuleFreeUnitClients.Monoidal

namespace MathlibExtTest.RightModuleFreeUnitClients.Enriched

universe uV vV uI uJ
open CategoryTheory.EnrichedFunctorCat CategoryTheory.Enriched.RightModuleFreeEvaluation
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
attribute [local irreducible] Unit.sourceFreeRegularIso Unit.regularUnitOperatorIso
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V] {I : Type uI} [EnrichedCategory V I]
  [MonoidalCategory (EnrichedFunctorCat V I)]
  (S : EnrichedFunctorCat V I) [MonObj S]

/-- The caller's full enriched free source identifies the regular scalar module. -/
def selectedSourceUnit (n : I) (X : V)
    (q : Free.object n X ≅ 𝟙_ (EnrichedFunctorCat V I)) :
    (Primitive.free S n).obj X ≅ RightModuleFree.regularObject S :=
  Unit.sourceFreeRegularIso S n X q

/-- The forward arrow keeps the original free functor map and source-unit unitor. -/
theorem selectedSourceUnit_forward (n : I) (X : V)
    (q : Free.object n X ≅ 𝟙_ (EnrichedFunctorCat V I)) :
    (selectedSourceUnit S n X q).hom = eqToHom (Unit.sourceFreeObjectEq S n X) ≫
      (RightModuleFree.functor S).map q.hom ≫ (RightModuleFree.freeUnitRegularIso S).hom :=
  Unit.sourceFreeRegularIso_hom S n X q

variable {J : Type uJ} [EnrichedCategory V J]

/-- Actual source evaluation and equivalence data construct the entire operator free unit. -/
def selectedOperatorUnit
    (e : CommutativeModuleConversion.RightModule S ≌ EnrichedFunctorCat V J)
    (n : I) (a : J)
    (q : Free.object n (𝟙_ V) ≅ 𝟙_ (EnrichedFunctorCat V I))
    (h : e.functor ⋙ EnrichedFunctorCat.evaluation a ≅ Primitive.evaluation S n) :
    e.functor.obj (RightModuleFree.regularObject S) ≅ Free.object a (𝟙_ V) :=
  Unit.regularUnitOperatorIso S e n a q h

end MathlibExtTest.RightModuleFreeUnitClients.Enriched
