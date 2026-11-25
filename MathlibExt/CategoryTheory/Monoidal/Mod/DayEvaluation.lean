/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Monoidal.Mod.ColimitsFree
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Monoidal.DayConvolution.DayFunctor

/-!
# Evaluation and free-at-object for modules in a Day functor category

For a monoid object `A` in a selected monoidal structure on a Day functor
category, this file composes three existing adjunctions:

* free diagram at an object versus evaluation;
* the tautological equivalence between ordinary and Day functors; and
* free internal `A`-module versus the forgetful functor.

The result is a generic evaluation/free-at-object adjunction for internal
modules, using only the displayed categorical and coproduct data.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe vI uI vV uV

open CategoryTheory Limits MonoidalCategory MonObj
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace CategoryTheory.Mod

variable {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
variable [MonoidalCategory (DayFunctor I V)]
variable (A : DayFunctor I V) [MonObj A]

/-- Evaluation at `i` after forgetting a module and then its Day wrapper. -/
noncomputable def dayEvaluation (i : I) :
    CategoryTheory.Mod (DayFunctor I V) A ⥤ V where
  obj M := M.X.functor.obj i
  map f := f.hom.natTrans.app i
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The complete original module evaluation functor retains both original
object and map values of the forgetful, Day and evaluation composition. -/
theorem dayEvaluation_eq_originalComposite (i : I) :
    dayEvaluation A i = CategoryTheory.Mod.forget A ⋙
      ((DayFunctor.equiv I V).symm.inverse ⋙
        (CategoryTheory.evaluation I V).obj i) := rfl

/-- The original module evaluation preserves every colimit preserved by its
forgetful functor, through the actual Day equivalence and ordinary evaluation. -/
instance dayEvaluationPreservesColimitsOfSize.{w, w'} (i : I)
    [HasColimitsOfSize.{w, w'} V]
    [PreservesColimitsOfSize.{w, w'} (CategoryTheory.Mod.forget (D := DayFunctor I V) A)] :
    PreservesColimitsOfSize.{w, w'} (dayEvaluation A i) := by
  let _ : PreservesColimitsOfSize.{w, w'} ((CategoryTheory.evaluation I V).obj i) :=
    ⟨fun {J} _ => inferInstance⟩
  change PreservesColimitsOfSize.{w, w'} (CategoryTheory.Mod.forget (D := DayFunctor I V) A ⋙
    ((DayFunctor.equiv I V).symm.inverse ⋙ (CategoryTheory.evaluation I V).obj i))
  infer_instance

variable [∀ i j : I, HasCoproductsOfShape (i ⟶ j) V]

/-- The free `A`-module on the ordinary free diagram concentrated at `i`. -/
noncomputable def dayFreeAt (i : I) :
    V ⥤ CategoryTheory.Mod (DayFunctor I V) A :=
  (CategoryTheory.evaluationLeftAdjoint V i ⋙
    (DayFunctor.equiv I V).symm.functor) ⋙
      CategoryTheory.Mod.free A

/-- Free at `i` is left adjoint to evaluation at `i` for Day modules. -/
noncomputable def dayFreeAtEvaluationAdjunction (i : I) :
    dayFreeAt A i ⊣ dayEvaluation A i :=
  ((CategoryTheory.evaluationAdjunctionRight V i).comp
    (DayFunctor.equiv I V).symm.toAdjunction).comp
      (CategoryTheory.Mod.freeForgetAdjunction A)

/-- The Hom equivalence is the composite of module free/forget, the inverse
Day equivalence, and ordinary free-diagram/evaluation. -/
theorem dayFreeAtEvaluationAdjunction_homEquiv
    (i : I) (X : V) (M : CategoryTheory.Mod (DayFunctor I V) A) :
    (dayFreeAtEvaluationAdjunction A i).homEquiv X M =
      ((CategoryTheory.Mod.freeForgetAdjunction A).homEquiv
        ((DayFunctor.equiv I V).symm.functor.obj
          ((CategoryTheory.evaluationLeftAdjoint V i).obj X)) M).trans
        (((DayFunctor.equiv I V).symm.toAdjunction.homEquiv
          ((CategoryTheory.evaluationLeftAdjoint V i).obj X)
          ((CategoryTheory.Mod.forget A).obj M)).trans
        ((CategoryTheory.evaluationAdjunctionRight V i).homEquiv X
          ((DayFunctor.equiv I V).symm.inverse.obj
            ((CategoryTheory.Mod.forget A).obj M)))) := by
  change
    ((((CategoryTheory.evaluationAdjunctionRight V i).comp
      (DayFunctor.equiv I V).symm.toAdjunction).comp
        (CategoryTheory.Mod.freeForgetAdjunction A)).homEquiv X M) = _
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  simp only [Functor.comp_obj]

/-- The composite unit, with the free-module unit and its carrier transport
displayed explicitly. -/
theorem dayFreeAtEvaluationAdjunction_unit_app
    (i : I) (X : V) :
    (dayFreeAtEvaluationAdjunction A i).unit.app X =
      (CategoryTheory.evaluationAdjunctionRight V i).unit.app X ≫
        ((CategoryTheory.evaluation I V).obj i).map
          ((DayFunctor.equiv I V).symm.toAdjunction.unit.app
            ((CategoryTheory.evaluationLeftAdjoint V i).obj X)) ≫
        ((DayFunctor.equiv I V).symm.inverse ⋙
          (CategoryTheory.evaluation I V).obj i).map
          ((λ_ ((DayFunctor.equiv I V).symm.functor.obj
            ((CategoryTheory.evaluationLeftAdjoint V i).obj X))).inv ≫
          (η[A] ▷ ((DayFunctor.equiv I V).symm.functor.obj
            ((CategoryTheory.evaluationLeftAdjoint V i).obj X))) ≫
          eqToHom (CategoryTheory.Mod.free_obj A
            ((DayFunctor.equiv I V).symm.functor.obj
              ((CategoryTheory.evaluationLeftAdjoint V i).obj X))).symm) := by
  change
    ((((CategoryTheory.evaluationAdjunctionRight V i).comp
      (DayFunctor.equiv I V).symm.toAdjunction).comp
        (CategoryTheory.Mod.freeForgetAdjunction A)).unit.app X) = _
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app,
    CategoryTheory.Mod.freeForgetAdjunction_unit_app]
  simp only [Functor.comp_obj, Category.assoc]
  congr 1

/-- The underlying composite counit. It retains the free-module carrier
transport, both evaluation/Day counit stages, and the target module action. -/
theorem dayFreeAtEvaluationAdjunction_counit_app
    (i : I) (M : CategoryTheory.Mod (DayFunctor I V) A) :
    ((dayFreeAtEvaluationAdjunction A i).counit.app M).hom =
      eqToHom (CategoryTheory.Mod.free_obj A
        ((DayFunctor.equiv I V).symm.functor.obj
          ((CategoryTheory.evaluationLeftAdjoint V i).obj
            (((CategoryTheory.evaluation I V).obj i).obj
              ((DayFunctor.equiv I V).symm.inverse.obj M.X))))) ≫
      (A ◁
        ((DayFunctor.equiv I V).symm.functor.map
          ((CategoryTheory.evaluationAdjunctionRight V i).counit.app
            ((DayFunctor.equiv I V).symm.inverse.obj M.X)) ≫
        (DayFunctor.equiv I V).symm.toAdjunction.counit.app M.X)) ≫
      ModObj.smul (M := A) (X := M.X) := by
  let k1 := (DayFunctor.equiv I V).symm.functor.map
    ((CategoryTheory.evaluationAdjunctionRight V i).counit.app
      ((DayFunctor.equiv I V).symm.inverse.obj M.X))
  let k2 := (DayFunctor.equiv I V).symm.toAdjunction.counit.app M.X
  change
    (((((CategoryTheory.evaluationAdjunctionRight V i).comp
      (DayFunctor.equiv I V).symm.toAdjunction).comp
        (CategoryTheory.Mod.freeForgetAdjunction A)).counit.app M).hom) =
      eqToHom (CategoryTheory.Mod.free_obj A
        ((DayFunctor.equiv I V).symm.functor.obj
          ((CategoryTheory.evaluationLeftAdjoint V i).obj
            (((CategoryTheory.evaluation I V).obj i).obj
              ((DayFunctor.equiv I V).symm.inverse.obj M.X))))) ≫
      (A ◁ (k1 ≫ k2)) ≫ ModObj.smul (M := A) (X := M.X)
  rw [Adjunction.comp_counit_app, Adjunction.comp_counit_app]
  rw [Functor.map_comp]
  simp only [CategoryTheory.Mod.comp_hom', Category.assoc,
    CategoryTheory.Mod.freeForgetAdjunction_counit_app_hom]
  change
    ((CategoryTheory.Mod.free A).map k1).hom ≫
        ((CategoryTheory.Mod.free A).map k2).hom ≫
        eqToHom (CategoryTheory.Mod.free_obj A M.X) ≫
        ModObj.smul (M := A) (X := M.X) =
      eqToHom (CategoryTheory.Mod.free_obj A
        ((DayFunctor.equiv I V).symm.functor.obj
          ((CategoryTheory.evaluationLeftAdjoint V i).obj
            (((CategoryTheory.evaluation I V).obj i).obj
              ((DayFunctor.equiv I V).symm.inverse.obj M.X))))) ≫
        (A ◁ (k1 ≫ k2)) ≫ ModObj.smul (M := A) (X := M.X)
  slice_lhs 2 3 =>
    rw [← CategoryTheory.Mod.free_map A k2]
  slice_lhs 1 2 =>
    rw [← CategoryTheory.Mod.free_map A k1]
  slice_lhs 2 3 =>
    rw [← MonoidalCategory.whiskerLeft_comp]

end CategoryTheory.Mod
