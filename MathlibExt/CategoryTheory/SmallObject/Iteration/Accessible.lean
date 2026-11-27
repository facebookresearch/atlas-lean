/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration
public import Mathlib.CategoryTheory.Presentable.Basic
public import MathlibExt.CategoryTheory.Presentable.Colimits

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v w μU
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SmallObject.SuccStruct

variable {C : Type u} [Category.{v} C]
    {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    [HasIterationOfShape J C]
    {F : C ⥤ C} (ε : 𝟭 C ⟶ F) (μ : Cardinal.{μU}) [Fact μ.IsRegular]
    [F.IsCardinalAccessible μ]

/-- Every original stage of a pointed accessible endofunctor is accessible. -/
theorem isCardinalAccessible_iterationFunctor_obj (j : J) :
    (((ofNatTrans ε).iterationFunctor J).obj j).IsCardinalAccessible μ := by
  let Φ : SuccStruct (C ⥤ C) := ofNatTrans ε
  let M : J ⥤ C ⥤ C := Φ.iterationFunctor J
  change (M.obj j).IsCardinalAccessible μ
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
      have hjbot : j = ⊥ := isMin_iff_eq_bot.mp hj
      subst j
      let e : M.obj ⊥ ≅ 𝟭 C := Φ.iterationFunctorObjBotIso J
      exact Functor.isCardinalAccessible_of_natIso e.symm μ
  | succ j hj ih =>
      let _ : (M.obj j).IsCardinalAccessible μ := ih
      let _ : (M.obj j ⋙ F).IsCardinalAccessible μ := inferInstance
      let e : M.obj (Order.succ j) ≅ M.obj j ⋙ F :=
        Φ.iterationFunctorObjSuccIso j hj
      exact Functor.isCardinalAccessible_of_natIso e.symm μ
  | isSuccLimit j hj ih =>
      let H : Set.Iio j ⥤ C ⥤ C :=
        (Set.principalSegIio j).monotone.functor ⋙ M
      let c : Cocone H := (Set.principalSegIio j).cocone M
      let _ : HasColimitsOfShape (Set.Iio j) C :=
        hasColimitsOfShape_of_isSuccLimit C j hj
      let _ : ∀ k : Set.Iio j, (H.obj k).IsCardinalAccessible μ := fun k => by
        change (M.obj k.1).IsCardinalAccessible μ
        exact ih k.1 k.2
      exact Functor.isCardinalAccessible_of_isColimit μ H c
        (M.isColimitOfIsWellOrderContinuous j hj)

/-- The SAME original final iteration cocone point is accessible. -/
theorem isCardinalAccessible_iteration :
    ((ofNatTrans ε).iteration J).IsCardinalAccessible μ := by
  let Φ : SuccStruct (C ⥤ C) := ofNatTrans ε
  let M : J ⥤ C ⥤ C := Φ.iterationFunctor J
  let _ : ∀ j : J, (M.obj j).IsCardinalAccessible μ := fun j =>
    isCardinalAccessible_iterationFunctor_obj ε μ j
  exact Functor.isCardinalAccessible_of_isColimit μ M
    (Φ.iterationCocone J) (Φ.isColimitIterationCocone J)

end CategoryTheory.SmallObject.SuccStruct
