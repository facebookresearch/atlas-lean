/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.CategoryTheory.Linear.Yoneda
@[expose] public section

noncomputable section

open CategoryTheory Limits

universe w v u vJ uJ

namespace CategoryTheory

/-- A represented `ModuleCat`-valued linear Yoneda presheaf preserves limits. -/
instance preservesLimits_linearYoneda_obj (R : Type w) [Ring R]
    (C : Type u) [Category.{v} C] [Preadditive C] [Linear R C]
    (X : C) : PreservesLimitsOfSize.{vJ, uJ} ((linearYoneda R C).obj X) := by
  have : PreservesLimitsOfSize.{vJ, uJ}
      (((linearYoneda R C).obj X) ⋙
         (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v} ⋙ forget AddCommGrpCat.{v})) := by
    change PreservesLimitsOfSize.{vJ, uJ} (yoneda.obj X)
    infer_instance
  exact preservesLimits_of_reflects_of_preserves _
    (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v} ⋙ forget AddCommGrpCat.{v})

/-- A represented `ModuleCat`-valued linear Coyoneda functor preserves limits
of arbitrary diagram size in a preadditive linear category. -/
instance preservesLimits_linearCoyoneda_obj (R : Type w) [Ring R]
    (C : Type u) [Category.{v} C] [Preadditive C] [Linear R C]
    (X : Cᵒᵖ) : PreservesLimitsOfSize.{vJ, uJ} ((linearCoyoneda R C).obj X) := by
  have : PreservesLimitsOfSize.{vJ, uJ}
      (((linearCoyoneda R C).obj X) ⋙
        (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v} ⋙ forget AddCommGrpCat.{v})) := by
    change PreservesLimitsOfSize.{vJ, uJ} (coyoneda.obj X)
    infer_instance
  exact preservesLimits_of_reflects_of_preserves _
    (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v} ⋙ forget AddCommGrpCat.{v})
end CategoryTheory
