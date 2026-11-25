/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.FreeActions.Units

/-!
# Original free module units at the original degree zero

The original module unit retains the tensor unitor, actual monoid unit and
the actual free carrier transport. Its degree zero map and its naturality
are evaluated on the same original Day and R-module objects.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe v u

open CategoryTheory Limits MonoidalCategory MonObj
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace HomotopicalAlgebra.PositiveLevelModel

local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [HasColimitsOfSize.{0, 0} C]
  [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
  [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorRight Z)]
  (R : DayFunctor I C) [MonObj R]

/-- The actual module unit has its original unitor, R unit and free carrier transport at degree
zero. -/
theorem freeModuleUnit_zero (N : DayFunctor I C) :
    ((CategoryTheory.Mod.freeForgetAdjunction R).unit.app N).natTrans.app
        (CategoryTheory.Operad.SmallFinBijGroupoid.card 0) =
      ((λ_ N).inv ≫ (η[R] ▷ N) ≫ eqToHom (CategoryTheory.Mod.free_obj R N).symm).natTrans.app
        (CategoryTheory.Operad.SmallFinBijGroupoid.card 0) :=
  congrArg (fun f : N ⟶ ((CategoryTheory.Mod.free R).obj N).X =>
    f.natTrans.app (CategoryTheory.Operad.SmallFinBijGroupoid.card 0))
    (CategoryTheory.Mod.freeForgetAdjunction_unit_app R N)

/-- Every original Day arrow retains the actual free unit naturality word at degree zero. -/
theorem freeModuleUnit_zero_naturality {A B : DayFunctor I C} (f : A ⟶ B) :
    ((CategoryTheory.Mod.freeForgetAdjunction R).unit.app A).natTrans.app
        (CategoryTheory.Operad.SmallFinBijGroupoid.card 0) ≫
      ((CategoryTheory.Mod.forget R).map ((CategoryTheory.Mod.free R).map f)).natTrans.app
        (CategoryTheory.Operad.SmallFinBijGroupoid.card 0) =
      f.natTrans.app (CategoryTheory.Operad.SmallFinBijGroupoid.card 0) ≫
        ((CategoryTheory.Mod.freeForgetAdjunction R).unit.app B).natTrans.app
          (CategoryTheory.Operad.SmallFinBijGroupoid.card 0) := by
  exact congrArg (fun g : A ⟶ ((CategoryTheory.Mod.free R).obj B).X =>
    g.natTrans.app (CategoryTheory.Operad.SmallFinBijGroupoid.card 0))
    ((CategoryTheory.Mod.freeForgetAdjunction R).unit.naturality f).symm

end HomotopicalAlgebra.PositiveLevelModel
