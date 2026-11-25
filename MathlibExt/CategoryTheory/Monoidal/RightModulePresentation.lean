/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.Monoidal.CommutativeModuleConversion

/-!
# Characteristic laws for the existing right-module carrier

The right-module category is `CommutativeModuleConversion.RightModule M`,
definitionally the existing `Mod (C := Cᴹᵒᵖ) C (mop M)`. These laws expose its
right action without adding object, morphism, category, or forgetful structures.
They apply to every monoid object, without a braiding or commutativity premise.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory MonoidalOpposite
open scoped CategoryTheory.MonObj

namespace CategoryTheory.CommutativeModuleConversion.RightModule

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
variable {M : C} [MonObj M]

/-- The original stock module action is tensoring on the right. -/
abbrev action (X : RightModule M) : X.X ⊗ M ⟶ X.X := X.mod.smul

/-- The stock right action has the original right-unit equation. -/
@[reassoc]
theorem one_action (X : RightModule M) :
    (X.X ◁ η[M]) ≫ X.action = (ρ_ X.X).hom :=
  ModObj.one_smul (M := mop M) X.X

/-- The stock right action uses the original inverse associator. -/
@[reassoc]
theorem mul_action (X : RightModule M) :
    (X.X ◁ μ[M]) ≫ X.action =
      (α_ X.X M M).inv ≫ (X.action ▷ M) ≫ X.action :=
  ModObj.mul_smul (M := mop M) X.X

/-- Every existing module morphism retains its full right-action square. -/
@[reassoc]
theorem comm {X Y : RightModule M} (f : X ⟶ Y) :
    X.action ≫ f.hom = (f.hom ▷ M) ≫ Y.action :=
  IsModHom.smul_hom (A := mop M) (f := f.hom)

end CategoryTheory.CommutativeModuleConversion.RightModule
