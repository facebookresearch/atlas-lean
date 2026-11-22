/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Action.Arrow
public import Mathlib.CategoryTheory.Action.Monoidal

/-!
# Coefficient tensors of complete equivariant arrows

The coefficient and both endpoints retain their original actions. The
coefficient tensor diagram and its transformation give the complete
diagonal action on the original arrow, using focused action and tensor
imports. The operadic profile-cell module re-exports these declarations.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe ug u v

namespace CategoryTheory.OperadicOrbitCells

open CategoryTheory Limits MonoidalCategory
open scoped MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {G : Type ug} [Group G] [HasColimitsOfShape (SingleObj G) C]

/-- The original coefficient tensored with the original source action. -/
def coefficientSourceFunctor (Y B : Action C G) : SingleObj G ⥤ C :=
  (Action.functorCategoryEquivalence C G).functor.obj (Y ⊗ B)

/-- The same equivariant coefficient tensors the entire original action arrow. -/
def coefficientTransformation (Y : Action C G) {B T : Action C G} (p : B ⟶ T) :
    coefficientSourceFunctor Y B ⟶ coefficientSourceFunctor Y T :=
  (Action.functorCategoryEquivalence C G).functor.map (Y ◁ p)

omit [HasColimitsOfShape (SingleObj G) C] in
/-- Every coefficient/action transition is literally the diagonal tensor action. -/
theorem coefficientSourceFunctor_map (Y B : Action C G) (g : G) :
    (coefficientSourceFunctor Y B).map
        (show SingleObj.star G ⟶ SingleObj.star G from g) =
      (Y.ρ g).asHom ⊗ₘ (B.ρ g).asHom := rfl

/-- The actual coefficient tensor has its own complete diagonal whole-arrow action. -/
def coefficientArrowAction (Y : Action C G) (A : Action (Arrow C) G) : Action (Arrow C) G :=
  (Action.functorCategoryEquivalence (Arrow C) G).inverse.obj
    (CategoryTheory.naturalArrowFunctor (coefficientTransformation Y (Action.actionUnderlyingHom A)))

end CategoryTheory.OperadicOrbitCells
