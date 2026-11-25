/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Monad.ClassifyingBundle
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

/-!
# Cartesian point data for classifying bars

For an internal monoid `M : Mon C` in a cartesian monoidal category, the tensor unit is terminal
and hence has canonical trivial left and right `M`-actions, together with the terminal augmentation
from `M.X`.  This file packages exactly that point datum and evaluation at the canonical object of
`Discrete PUnit`.

The generic bar objects remain `classifyingBar` and `universalBar`; no second generic `BBar` or
`EBar` API is introduced.  Concrete categories can form thin evaluated aliases by substituting
the data below into those existing two-sided-bar specializations.  No functoriality, realization,
or new simplicial identity is claimed here.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory

namespace CategoryTheory.Monad.ClassifyingBar

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- The canonical trivial left action of an internal monoid on the cartesian tensor unit. -/
@[instance_reducible]
noncomputable def pointModObj (M : Mon C) : ModObj M.X (𝟙_ C) :=
  ModObj.trivialAction M.X (𝟙_ C)

attribute [local instance] pointModObj

/-- The canonical terminal right action of an internal monoid on the cartesian tensor unit. -/
noncomputable def pointRightAction (M : Mon C) : (𝟙_ C) ⊗ M.X ⟶ 𝟙_ C :=
  CartesianMonoidalCategory.fst (𝟙_ C) M.X

/-- Unit law for the terminal right action. -/
theorem pointRightAction_one (M : Mon C) :
    ((𝟙_ C) ◁ MonObj.one (X := M.X)) ≫ pointRightAction M =
      (ρ_ (𝟙_ C)).hom :=
  CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _

/-- Associativity law for the terminal right action. -/
theorem pointRightAction_assoc (M : Mon C) :
    (α_ (𝟙_ C) M.X M.X).hom ≫
        ((𝟙_ C) ◁ MonObj.mul (X := M.X)) ≫ pointRightAction M =
      (pointRightAction M ▷ M.X) ≫ pointRightAction M :=
  CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _

/-- The terminal augmentation of an internal monoid. -/
noncomputable def augmentation (M : Mon C) : M.X ⟶ 𝟙_ C :=
  CartesianMonoidalCategory.toUnit M.X

/-- The terminal augmentation intertwines multiplication with the terminal right action. -/
theorem augmentation_compat (M : Mon C) :
    (augmentation M ▷ M.X) ≫ pointRightAction M =
      MonObj.mul (X := M.X) ≫ augmentation M :=
  CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _

/-- The canonical object of the one-object indexing category. -/
def index : Discrete PUnit.{1} :=
  Discrete.mk PUnit.unit

/-- Evaluation of a point-indexed diagram at its canonical point. -/
noncomputable def pointEvaluation (C : Type u) [Category.{v} C] :
    (Discrete PUnit.{1} ⥤ C) ⥤ C :=
  (evaluation (Discrete PUnit.{1}) C).obj index

end CategoryTheory.Monad.ClassifyingBar
