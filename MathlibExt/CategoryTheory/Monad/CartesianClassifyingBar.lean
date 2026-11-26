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
# Terminal point data for cartesian classifying bars

Let C be a cartesian monoidal category with object and morphism universes u,v, and M an internal
monoid. The tensor unit I is terminal. It therefore has a trivial left M-action M⊗I→I and a
terminal right M-action I⊗M→I, given by the respective projections.

The unique augmentation M→I is compatible with multiplication and the right point action. These
data specialize the two-sided bar to the classifying and universal bar constructions. Evaluation
at the chosen object of the one-object discrete category turns a point-indexed diagram into an
object of C; this evaluation itself requires only a category.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory

namespace CategoryTheory.Monad.ClassifyingBar

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- Let C be a cartesian monoidal category with object universe u and morphism universe v, and let M
be an internal monoid with underlying object M. Write I for the terminal tensor unit, e:I→M for
the unit, and m:M⊗M→M for multiplication. The trivial left M-module structure on I has action
M⊗I→I equal to the second product projection. The unit and associativity laws hold because all
resulting maps have terminal target I. -/
@[instance_reducible]
noncomputable def pointModObj (M : Mon C) : ModObj M.X (𝟙_ C) :=
  ModObj.trivialAction M.X (𝟙_ C)

attribute [local instance] pointModObj

/-- Let C be a cartesian monoidal category with object universe u and morphism universe v, and let M
be an internal monoid with underlying object M. Write I for the terminal tensor unit, e:I→M for
the unit, and m:M⊗M→M for multiplication. The right action r_M:I⊗M→I is the first product
projection, hence the unique morphism to I. It is the point right action used in the cartesian
classifying bar. -/
noncomputable def pointRightAction (M : Mon C) : (𝟙_ C) ⊗ M.X ⟶ 𝟙_ C :=
  CartesianMonoidalCategory.fst (𝟙_ C) M.X

/-- Let C be a cartesian monoidal category with object universe u and morphism universe v, and let M
be an internal monoid with underlying object M. Write I for the terminal tensor unit, e:I→M for
the unit, and m:M⊗M→M for multiplication. For r_M:I⊗M→I, the right unit identity is
(id_I⊗e)≫r_M=ρ_I, where ρ_I:I⊗I≅I is the right unitor. Both sides are the unique map I⊗I→I. -/
theorem pointRightAction_one (M : Mon C) :
    ((𝟙_ C) ◁ MonObj.one (X := M.X)) ≫ pointRightAction M =
      (ρ_ (𝟙_ C)).hom :=
  CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _

/-- Let C be a cartesian monoidal category with object universe u and morphism universe v, and let M
be an internal monoid with underlying object M. Write I for the terminal tensor unit, e:I→M for
the unit, and m:M⊗M→M for multiplication. The right action r_M satisfies
α_{I,M,M}≫(id_I⊗m)≫r_M=(r_M⊗id_M)≫r_M. Each side maps (I⊗M)⊗M to the terminal object I, so the
two possible action composites agree. -/
theorem pointRightAction_assoc (M : Mon C) :
    (α_ (𝟙_ C) M.X M.X).hom ≫
        ((𝟙_ C) ◁ MonObj.mul (X := M.X)) ≫ pointRightAction M =
      (pointRightAction M ▷ M.X) ≫ pointRightAction M :=
  CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _

/-- Let C be a cartesian monoidal category with object universe u and morphism universe v, and let M
be an internal monoid with underlying object M. Write I for the terminal tensor unit, e:I→M for
the unit, and m:M⊗M→M for multiplication. The augmentation ε_M:M→I is the unique morphism to the
terminal tensor unit. It supplies the terminal coefficient map for the cartesian universal-bar
augmentation. -/
noncomputable def augmentation (M : Mon C) : M.X ⟶ 𝟙_ C :=
  CartesianMonoidalCategory.toUnit M.X

/-- Let C be a cartesian monoidal category with object universe u and morphism universe v, and let M
be an internal monoid with underlying object M. Write I for the terminal tensor unit, e:I→M for
the unit, and m:M⊗M→M for multiplication. The augmentation ε_M:M→I and right action r_M:I⊗M→I
satisfy (ε_M⊗id_M)≫r_M=m≫ε_M. Both morphisms have source M⊗M and terminal target I. -/
theorem augmentation_compat (M : Mon C) :
    (augmentation M ▷ M.X) ≫ pointRightAction M =
      MonObj.mul (X := M.X) ≫ augmentation M :=
  CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _

/-- The discrete category on the one-element type has a chosen object ⋆ represented by its unique
element. This object is the index at which a point-indexed classifying-bar diagram is evaluated. -/
def index : Discrete PUnit.{1} :=
  Discrete.mk PUnit.unit

/-- Let C be any category with object universe u and morphism universe v. Evaluation at the unique
object ⋆ defines a functor (Discrete{⋆}→C)→C. It sends a diagram F to F(⋆) and a natural
transformation α:F→H to its component α_⋆. -/
noncomputable def pointEvaluation (C : Type u) [Category.{v} C] :
    (Discrete PUnit.{1} ⥤ C) ⥤ C :=
  (evaluation (Discrete PUnit.{1}) C).obj index

end CategoryTheory.Monad.ClassifyingBar
