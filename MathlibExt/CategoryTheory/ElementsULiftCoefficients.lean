/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Types.Basic

/-!
# The full native elements functor under coefficient universe lift

The canonical coefficient lift retains the same original object and
every original arrow of the category of elements. Its value is the
full original coefficient, tagged in the larger universe.
-/

noncomputable section

universe u v w l

open CategoryTheory

namespace CategoryTheory.Functor.Elements

variable {C : Type u} [Category.{v} C]

/-- The same full original elements category maps to the actual canonical coefficient-lift
elements category. -/
def uliftCoefficients (F : C ⥤ Type w) :
    F.Elements ⥤ (F ⋙ CategoryTheory.uliftFunctor.{l,w}).Elements where
  obj x := .mk (ULift.up x.val)
  map f := homMk f.hom (congrArg ULift.up f.map_val)
  map_id x := by apply hom_ext; rfl
  map_comp f g := by apply hom_ext; rfl

/-- The same native coefficient lift retains the entire original object and arrow projection. -/
theorem uliftCoefficients_comp_π (F : C ⥤ Type w) :
    uliftCoefficients.{u,v,w,l} F ⋙ π (F ⋙ CategoryTheory.uliftFunctor.{l,w}) = π F := rfl

end CategoryTheory.Functor.Elements
