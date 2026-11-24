/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.CategoryTheory.GradedObject.Preadditive

/-!
# Direct clients of canonical graded preadditivity

Only the canonical provider is imported. The first client keeps arbitrary
grading, object and Hom universes independent. The second uses the original
integer-graded coprojections and maps; it requires no finite-fiber premise.
-/

@[expose] public section

namespace CategoryTheory.GradedObject

open Limits

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

example (β : Type w) : Preadditive (GradedObject β C) := inferInstance

example [HasCoproducts.{0} C] {X Y : GradedObject ℤ C} (f g : X ⟶ Y) (i : ℤ) :
    Sigma.ι X i ≫ (total ℤ C).map (f + g) =
      Sigma.ι X i ≫ (total ℤ C).map f + Sigma.ι X i ≫ (total ℤ C).map g := by
  let F := total ℤ C
  let ι : X i ⟶ F.obj X := Sigma.ι X i
  let f' : F.obj X ⟶ F.obj Y := F.map f
  let g' : F.obj X ⟶ F.obj Y := F.map g
  have hmap : F.map (f + g) = f' + g' := Functor.map_add F
  change ι ≫ F.map (f + g) = ι ≫ f' + ι ≫ g'
  exact (congrArg (fun h : F.obj X ⟶ F.obj Y => ι ≫ h) hmap).trans
    (Preadditive.comp_add (X i) (F.obj X) (F.obj Y) ι f' g')

#check CategoryTheory.GradedObject.gradedObjectPreadditive
#check CategoryTheory.GradedObject.gradedObjectTotalAdditive

end CategoryTheory.GradedObject
