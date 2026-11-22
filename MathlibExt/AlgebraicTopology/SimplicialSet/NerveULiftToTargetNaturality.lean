/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.NerveULiftToTarget

/-!
# The same original lifted nerve map retains full source composition

The existing full original nerve lift sends every complete original
chain through both supplied original functors. This gives its exact
source-composition square at the original independent universes.
-/

noncomputable section

universe u w vA vB

open CategoryTheory Opposite

namespace SSet

variable {C A : Type u} {B : Type (max u w)}
  [Category.{vA} C] [Category.{vA} A] [Category.{max vA vB} B]

/-- Both entire original source functors retain their exact full original lifted nerve composite. -/
theorem nerveMapULiftToTarget_precomp (F : C ⥤ A) (G : A ⥤ B) :
    uliftFunctor.{max u w vA vB,max u vA}.map (nerveMap F) ≫ nerveMapULiftToTarget G =
      nerveMapULiftToTarget (F ⋙ G) := by
  apply NatTrans.ext
  funext q
  apply ConcreteCategory.hom_ext
  intro x
  rfl

end SSet
