/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.MorphismProperty.SharpMaps
import MathlibExt.AlgebraicTopology.ModelCategory.Proper

/-!
# Original fibrations are sharp in a right proper model

Every original base change is retained. This is Rezk's fibration example
of sharpness and uses the actual right-proper weak/fibration classes.
-/

noncomputable section
universe v u
open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C] [IsRightProper C]

/-- Each actual original fibration is sharp, including all its full base changes. -/
theorem sharpMaps_of_fibration {E B : C} (p : E ⟶ B) [Fibration p] :
    sharpMaps (weakEquivalences C) p := by
  intro E' B' a b p' sq
  have hp' : fibrations C p' := MorphismProperty.of_isPullback sq.flip (mem_fibrations p)
  exact IsRightProper.weakEquivalences_isStableUnderBaseChangeAgainst_fibrations
    |>.isStableUnderBaseChangeAlong p' hp'

end HomotopicalAlgebra
