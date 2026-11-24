/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentProperFaceIndex

/-!
# The actual original proper-face diagram and opposite matching diagram

The original structured-arrow right projection gives the whole
proper-injection diagram. For every supplied covariant simplex diagram,
it is the literal opposite of the existing matching diagram. Independent
coefficient object and morphism universes are retained.
-/

noncomputable section
universe u v
open CategoryTheory Opposite

namespace CategoryTheory.CoherentRealization.ProperFaceIndex

/-- The actual original ordinal projection from the opposite proper-injection index. -/
def diagram (n : ℕ) : (SimplicialObject.matchingIndex n)ᵒᵖ ⥤ SimplexCategory where
  obj a := a.unop.obj.right.unop
  map g := g.unop.hom.right.unop
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Every original covariant simplex diagram has this same proper-face diagram as the literal opposite
  matching diagram. -/
theorem matchingDiagram_leftOp {C : Type u} [Category.{v} C] (X : SimplexCategory ⥤ C) (n : ℕ) :
    (SimplicialObject.matchingDiagram X.op n).leftOp = diagram n ⋙ X := rfl

end CategoryTheory.CoherentRealization.ProperFaceIndex
