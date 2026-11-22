/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedBoundaryReadback
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRightMappingJoyalPointedHom

/-!
# The same full fixed-front Hom space at an arbitrary original pointed input

The original entire boundary is reconstructed by its two literal face
vertices. The existing original pointed right-mapping dictionary and
canonical carrier equivalence therefore identify the full Hom diagram
at every same original pointed input, with both inverse maps retained.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalRawRightMapping

open OriginalFixedFrontContraction

/-- The same original pointed input is exactly the canonical pointed object of its original endpoint maps. -/
theorem pointedInput_readback (X : OriginalPointed.Category.{u}) :
    pointedInput (OriginalPointed.source X) (OriginalPointed.target X) = X := by
  apply StructuredArrow.obj_ext (T := 𝟭 SSet.{u})
    (pointedInput (OriginalPointed.source X) (OriginalPointed.target X)) X rfl
  change SSet.boundaryOneMap (OriginalPointed.sourceVertex X) (OriginalPointed.targetVertex X) ≫ 𝟙 X.right = X.hom
  rw [Category.comp_id]
  exact (OriginalPointed.hom_eq_boundaryOneMap X).symm

/-- The same full original pointed Joyal Hom diagram is the whole original right mapping space of the arbitrary pointed
target. -/
def arbitraryPointedHomIso (X : OriginalPointed.Category.{u}) :
    SSet.mappingSpaceRight X.right (OriginalPointed.source X) (OriginalPointed.target X) ≅
      pointedJoyalDiagram.op ⋙ yoneda.obj (pointedCopyFunctor.obj X) :=
  pointedJoyalHomSpaceIso (OriginalPointed.source X) (OriginalPointed.target X) ≪≫
    eqToIso (congrArg (fun K => pointedJoyalDiagram.op ⋙ yoneda.obj (pointedCopyFunctor.obj K))
      (pointedInput_readback X))

end CategoryTheory.CoherentRealization.OriginalRawRightMapping
