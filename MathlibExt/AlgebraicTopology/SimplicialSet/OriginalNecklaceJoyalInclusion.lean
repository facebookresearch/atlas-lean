/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceFirstCrossingRank
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.InnerAnodyneCategorical
import MathlibExt.AlgebraicTopology.SimplicialSet.BoundaryOneMapNaturality
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceAmbientHom

/-!
# The same original native necklace pointed Joyal inclusion

The actual native inclusion is inner anodyne by its full original
first-crossing pairing. Its original two endpoint maps give the actual
pointed Joyal weak inclusion into the same complete ambient simplex.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.OriginalNecklace

open CategoryTheory.CoherentRealization.OriginalNecklaceHom

/-- The actual original native inclusion is a categorical equivalence in every universe. -/
theorem inclusion_categoricalEquivalence (T : Data) :
    SSet.categoricalEquivalences (complex.{u} T.joints).ι :=
  SSet.categoricalEquivalences.of_innerAnodyneExtensions
    (CrossedJoints.inclusion_innerAnodyne T.joints)

/-- The original native necklace with its same initial and terminal marked boundary vertices. -/
def pointedObject (T : Data) : Under (∂Δ[1] : SSet.{u}) :=
  Under.mk (SSet.boundaryOneMap (sourceVertex T) (targetVertex T))

/-- The same complete ambient simplex with the literal images of both original native vertices. -/
def ambientPointedObject (T : Data) : Under (∂Δ[1] : SSet.{u}) :=
  Under.mk (SSet.boundaryOneMap
    ((complex.{u} T.joints).ι.app (op ⦋0⦌) (sourceVertex T))
    ((complex.{u} T.joints).ι.app (op ⦋0⦌) (targetVertex T)))

/-- The whole actual pointed inclusion retains the same complete original native simplicial map. -/
def pointedInclusion (T : Data) : pointedObject.{u} T ⟶ ambientPointedObject.{u} T :=
  Under.homMk (complex T.joints).ι
    (SSet.boundaryOneMap_naturality _ (sourceVertex T) (targetVertex T))

/-- The original pointed inclusion reads back its same entire original native simplicial inclusion. -/
theorem pointedInclusion_right (T : Data) :
    (pointedInclusion.{u} T).right = (complex T.joints).ι := rfl

end SSet.OriginalNecklace
