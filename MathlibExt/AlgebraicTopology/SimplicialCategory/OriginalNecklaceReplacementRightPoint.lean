/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceReplacementMappingPoint
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedRightMappingFunctor

/-!
# The actual original native replacement right-mapping point map is weak

The canonical original unit and native inclusion determine the same
original endpoint images of the actual ambient extension. The full
original right-mapping map to the same ordinal right-mapping space is
weak; its original point projection gives genuine contractibility.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalNecklaceHom

open SSet.OriginalNecklace OriginalRawRightMapping

/-- The actual replacement has the same whole original source endpoint unit map. -/
def replacementSource (T : Data) :
    (Δ[0] : SSet.{u}) ⟶ SSet.innerHornReplacement.obj T.object :=
  T.source ≫ SSet.innerHornReplacementUnit.app T.object

/-- The actual replacement has the same whole original target endpoint unit map. -/
def replacementTarget (T : Data) :
    (Δ[0] : SSet.{u}) ⟶ SSet.innerHornReplacement.obj T.object :=
  T.target ≫ SSet.innerHornReplacementUnit.app T.object

/-- The same entire original ambient extension retains the original initial ordinal endpoint. -/
theorem replacementAmbientExtension_source (T : Data) :
    replacementSource.{u} T ≫ replacementAmbientExtension T = simplexVertex T.dimension 0 :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun f => T.source ≫ f) (replacementAmbientExtension_unit T)).trans
      (SSet.OriginalNecklace.vertexMap_ι T.joints 0))

/-- The same entire original ambient extension retains the original terminal ordinal endpoint. -/
theorem replacementAmbientExtension_target (T : Data) :
    replacementTarget.{u} T ≫ replacementAmbientExtension T = simplexVertex T.dimension (Fin.last T.dimension) :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun f => T.target ≫ f) (replacementAmbientExtension_unit T)).trans
      (SSet.OriginalNecklace.vertexMap_ι T.joints (Fin.last T.dimension)))

/-- The full actual original native replacement-to-ambient right-mapping map retains both original endpoint
equalities. -/
def replacementRightMap (T : Data) :
    SSet.mappingSpaceRight (SSet.innerHornReplacement.obj T.object.{u}) (replacementSource T) (replacementTarget T) ⟶
      SSet.mappingSpaceRight (Δ[T.dimension] : SSet.{u}) (simplexVertex T.dimension 0)
        (simplexVertex T.dimension (Fin.last T.dimension)) :=
  SSet.mappingSpaceRight.map _ _ _ (replacementAmbientExtension T) ≫
    (SSet.PointedRightMappingSpace.endpointIso (replacementAmbientExtension_source T)
      (replacementAmbientExtension_target T)).hom

/-- The same actual full original native replacement-to-ambient right-mapping map is genuinely weak. -/
theorem replacementRightMap_weak (T : Data) : SSet.realizationWeakEquivalences (replacementRightMap.{u} T) := by
  let _ := SSet.innerHornReplacement_quasicategory T.object.{u}
  exact SSet.realizationWeakEquivalences.comp_mem _ _
    ((replacementAmbientExtension_categorical T).rightMappingSpaceMap_weak (replacementSource T) (replacementTarget T))
    (SSet.realizationWeakEquivalences.of_isIso
      (SSet.PointedRightMappingSpace.endpointIso (replacementAmbientExtension_source T)
        (replacementAmbientExtension_target T)).hom)

/-- The same whole original native replacement right-mapping point projection is genuinely weak. -/
theorem replacementRightMapping_point_weak (T : Data) :
    SSet.realizationWeakEquivalences (SSet.stdSimplex.isTerminalObj₀.from
      (SSet.mappingSpaceRight (SSet.innerHornReplacement.obj T.object.{u})
        (replacementSource T) (replacementTarget T))) := by
  have h := SSet.realizationWeakEquivalences.comp_mem _ _ (replacementRightMap_weak T)
    (simplexMappingPoint_weak (0 : Fin (T.dimension + 1)) (Fin.last T.dimension) (Fin.zero_le _))
  have he : replacementRightMap T ≫ SSet.stdSimplex.isTerminalObj₀.from
      (SSet.mappingSpaceRight (Δ[T.dimension] : SSet.{u}) (simplexVertex T.dimension 0)
        (simplexVertex T.dimension (Fin.last T.dimension))) =
      SSet.stdSimplex.isTerminalObj₀.from
        (SSet.mappingSpaceRight (SSet.innerHornReplacement.obj T.object.{u})
          (replacementSource T) (replacementTarget T)) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  exact he ▸ h

end CategoryTheory.CoherentRealization.OriginalNecklaceHom
