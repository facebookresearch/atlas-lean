/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceAmbientHomNaturality
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentBeadCoefficientGluing
import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceConcatenationMaps

/-!
# Full original raw Hom maps into the concatenated necklace

Both entire native inclusions retain the original source, common pivot
and target. Their full ambient Hom squares are the original prefix and
suffix coefficient maps, including zero-dimensional necklaces.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalNecklaceHom

open SSet.OriginalNecklace SSet.OriginalTwoBead.OrdinalCharts OriginalBead

variable (T U : Data)

/-- The complete original first inclusion retains its literal source vertex. -/
theorem concatLeft_sourceVertex :
    (concatLeft.{u} T U).app (op ⦋0⦌) (sourceVertex T) = sourceVertex (T.concat U) :=
  (SSet.yonedaEquiv_comp T.source (concatLeft T U)).symm.trans
    (congrArg SSet.yonedaEquiv (concatLeft_source T U))

/-- The complete original first inclusion retains the common original pivot. -/
theorem concatLeft_targetVertex :
    (concatLeft.{u} T U).app (op ⦋0⦌) (targetVertex T) =
      nativeVertex (T.concat U) (pivot T.dimension U.dimension) :=
  (SSet.yonedaEquiv_comp T.target (concatLeft T U)).symm.trans
    (congrArg SSet.yonedaEquiv (concatLeft_target T U))

/-- The complete original second inclusion starts at that same original pivot. -/
theorem concatRight_sourceVertex :
    (concatRight.{u} T U).app (op ⦋0⦌) (sourceVertex U) =
      nativeVertex (T.concat U) (pivot T.dimension U.dimension) :=
  (SSet.yonedaEquiv_comp U.source (concatRight T U)).symm.trans
    (congrArg SSet.yonedaEquiv (concatRight_source T U))

/-- The complete original second inclusion retains its literal target vertex. -/
theorem concatRight_targetVertex :
    (concatRight.{u} T U).app (op ⦋0⦌) (targetVertex U) = targetVertex (T.concat U) :=
  (SSet.yonedaEquiv_comp U.target (concatRight T U)).symm.trans
    (congrArg SSet.yonedaEquiv (concatRight_target T U))

/-- The SAME entire original prefix map on its full raw Hom. -/
def concatLeftHomMap : hom T.object.{u} (sourceVertex T) (targetVertex T) ⟶
    hom (T.concat U).object.{u} (sourceVertex (T.concat U))
      (nativeVertex (T.concat U) (pivot T.dimension U.dimension)) :=
  pointedHomMap (concatLeft T U) (concatLeft_sourceVertex T U) (concatLeft_targetVertex T U)

/-- The SAME entire original suffix map on its full raw Hom. -/
def concatRightHomMap : hom U.object.{u} (sourceVertex U) (targetVertex U) ⟶
    hom (T.concat U).object.{u} (nativeVertex (T.concat U) (pivot T.dimension U.dimension))
      (targetVertex (T.concat U)) :=
  pointedHomMap (concatRight T U) (concatRight_sourceVertex T U) (concatRight_targetVertex T U)

/-- The entire original prefix Hom square retains the original full coefficient image. -/
theorem concatLeftHomMap_ambient :
    concatLeftHomMap.{u} T U ≫ ambientIntervalMap (T.concat U) 0 (pivot T.dimension U.dimension) =
      ambientHomMap T ≫ CoefficientGluing.leftMap.{u} T.dimension U.dimension := by
  have h := ambientIntervalMap_square_retarget T (T.concat U) (concatLeft T U)
    (prefixOperator T.dimension U.dimension) (concatLeft_ι T U) 0 (pivot T.dimension U.dimension)
    (prefix_zero T.dimension U.dimension) (prefix_last T.dimension U.dimension)
  exact h.trans (congrArg (fun e => ambientHomMap T ≫ e)
    (CoefficientGluing.leftMap_original.{u} T.dimension U.dimension).symm)

/-- The entire original suffix Hom square retains the original full coefficient image. -/
theorem concatRightHomMap_ambient :
    concatRightHomMap.{u} T U ≫
        ambientIntervalMap (T.concat U) (pivot T.dimension U.dimension) (Fin.last (T.concat U).dimension) =
      ambientHomMap U ≫ CoefficientGluing.rightMap.{u} T.dimension U.dimension := by
  have h := ambientIntervalMap_square_retarget U (T.concat U) (concatRight T U)
    (suffixOperator T.dimension U.dimension) (concatRight_ι T U) (pivot T.dimension U.dimension)
    (Fin.last (T.concat U).dimension) (suffix_zero T.dimension U.dimension)
    (suffix_last T.dimension U.dimension)
  exact h.trans (congrArg (fun e => ambientHomMap U ≫ e)
    (CoefficientGluing.rightMap_original.{u} T.dimension U.dimension).symm)

end CategoryTheory.CoherentRealization.OriginalNecklaceHom
