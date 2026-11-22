/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNativeGadgetInputMap
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceRawCoefficientContractible
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceHocolimRawAugmentation
import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanIndexAugmentationSquare

/-!
# The SAME full original gadget raw-Hom augmentation is weak

Both original native pointed coefficient directions retain all input
maps and literal endpoint equations. The exact full BK index and
augmentation squares transfer the proved SAME native augmentation to
the entire original gadget diagram. No mapping comparison or model
equivalence outcome is assumed.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalGadgetComparison

open OriginalNecklaceInput OriginalPointed

/-- Both full original target Hom directions retain the original endpoints in their complete one-boundary. -/
def boundaryRawHomIso (K : SSet.{u}) (x y : K _⦋0⦌) :
    hom K x y ≅ homObject (Under.mk (SSet.boundaryOneMap x y)) :=
  eqToIso (congrArg₂ (fun a b : K _⦋0⦌ => hom K a b)
    (sourceVertex_boundaryOneMap x y).symm (targetVertex_boundaryOneMap x y).symm)

/-- Every original native raw coefficient maps by its SAME original full pointed raw coefficient isomorphism. -/
def nativeOriginalRawHomComparison (K : SSet.{u}) (x y : K _⦋0⦌) :
    rawCoefficientDiagram K x y ⋙ SSet.uliftFunctor.{u+1,u} ⟶
      nativeOriginalGadgetInputs K x y ⋙ liftedRawHomDiagram (Under.mk (SSet.boundaryOneMap x y)) where
  app T := SSet.uliftFunctor.map (nativePointedRawCoefficientIso.hom.app T.necklace)
  naturality T U f := by
    have h : OriginalNecklaceHom.nativeHomMap f.necklaceMap ≫ nativePointedRawCoefficientIso.hom.app U.necklace =
        nativePointedRawCoefficientIso.hom.app T.necklace ≫ homFunctor.map (pointedNativeFunctor.map f.necklaceMap) :=
      nativePointedRawCoefficientIso.hom.naturality f.necklaceMap
    exact (SSet.uliftFunctor.map_comp _ _).symm.trans
      ((congrArg SSet.uliftFunctor.map h).trans (SSet.uliftFunctor.map_comp _ _))

/-- Every actual original native input retains its SAME complete raw-Hom augmentation triangle. -/
theorem nativeOriginalRawHomComparison_augmentation (K : SSet.{u}) (x y : K _⦋0⦌) (T : Object K x y) :
    (nativeOriginalRawHomComparison K x y).app T ≫
      (liftedRawHomInputAugmentation (Under.mk (SSet.boundaryOneMap x y))).app
        ((nativeOriginalGadgetInputs K x y).obj T) =
    SSet.uliftFunctor.{u+1,u}.map ((rawInputAugmentation K x y).app T) ≫
      SSet.uliftFunctor.map (boundaryRawHomIso K x y).hom := by
  have h : nativePointedRawCoefficientIso.hom.app T.necklace ≫ homFunctor.map (pointedInputMap T) =
      (rawInputAugmentation K x y).app T ≫ (boundaryRawHomIso K x y).hom :=
    EnrichedFunctor.homMap_endpoint_square (realizationMap T.input)
      (pointedNative_sourceVertex T.necklace).symm (pointedNative_targetVertex T.necklace).symm
      (sourceVertex_boundaryOneMap x y).symm (targetVertex_boundaryOneMap x y).symm
      (input_source T) (input_target T)
      (sourceVertex_map (pointedInputMap T)) (targetVertex_map (pointedInputMap T))
  exact (SSet.uliftFunctor.map_comp _ _).symm.trans
    ((congrArg SSet.uliftFunctor.map h).trans (SSet.uliftFunctor.map_comp _ _))

/-- The SAME full original native-to-gadget raw-Hom BK index map is weak from its actual original coefficient point
maps. -/
theorem nativeOriginalRawHomIndexComparison_weak (K : SSet.{u}) (x y : K _⦋0⦌) :
    SSet.realizationWeakEquivalences (SSet.bkHocolimIndexMapULift.{u,u+1,0,u}
      (nativeOriginalGadgetInputs K x y) (nativeOriginalRawHomComparison K x y)) :=
  SSet.bkHocolimIndexMapULift_weak_of_pointCoefficients.{u,u+1,0,u} _ _
    (fun T => OriginalNecklaceHom.rawCoefficient_to_point_weak T.necklace)
    (liftedRawHomDiagram_point_weak (Under.mk (SSet.boundaryOneMap x y)))
    (nativeOriginalGadgetInputs_nerve_weak K x y)

/-- The SAME actual full original gadget raw-Hom augmentation is weak for every original simplicial set and both
original endpoints. -/
theorem rawHomHocolimAugmentation_weak (K : SSet.{u}) (x y : K _⦋0⦌) :
    SSet.realizationWeakEquivalences (rawHomHocolimAugmentation (Under.mk (SSet.boundaryOneMap x y))) := by
  have hSquare := SSet.bkHocolimIndexMapULift_augmentationSquare.{u,u+1,0,u}
    (nativeOriginalGadgetInputs K x y) (nativeOriginalRawHomComparison K x y)
    (rawInputAugmentation K x y) (liftedRawHomInputAugmentation (Under.mk (SSet.boundaryOneMap x y)))
    (SSet.uliftFunctor.{u+1,u}.map (boundaryRawHomIso K x y).hom)
    (nativeOriginalRawHomComparison_augmentation K x y)
  have hSource := (SSet.realizationWeak_ulift_map_iff.{u,u+1} (hocolimRawAugmentation K x y)).mpr
    (hocolimRawAugmentation_weak K x y)
  have hTarget := SSet.realizationWeakEquivalences.of_isIso
    (SSet.uliftFunctor.{u+1,u}.map (boundaryRawHomIso K x y).hom)
  have hComposite := SSet.realizationWeakEquivalences.comp_mem _ _ hSource hTarget
  exact SSet.realizationWeakEquivalences.of_precomp _ _ (nativeOriginalRawHomIndexComparison_weak K x y)
    (hSquare.symm ▸ hComposite)

end CategoryTheory.CoherentRealization.OriginalGadgetComparison
