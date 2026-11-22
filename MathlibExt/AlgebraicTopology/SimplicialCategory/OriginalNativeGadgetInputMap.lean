/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalGadgetRawHomDiagram
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNativePointedRawCoefficientIso
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceGadgetCommaPoint
import MathlibExt.AlgebraicTopology.SimplicialSet.NerveULiftToTargetNaturality

/-!
# Every same original native input in the full gadget category

The proved full native input equivalence and original gadget functor
retain every original necklace, input and arrow. Their same original
nerve map is weak by genuine full comma recognition and the actual
coefficient universe lift.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalGadgetComparison

open OriginalNecklaceInput OriginalPointed

/-- The entire original native input category maps to the same full original gadget inputs with its literal original
endpoint boundary. -/
def nativeOriginalGadgetInputs (K : SSet.{u}) (x y : K _⦋0⦌) :
    Object K x y ⥤ Input (Under.mk (SSet.boundaryOneMap x y)) :=
  (pointedInputEquivalence K x y).functor ⋙ nativeGadgetInputs (Under.mk (SSet.boundaryOneMap x y))

/-- Every same original native input retains its entire literal original input map. -/
theorem nativeOriginalGadgetInputs_input (K : SSet.{u}) (x y : K _⦋0⦌) (T : Object K x y) :
    (((nativeOriginalGadgetInputs K x y).obj T).hom).right = T.input := rfl

/-- The whole same original raw coefficient diagram is the full original pointed native coefficient diagram. -/
theorem nativeOriginalGadgetInputs_rawHomDiagram (K : SSet.{u}) (x y : K _⦋0⦌) :
    nativeOriginalGadgetInputs K x y ⋙ rawHomDiagram (Under.mk (SSet.boundaryOneMap x y)) =
      OriginalNecklaceInput.forget K x y ⋙ pointedNativeFunctor ⋙ homFunctor := rfl

/-- The SAME original full native gadget input nerve map is weak with its explicit original coefficient universe
lift. -/
theorem nativeOriginalGadgetInputs_nerve_weak (K : SSet.{u}) (x y : K _⦋0⦌) :
    SSet.realizationWeakEquivalences (SSet.nerveMapULiftToTarget.{u,u+1,0,u} (nativeOriginalGadgetInputs K x y)) := by
  let e := pointedInputEquivalence K x y
  let G := nativeGadgetInputs (Under.mk (SSet.boundaryOneMap x y))
  have hF := nerveMap_mem_realizationWeakEquivalences_of_isEquivalence e.functor
  have hLift := (SSet.realizationWeak_ulift_map_iff.{u,u+1} (nerveMap e.functor)).mpr hF
  have hG := SSet.nerveMapULiftToTarget_weak_of_rightComma.{u,u+1,0,u} G
    (nativeGadgetCommaNerve_point_weak (Under.mk (SSet.boundaryOneMap x y)))
  have h := SSet.realizationWeakEquivalences.comp_mem _ _ hLift hG
  exact SSet.nerveMapULiftToTarget_precomp.{u,u+1,0,u} e.functor G ▸ h

end CategoryTheory.CoherentRealization.OriginalGadgetComparison
