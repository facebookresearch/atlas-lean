/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFullBoundaryPositiveMaps
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentHomChartRestriction
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornNegativeIntersection

/-!
# Genuine full-boundary negative-face compatibility

Both existing original common charts read the same supplied complete
boundary subface. The actual full-boundary face equality proves their
agreement, including the low-dimensional negative intersections. No
missing-index hypothesis or compatibility outcome is assumed.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.BoundaryNegativeCommon
open SimplicialEnrichment HornBoxFaces HornHomFaces
variable {C : Carrier.{u}} {n : ℕ}
  (f : (∂Δ[n+2] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)
  (j k : Interior.{u} n) (hjk : HornBoxFaces.vertex j < HornBoxFaces.vertex k)

/-- The same original first restricted boundary face. -/
abbrev leftFace :=
  coherentSimplexMap (SimplexCategory.δ ((HornBoxFaces.vertex k).pred (Fin.ne_zero_of_lt hjk))) ≫
    BoundaryFaces.faceFunctor f (HornBoxFaces.vertex j)

/-- The same original other restricted boundary face. -/
abbrev rightFace :=
  coherentSimplexMap (SimplexCategory.δ ((HornBoxFaces.vertex j).castPred (Fin.ne_last_of_lt hjk))) ≫
    BoundaryFaces.faceFunctor f (HornBoxFaces.vertex k)

/-- The original first restricted face retains its same original zero vertex. -/
theorem left_zero : (leftFace f j k hjk).obj (.mk (ULift.up (0 : Fin (n+1)))) = BoundaryFaces.object f 0 :=
  (BoundaryFaces.faceFunctor_obj f (HornBoxFaces.vertex j) _).trans
    (congrArg (BoundaryFaces.object f)
      ((congrArg (HornBoxFaces.vertex j).succAbove (InnerFaceEndpoints.left_zero j k hjk)).trans (source_zero j)))

/-- The original first restricted face retains its same original last vertex. -/
theorem left_last : (leftFace f j k hjk).obj (.mk (ULift.up (Fin.last n))) =
    BoundaryFaces.object f (Fin.last (n+2)) :=
  (BoundaryFaces.faceFunctor_obj f (HornBoxFaces.vertex j) _).trans
    (congrArg (BoundaryFaces.object f)
      ((congrArg (HornBoxFaces.vertex j).succAbove (InnerFaceEndpoints.left_last j k hjk)).trans (target_last j)))

/-- The original other restricted face retains the same original zero vertex. -/
theorem right_zero : (rightFace f j k hjk).obj (.mk (ULift.up (0 : Fin (n+1)))) = BoundaryFaces.object f 0 :=
  (BoundaryFaces.faceFunctor_obj f (HornBoxFaces.vertex k) _).trans
    (congrArg (BoundaryFaces.object f)
      ((congrArg (HornBoxFaces.vertex k).succAbove (InnerFaceEndpoints.right_zero j k hjk)).trans (source_zero k)))

/-- The original other restricted face retains the same original last vertex. -/
theorem right_last : (rightFace f j k hjk).obj (.mk (ULift.up (Fin.last n))) =
    BoundaryFaces.object f (Fin.last (n+2)) :=
  (BoundaryFaces.faceFunctor_obj f (HornBoxFaces.vertex k) _).trans
    (congrArg (BoundaryFaces.object f)
      ((congrArg (HornBoxFaces.vertex k).succAbove (InnerFaceEndpoints.right_last j k hjk)).trans (target_last k)))

/-- The whole original first common chart reads precisely its complete original boundary subface. -/
theorem left_readback :
    HornNegativeCommon.leftChart j k hjk ≫ BoundaryHomFaces.negativeMap f j =
      retargetMap (leftFace f j k hjk)
        (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last n))) (left_zero f j k hjk) (left_last f j k hjk) :=
  OriginalHomChartRestriction.retarget_inverse
    (coherentSimplexMap (SimplexCategory.δ ((HornBoxFaces.vertex k).pred (Fin.ne_zero_of_lt hjk))))
    (BoundaryFaces.faceFunctor f (HornBoxFaces.vertex j))
    (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last n)))
    (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (n+1))))
    (congrArg SimplicialThickening.mk (ULift.ext (InnerFaceEndpoints.left_zero j k hjk)))
    (congrArg SimplicialThickening.mk (ULift.ext (InnerFaceEndpoints.left_last j k hjk)))
    ((BoundaryFaces.faceFunctor_obj f (HornBoxFaces.vertex j) _).trans
      (congrArg (BoundaryFaces.object f) (source_zero j)))
    ((BoundaryFaces.faceFunctor_obj f (HornBoxFaces.vertex j) _).trans
      (congrArg (BoundaryFaces.object f) (target_last j))) (negativeChart j)

/-- The whole original other common chart reads precisely its same complete original boundary subface. -/
theorem right_readback :
    HornNegativeCommon.rightChart j k hjk ≫ BoundaryHomFaces.negativeMap f k =
      retargetMap (rightFace f j k hjk)
        (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last n))) (right_zero f j k hjk) (right_last f j k hjk) :=
  OriginalHomChartRestriction.retarget_inverse
    (coherentSimplexMap (SimplexCategory.δ ((HornBoxFaces.vertex j).castPred (Fin.ne_last_of_lt hjk))))
    (BoundaryFaces.faceFunctor f (HornBoxFaces.vertex k))
    (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last n)))
    (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (n+1))))
    (congrArg SimplicialThickening.mk (ULift.ext (InnerFaceEndpoints.right_zero j k hjk)))
    (congrArg SimplicialThickening.mk (ULift.ext (InnerFaceEndpoints.right_last j k hjk)))
    ((BoundaryFaces.faceFunctor_obj f (HornBoxFaces.vertex k) _).trans
      (congrArg (BoundaryFaces.object f) (source_zero k)))
    ((BoundaryFaces.faceFunctor_obj f (HornBoxFaces.vertex k) _).trans
      (congrArg (BoundaryFaces.object f) (target_last k))) (negativeChart k)

/-- Both whole original negative maps agree on their same actual original common chart. -/
theorem agreement :
    HornNegativeCommon.leftChart j k hjk ≫ BoundaryHomFaces.negativeMap f j =
      HornNegativeCommon.rightChart j k hjk ≫ BoundaryHomFaces.negativeMap f k :=
  (left_readback f j k hjk).trans
    ((retargetMap_eq (BoundaryFaces.faceFunctor_compatibility f _ _ hjk) _ _ _ _ _ _).trans
      (right_readback f j k hjk).symm)

end CategoryTheory.CoherentRealization.BoundaryNegativeCommon
