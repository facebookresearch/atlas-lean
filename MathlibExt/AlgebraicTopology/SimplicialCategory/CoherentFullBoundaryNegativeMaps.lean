/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFullBoundaryVertices
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornBoxFaces

/-!
# Full original boundary negative Hom maps

Every actual interior boundary face has its complete original negative
Hom map, through the same existing chart and its true original
endpoints. It agrees with the same map extracted from any retaining
original horn; no compatibility or weak outcome is assumed.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.BoundaryHomFaces
open SimplicialEnrichment HornBoxFaces

variable {C : Carrier.{u}} {n : ℕ}
  (f : (∂Δ[n + 2] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)

/-- The whole original negative Hom map of every supplied full-boundary interior face. -/
def negativeMap (k : Interior.{u} n) :
    (HomBoxDecomposition.negative (ULift.up 0) k.val (ULift.up (Fin.last (n + 2))) : SSet.{u}) ⟶
      (BoundaryFaces.object f 0 ⟶[SSet.{u}] BoundaryFaces.object f (Fin.last (n + 2))) :=
  (negativeChart k).inv ≫ HornHomFaces.retargetMap (BoundaryFaces.faceFunctor f
    (HornBoxFaces.vertex k))
    (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (n + 1))))
    ((BoundaryFaces.faceFunctor_obj f (HornBoxFaces.vertex k) _).trans
      (congrArg (BoundaryFaces.object f) (source_zero k)))
    ((BoundaryFaces.faceFunctor_obj f (HornBoxFaces.vertex k) _).trans
      (congrArg (BoundaryFaces.object f) (target_last k)))

/-- The actual original negative chart reads back the same whole supplied boundary Hom map. -/
theorem negativeMap_readback (k : Interior.{u} n) :
    (negativeChart k).hom ≫ negativeMap f k =
      HornHomFaces.retargetMap (BoundaryFaces.faceFunctor f (HornBoxFaces.vertex k))
        (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (n + 1))))
        ((BoundaryFaces.faceFunctor_obj f (HornBoxFaces.vertex k) _).trans
          (congrArg (BoundaryFaces.object f) (source_zero k)))
        ((BoundaryFaces.faceFunctor_obj f (HornBoxFaces.vertex k) _).trans
          (congrArg (BoundaryFaces.object f) (target_last k))) :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ _) (negativeChart k).hom_inv_id).trans (Category.id_comp _))

/-- Any original horn retaining that full face extracts precisely the same whole boundary
negative Hom map. -/
theorem negativeMap_horn (i : Fin (n + 3)) (k : Interior.{u} n) (hk : HornBoxFaces.vertex k ≠ i) :
    HornBoxFaces.negativeMap (BoundaryFaces.horn f i) k hk = negativeMap f k := by
  unfold HornBoxFaces.negativeMap negativeMap
  congr 1

end CategoryTheory.CoherentRealization.BoundaryHomFaces
