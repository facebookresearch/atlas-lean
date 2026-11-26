/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentInnerFaceEndpoints
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomRetargetAlgebra

/-!
# Actual common charts of constructed negative Hom-box pieces

The two actual common-face charts keep the original outer endpoints.
Their constructed negative-piece maps agree on the entire original
common Hom. The proof uses the actual horn's face-functor equality and
exact original source retargeting; no compatibility result is an input.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HornNegativeCommon
open SimplicialEnrichment HornBoxFaces
variable {n : ℕ} (j k : Interior.{u} n) (hjk : HornBoxFaces.vertex j < HornBoxFaces.vertex k)

/-- The first original common ordinal Hom chart, retaining the actual zero/last endpoints in its supplied face. -/
def leftChart : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 1))) (ULift.up.{u} (Fin.last n))) ⟶
    HomBoxDecomposition.negative (ULift.up 0) j.val (ULift.up (Fin.last (n + 2))) :=
  (coherentSimplexMap (SimplexCategory.δ ((HornBoxFaces.vertex k).pred (Fin.ne_zero_of_lt hjk)))).map
    (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last n))) ≫
      eqToHom (congrArg₂ (fun a b : ULift.{u} (Fin (n + 2)) => nerve (SimplicialThickening.Path a b))
        (ULift.ext (InnerFaceEndpoints.left_zero j k hjk)) (ULift.ext (InnerFaceEndpoints.left_last j k hjk))) ≫
          (negativeChart j).hom

/-- The other original common Hom chart into its supplied negative face, with the same outer endpoints. -/
def rightChart : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 1))) (ULift.up.{u} (Fin.last n))) ⟶
    HomBoxDecomposition.negative (ULift.up 0) k.val (ULift.up (Fin.last (n + 2))) :=
  (coherentSimplexMap (SimplexCategory.δ ((HornBoxFaces.vertex j).castPred (Fin.ne_last_of_lt hjk)))).map
    (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last n))) ≫
      eqToHom (congrArg₂ (fun a b : ULift.{u} (Fin (n + 2)) => nerve (SimplicialThickening.Path a b))
        (ULift.ext (InnerFaceEndpoints.right_zero j k hjk)) (ULift.ext (InnerFaceEndpoints.right_last j k hjk))) ≫
          (negativeChart k).hom

variable {C : Carrier.{u}} {i : Fin (n + 3)}
  (f : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)
  (hj : HornBoxFaces.vertex j ≠ i) (hk : HornBoxFaces.vertex k ≠ i)

/-- The first common chart reads back the whole actual restricted face functor at the original outer objects. -/
theorem left_readback : leftChart j k hjk ≫ negativeMap f j hj =
    HornHomFaces.retargetMap
      (coherentSimplexMap (SimplexCategory.δ ((HornBoxFaces.vertex k).pred (Fin.ne_zero_of_lt hjk))) ≫
        HornFaces.faceFunctor f (HornBoxFaces.vertex j) hj)
      (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last n)))
      ((congrArg (HornFaces.faceFunctor f (HornBoxFaces.vertex j) hj).obj
        (congrArg (fun a : ULift.{u} (Fin (n + 2)) => (SimplicialThickening.mk a))
          (ULift.ext (InnerFaceEndpoints.left_zero j k hjk)))).trans
        ((HornFaces.faceFunctor_obj f (HornBoxFaces.vertex j) hj (.mk (ULift.up 0))).trans
          (congrArg (HornFaces.object f) (source_zero j))))
      ((congrArg (HornFaces.faceFunctor f (HornBoxFaces.vertex j) hj).obj
        (congrArg (fun a : ULift.{u} (Fin (n + 2)) => (SimplicialThickening.mk a))
          (ULift.ext (InnerFaceEndpoints.left_last j k hjk)))).trans
        ((HornFaces.faceFunctor_obj f (HornBoxFaces.vertex j) hj (.mk (ULift.up (Fin.last (n + 1))))).trans
          (congrArg (HornFaces.object f) (target_last j)))) := by
  let d := coherentSimplexMap (SimplexCategory.δ ((HornBoxFaces.vertex k).pred (Fin.ne_zero_of_lt hjk)))
  let S := eqToHom (congrArg₂ (fun a b : ULift.{u} (Fin (n + 2)) => nerve (SimplicialThickening.Path a b))
    (ULift.ext (InnerFaceEndpoints.left_zero j k hjk)) (ULift.ext (InnerFaceEndpoints.left_last j k hjk)))
  let E := negativeChart j
  let N := negativeMap f j hj
  have h₁ := (Category.assoc (d.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last n)))) (S ≫ E.hom) N).trans
    (congrArg (fun h => d.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last n))) ≫ h) (Category.assoc S E.hom N))
  have h₂ := congrArg (fun h => d.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last n))) ≫ (S ≫ h))
    (negativeMap_readback f j hj)
  have h₃ := HomRetargetAlgebra.restriction_reindex d (HornFaces.faceFunctor f (HornBoxFaces.vertex j) hj)
    (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last n)))
    (congrArg (fun a : ULift.{u} (Fin (n + 2)) => SimplicialThickening.mk a) (ULift.ext
      (InnerFaceEndpoints.left_zero j k hjk)))
    (congrArg (fun a : ULift.{u} (Fin (n + 2)) => SimplicialThickening.mk a) (ULift.ext
      (InnerFaceEndpoints.left_last j k hjk)))
    ((HornFaces.faceFunctor_obj f (HornBoxFaces.vertex j) hj (.mk (ULift.up 0))).trans
      (congrArg (HornFaces.object f) (source_zero j)))
    ((HornFaces.faceFunctor_obj f (HornBoxFaces.vertex j) hj (.mk (ULift.up (Fin.last (n + 1))))).trans
      (congrArg (HornFaces.object f) (target_last j)))
  exact h₁.trans (h₂.trans h₃)

/-- The other chart reads back its whole actual face functor at exactly the same original outer objects. -/
theorem right_readback : rightChart j k hjk ≫ negativeMap f k hk =
    HornHomFaces.retargetMap
      (coherentSimplexMap (SimplexCategory.δ ((HornBoxFaces.vertex j).castPred (Fin.ne_last_of_lt hjk))) ≫
        HornFaces.faceFunctor f (HornBoxFaces.vertex k) hk)
      (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last n)))
      ((congrArg (HornFaces.faceFunctor f (HornBoxFaces.vertex k) hk).obj
        (congrArg (fun a : ULift.{u} (Fin (n + 2)) => SimplicialThickening.mk a)
          (ULift.ext (InnerFaceEndpoints.right_zero j k hjk)))).trans
        ((HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk (.mk (ULift.up 0))).trans
          (congrArg (HornFaces.object f) (source_zero k))))
      ((congrArg (HornFaces.faceFunctor f (HornBoxFaces.vertex k) hk).obj
        (congrArg (fun a : ULift.{u} (Fin (n + 2)) => SimplicialThickening.mk a)
          (ULift.ext (InnerFaceEndpoints.right_last j k hjk)))).trans
        ((HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk (.mk (ULift.up (Fin.last (n + 1))))).trans
          (congrArg (HornFaces.object f) (target_last k)))) := by
  let d := coherentSimplexMap (SimplexCategory.δ ((HornBoxFaces.vertex j).castPred (Fin.ne_last_of_lt hjk)))
  let S := eqToHom (congrArg₂ (fun a b : ULift.{u} (Fin (n + 2)) => nerve (SimplicialThickening.Path a b))
    (ULift.ext (InnerFaceEndpoints.right_zero j k hjk)) (ULift.ext (InnerFaceEndpoints.right_last j k hjk)))
  let E := negativeChart k
  let N := negativeMap f k hk
  have h₁ := (Category.assoc (d.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last n)))) (S ≫ E.hom) N).trans
    (congrArg (fun h => d.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last n))) ≫ h) (Category.assoc S E.hom N))
  have h₂ := congrArg (fun h => d.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last n))) ≫ (S ≫ h))
    (negativeMap_readback f k hk)
  have h₃ := HomRetargetAlgebra.restriction_reindex d (HornFaces.faceFunctor f (HornBoxFaces.vertex k) hk)
    (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last n)))
    (congrArg (fun a : ULift.{u} (Fin (n + 2)) => SimplicialThickening.mk a) (ULift.ext
      (InnerFaceEndpoints.right_zero j k hjk)))
    (congrArg (fun a : ULift.{u} (Fin (n + 2)) => SimplicialThickening.mk a) (ULift.ext
      (InnerFaceEndpoints.right_last j k hjk)))
    ((HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk (.mk (ULift.up 0))).trans
      (congrArg (HornFaces.object f) (source_zero k)))
    ((HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk (.mk (ULift.up (Fin.last (n + 1))))).trans
      (congrArg (HornFaces.object f) (target_last k)))
  exact h₁.trans (h₂.trans h₃)

/-- Both constructed negative pieces agree on the entire actual common original Hom chart. -/
theorem agreement : leftChart j k hjk ≫ negativeMap f j hj = rightChart j k hjk ≫ negativeMap f k hk :=
  (left_readback j k hjk f hj).trans
    ((HornHomFaces.retargetMap_eq
      (HornFaces.faceFunctor_compatibility f (HornBoxFaces.vertex j) (HornBoxFaces.vertex k) hj hk hjk)
      (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last n))) _ _ _ _).trans (right_readback j k hjk f hk).symm)

end CategoryTheory.CoherentRealization.HornNegativeCommon
