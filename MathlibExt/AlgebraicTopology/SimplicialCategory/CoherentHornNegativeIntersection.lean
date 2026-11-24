/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornNegativeCommon
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornNegativeMaps
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentDoubleOrdinalFace

/-!
# The genuine common chart of fixed-outer negative Hom-box faces

The supported common ordinal Hom chart is identified with the actual
intersection of the two constructed negative box faces. Its two original
outer endpoints are retained by the proved interior face equations.
The whole ambient chart map is the original composite ordinal Hom map
with precisely those endpoint transports.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HornNegativeIntersection
open SimplicialEnrichment HornBoxFaces
variable {n : ℕ} (j k : Interior.{u} n) (hjk : HornBoxFaces.vertex j < HornBoxFaces.vertex k)

/-- The actual intersection of the two negative faces at the fixed original outer endpoints. -/
def face : (outerHom.{u} n).Subcomplex :=
  HomBoxDecomposition.negative (ULift.up 0) j.val (ULift.up (Fin.last (n + 2))) ⊓
    HomBoxDecomposition.negative (ULift.up 0) k.val (ULift.up (Fin.last (n + 2)))

/-- The exact common-chart endpoint transport to the same actual outer negative intersection. -/
def endpointIso :
    (DoubleOrdinalFace.face (HornBoxFaces.vertex j) (HornBoxFaces.vertex k) hjk
      (ULift.up (0 : Fin (n + 1))) (ULift.up (Fin.last n)) : SSet.{u}) ≅ face j k :=
  eqToIso (congrArg₂ (fun a b : ULift.{u} (Fin (n + 3)) =>
    ((HomBoxDecomposition.negative a j.val b ⊓ HomBoxDecomposition.negative a k.val b) :
      (nerve (SimplicialThickening.Path a b)).Subcomplex).toSSet)
    (InnerFaceEndpoints.common_zero j k hjk) (InnerFaceEndpoints.common_last j k hjk))

/-- The genuine original common Hom chart onto the actual fixed-outer negative intersection. -/
def commonChart :
    nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 1))) (ULift.up.{u} (Fin.last n))) ≅ face j k :=
  DoubleOrdinalFace.homIso (HornBoxFaces.vertex j) (HornBoxFaces.vertex k) hjk
    (ULift.up 0) (ULift.up (Fin.last n)) ≪≫ endpointIso j k hjk

/-- The fixed-outer common chart reads back the entire original composite coherent ordinal Hom map. -/
theorem chart_operator : (commonChart j k hjk).hom ≫ (face j k).ι =
    (coherentSimplexMap (SimplexCategory.δ ((HornBoxFaces.vertex k).pred (Fin.ne_zero_of_lt hjk))) ≫
      coherentSimplexMap (SimplexCategory.δ (HornBoxFaces.vertex j))).map
        (.mk (ULift.up (0 : Fin (n + 1)))) (.mk (ULift.up (Fin.last n))) ≫
          eqToHom (congrArg₂ (fun a b : ULift.{u} (Fin (n + 3)) => nerve (SimplicialThickening.Path a b))
            (InnerFaceEndpoints.common_zero j k hjk) (InnerFaceEndpoints.common_last j k hjk)) := by
  let E := DoubleOrdinalFace.homIso (HornBoxFaces.vertex j) (HornBoxFaces.vertex k) hjk
    (ULift.up (0 : Fin (n + 1))) (ULift.up (Fin.last n))
  let S := endpointIso j k hjk
  let T := eqToHom (congrArg₂ (fun a b : ULift.{u} (Fin (n + 3)) => nerve (SimplicialThickening.Path a b))
    (InnerFaceEndpoints.common_zero j k hjk) (InnerFaceEndpoints.common_last j k hjk))
  have h := eqToHom_naturality
    (f := fun p : ULift.{u} (Fin (n + 3)) × ULift.{u} (Fin (n + 3)) =>
      ((HomBoxDecomposition.negative p.1 j.val p.2 ⊓ HomBoxDecomposition.negative p.1 k.val p.2) :
        (nerve (SimplicialThickening.Path p.1 p.2)).Subcomplex).toSSet)
    (g := fun p : ULift.{u} (Fin (n + 3)) × ULift.{u} (Fin (n + 3)) => nerve (SimplicialThickening.Path p.1 p.2))
    (fun p => ((HomBoxDecomposition.negative p.1 j.val p.2 ⊓ HomBoxDecomposition.negative p.1 k.val p.2) :
      (nerve (SimplicialThickening.Path p.1 p.2)).Subcomplex).ι)
    (show (TwoOutsideFaces.point (HornBoxFaces.vertex j) (HornBoxFaces.vertex k) hjk (ULift.up (0 : Fin (n + 1))),
        TwoOutsideFaces.point (HornBoxFaces.vertex j) (HornBoxFaces.vertex k) hjk (ULift.up (Fin.last n))) =
      ((ULift.up (0 : Fin (n + 3))), (ULift.up (Fin.last (n + 2)))) from
        Prod.ext (InnerFaceEndpoints.common_zero j k hjk) (InnerFaceEndpoints.common_last j k hjk))
  have hS : S.hom ≫ (face j k).ι = (DoubleOrdinalFace.face (HornBoxFaces.vertex j) (HornBoxFaces.vertex k) hjk
      (ULift.up (0 : Fin (n + 1))) (ULift.up (Fin.last n))).ι ≫ T := h.symm
  exact (Category.assoc E.hom S.hom _).trans
    ((congrArg (fun h => E.hom ≫ h) hS).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun h => h ≫ T) (DoubleOrdinalFace.homIso_operator (HornBoxFaces.vertex j)
          (HornBoxFaces.vertex k) hjk (ULift.up 0) (ULift.up (Fin.last n))))))

/-- The actual first negative-face inclusion from the fixed-outer intersection. -/
def firstInclusion : (face j k : SSet.{u}) ⟶
    HomBoxDecomposition.negative (ULift.up 0) j.val (ULift.up (Fin.last (n + 2))) :=
  SSet.Subcomplex.homOfLE (show face j k ≤ _ from inf_le_left)

/-- The actual other negative-face inclusion from that same fixed-outer intersection. -/
def secondInclusion : (face j k : SSet.{u}) ⟶
    HomBoxDecomposition.negative (ULift.up 0) k.val (ULift.up (Fin.last (n + 2))) :=
  SSet.Subcomplex.homOfLE (show face j k ≤ _ from inf_le_right)

private def leftAmbient :
    nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 1))) (ULift.up.{u} (Fin.last n))) ⟶ outerHom.{u} n :=
  HornHomFaces.retargetMap
    (coherentSimplexMap (SimplexCategory.δ ((HornBoxFaces.vertex k).pred (Fin.ne_zero_of_lt hjk))) ≫
      coherentSimplexMap (SimplexCategory.δ (HornBoxFaces.vertex j)))
    (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last n)))
    (congrArg (fun a : ULift.{u} (Fin (n + 3)) => SimplicialThickening.mk a) (InnerFaceEndpoints.common_zero j k hjk))
    (congrArg (fun a : ULift.{u} (Fin (n + 3)) => SimplicialThickening.mk a) (InnerFaceEndpoints.common_last j k hjk))

private def rightAmbient :
    nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 1))) (ULift.up.{u} (Fin.last n))) ⟶ outerHom.{u} n :=
  HornHomFaces.retargetMap
    (coherentSimplexMap (SimplexCategory.δ ((HornBoxFaces.vertex j).castPred (Fin.ne_last_of_lt hjk))) ≫
      coherentSimplexMap (SimplexCategory.δ (HornBoxFaces.vertex k)))
    (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last n)))
    (congrArg (fun a : ULift.{u} (Fin (n + 3)) => SimplicialThickening.mk a)
      ((TwoOutsideFaces.point_right (HornBoxFaces.vertex j) (HornBoxFaces.vertex k) hjk (ULift.up 0)).symm.trans
        (InnerFaceEndpoints.common_zero j k hjk)))
    (congrArg (fun a : ULift.{u} (Fin (n + 3)) => SimplicialThickening.mk a)
      ((TwoOutsideFaces.point_right (HornBoxFaces.vertex j) (HornBoxFaces.vertex k) hjk (ULift.up (Fin.last
        n))).symm.trans
        (InnerFaceEndpoints.common_last j k hjk)))

private theorem left_ambient : HornNegativeCommon.leftChart j k hjk ≫
    (HomBoxDecomposition.negative (ULift.up 0) j.val (ULift.up (Fin.last (n + 2)))).ι = leftAmbient j k hjk := by
  let d := coherentSimplexMap (SimplexCategory.δ ((HornBoxFaces.vertex k).pred (Fin.ne_zero_of_lt hjk)))
  let G := coherentSimplexMap (SimplexCategory.δ (HornBoxFaces.vertex j))
  let S := eqToHom (congrArg₂ (fun a b : ULift.{u} (Fin (n + 2)) => nerve (SimplicialThickening.Path a b))
    (ULift.ext (InnerFaceEndpoints.left_zero j k hjk)) (ULift.ext (InnerFaceEndpoints.left_last j k hjk)))
  let E := negativeChart j
  let I := (HomBoxDecomposition.negative (ULift.up 0) j.val (ULift.up (Fin.last (n + 2)))).ι
  have h₁ := (Category.assoc (d.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last n)))) (S ≫ E.hom) I).trans
    (congrArg (fun h => d.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last n))) ≫ h) (Category.assoc S E.hom I))
  have h₂ := congrArg (fun h => d.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last n))) ≫ (S ≫ h))
    (HornNegativeMaps.chart_operator j)
  have h₃ := HomRetargetAlgebra.restriction_reindex d G (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last n)))
    (congrArg (fun a : ULift.{u} (Fin (n + 2)) => SimplicialThickening.mk a) (ULift.ext
      (InnerFaceEndpoints.left_zero j k hjk)))
    (congrArg (fun a : ULift.{u} (Fin (n + 2)) => SimplicialThickening.mk a) (ULift.ext
      (InnerFaceEndpoints.left_last j k hjk)))
    (congrArg (fun a : ULift.{u} (Fin (n + 3)) => SimplicialThickening.mk a) (ULift.ext (source_zero j)))
    (congrArg (fun a : ULift.{u} (Fin (n + 3)) => SimplicialThickening.mk a) (ULift.ext (target_last j)))
  exact h₁.trans (h₂.trans h₃)

private theorem right_ambient : HornNegativeCommon.rightChart j k hjk ≫
    (HomBoxDecomposition.negative (ULift.up 0) k.val (ULift.up (Fin.last (n + 2)))).ι = rightAmbient j k hjk := by
  let d := coherentSimplexMap (SimplexCategory.δ ((HornBoxFaces.vertex j).castPred (Fin.ne_last_of_lt hjk)))
  let G := coherentSimplexMap (SimplexCategory.δ (HornBoxFaces.vertex k))
  let S := eqToHom (congrArg₂ (fun a b : ULift.{u} (Fin (n + 2)) => nerve (SimplicialThickening.Path a b))
    (ULift.ext (InnerFaceEndpoints.right_zero j k hjk)) (ULift.ext (InnerFaceEndpoints.right_last j k hjk)))
  let E := negativeChart k
  let I := (HomBoxDecomposition.negative (ULift.up 0) k.val (ULift.up (Fin.last (n + 2)))).ι
  have h₁ := (Category.assoc (d.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last n)))) (S ≫ E.hom) I).trans
    (congrArg (fun h => d.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last n))) ≫ h) (Category.assoc S E.hom I))
  have h₂ := congrArg (fun h => d.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last n))) ≫ (S ≫ h))
    (HornNegativeMaps.chart_operator k)
  have h₃ := HomRetargetAlgebra.restriction_reindex d G (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last n)))
    (congrArg (fun a : ULift.{u} (Fin (n + 2)) => SimplicialThickening.mk a) (ULift.ext
      (InnerFaceEndpoints.right_zero j k hjk)))
    (congrArg (fun a : ULift.{u} (Fin (n + 2)) => SimplicialThickening.mk a) (ULift.ext
      (InnerFaceEndpoints.right_last j k hjk)))
    (congrArg (fun a : ULift.{u} (Fin (n + 3)) => SimplicialThickening.mk a) (ULift.ext (source_zero k)))
    (congrArg (fun a : ULift.{u} (Fin (n + 3)) => SimplicialThickening.mk a) (ULift.ext (target_last k)))
  exact h₁.trans (h₂.trans h₃)

private theorem ambient_agreement : rightAmbient j k hjk = leftAmbient j k hjk := by
  have hδ : SimplexCategory.δ ((HornBoxFaces.vertex j).castPred (Fin.ne_last_of_lt hjk)) ≫
      SimplexCategory.δ (HornBoxFaces.vertex k) =
    SimplexCategory.δ ((HornBoxFaces.vertex k).pred (Fin.ne_zero_of_lt hjk)) ≫ SimplexCategory.δ
      (HornBoxFaces.vertex j) := by
    apply SimplexCategory.δ_comp_δ'
    simpa only [Fin.castSucc_castPred] using hjk
  have hF : coherentSimplexMap (SimplexCategory.δ ((HornBoxFaces.vertex j).castPred (Fin.ne_last_of_lt hjk))) ≫
      coherentSimplexMap (SimplexCategory.δ (HornBoxFaces.vertex k)) =
    coherentSimplexMap (SimplexCategory.δ ((HornBoxFaces.vertex k).pred (Fin.ne_zero_of_lt hjk))) ≫
      coherentSimplexMap (SimplexCategory.δ (HornBoxFaces.vertex j)) :=
    (coherentSimplices.map_comp _ _).symm.trans
      ((congrArg (fun θ : ⦋n⦌ ⟶ ⦋n + 2⦌ => coherentSimplexMap θ) hδ).trans (coherentSimplices.map_comp _ _))
  exact HornHomFaces.retargetMap_eq hF (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last n))) _ _ _ _

/-- The actual common chart's first projection is the original constructed first negative-piece chart. -/
theorem first_chart : (commonChart j k hjk).hom ≫ firstInclusion j k = HornNegativeCommon.leftChart j k hjk := by
  apply (cancel_mono (HomBoxDecomposition.negative (ULift.up 0) j.val (ULift.up (Fin.last (n + 2)))).ι).mp
  have h₁ := (Category.assoc (commonChart j k hjk).hom (firstInclusion j k)
    (HomBoxDecomposition.negative (ULift.up 0) j.val (ULift.up (Fin.last (n + 2)))).ι).trans
      (congrArg (fun h => (commonChart j k hjk).hom ≫ h) (SSet.Subcomplex.homOfLE_ι (show face j k ≤ _ from
        inf_le_left)))
  exact h₁.trans ((chart_operator j k hjk).trans (left_ambient j k hjk).symm)

/-- The same common chart's other projection retains the original constructed other negative-piece chart. -/
theorem second_chart : (commonChart j k hjk).hom ≫ secondInclusion j k = HornNegativeCommon.rightChart j k hjk := by
  apply (cancel_mono (HomBoxDecomposition.negative (ULift.up 0) k.val (ULift.up (Fin.last (n + 2)))).ι).mp
  have h₁ := (Category.assoc (commonChart j k hjk).hom (secondInclusion j k)
    (HomBoxDecomposition.negative (ULift.up 0) k.val (ULift.up (Fin.last (n + 2)))).ι).trans
      (congrArg (fun h => (commonChart j k hjk).hom ≫ h) (SSet.Subcomplex.homOfLE_ι (show face j k ≤ _ from
        inf_le_right)))
  exact h₁.trans ((chart_operator j k hjk).trans ((right_ambient j k hjk).trans (ambient_agreement j k hjk)).symm)

include hjk in
/-- The two constructed negative Hom-box pieces agree on their actual fixed-outer intersection for the
  supplied original horn. -/
theorem agreement {C : Carrier.{u}} {i : Fin (n + 3)}
    (f : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)
    (hj : HornBoxFaces.vertex j ≠ i) (hk : HornBoxFaces.vertex k ≠ i) :
    firstInclusion j k ≫ negativeMap f j hj = secondInclusion j k ≫ negativeMap f k hk := by
  apply (cancel_epi (commonChart j k hjk).hom).mp
  have hL := (Category.assoc (commonChart j k hjk).hom (firstInclusion j k) (negativeMap f j hj)).symm.trans
    (congrArg (fun h => h ≫ negativeMap f j hj) (first_chart j k hjk))
  have hR := (Category.assoc (commonChart j k hjk).hom (secondInclusion j k) (negativeMap f k hk)).symm.trans
    (congrArg (fun h => h ≫ negativeMap f k hk) (second_chart j k hjk))
  exact hL.trans ((HornNegativeCommon.agreement j k hjk f hj hk).trans hR.symm)

end CategoryTheory.CoherentRealization.HornNegativeIntersection
