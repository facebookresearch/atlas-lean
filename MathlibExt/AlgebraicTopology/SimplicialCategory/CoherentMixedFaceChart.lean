/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornInteriorFace
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentSupportedCompositionFace
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornNegativeMaps

/-!
# The actual mixed negative and positive coherent Hom face

The source positive Hom chart in an original supplied ordinal face is
identified with its actual negative-positive intersection. Both outer
endpoints and the individual image middle vertex are preserved.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.MixedFaceChart
open SimplicialEnrichment HornBoxFaces HornInteriorFace
variable {n : ℕ} (k : Interior.{u} n) (t : SourceInterior n)

/-- The actual fixed-outer intersection of the supplied negative face and the image positive face. -/
def face : (outerHom.{u} n).Subcomplex :=
  HomBoxDecomposition.negative (ULift.up 0) k.val (ULift.up (Fin.last (n + 2))) ⊓
    CompositionFace.positive (ULift.up 0) (middle k t).val (ULift.up (Fin.last (n + 2)))

private def rawFace :
    (nerve (SimplicialThickening.Path
      ((OrdinalFace.embedding (HornBoxFaces.vertex k)) (ULift.up (0 : Fin (n + 2))))
      ((OrdinalFace.embedding (HornBoxFaces.vertex k)) (ULift.up (Fin.last (n + 1)))))).Subcomplex :=
  HomBoxDecomposition.negative ((OrdinalFace.embedding (HornBoxFaces.vertex k)) (ULift.up (0 : Fin (n + 2)))) k.val
      ((OrdinalFace.embedding (HornBoxFaces.vertex k)) (ULift.up (Fin.last (n + 1)))) ⊓
    CompositionFace.positive ((OrdinalFace.embedding (HornBoxFaces.vertex k)) (ULift.up (0 : Fin (n + 2))))
      (middle k t).val ((OrdinalFace.embedding (HornBoxFaces.vertex k)) (ULift.up (Fin.last (n + 1))))

private theorem image_face_eq :
    SupportedCompositionFace.face (OrdinalFace.embedding (HornBoxFaces.vertex k))
      (ULift.up (0 : Fin (n + 2))) (ULift.up t.val) (ULift.up (Fin.last (n + 1))) = rawFace k t :=
  congrArg (fun S => S ⊓ CompositionFace.positive
      ((OrdinalFace.embedding (HornBoxFaces.vertex k)) (ULift.up (0 : Fin (n + 2))))
      (middle k t).val ((OrdinalFace.embedding (HornBoxFaces.vertex k)) (ULift.up (Fin.last (n + 1)))))
    (OrdinalFace.imageFace_eq_negative (HornBoxFaces.vertex k) (ULift.up 0) (ULift.up (Fin.last (n + 1))))

private def imageIso :
    (SupportedCompositionFace.face (OrdinalFace.embedding (HornBoxFaces.vertex k))
      (ULift.up (0 : Fin (n + 2))) (ULift.up t.val) (ULift.up (Fin.last (n + 1))) : SSet.{u}) ≅ rawFace k t :=
  SSet.Subcomplex.eqToIso (image_face_eq k t)

private def endpointIso : (rawFace k t : SSet.{u}) ≅ face k t :=
  eqToIso (congrArg₂ (fun a b : ULift.{u} (Fin (n + 3)) =>
    ((HomBoxDecomposition.negative a k.val b ⊓ CompositionFace.positive a (middle k t).val b) :
      (nerve (SimplicialThickening.Path a b)).Subcomplex).toSSet)
    (ULift.ext (source_zero k)) (ULift.ext (target_last k)))

/-- The genuine original two-Hom product chart on the entire fixed-outer mixed face. -/
def chart :
    nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 2))) (ULift.up.{u} t.val)) ⊗
      nerve (SimplicialThickening.Path (ULift.up.{u} t.val) (ULift.up.{u} (Fin.last (n + 1)))) ≅ face k t :=
  CompositionFace.positiveIso (ULift.up 0) (ULift.up t.val) (ULift.up (Fin.last (n + 1))) ≪≫
    SupportedCompositionFace.faceIso (OrdinalFace.embedding (HornBoxFaces.vertex k))
      (ULift.up 0) (ULift.up t.val) (ULift.up (Fin.last (n + 1))) ≪≫ imageIso k t ≪≫ endpointIso k t

private theorem endpoint_ambient : (endpointIso k t).hom ≫ (face k t).ι =
    (rawFace k t).ι ≫ eqToHom (congrArg₂ (fun a b : ULift.{u} (Fin (n + 3)) => nerve (SimplicialThickening.Path a b))
      (ULift.ext (source_zero k)) (ULift.ext (target_last k))) := by
  exact (eqToHom_naturality
    (f := fun p : ULift.{u} (Fin (n + 3)) × ULift.{u} (Fin (n + 3)) =>
      ((HomBoxDecomposition.negative p.1 k.val p.2 ⊓ CompositionFace.positive p.1 (middle k t).val p.2) :
        (nerve (SimplicialThickening.Path p.1 p.2)).Subcomplex).toSSet)
    (g := fun p : ULift.{u} (Fin (n + 3)) × ULift.{u} (Fin (n + 3)) => nerve (SimplicialThickening.Path p.1 p.2))
    (fun p => ((HomBoxDecomposition.negative p.1 k.val p.2 ⊓ CompositionFace.positive p.1 (middle k t).val p.2) :
      (nerve (SimplicialThickening.Path p.1 p.2)).Subcomplex).ι)
    (show (((OrdinalFace.embedding (HornBoxFaces.vertex k)) (ULift.up (0 : Fin (n + 2)))),
        ((OrdinalFace.embedding (HornBoxFaces.vertex k)) (ULift.up (Fin.last (n + 1))))) =
      ((ULift.up (0 : Fin (n + 3))), ULift.up (Fin.last (n + 2))) from
        Prod.ext (ULift.ext (source_zero k)) (ULift.ext (target_last k)))).symm

/-- The chart retains the whole original ordinal Hom map after the original source composition. -/
theorem chart_ambient : (chart k t).hom ≫ (face k t).ι =
    CompositionFace.composition (ULift.up.{u} (0 : Fin (n + 2))) (ULift.up.{u} t.val) (ULift.up.{u}
      (Fin.last (n + 1))) ≫
      (coherentSimplexMap (SimplexCategory.δ (HornBoxFaces.vertex k))).map
        (.mk (ULift.up (0 : Fin (n + 2)))) (.mk (ULift.up (Fin.last (n + 1)))) ≫
      eqToHom (congrArg₂ (fun a b : ULift.{u} (Fin (n + 3)) => nerve (SimplicialThickening.Path a b))
        (ULift.ext (source_zero k)) (ULift.ext (target_last k))) := by
  let P := CompositionFace.positiveIso (ULift.up.{u} (0 : Fin (n + 2))) (ULift.up.{u} t.val) (ULift.up.{u}
    (Fin.last (n + 1)))
  let S := SupportedCompositionFace.faceIso (OrdinalFace.embedding (HornBoxFaces.vertex k))
    (ULift.up.{u} (0 : Fin (n + 2))) (ULift.up.{u} t.val) (ULift.up.{u} (Fin.last (n + 1)))
  let T := eqToHom (congrArg₂ (fun a b : ULift.{u} (Fin (n + 3)) => nerve (SimplicialThickening.Path a b))
    (ULift.ext (source_zero k)) (ULift.ext (target_last k)))
  have hI : (imageIso k t).hom ≫ (rawFace k t).ι =
      (SupportedCompositionFace.face (OrdinalFace.embedding (HornBoxFaces.vertex k))
        (ULift.up 0) (ULift.up t.val) (ULift.up (Fin.last (n + 1)))).ι := SSet.Subcomplex.homOfLE_ι
          (image_face_eq k t).le
  have hS : S.hom ≫ (imageIso k t).hom ≫ (rawFace k t).ι =
      (CompositionFace.positive (ULift.up 0) (ULift.up t.val) (ULift.up (Fin.last (n + 1)))).ι ≫
        (coherentSimplexMap (SimplexCategory.δ (HornBoxFaces.vertex k))).map
          (.mk (ULift.up (0 : Fin (n + 2)))) (.mk (ULift.up (Fin.last (n + 1)))) :=
    (congrArg (fun g => S.hom ≫ g) hI).trans
      (SupportedCompositionFace.faceIso_ι (OrdinalFace.embedding (HornBoxFaces.vertex k))
        (ULift.up 0) (ULift.up t.val) (ULift.up (Fin.last (n + 1))))
  have h := (congrArg (fun g => P.hom ≫ S.hom ≫ (imageIso k t).hom ≫ g) (endpoint_ambient k t)).trans
    ((congrArg (fun g => P.hom ≫ g ≫ T) hS).trans
      (congrArg (fun g => g ≫ (coherentSimplexMap (SimplexCategory.δ (HornBoxFaces.vertex k))).map
        (.mk (ULift.up (0 : Fin (n + 2)))) (.mk (ULift.up (Fin.last (n + 1)))) ≫ T)
        (CompositionFace.positiveIso_composition (ULift.up 0) (ULift.up t.val) (ULift.up (Fin.last (n + 1))))))
  change (((P.hom ≫ S.hom) ≫ (imageIso k t).hom) ≫ (endpointIso k t).hom) ≫ (face k t).ι =
    CompositionFace.composition (ULift.up.{u} (0 : Fin (n + 2))) (ULift.up.{u} t.val) (ULift.up.{u}
      (Fin.last (n + 1))) ≫
      (coherentSimplexMap (SimplexCategory.δ (HornBoxFaces.vertex k))).map
        (.mk (ULift.up (0 : Fin (n + 2)))) (.mk (ULift.up (Fin.last (n + 1)))) ≫ T
  rw [Category.assoc, Category.assoc, Category.assoc]
  exact h

/-- The actual negative projection of the same whole mixed face. -/
def negativeProjection : (face k t : SSet.{u}) ⟶
    HomBoxDecomposition.negative (ULift.up 0) k.val (ULift.up (Fin.last (n + 2))) :=
  SSet.Subcomplex.homOfLE (show face k t ≤ _ from inf_le_left)

/-- The actual positive projection of that same whole mixed face. -/
def positiveProjection : (face k t : SSet.{u}) ⟶
    CompositionFace.positive (ULift.up 0) (middle k t).val (ULift.up (Fin.last (n + 2))) :=
  SSet.Subcomplex.homOfLE (show face k t ≤ _ from inf_le_right)

/-- The negative projection reads back the original source union and the genuine whole supplied negative chart. -/
theorem negative_chart : (chart k t).hom ≫ negativeProjection k t =
    CompositionFace.composition (ULift.up.{u} (0 : Fin (n + 2))) (ULift.up.{u} t.val) (ULift.up.{u}
      (Fin.last (n + 1))) ≫
      (negativeChart k).hom := by
  apply (cancel_mono (HomBoxDecomposition.negative (ULift.up 0) k.val (ULift.up (Fin.last (n + 2)))).ι).mp
  have hL := (Category.assoc (chart k t).hom (negativeProjection k t)
    (HomBoxDecomposition.negative (ULift.up 0) k.val (ULift.up (Fin.last (n + 2)))).ι).trans
      (congrArg (fun g => (chart k t).hom ≫ g) (SSet.Subcomplex.homOfLE_ι (show face k t ≤ _ from inf_le_left)))
  have hR := (Category.assoc
    (CompositionFace.composition (ULift.up.{u} (0 : Fin (n + 2))) (ULift.up.{u} t.val) (ULift.up.{u}
      (Fin.last (n + 1))))
    (negativeChart k).hom (HomBoxDecomposition.negative (ULift.up 0) k.val (ULift.up (Fin.last (n + 2)))).ι).trans
      (congrArg (fun g => CompositionFace.composition (ULift.up.{u} (0 : Fin (n + 2))) (ULift.up.{u} t.val)
        (ULift.up.{u} (Fin.last (n + 1))) ≫ g) (HornNegativeMaps.chart_operator k))
  exact hL.trans ((chart_ambient k t).trans hR.symm)

end CategoryTheory.CoherentRealization.MixedFaceChart
