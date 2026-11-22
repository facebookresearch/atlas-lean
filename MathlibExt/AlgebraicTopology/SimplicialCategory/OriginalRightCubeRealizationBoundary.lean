/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRightCubeRealizationNaturality
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeLatchingMono
import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalInnerBoundaryProperFaces

/-!
# Genuine boundary presentation of the SAME quotient-cube realization

The actual original all-proper-face boundary colimit is preserved
by the SAME realization adjunction. Its complete standard-simplex
isomorphism identifies the result with the genuine original
quotient-cube latching boundary. Every original face is retained.
-/

noncomputable section
universe u
open CategoryTheory Opposite Limits
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalRightCubeRealization
open SimplicialSpace.OriginalInnerRealization

/-- The actual whole original proper-face diagram isomorphism between realized simplices and original cubes. -/
def properFaceIso (n : ℕ) :
    properFaceSimplexDiagram.{u} n ⋙ functor.{u} ≅ RightCubeLatchingDiagram.diagram.{u} n :=
  NatIso.ofComponents
    (fun e => simplexIso e.unop.obj.right.unop)
    (fun f => simplexIso_naturality f.unop.hom.right.unop)

/-- The genuine full original boundary cocone after the original quotient-cube realization and exact standard-simplex
chart. -/
def boundaryCocone (n : ℕ) : Cocone (RightCubeLatchingDiagram.diagram.{u} n) :=
  (Cocone.precompose (properFaceIso.{u} n).inv).obj
    (functor.{u}.mapCocone (properFaceBoundaryCocone.{u} n))

/-- Every original proper-face leg is the same full original inverse simplex chart followed by the realized original
boundary face. -/
theorem boundaryCocone_app (n : ℕ) (e : (SimplicialObject.matchingIndex n)ᵒᵖ) :
    (boundaryCocone.{u} n).ι.app e =
      (simplexIso e.unop.obj.right.unop).inv ≫
        map (properFaceBoundaryInclusion.{u} e.unop) := rfl

/-- The SAME original full boundary realization is the actual colimit of ALL original proper-face cubes. -/
def boundaryIsColimit (n : ℕ) : IsColimit (boundaryCocone.{u} n) :=
  (IsColimit.precomposeHomEquiv (properFaceIso.{u} n).symm
    (functor.{u}.mapCocone (properFaceBoundaryCocone.{u} n))).symm
      (isColimitOfPreserves functor.{u} (properFaceBoundaryIsColimit.{u} n))

/-- The genuine original boundary realization isomorphism with the whole original support boundary. -/
def boundaryIso (n : ℕ) :
    object (∂Δ[n] : SSet.{u}) ≅ (RightCubeSupportBoundary.boundary.{u} n : SSet.{u}) :=
  IsColimit.coconePointUniqueUpToIso (boundaryIsColimit.{u} n)
    (RightCubeLatchingColimit.isColimit.{u} n)

/-- Each complete original proper face is retained by the SAME actual boundary isomorphism. -/
theorem boundaryIso_face (n : ℕ) (e : (SimplicialObject.matchingIndex n)ᵒᵖ) :
    (boundaryCocone.{u} n).ι.app e ≫ (boundaryIso n).hom =
      RightCubeLatchingDiagram.inclusion e.unop :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (boundaryIsColimit.{u} n)
    (RightCubeLatchingColimit.isColimit.{u} n) e

/-- The SAME original realized boundary inclusion retains exactly the original support-boundary inclusion and full cube
chart. -/
theorem boundaryIso_inclusion (n : ℕ) :
    (boundaryIso.{u} n).hom ≫ (RightCubeSupportBoundary.boundary n).ι =
      map (SSet.boundary.{u} n).ι ≫ (simplexIso ⦋n⦌).hom := by
  apply (boundaryIsColimit.{u} n).hom_ext
  intro e
  have hFace := boundaryIso_face n e
  have hι := RightCubeLatchingDiagram.inclusion_ι.{u} e.unop
  have hNat := simplexIso_naturality.{u} e.unop.obj.hom.unop
  have hQ : (simplexIso e.unop.obj.right.unop).inv ≫
      map (SSet.stdSimplex.map e.unop.obj.hom.unop) ≫ (simplexIso ⦋n⦌).hom =
        RightCubeCosimplicial.diagram.map e.unop.obj.hom.unop :=
    (congrArg (fun q => (simplexIso e.unop.obj.right.unop).inv ≫ q) hNat).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun q => q ≫ _) (simplexIso e.unop.obj.right.unop).inv_hom_id).trans
          (Category.id_comp _)))
  have hL : (boundaryCocone.{u} n).ι.app e ≫
      ((boundaryIso n).hom ≫ (RightCubeSupportBoundary.boundary n).ι) =
      RightCubeCosimplicial.diagram.map e.unop.obj.hom.unop :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ _) hFace).trans hι)
  have hR : (boundaryCocone.{u} n).ι.app e ≫
      (map (SSet.boundary.{u} n).ι ≫ (simplexIso ⦋n⦌).hom) =
      RightCubeCosimplicial.diagram.map e.unop.obj.hom.unop := by
    calc
      _ = (simplexIso e.unop.obj.right.unop).inv ≫
          ((map (properFaceBoundaryInclusion.{u} e.unop) ≫ map (SSet.boundary.{u} n).ι) ≫
            (simplexIso ⦋n⦌).hom) := by
        exact (congrArg (fun q => q ≫
          (map (SSet.boundary.{u} n).ι ≫ (simplexIso ⦋n⦌).hom)) (boundaryCocone_app n e)).trans
            ((Category.assoc _ _ _).trans
              (congrArg (fun q => (simplexIso e.unop.obj.right.unop).inv ≫ q)
                (Category.assoc _ _ _).symm))
      _ = (simplexIso e.unop.obj.right.unop).inv ≫
          (map (properFaceBoundaryInclusion.{u} e.unop ≫ (SSet.boundary.{u} n).ι) ≫
            (simplexIso ⦋n⦌).hom) :=
        congrArg (fun q => (simplexIso e.unop.obj.right.unop).inv ≫ (q ≫ (simplexIso ⦋n⦌).hom))
          (map_comp _ _).symm
      _ = (simplexIso e.unop.obj.right.unop).inv ≫
          (map (SSet.stdSimplex.map e.unop.obj.hom.unop) ≫ (simplexIso ⦋n⦌).hom) :=
        congrArg (fun q => (simplexIso e.unop.obj.right.unop).inv ≫ (map q ≫ (simplexIso ⦋n⦌).hom))
          (properFaceBoundaryInclusion_ι.{u} e.unop)
      _ = _ := hQ
  exact hL.trans hR.symm

end CategoryTheory.CoherentRealization.OriginalRightCubeRealization
