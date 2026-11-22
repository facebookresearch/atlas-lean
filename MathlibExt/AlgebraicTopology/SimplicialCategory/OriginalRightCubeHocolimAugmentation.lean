/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRightCubeMaximumWeak
import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalSimplexDiagram
import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanIndexNerveSquare
import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanIndexAugmentationSquare

/-!
# The SAME original quotient-cube BK augmentation to its genuine realization

Every original simplex contributes its full original quotient cube and
maximum. The canonical entire elements/simplex dictionary retains all
operators and full input maps. Its exact augmentation square with the
proved original standard-simplex resolution and SAME all-input maximum
proves weakness of the actual Q-realization BK augmentation.
-/

noncomputable section

universe u

open CategoryTheory Opposite Limits
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalRightCubeRealization

/-- The actual full original elements-to-simplex input dictionary for the same original input. -/
def elementsToSimplex (K : SSet.{u}) : K.Elementsᵒᵖ ⥤ SSet.SimplexIndex K :=
  (Functor.Elements.costructuredArrowULiftYonedaEquivalence.{u,0,0} K).functor

/-- The SAME original coefficient maximum into the same complete original standard-simplex input diagram. -/
def maximumDiagramMap (K : SSet.{u}) :
    diagram K ⋙ SSet.uliftFunctor.{u,u} ⟶ elementsToSimplex K ⋙ SSet.originalSimplexDiagram K where
  app e := (SSet.uliftContainedIso.{u,0} ((diagram K).obj e)).hom ≫ RightCubeMaximum.map e.unop.obj.unop.len
  naturality e d f := by
    have hLift := SSet.uliftContainedIso_naturality.{u,0} (RightCubeCosimplicialMaps.map f.unop.hom.unop)
    have hMax : RightCubeCosimplicialMaps.map f.unop.hom.unop ≫ RightCubeMaximum.map d.unop.obj.unop.len =
        RightCubeMaximum.map e.unop.obj.unop.len ≫ SSet.stdSimplex.map f.unop.hom.unop :=
      RightCubeMaximumNaturality.map.naturality f.unop.hom.unop
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun g => g ≫ RightCubeMaximum.map d.unop.obj.unop.len) hLift).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun g => (SSet.uliftContainedIso.{u,0} ((diagram K).obj e)).hom ≫ g) hMax)))

/-- Every full original quotient-cube coefficient inserts into its SAME genuine original realization. -/
def inputAugmentation (K : SSet.{u}) : diagram K ⟶ (CategoryTheory.Functor.const K.Elementsᵒᵖ).obj (object K) where
  app e := insertion K e
  naturality e d f := by
    have h : (diagram K).map f ≫ insertion K d = insertion K e := insertion_naturality K f
    exact h.trans (Category.comp_id _).symm

/-- The actual original quotient-cube BK augmentation to its SAME complete original realization. -/
def hocolimAugmentation (K : SSet.{u}) : SSet.bkHocolim (diagram K) ⟶ object K :=
  SSet.bkAugmentation (inputAugmentation K)

/-- Every same original coefficient retains its whole original maximum/augmentation source triangle. -/
theorem maximumDiagramMap_augmentation (K : SSet.{u}) (e : K.Elementsᵒᵖ) :
    (maximumDiagramMap K).app e ≫ (SSet.originalSimplexCocone K).app ((elementsToSimplex K).obj e) =
      SSet.uliftFunctor.{u,u}.map ((maximumCocone K).ι.app e) ≫ (SSet.uliftContainedIso.{u,0} K).hom := by
  have h := SSet.uliftContainedIso_naturality.{u,0} ((maximumCocone K).ι.app e)
  exact (Category.assoc _ _ _).trans h.symm

end CategoryTheory.CoherentRealization.OriginalRightCubeRealization
