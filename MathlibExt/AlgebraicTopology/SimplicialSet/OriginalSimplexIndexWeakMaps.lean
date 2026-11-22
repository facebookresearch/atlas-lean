/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalSimplexDiagram
import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanIndexNerveSquare
import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanIndexAugmentationSquare
import MathlibExt.AlgebraicTopology.SimplicialSet.NerveULiftToTargetWeak

/-!
# The SAME full original simplex-index nerve map recognizes weak inputs

Every original standard-simplex coefficient and source map is retained
by the canonical costructured-arrow map. Its full original augmentation
and projection squares prove weakness of the SAME native simplex-index
nerve map whenever the supplied original simplicial map is weak.
No fibrancy or coherent comparison outcome is assumed.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet

variable {K L : SSet.{u}}

/-- The same full original simplex index map retains each complete original coefficient under its actual contained
universe lift. -/
def originalSimplexIndexCoefficient (f : K ⟶ L) :
    originalSimplexDiagram K ⋙ uliftFunctor.{u,u} ⟶
      CostructuredArrow.map (S := SSet.stdSimplex.{u}) f ⋙ originalSimplexDiagram L where
  app s := (uliftContainedIso.{u,0}
    ((originalSimplexDiagram L).obj ((CostructuredArrow.map (S := SSet.stdSimplex.{u}) f).obj s))).hom
  naturality s t g := by
    have h : uliftFunctor.map (SSet.stdSimplex.map g.left) ≫
        (uliftContainedIso.{u,0} (SSet.stdSimplex.obj t.left)).hom =
      (uliftContainedIso.{u,0} (SSet.stdSimplex.obj s.left)).hom ≫ SSet.stdSimplex.map g.left :=
      uliftContainedIso_naturality (SSet.stdSimplex.map g.left)
    exact h

/-- Every same original simplex retains its entire original source-map augmentation triangle. -/
theorem originalSimplexIndexCoefficient_augmentation (f : K ⟶ L) (s : SimplexIndex K) :
    (originalSimplexIndexCoefficient f).app s ≫
      (originalSimplexCocone L).app ((CostructuredArrow.map (S := SSet.stdSimplex.{u}) f).obj s) =
      uliftFunctor.{u,u}.map ((originalSimplexCocone K).app s) ≫ ((uliftContainedIso.{u,0} K).hom ≫ f) := by
  have h := uliftContainedIso_naturality.{u,0} s.hom
  change (uliftContainedIso.{u,0} (SSet.stdSimplex.obj s.left)).hom ≫ (s.hom ≫ f) =
    uliftFunctor.map s.hom ≫ ((uliftContainedIso.{u,0} K).hom ≫ f)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun g => g ≫ f) h.symm).trans (Category.assoc _ _ _))

/-- The SAME original full standard-simplex index BK map is weak for every actual original weak source map. -/
theorem originalSimplexIndexMap_hocolim_weak (f : K ⟶ L) (hf : realizationWeakEquivalences f) :
    realizationWeakEquivalences (bkHocolimIndexMapULift.{u,0,0,0}
      (CostructuredArrow.map (S := SSet.stdSimplex.{u}) f) (originalSimplexIndexCoefficient f)) := by
  have hSquare := bkHocolimIndexMapULift_augmentationSquare.{u,0,0,0}
    (CostructuredArrow.map (S := SSet.stdSimplex.{u}) f) (originalSimplexIndexCoefficient f)
    (originalSimplexCocone K) (originalSimplexCocone L)
    ((uliftContainedIso.{u,0} K).hom ≫ f) (originalSimplexIndexCoefficient_augmentation f)
  have hSource := (realizationWeak_ulift_map_iff.{u,u} (originalSimplexAugmentation K)).mpr
    (originalSimplexAugmentation_weak K)
  have hInput : realizationWeakEquivalences ((uliftContainedIso.{u,0} K).hom ≫ f) :=
    realizationWeakEquivalences.comp_mem _ _ (realizationWeakEquivalences.of_isIso _) hf
  have hComposite := realizationWeakEquivalences.comp_mem _ _ hSource hInput
  exact realizationWeakEquivalences.of_postcomp _ _ (originalSimplexAugmentation_weak L)
    (hSquare.symm ▸ hComposite)

/-- The SAME complete original native simplex-index nerve map is weak for every original weak simplicial map. -/
theorem originalSimplexIndexMap_nerve_weak (f : K ⟶ L) (hf : realizationWeakEquivalences f) :
    realizationWeakEquivalences (nerveMap (CostructuredArrow.map (S := SSet.stdSimplex.{u}) f)) := by
  have hSquare := bkHocolimIndexMapULift_nerveSquare.{u,0,0,0}
    (CostructuredArrow.map (S := SSet.stdSimplex.{u}) f) (originalSimplexIndexCoefficient f)
  have hSource := (realizationWeak_ulift_map_iff.{u,u} (bkHocolimToNerve (originalSimplexDiagram K))).mpr
    (bkHocolimToNerve_weak _ (originalSimplexDiagram_point_weak K))
  have hTarget := bkHocolimToNerve_weak _ (originalSimplexDiagram_point_weak L)
  have hComposite := realizationWeakEquivalences.comp_mem _ _ (originalSimplexIndexMap_hocolim_weak f hf) hTarget
  have hLift := realizationWeakEquivalences.of_precomp _ _ hSource (hSquare ▸ hComposite)
  exact (nerveMapULiftToTarget_weak_iff (CostructuredArrow.map (S := SSet.stdSimplex.{u}) f)).mp hLift

end SSet
