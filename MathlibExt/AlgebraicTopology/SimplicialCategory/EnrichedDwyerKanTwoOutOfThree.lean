/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedHomWeakRecognition
import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedDwyerKanClasses

/-!
# The actual original global enriched DK weak class has two out of three

Original scalar cancellation detects weakness at the actual source
image pairs. Genuine essential surjectivity supplies the original
component isomorphisms at every remaining original target object. The
proved full Hom weak transport then gives weakness of the SAME original
maps at all pairs, without a Kan or desired whole-map outcome premise.
The weak predicate, object functions and full enriched maps are unchanged.
-/

noncomputable section
universe u
open CategoryTheory

namespace CategoryTheory.SimplicialEnrichment.EnrichedDwyerKan
open ComponentCategory EnrichedHomWeakRecognition

variable {C D E : Carrier.{u}}

/-- Original postcomposition cancellation retains the SAME enriched map, full Hom maps and actual component
essential surjectivity. -/
theorem weak_of_postcomp (F : C ⟶ D) (G : D ⟶ E) (hG : weakEquivalences G)
    (hFG : weakEquivalences (F ≫ G)) : weakEquivalences F := by
  refine ⟨fun x y => SSet.realizationWeakEquivalences.of_postcomp _ _
    (hG.1 (F.obj x) (F.obj y)) (hFG.1 x y), ?_⟩
  let _ := componentIsEquivalence G hG
  let _ : (mapFunctor F ⋙ mapFunctor G).EssSurj := by
    rw [← mapFunctor_comp F G]
    exact hFG.2
  exact Functor.essSurj_of_comp_fully_faithful (mapFunctor F) (mapFunctor G)

/-- Actual original image-Hom cancellation and component-object transport give the SAME whole-map precomposition
cancellation for arbitrary targets. -/
theorem weak_of_precomp (F : C ⟶ D) (G : D ⟶ E) (hF : weakEquivalences F)
    (hFG : weakEquivalences (F ≫ G)) : weakEquivalences G := by
  constructor
  · intro x y
    let _ : (mapFunctor F).EssSurj := hF.2
    obtain ⟨a, ⟨ea⟩⟩ := Functor.EssSurj.mem_essImage (mapFunctor F) (objectOf.{u} D x)
    obtain ⟨b, ⟨eb⟩⟩ := Functor.EssSurj.mem_essImage (mapFunctor F) (objectOf.{u} D y)
    let A : C := originalObject C a
    let B : C := originalObject C b
    have ea' : objectOf.{u} D (F.obj A) ≅ objectOf.{u} D x := ea
    have eb' : objectOf.{u} D (F.obj B) ≅ objectOf.{u} D y := eb
    have restricted : SSet.realizationWeakEquivalences (G.map (F.obj A) (F.obj B)) :=
      SSet.realizationWeakEquivalences.of_precomp _ _ (hF.1 A B) (hFG.1 A B)
    exact (weak_hom_iff_of_component_isos G ea' eb').mp restricted
  · refine ⟨fun x => ?_⟩
    let _ : (mapFunctor (F ≫ G)).EssSurj := hFG.2
    obtain ⟨a, ⟨ea⟩⟩ := Functor.EssSurj.mem_essImage (mapFunctor (F ≫ G)) x
    exact ⟨(mapFunctor F).obj a, ⟨ea⟩⟩

/-- The SAME original global enriched DK weak class satisfies the complete two-out-of-three property. -/
instance weak_twoOutOfThree : weakEquivalences.{u}.HasTwoOutOfThreeProperty where
  comp_mem F G hF hG := comp_weak F G hF hG
  of_postcomp F G hG hFG := weak_of_postcomp F G hG hFG
  of_precomp F G hF hFG := weak_of_precomp F G hF hFG

end CategoryTheory.SimplicialEnrichment.EnrichedDwyerKan
