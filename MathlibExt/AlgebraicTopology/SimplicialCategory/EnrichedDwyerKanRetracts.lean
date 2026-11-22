/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedDwyerKanTwoOutOfThree
import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedHomArrowRetract
import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!
# Retract closure of the SAME original global enriched DK weak class

The original whole enriched arrow retract supplies actual scalar Hom
arrow retracts at every original source pair. The native scalar weak
class gives their weakness. Actual original component functors transport
the same essential-image witness through the full retract rows. This
proves genuine global retract and isomorphism closure without changing
the original weak predicate, objects, functors or Hom maps.
-/

noncomputable section
universe u
open CategoryTheory

namespace CategoryTheory.SimplicialEnrichment.EnrichedDwyerKan
open ComponentCategory

variable {A B C D : Carrier.{u}} {F : A ⟶ B} {G : C ⟶ D}

/-- A genuine original enriched arrow retract preserves the SAME full scalar Hom weakness and actual original
component essential surjectivity. -/
theorem weak_of_retract (h : RetractArrow F G) (hG : weakEquivalences G) : weakEquivalences F := by
  constructor
  · intro x y
    exact MorphismProperty.of_retract (P := SSet.realizationWeakEquivalences)
      (originalHomArrowRetract h x y) (hG.1 (h.i.left.obj x) (h.i.left.obj y))
  · refine ⟨fun b => ?_⟩
    let _ : (mapFunctor G).EssSurj := hG.2
    obtain ⟨c, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (mapFunctor G) ((mapFunctor h.i.right).obj b)
    let Q := mapFunctor h.r.right
    have left : mapFunctor h.r.left ⋙ mapFunctor F = mapFunctor G ⋙ Q :=
      (mapFunctor_comp h.r.left F).symm.trans
        ((congrArg (fun K : C ⟶ B => mapFunctor K) h.r_w).trans (mapFunctor_comp G h.r.right))
    have right : mapFunctor h.i.right ⋙ Q = 𝟭 (objects.{u} B) :=
      (mapFunctor_comp h.i.right h.r.right).symm.trans
        ((congrArg (fun K : B ⟶ B => mapFunctor K) h.retract_right).trans (mapFunctor_id (C := B)))
    refine ⟨(mapFunctor h.r.left).obj c, ⟨?_⟩⟩
    exact eqToIso (congrArg (fun K => K.obj c) left) ≪≫ Q.mapIso e ≪≫
      eqToIso (congrArg (fun K => K.obj b) right)

/-- The actual unchanged original global enriched DK weak class is stable under all original arrow retracts. -/
instance weak_retracts : weakEquivalences.{u}.IsStableUnderRetracts where
  of_retract h hG := weak_of_retract h hG

/-- That SAME original weak class respects actual full enriched arrow isomorphisms. -/
instance weak_respectsIso : weakEquivalences.{u}.RespectsIso := inferInstance

end CategoryTheory.SimplicialEnrichment.EnrichedDwyerKan
