/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedLeftKanAdjunction
import Mathlib.CategoryTheory.Yoneda

/-!
# Native left extension of the actual free marked diagram

The original left-extension/restriction adjunction followed by the
actual free/evaluation correspondence corepresents evaluation at the
same original image object. Mathlib's corepresenter uniqueness gives
the whole original free image comparison through these actual unit
maps, with independent original source and target object universes.
No unspecified representer or model outcome is supplied.
-/

noncomputable section
universe u v
open CategoryTheory Limits Opposite

namespace SSet.Marked
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

variable {C : Type u} [EnrichedCategory SSet.{u} C]
  {D : Type v} [EnrichedCategory SSet.{u} D]
  (j : EnrichedFunctor SSet.{u} C D) (c : C) (A : Marked.{u})

/-- The actual native extension of the original free diagram corepresents evaluation at precisely the
  original enriched image object. -/
def enrichedLeftKanFreeCorepresenter :
    (enrichedDiagramEvaluation D (j.obj c) ⋙ coyoneda.obj (op A)).CorepresentableBy
      (EnrichedLeftKan.object j (enrichedFreeDiagram C c A)) where
  homEquiv := (EnrichedLeftKan.universalHomEquiv j (enrichedFreeDiagram C c A) _).trans
    (enrichedFreeHomEquiv C c A _)
  homEquiv_comp g f := by
    change enrichedFreeUnit C c A ≫
        (EnrichedLeftKan.universalHomEquiv j (enrichedFreeDiagram C c A) _ (f ≫ g)).app c =
      (enrichedFreeUnit C c A ≫
        (EnrichedLeftKan.universalHomEquiv j (enrichedFreeDiagram C c A) _ f).app c) ≫ g.app (j.obj c)
    rw [EnrichedLeftKan.universalHomEquiv_natural_right]
    exact (Category.assoc _ _ _).symm

/-- The actual free diagram at the original image object corepresents the same unchanged coefficient evaluation. -/
def enrichedImageFreeCorepresenter :
    (enrichedDiagramEvaluation D (j.obj c) ⋙ coyoneda.obj (op A)).CorepresentableBy
      (enrichedFreeDiagram D (j.obj c) A) where
  homEquiv := enrichedFreeHomEquiv D (j.obj c) A _
  homEquiv_comp g f := by
    change enrichedFreeUnit D (j.obj c) A ≫ (f.app (j.obj c) ≫ g.app (j.obj c)) =
      (enrichedFreeUnit D (j.obj c) A ≫ f.app (j.obj c)) ≫ g.app (j.obj c)
    exact (Category.assoc _ _ _).symm

/-- Native enriched left extension sends the whole original free marked diagram to the actual free diagram
  at its same enriched image object, through the original two unit mates. -/
def enrichedLeftKanFreeIso : EnrichedLeftKan.object j (enrichedFreeDiagram C c A) ≅
    enrichedFreeDiagram D (j.obj c) A :=
  (enrichedLeftKanFreeCorepresenter j c A).uniqueUpToIso (enrichedImageFreeCorepresenter j c A)

end SSet.Marked
