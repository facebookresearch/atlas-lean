/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeBasisChartFunctor
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedColimit

/-!
# The actual native straightening object of an original marked total space

Every original marked basis map into the total space carries its exact
original base composite. Its actual simplex or sharp-edge chart gives
the full enriched diagram. Straightening is the native marked
pointwise colimit of those charts, with all original injection maps
retained. This is a construction, not a supplied representing outcome.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace SSet.Marked
open CategoryTheory.CoherentRealization

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- Every original marked basis map contributes its actual chart over the unchanged composite base map. -/
def nativeStraighteningDiagram (B : SSet.{u}) (X : Over (max B)) :
    GeneratorBasis.Index X.left ⥤ EnrichedDiagram (realization B)ᵒᵖ :=
  CostructuredArrow.map X.hom ⋙ nativeBasisChartFunctor B

/-- The original marked total space has the actual whole marked colimit of its native basis charts. -/
def nativeStraighteningObject (B : SSet.{u}) (X : Over (max B)) : EnrichedDiagram (realization B)ᵒᵖ := by
  let _ : ∀ c : (realization B)ᵒᵖ, HasColimit (EnrichedColimit.evaluated (nativeStraighteningDiagram B X) c) :=
    fun _ => inferInstance
  exact EnrichedColimit.object (nativeStraighteningDiagram B X)

/-- Each original basis chart enters straightening through its actual whole marked colimit injection. -/
def nativeStraighteningInjection (B : SSet.{u}) (X : Over (max B)) (i : GeneratorBasis.Index X.left) :
    (nativeStraighteningDiagram B X).obj i ⟶ nativeStraighteningObject B X := by
  let _ : ∀ c : (realization B)ᵒᵖ, HasColimit (EnrichedColimit.evaluated (nativeStraighteningDiagram B X) c) :=
    fun _ => inferInstance
  exact EnrichedColimit.injection (nativeStraighteningDiagram B X) i

/-- The constructed whole chart cocone retains exactly the original native enriched colimit injections. -/
def nativeStraighteningCocone (B : SSet.{u}) (X : Over (max B)) : Cocone (nativeStraighteningDiagram B X) := by
  let _ : ∀ c : (realization B)ᵒᵖ, HasColimit (EnrichedColimit.evaluated (nativeStraighteningDiagram B X) c) :=
    fun _ => inferInstance
  exact EnrichedColimit.cocone (nativeStraighteningDiagram B X)

/-- Straightening has the genuine whole marked colimit universal property for all original basis charts. -/
def nativeStraighteningIsColimit (B : SSet.{u}) (X : Over (max B)) :
    IsColimit (nativeStraighteningCocone B X) := by
  let _ : ∀ c : (realization B)ᵒᵖ, HasColimit (EnrichedColimit.evaluated (nativeStraighteningDiagram B X) c) :=
    fun _ => inferInstance
  exact EnrichedColimit.isColimit (nativeStraighteningDiagram B X)

end SSet.Marked
