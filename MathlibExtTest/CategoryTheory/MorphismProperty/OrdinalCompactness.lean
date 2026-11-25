/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex

import MathlibExt.CategoryTheory.MorphismProperty.OrdinalCompactness
import Batteries.Tactic.Lint

/-!
# Ordinal source Hom clients with category theory imports

Both endpoint comparisons are assembled through the public constructor and
applied to the caller's original ordinal diagram and colimit cocone.
-/

set_option autoImplicit false
noncomputable section

universe u v w

open CategoryTheory Limits MorphismProperty Opposite

namespace CategoryTheory.MorphismProperty.OrdinalCompactnessClients

variable {C : Type u} [Category.{v} C]

/-- The public source data constructor and projections retain both complete
endpoint cocones on an arbitrary original ordinal diagram. -/
def ordinalEndpointCocones
    (I P : MorphismProperty C)
    (domains : ∀ i : I.toSet, PreservesOrdinalColimits.{u, v, w} P i.1.left)
    (codomains : ∀ i : I.toSet, PreservesOrdinalColimits.{u, v, w} P i.1.right)
    {O : Type w} [LinearOrder O] [OrderBot O] [WellFoundedLT O]
    (F : O ⥤ C) (hF : ∀ (a b : O) (f : a ⟶ b), P (F.map f))
    (c : Cocone F) (hc : IsColimit c) (i : I.toSet) :
    IsColimit ((coyoneda.obj (Opposite.op i.1.left)).mapCocone c) ×
      IsColimit ((coyoneda.obj (Opposite.op i.1.right)).mapCocone c) := by
  let hSources : SourceHomPreservation.{u, v, w} I P :=
    SourceHomPreservation.mk domains codomains
  let _ := hSources.domains i O F hF
  let _ := hSources.codomains i O F hF
  exact ⟨isColimitOfPreserves _ hc, isColimitOfPreserves _ hc⟩

#check @CategoryTheory.MorphismProperty.SourceHomPreservation.mk
#check @CategoryTheory.MorphismProperty.SourceHomPreservation.domains
#check @CategoryTheory.MorphismProperty.SourceHomPreservation.codomains

#print axioms ordinalEndpointCocones

end CategoryTheory.MorphismProperty.OrdinalCompactnessClients

#lint only unusedArguments in MathlibExt.CategoryTheory.MorphismProperty.OrdinalCompactness
#lint only unusedArguments in MathlibExtTest.CategoryTheory.MorphismProperty.OrdinalCompactness

#lint in MathlibExt.CategoryTheory.MorphismProperty.OrdinalCompactness
#lint in MathlibExtTest.CategoryTheory.MorphismProperty.OrdinalCompactness
