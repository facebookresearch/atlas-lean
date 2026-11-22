/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFilteredHomColimitReadback
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# The actual full source-under tail cocone

The existing original sourceDiagram and coconeUnderMap retain every
whole original enriched map. Finality of the original under-source
tail and creation of connected under-category colimits give the same
full original cocone its genuine universal property.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.OriginalFilteredUnderHom
attribute [local instance] IsFiltered.isConnected

variable {J : Type u} [Category.{u} J] (F : J ⥤ Carrier.{u}) (s : Cocone F) (j : J)

/-- The full original under-source tail cocone ends at the same original enriched cocone leg. -/
def sourceCocone : Cocone (sourceDiagram F j) where
  pt := Under.mk (s.ι.app j)
  ι :=
    { app a := coconeUnderMap F s j a
      naturality {_a _b} h := by
        apply Under.UnderMorphism.ext
        exact s.ι.naturality h.right }

/-- Original under forgetting retains the same full original tail cocone. -/
theorem sourceCocone_forget :
    (Under.forget (F.obj j)).mapCocone (sourceCocone F s j) = s.whisker (Under.forget j) := rfl

/-- The same complete original source-under tail cocone is genuinely colimiting. -/
def sourceIsColimit [IsFiltered J] (hs : IsColimit s) :
    IsColimit (sourceCocone F s j) := by
  have hc : IsColimit ((Under.forget (F.obj j)).mapCocone (sourceCocone F s j)) :=
    (Functor.Final.isColimitWhiskerEquiv (Under.forget j) s).symm hs
  exact isColimitOfReflects (Under.forget (F.obj j)) hc

end CategoryTheory.SimplicialEnrichment.OriginalFilteredUnderHom
