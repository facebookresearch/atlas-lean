/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerTwoObjectFiniteStageFactorization
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFilteredBergnerCoconeInjections
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Original two-object compactness on genuine filtered C0 diagrams

The same original two-object coyoneda cocone has its genuine colimit:
whole maps factor through actual stages, and the complete original
cocone legs reflect equality. Every original endpoint and full Hom map
is retained. The premise is the actual C0 diagram, as required by the
native original combined-generator small-object construction.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite

namespace CategoryTheory.SimplicialEnrichment.BergnerTwoObject

/-- The same whole original compact two-object coyoneda cocone is genuinely colimiting on any actual filtered C0
diagram. -/
def coyonedaIsColimit {J : Type u} [Category.{u} J] [IsFiltered J]
    (F : J ⥤ Carrier.{u}) (s : Cocone F) (hs : IsColimit s)
    (hC : ∀ {i j : J} (f : i ⟶ j), Bergner.cofibrations (F.map f))
    (K : SSet.{u}) [IsFinitelyPresentable.{u} K] :
    IsColimit ((coyoneda.obj (op (object K))).mapCocone s) := by
  let T := F ⋙ coyoneda.obj (op (object K))
  apply Types.FilteredColimit.isColimitOf'
  · intro G
    obtain ⟨j, H, hH⟩ := whole_map_factor F s hs hC K G
    exact ⟨j, H, hH.symm⟩
  · intro j G H he
    have h : G = H := OriginalFilteredUnderHom.cocone_postcomp_injective F s hs hC j (object K) he
    exact ⟨j, 𝟙 j, congrArg (fun q => (T.map (𝟙 j)) q) h⟩

/-- The SAME original two-object domain coyoneda preserves the actual filtered C0 colimit. -/
theorem coyonedaPreservesColimit {J : Type u} [Category.{u} J] [IsFiltered J]
    (F : J ⥤ Carrier.{u})
    (hC : ∀ {i j : J} (f : i ⟶ j), Bergner.cofibrations (F.map f))
    (K : SSet.{u}) [IsFinitelyPresentable.{u} K] :
    PreservesColimit F (coyoneda.obj (op (object K))) := by
  exact preservesColimit_of_preserves_colimit_cocone (colimit.isColimit F)
    (coyonedaIsColimit F (colimit.cocone F) (colimit.isColimit F) hC K)

end CategoryTheory.SimplicialEnrichment.BergnerTwoObject
