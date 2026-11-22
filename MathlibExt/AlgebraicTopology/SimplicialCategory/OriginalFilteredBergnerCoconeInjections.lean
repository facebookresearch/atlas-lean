/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFilteredBergnerHomMonicity
import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedWholePostcompositionInjections
import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerPointPresentability
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# The complete original filtered C0 cocone maps are injective

Original object forgetting preserves the genuine filtered colimit.
The original Type equality criterion and C0 object injectivity give
literal object injectivity of its cocone legs. Full Hom monicity then
makes postcomposition on whole original enriched functors injective,
with an independent original source object universe.
-/

noncomputable section
universe u v
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.OriginalFilteredUnderHom

variable {J : Type u} [Category.{u} J] [IsFiltered J]
  (F : J ⥤ Carrier.{u}) (s : Cocone F) (hs : IsColimit s)
  (hC : ∀ {i j : J} (f : i ⟶ j), Bergner.cofibrations (F.map f))

include hs hC

/-- Every same original filtered C0 cocone leg is injective on the actual original objects. -/
theorem cocone_obj_injective (j : J) : Function.Injective (s.ι.app j).obj := by
  have ht := isColimitOfPreserves forgetObjects.{u} hs
  intro x y he
  obtain ⟨k, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff' ht x y).mp he
  exact Bergner.cofibration_objects_injective (F.map f) (hC f) hf

/-- Every original cocone leg reflects equality of whole enriched maps from any independent original source. -/
theorem cocone_postcomp_injective (j : J) (A : Type v) [EnrichedCategory SSet.{u} A] :
    Function.Injective (fun G : EnrichedFunctor SSet.{u} A (F.obj j) =>
      EnrichedFunctor.comp SSet.{u} G (s.ι.app j)) :=
  EnrichedFunctor.postcomp_injective (s.ι.app j)
    (cocone_obj_injective F s hs hC j) (cocone_hom_mono F s hs hC j)

/-- The same complete original filtered C0 cocone leg is a genuine global monomorphism. -/
theorem cocone_isMono (j : J) : Mono (s.ι.app j) where
  right_cancellation := fun {A} G H h => show G = H from
    cocone_postcomp_injective F s hs hC j A h

end CategoryTheory.SimplicialEnrichment.OriginalFilteredUnderHom

namespace CategoryTheory.SimplicialEnrichment.Bergner

/-- Genuine original C0 lifting makes the same whole original enriched functor monic. -/
theorem cofibration_mono {C D : Carrier.{u}} (f : C ⟶ D) (hf : cofibrations f) : Mono f where
  right_cancellation := fun {A} G H h =>
    show G = H from EnrichedFunctor.postcomp_injective (C := A) f
      (cofibration_objects_injective f hf) (cofibration_original_hom_mono f hf) h

end CategoryTheory.SimplicialEnrichment.Bergner
