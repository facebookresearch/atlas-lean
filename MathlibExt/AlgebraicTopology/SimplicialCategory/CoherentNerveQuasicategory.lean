/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornHomMapFaces

/-!
# The genuine coherent nerve of a locally Kan original enrichment

Every actual enriched Hom is Kan. The original coherent horn geometry,
whole box gluing, enriched simplex assembly and exact supplied-face
restrictions therefore give every actual inner horn filler. This uses
no Bergner model, Quillen comparison or CSS presentation hypothesis.
-/

noncomputable section
universe u
open CategoryTheory
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment
open CoherentRealization

/-- The actual coherent nerve of an original simplicial enrichment with genuinely Kan Hom objects is a quasicategory. -/
theorem coherentNerve_quasicategory (C : Carrier.{u})
    (hKan : ∀ x y : C, SSet.KanComplex (x ⟶[SSet.{u}] y)) :
    SSet.Quasicategory (coherentNerveFunctor.obj C) := by
  apply SSet.quasicategory_of_filler
  intro n i f h₀ hₙ
  let _ : SSet.KanComplex (HornFaces.object f 0 ⟶[SSet.{u}] HornFaces.object f (Fin.last (n + 2))) := hKan _ _
  refine ⟨HornHomMaps.simplex f (ne_of_gt h₀) (ne_of_lt hₙ), ?_⟩
  intro j hj
  change coherentSimplexMap (SimplexCategory.δ j) ≫ HornHomMaps.simplex f (ne_of_gt h₀) (ne_of_lt hₙ) =
    HornFaces.faceFunctor f j hj
  exact HornHomMapFaces.simplex_face f (ne_of_gt h₀) (ne_of_lt hₙ) j hj

/-- The pinned Mathlib coherent nerve on the same original enrichment has the same genuinely proved
  quasicategory structure. -/
theorem mathlibCoherentNerve_quasicategory (C : Carrier.{u})
    (hKan : ∀ x y : C, SSet.KanComplex (x ⟶[SSet.{u}] y)) :
    SSet.Quasicategory (SimplicialNerve (ForgetEnrichment SSet.{u} C)) := by
  rw [← coherentNerve_eq_mathlib]
  exact coherentNerve_quasicategory C hKan

end CategoryTheory.SimplicialEnrichment
