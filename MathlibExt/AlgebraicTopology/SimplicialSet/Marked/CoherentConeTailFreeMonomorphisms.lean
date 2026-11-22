/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeTailFreeColimit
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedDiagramMonomorphisms
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Monomorphisms
import Mathlib.CategoryTheory.EpiMono

/-!
# Actual original tail free-leg monomorphisms

Each whole marked upper-face inclusion is injective on every
original scalar simplex. Its genuine support isomorphism and
original prism chart therefore make the actual free leg monic
at each coefficient, and hence as a whole enriched map.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The original marked upper-face union leg is monic on its whole actual simplex carrier. -/
theorem coneTailUpperUnionLeg_mono (n : ℕ) (i : Vertex.{u} (n + 1)) (j : Vertex.{u} n) :
    Mono ((coneVertexUpperMarkedCocone (coneTailEmbedding n).toOrderHom i).π j) := by
  let f := (coneVertexUpperMarkedCocone (coneTailEmbedding n).toOrderHom i).π j
  apply (mono_iff_underlying f).mpr
  let _ : ∀ q : SimplexCategoryᵒᵖ, Mono (f.hom.app q) := fun q =>
    (CategoryTheory.mono_iff_injective _).mpr (by
      intro x y h
      apply Subtype.ext
      exact congrArg
        (fun a : (coneVertexUpperMarkedCocone (coneTailEmbedding n).toOrderHom i).pt.toSSet.obj q => a.val) h)
  exact NatTrans.mono_of_mono_app f.hom

/-- The actual support comparison preserves the same whole marked upper-face leg monomorphism. -/
theorem coneTailUpperCocone_leg_mono (n : ℕ) (i : Vertex.{u} (n + 1)) (j : Vertex.{u} n) :
    Mono ((coneTailUpperCocone n i).π j) := by
  let f := (coneVertexUpperMarkedCocone (coneTailEmbedding n).toOrderHom i).π j
  let e := coneTailUpperPointIso n i
  change Mono (f ≫ e.hom)
  exact mono_comp' (coneTailUpperUnionLeg_mono n i j)
    (SplitMono.mono { retraction := e.inv, id := e.hom_inv_id })

/-- Every original free tail leg is monic at each whole original marked coefficient through its actual prism chart. -/
theorem coneTailFreeLeg_app_mono (n : ℕ) (i : Vertex.{u} (n + 1)) (j : Vertex.{u} n) :
    Mono ((coneTailFreeLeg n j).app (op (SimplicialThickening.mk i))) := by
  let e := coneUpperFacePrismIso i (coneTailEmbedding n j)
  let f := (coneTailUpperCocone n i).π j
  have h : Mono (e.inv ≫ f) := mono_comp'
    (SplitMono.mono { retraction := e.hom, id := e.inv_hom_id }) (coneTailUpperCocone_leg_mono n i j)
  exact (coneTailUpperPrism_inv_leg n i j) ▸ h

/-- The same original free tail leg is a genuine monomorphism of whole marked enriched diagrams. -/
theorem coneTailFreeLeg_mono (n : ℕ) (j : Vertex.{u} n) : Mono (coneTailFreeLeg n j) := by
  apply enrichedDiagramMap_mono_of_components
  intro i
  exact coneTailFreeLeg_app_mono n i.unop.as j

end SSet.Marked.CoherentWeight
