/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeTailLeftKanComparison

/-!
# Actual whole positive-cone Hom detection at original positive vertices

The genuine original whole tail left-Kan comparison presents the
actual positive cone. Its original universal units show that maps
from this same enriched diagram are detected on the full original
positive coefficients, retaining all original path and scalar data.
-/

noncomputable section
universe u
open CategoryTheory Opposite

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- All whole marked positive coefficients detect maps from the same actual original positive-cone enriched diagram
by its genuine original tail left-Kan comparison. -/
theorem coneAfterDiagram_hom_ext_positive (n : ℕ) {F : EnrichedDiagram (Index.{u} (n + 1))ᵒᵖ}
    (a b : coneAfterDiagram (⊥ : Vertex.{u} (n + 1)) ⟶ F)
    (h : ∀ i : Vertex.{u} n, a.app (op (SimplicialThickening.mk (coneTailEmbedding n i))) =
      b.app (op (SimplicialThickening.mk (coneTailEmbedding n i)))) : a = b := by
  let j := coneTailIndex.{u} n
  let W := coneDiagram.{u} n
  let V := coneAfterDiagram (⊥ : Vertex.{u} (n + 1))
  let f := coneTailLeftKanMap.{u} n
  let U := EnrichedLeftKan.universalHomEquiv j W F
  have hi : (coneTailLeftKanIso.{u} n).hom = f := coneTailLeftKanIso_hom n
  have : IsIso f := hi ▸ (coneTailLeftKanIso n).isIso_hom
  apply (cancel_epi f).mp
  apply U.injective
  have hf : EnrichedLeftKan.universalHomEquiv j W V f = coneTailOperator n :=
    (EnrichedLeftKan.universalHomEquiv j W V).apply_symm_apply (coneTailOperator n)
  have ha : U (f ≫ a) = coneTailOperator n ≫ (enrichedDiagramRestrict j).map a :=
    (EnrichedLeftKan.universalHomEquiv_natural_right j W f a).trans
      (congrArg (fun z => z ≫ (enrichedDiagramRestrict j).map a) hf)
  have hb : U (f ≫ b) = coneTailOperator n ≫ (enrichedDiagramRestrict j).map b :=
    (EnrichedLeftKan.universalHomEquiv_natural_right j W f b).trans
      (congrArg (fun z => z ≫ (enrichedDiagramRestrict j).map b) hf)
  have he : coneTailOperator n ≫ (enrichedDiagramRestrict j).map a = coneTailOperator n ≫ (enrichedDiagramRestrict
    j).map b := by
    apply EnrichedDiagramMap.ext
    funext i
    exact congrArg (fun z => (coneTailAfterCoefficientIso n i.unop.as).hom ≫ z) (h i.unop.as)
  exact ha.trans (he.trans hb.symm)

end SSet.Marked.CoherentWeight
