/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedLeftKanComposition

/-!
# Actual whole Hom readbacks of composed marked left extension

The native adjunction Hom equivalence is the proved coequalizer
universal equivalence. Composing two actual adjunctions and extending
an original source map therefore reads its original universal image
followed by the actual second unit. This calculation is independent
of any particular cone or base presentation.
-/

noncomputable section
universe u v
open CategoryTheory

namespace SSet.Marked
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The actual native adjunction and original coequalizer construction have the same whole universal Hom
  correspondence. -/
theorem enrichedLeftKanAdjunction_homEquiv_eq {C : Type u} [EnrichedCategory SSet.{u} C]
    {D : Type v} [EnrichedCategory SSet.{u} D] (j : EnrichedFunctor SSet.{u} C D)
    (W : EnrichedDiagram C) (F : EnrichedDiagram D) (a : EnrichedLeftKan.object j W ⟶ F) :
    (EnrichedLeftKan.adjunction j).homEquiv W F a = EnrichedLeftKan.universalHomEquiv j W F a :=
  ((EnrichedLeftKan.adjunction j).homEquiv_unit W F a).trans
    (EnrichedLeftKan.universalHomEquiv_unit j W F a).symm

/-- Extending an original map through the second native left adjoint reads its whole first universal map
  followed by the actual second unit. -/
theorem enrichedLeftKanComposite_map_hom {C D : Type u}
    [EnrichedCategory SSet.{u} C] [EnrichedCategory SSet.{u} D]
    {E : Type v} [EnrichedCategory SSet.{u} E]
    (j : EnrichedFunctor SSet.{u} C D) (k : EnrichedFunctor SSet.{u} D E)
    (W : EnrichedDiagram C) (V : EnrichedDiagram D) (f : EnrichedLeftKan.object j W ⟶ V) :
    ((EnrichedLeftKan.adjunction j).comp (EnrichedLeftKan.adjunction k)).homEquiv W
        (EnrichedLeftKan.object k V) (EnrichedLeftKan.map k f) =
      EnrichedLeftKan.universalHomEquiv j W V f ≫
        (enrichedDiagramRestrict j).map (EnrichedLeftKan.unit k V) := by
  let F := EnrichedLeftKan.object k V
  let R := enrichedDiagramRestrict k
  let a := EnrichedLeftKan.adjunction j
  let b := EnrichedLeftKan.adjunction k
  let g := EnrichedLeftKan.map k f
  have h₁ : (a.comp b).homEquiv W F g = a.homEquiv W (R.obj F)
      (b.homEquiv (EnrichedLeftKan.object j W) F g) :=
    congrArg (fun e => e W F g) (Adjunction.comp_homEquiv a b)
  have h₂ := congrArg (a.homEquiv W (R.obj F))
    ((enrichedLeftKanAdjunction_homEquiv_eq k (EnrichedLeftKan.object j W) F g).trans
      (EnrichedLeftKan.map_homEquiv k f))
  have h₃ := enrichedLeftKanAdjunction_homEquiv_eq j W (R.obj F) (f ≫ EnrichedLeftKan.unit k V)
  have h₄ := EnrichedLeftKan.universalHomEquiv_natural_right j W f (EnrichedLeftKan.unit k V)
  exact h₁.trans (h₂.trans (h₃.trans h₄))

end SSet.Marked
