/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedDiagram

/-!
# Whole enriched inverses of actual component isomorphisms

An existing full enriched natural map whose actual components are
isomorphisms has the same component inverses as a whole enriched map.
The inverse Hom naturality follows from the original full prism
equations. No equivalence, model or replacement outcome is supplied.
-/

noncomputable section
universe u v
open CategoryTheory Opposite

namespace SSet.Marked
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

variable {C : Type v} [EnrichedCategory SSet.{u} C]

/-- The original component inverses commute with every whole enriched Hom prism. -/
def enrichedDiagramComponentInverse {F G : EnrichedDiagram C} (α : F ⟶ G)
    [∀ x : C, IsIso (α.app x)] : G ⟶ F where
  app x := inv (α.app x)
  naturality x y := by
    ext n h
    apply Hom.ext
    ext q z
    have hx := congrArg (fun m : G.obj x ⟶ G.obj x => m.hom.app q z.2)
      (IsIso.inv_hom_id (α.app x))
    have hn := congrArg (fun m => m.hom.app q (z.1, (inv (α.app x)).hom.app q z.2))
      congr($(α.naturality x y).app n h)
    have hr := congrArg (fun a => ((G.map x y).app n h).hom.app q (z.1, a)) hx
    have hy := congrArg (fun m : F.obj y ⟶ F.obj y =>
      m.hom.app q (((F.map x y).app n h).hom.app q (z.1, (inv (α.app x)).hom.app q z.2)))
        (IsIso.hom_inv_id (α.app y))
    exact (congrArg (fun a => (inv (α.app y)).hom.app q a) (hn.trans hr)).symm.trans hy

/-- An existing actual componentwise isomorphism is a genuine whole enriched isomorphism with those same
  native inverses. -/
def enrichedDiagramAsIsoOfComponents {F G : EnrichedDiagram C} (α : F ⟶ G)
    [∀ x : C, IsIso (α.app x)] : F ≅ G where
  hom := α
  inv := enrichedDiagramComponentInverse α
  hom_inv_id := by
    apply EnrichedDiagramMap.ext
    funext x
    exact IsIso.hom_inv_id (α.app x)
  inv_hom_id := by
    apply EnrichedDiagramMap.ext
    funext x
    exact IsIso.inv_hom_id (α.app x)

/-- Full natural marked component isomorphisms give a whole native diagram isomorphism, without a new global
  instance. -/
theorem enrichedDiagramMap_isIso_of_components {F G : EnrichedDiagram C} (α : F ⟶ G)
    [∀ x : C, IsIso (α.app x)] : IsIso α :=
  (enrichedDiagramAsIsoOfComponents α).isIso_hom

end SSet.Marked
