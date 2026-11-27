/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedDiagramAction

/-!
# Whole marked action equations and genuine enriched naturality

Native maximal currying and uncurrying identify full Hom naturality
with equality of the actual whole marked action maps. This equivalence
does not reduce naturality to ordinary arrows or zero vertices.
-/

noncomputable section
universe u v w
open CategoryTheory

namespace SSet.Marked

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- Original source precomposition commutes with native whole maximal uncurrying. -/
theorem maxUncurry_source {A : SSet.{u}} {X X' Y : Marked.{u}}
    (f : X ⟶ X') (g : A ⟶ mappingComplex .maximal X' Y) :
    maxUncurry (g ≫ mappingComplexPre .maximal f Y) = prodMap (𝟙 (max A)) f ≫ maxUncurry g := by
  apply (maxFamilyHomEquiv A X Y).injective
  change maxCurry (maxUncurry (g ≫ mappingComplexPre .maximal f Y)) =
    maxCurry (prodMap (𝟙 (max A)) f ≫ maxUncurry g)
  rw [maxCurry_maxUncurry, maxCurry_source, maxCurry_maxUncurry]

variable {C : Type v} [EnrichedCategory SSet.{u} C]

/-- Entire native marked action equations construct a genuinely full enriched natural map. -/
def EnrichedDiagramMap.ofAction {F G : EnrichedDiagram C}
    (a : ∀ x : C, F.obj x ⟶ G.obj x)
    (h : ∀ x y : C, enrichedDiagramAction F x y ≫ a y =
      prodMap (𝟙 (max (x ⟶[SSet.{u}] y))) (a x) ≫ enrichedDiagramAction G x y) :
    EnrichedDiagramMap F G where
  app := a
  naturality x y := by
    apply (maxFamilyHomEquiv (x ⟶[SSet.{u}] y) (F.obj x) (G.obj y)).symm.injective
    change maxUncurry (F.map x y ≫ mappingComplexPost .maximal (F.obj x) (a y)) =
      maxUncurry (G.map x y ≫ mappingComplexPre .maximal (a x) (G.obj y))
    rw [maxUncurry_post, maxUncurry_source]
    exact h x y

/-- Restriction of a diagram retains the original index Hom map in its whole marked action. -/
theorem enrichedDiagramAction_restriction {D : Type w} [EnrichedCategory SSet.{u} D]
    (j : EnrichedFunctor SSet.{u} C D) (F : EnrichedDiagram D) (x y : C) :
    enrichedDiagramAction (j.comp SSet.{u} F) x y =
      prodMap (maximal.map (j.map x y)) (𝟙 (F.obj (j.obj x))) ≫
        enrichedDiagramAction F (j.obj x) (j.obj y) :=
  maxUncurry_pre (j.map x y) (F.map (j.obj x) (j.obj y))

end SSet.Marked
