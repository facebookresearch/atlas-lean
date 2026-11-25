/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedDiagram

/-!
# The whole native action of a marked enriched diagram

The enriched Hom map uncurries to an actual marked map on the whole
maximally marked Hom parameter. Its unit, composition and all simplex
restriction formulas read the original marked prism, with the same
source vertex and coefficient. These are action laws, not assumptions
of a diagram model or straightening comparison.
-/

noncomputable section
universe u v
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

variable {C : Type v} [EnrichedCategory SSet.{u} C]

/-- The actual enriched Hom action uses the existing whole maximal uncurrying map. -/
def enrichedDiagramAction (F : EnrichedDiagram C) (x y : C) :
    prod (max (x ⟶[SSet.{u}] y)) (F.obj x) ⟶ F.obj y :=
  maxUncurry (F.map x y)

/-- The action reads the original marked Hom prism at the identity parameter simplex. -/
theorem enrichedDiagramAction_app (F : EnrichedDiagram C) (x y : C)
    (q : SimplexCategoryᵒᵖ) (h : (x ⟶[SSet.{u}] y).obj q) (a : (F.obj x).toSSet.obj q) :
    (enrichedDiagramAction F x y).hom.app q (h, a) =
      ((F.map x y).app q h).hom.app q
        (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj q.unop)), a) := rfl

/-- Every entire original Hom prism is recovered by restriction followed by native action. -/
theorem enrichedDiagramAction_restrict (F : EnrichedDiagram C) (x y : C)
    (n q : SimplexCategoryᵒᵖ) (h : (x ⟶[SSet.{u}] y).obj n)
    (θ : (SSet.stdSimplex.obj n.unop).obj q) (a : (F.obj x).toSSet.obj q) :
    ((F.map x y).app n h).hom.app q (θ, a) =
      (enrichedDiagramAction F x y).hom.app q ((SSet.yonedaEquiv.symm h).app q θ, a) :=
  congrArg (fun g => (g.app n h).hom.app q (θ, a)) (maxCurry_maxUncurry (F.map x y)).symm

/-- The original enriched identity acts as the actual coefficient identity in every degree. -/
theorem enrichedDiagramAction_id (F : EnrichedDiagram C) (x : C)
    (q : SimplexCategoryᵒᵖ) (a : (F.obj x).toSSet.obj q) :
    (enrichedDiagramAction F x x).hom.app q ((eId SSet.{u} x).app q PUnit.unit, a) = a :=
  congrArg (fun f => (f.app q PUnit.unit).hom.app q
    (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj q.unop)), a)) (F.map_id x)

/-- Full enriched composition is the same consecutive action on the original coefficient. -/
theorem enrichedDiagramAction_comp (F : EnrichedDiagram C) (x y z : C)
    (q : SimplexCategoryᵒᵖ) (f : (x ⟶[SSet.{u}] y).obj q)
    (g : (y ⟶[SSet.{u}] z).obj q) (a : (F.obj x).toSSet.obj q) :
    (enrichedDiagramAction F x z).hom.app q ((eComp SSet.{u} x y z).app q (f, g), a) =
      (enrichedDiagramAction F y z).hom.app q
        (g, (enrichedDiagramAction F x y).hom.app q (f, a)) :=
  congrArg (fun t => (t.app q (f, g)).hom.app q
    (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj q.unop)), a)) (F.map_comp x y z)

/-- A full natural marked map commutes with the whole original enriched Hom action. -/
theorem enrichedDiagramAction_natural {F G : EnrichedDiagram C} (α : EnrichedDiagramMap F G)
    (x y : C) :
    enrichedDiagramAction F x y ≫ α.app y =
      prodMap (𝟙 (max (x ⟶[SSet.{u}] y))) (α.app x) ≫ enrichedDiagramAction G x y := by
  apply Hom.ext
  ext q a
  exact congrArg (fun t => (t.app q a.1).hom.app q
    (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj q.unop)), a.2)) (α.naturality x y)

end SSet.Marked
