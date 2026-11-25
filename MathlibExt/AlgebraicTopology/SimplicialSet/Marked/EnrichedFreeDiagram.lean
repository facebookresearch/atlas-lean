/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedDiagram

/-!
# Native free marked-valued enriched diagrams

At an original source object `c`, the free diagram on `A` has value
`max(Hom(c,x)) × A` at `x`. Its action uses the actual enriched
composition, retaining the entire original coefficient and Hom simplex.
No local Kan hypothesis or diagram-model construction is required.
-/

noncomputable section
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

variable (C : Type v) [EnrichedCategory SSet.{u} C]

/-- The free value keeps the original Hom simplicial set and original marked coefficient. -/
def enrichedFreeValue (c x : C) (A : Marked.{u}) : Marked.{u} :=
  prod (max (c ⟶[SSet.{u}] x)) A

/-- The whole free action composes the original enriched Homs and leaves the coefficient fixed. -/
def enrichedFreeActionPrism (c x y : C) (A : Marked.{u}) :
    prod (max (x ⟶[SSet.{u}] y)) (enrichedFreeValue C c x A) ⟶ enrichedFreeValue C c y A :=
  prodLift
    (toMax (CartesianMonoidalCategory.lift
      ((prodSnd (max (x ⟶[SSet.{u}] y)) (enrichedFreeValue C c x A) ≫
        prodFst (max (c ⟶[SSet.{u}] x)) A).hom)
      ((prodFst (max (x ⟶[SSet.{u}] y)) (enrichedFreeValue C c x A)).hom) ≫ eComp SSet.{u} c x y))
    (prodSnd (max (x ⟶[SSet.{u}] y)) (enrichedFreeValue C c x A) ≫
      prodSnd (max (c ⟶[SSet.{u}] x)) A)

/-- The actual whole Hom action of the free diagram is the native maximal currying map. -/
def enrichedFreeAction (c x y : C) (A : Marked.{u}) :
    (x ⟶[SSet.{u}] y) ⟶
      mappingComplex .maximal (enrichedFreeValue C c x A) (enrichedFreeValue C c y A) :=
  maxCurry (enrichedFreeActionPrism C c x y A)

/-- Reading a whole free-action prism uses the original enriched composition and unchanged coefficient. -/
theorem enrichedFreeAction_app (c x y : C) (A : Marked.{u}) (n : SimplexCategoryᵒᵖ)
    (f : (x ⟶[SSet.{u}] y).obj n) (q : SimplexCategoryᵒᵖ)
    (z : (SSet.stdSimplex.obj n.unop ⊗ ((c ⟶[SSet.{u}] x) ⊗ A.toSSet)).obj q) :
    ((enrichedFreeAction C c x y A).app n f).hom.app q z =
      ((eComp SSet.{u} c x y).app q
        (z.2.1, (SSet.yonedaEquiv.symm f).app q z.1), z.2.2) := rfl

/-- The free marked-valued diagram is a genuine enriched functor with the original Hom composition. -/
def enrichedFreeDiagram (c : C) (A : Marked.{u}) : EnrichedDiagram C where
  obj x := enrichedFreeValue C c x A
  map x y := enrichedFreeAction C c x y A
  map_id x := by
    ext n z
    apply Hom.ext
    ext q a
    apply Prod.ext
    · change (eComp SSet.{u} c x x).app q
        (a.2.1, (SSet.yonedaEquiv.symm ((eId SSet.{u} x).app n z)).app q a.1) = a.2.1
      let θ := (SSet.stdSimplex.objEquiv a.1).op
      have hi : (SSet.yonedaEquiv.symm ((eId SSet.{u} x).app n z)).app q a.1 =
          (eId SSet.{u} x).app q PUnit.unit := by
        cases z
        exact congr($((eId SSet.{u} x).naturality θ) PUnit.unit).symm
      exact (congrArg (fun h => (eComp SSet.{u} c x x).app q (a.2.1, h)) hi).trans
        congr($(e_comp_id SSet.{u} c x).app q a.2.1)
    · rfl
  map_comp x y z := by
    ext n fg
    apply Hom.ext
    ext q a
    apply Prod.ext
    · let θ := (SSet.stdSimplex.objEquiv a.1).op
      let f := (x ⟶[SSet.{u}] y).map θ fg.1
      let g := (y ⟶[SSet.{u}] z).map θ fg.2
      have hc : (SSet.yonedaEquiv.symm ((eComp SSet.{u} x y z).app n fg)).app q a.1 =
          (eComp SSet.{u} x y z).app q (f, g) :=
        congr($((eComp SSet.{u} x y z).naturality θ) fg).symm
      change (eComp SSet.{u} c x z).app q
          (a.2.1, (SSet.yonedaEquiv.symm ((eComp SSet.{u} x y z).app n fg)).app q a.1) =
        (eComp SSet.{u} c y z).app q ((eComp SSet.{u} c x y).app q (a.2.1, f), g)
      exact (congrArg (fun h => (eComp SSet.{u} c x z).app q (a.2.1, h)) hc).trans
        congr($(e_assoc SSet.{u} c x y z).app q (a.2.1, f, g)).symm
    · rfl

/-- Original coefficient maps act on the free enriched diagram without changing any Hom coordinate. -/
def enrichedFreeDiagramFunctor (c : C) : Marked.{u} ⥤ EnrichedDiagram C where
  obj A := enrichedFreeDiagram C c A
  map f :=
    { app x := prodMap (𝟙 (max (c ⟶[SSet.{u}] x))) f
      naturality x y := by
        ext n h
        apply Hom.ext
        rfl }
  map_id A := by
    apply EnrichedDiagramMap.ext
    funext x
    exact prodMap_id (max (c ⟶[SSet.{u}] x)) A
  map_comp f g := by
    apply EnrichedDiagramMap.ext
    funext x
    exact (prodMap_comp (𝟙 (max (c ⟶[SSet.{u}] x))) (𝟙 (max (c ⟶[SSet.{u}] x))) f g).symm

end SSet.Marked
