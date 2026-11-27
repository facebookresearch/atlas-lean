/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedDiagram

/-!
# Original scalar tensors on genuine marked enriched diagrams

The maximally marked original parameter is retained as the first
coordinate. Whole Hom actions use that coordinate unchanged, while the
second coordinate is the original marked prism. This is an enriched
functor, and therefore tensors genuine enriched diagrams and their full
natural maps. No parameter or target fibrancy condition is imposed.
-/

noncomputable section
universe u v
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- Scalar tensoring retains the entire original parameter coordinate in every marked Hom prism. -/
def scalarTensorMapping (K : SSet.{u}) (X Y : Marked.{u}) :
    mappingComplex .maximal X Y ⟶ mappingComplex .maximal (prod (max K) X) (prod (max K) Y) where
  app n := ↾fun f =>
    prodLift
      (prodSnd (max (SSet.stdSimplex.obj n.unop)) (prod (max K) X) ≫ prodFst (max K) X)
      (prodLift (prodFst (max (SSet.stdSimplex.obj n.unop)) (prod (max K) X))
        (prodSnd (max (SSet.stdSimplex.obj n.unop)) (prod (max K) X) ≫ prodSnd (max K) X) ≫ f)
  naturality n m a := by
    ext f
    apply Hom.ext
    ext q z
    rfl

/-- The actual scalar product is a genuine enriched functor on the original marked carrier. -/
def scalarTensorEnriched (K : SSet.{u}) : EnrichedFunctor SSet.{u} Marked.{u} Marked.{u} where
  obj X := prod (max K) X
  map := scalarTensorMapping K
  map_id X := by
    ext n z
    apply Hom.ext
    rfl
  map_comp X Y Z := by
    ext n fg
    apply Hom.ext
    rfl

/-- Whole scalar tensoring applies to the actual marked-valued enriched diagram, object by object. -/
def enrichedDiagramTensor (C : Type v) [EnrichedCategory SSet.{u} C] (K : SSet.{u}) :
    EnrichedDiagram C ⥤ EnrichedDiagram C where
  obj F := F.comp SSet.{u} (scalarTensorEnriched K)
  map {F G} α :=
    { app x := prodMap (𝟙 (max K)) (α.app x)
      naturality x y := by
        ext n f
        apply Hom.ext
        ext q z
        have h := congr($(α.naturality x y).app n f)
        have h' := congrArg (fun a => a.hom.app q (z.1, z.2.2)) h
        exact Prod.ext rfl h' }
  map_id F := by
    apply EnrichedDiagramMap.ext
    funext x
    exact prodMap_id (max K) (F.obj x)
  map_comp α β := by
    apply EnrichedDiagramMap.ext
    funext x
    exact (prodMap_comp (𝟙 (max K)) (𝟙 (max K)) (α.app x) (β.app x)).symm

/-- Every tensor Hom simplex retains the same original scalar coordinate and marked target action. -/
theorem scalarTensorMapping_app (K : SSet.{u}) (X Y : Marked.{u}) (n : ℕ)
    (f : (mappingComplex .maximal X Y) _⦋n⦌) (q : SimplexCategoryᵒᵖ)
    (z : (SSet.stdSimplex.obj ⦋n⦌ ⊗ (K ⊗ X.toSSet)).obj q) :
    ((scalarTensorMapping K X Y).app (op ⦋n⦌) f).hom.app q z =
      (z.2.1, f.hom.app q (z.1, z.2.2)) := rfl

end SSet.Marked
