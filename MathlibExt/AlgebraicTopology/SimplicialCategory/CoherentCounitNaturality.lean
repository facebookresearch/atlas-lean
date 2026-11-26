/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFunctor
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentCounit
import MathlibExt.CategoryTheory.Enriched.HomEqualityTransport

/-!
# Counit naturality

The evaluation counit is natural for enriched functors. Its
characteristic Hom equations retain every individual object equality
transport and all Hom simplices, including noninvertible cells.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization
open SimplicialEnrichment SimplicialQuiver

/-- An enriched Hom map commutes with the two literal endpoint equality transports. -/
theorem enriched_map_reindex {C D : Carrier.{u}} (F : C ⟶ D) {a b a' b' : C}
    (ha : a = a') (hb : b = b') :
    eqToHom (congrArg₂ (fun x y : C => x ⟶[SSet.{u}] y) ha hb) ≫ F.map a' b' =
      F.map a b ≫ eqToHom (congrArg₂ (fun x y : D => x ⟶[SSet.{u}] y)
        (congrArg F.obj ha) (congrArg F.obj hb)) :=
  (EnrichedHomEqualityTransport.functor_map F ha hb).symm

/-- The counit Hom evaluation with the two supplied endpoint equations. -/
theorem counit_simplexHom_reindex (C : Carrier.{u}) {n : SimplexCategory} (σ :
  CoherentSimplexIn C n)
    (i j : coherentSimplex.{u} n) {x y : (coherentNerveFunctor.obj C) _⦋0⦌}
    (hx : vertex (coherentNerveFunctor.obj C) σ i = x)
    (hy : vertex (coherentNerveFunctor.obj C) σ j = y) :
    simplexHom (coherentNerveFunctor.obj C) σ i j hx hy ≫ (counit C).map x y =
      σ.map i j ≫ eqToHom (congrArg₂ (fun x y : C => x ⟶[SSet.{u}] y)
        (congrArg (vertexOf C) hx) (congrArg (vertexOf C) hy)) := by
  ext q a
  exact counit_eval_arrow C σ i j hx hy a

/-- Counit evaluation of a coherent Hom commutes with the same 
enriched map. -/
theorem counit_simplex_naturality {C D : Carrier.{u}} (F : C ⟶ D)
    {n : SimplexCategory} (σ : CoherentSimplexIn C n) (i j : coherentSimplex.{u} n)
    {x y : (coherentNerveFunctor.obj C) _⦋0⦌}
    (hx : vertex (coherentNerveFunctor.obj C) σ i = x)
    (hy : vertex (coherentNerveFunctor.obj C) σ j = y) :
    (simplexHom (coherentNerveFunctor.obj C) σ i j hx hy ≫ (counit C).map x y) ≫
      F.map (vertexOf C x) (vertexOf C y) =
        simplexHom (coherentNerveFunctor.obj D) (σ.comp SSet.{u} F) i j
          (vertex_image (coherentNerveFunctor.map F) σ i hx)
          (vertex_image (coherentNerveFunctor.map F) σ j hy) ≫
            (counit D).map ((coherentNerveFunctor.map F).app (op ⦋0⦌) x)
              ((coherentNerveFunctor.map F).app (op ⦋0⦌) y) := by
  have hc := counit_simplexHom_reindex C σ i j hx hy
  have hd := counit_simplexHom_reindex D (σ.comp SSet.{u} F) i j
    (vertex_image (coherentNerveFunctor.map F) σ i hx)
    (vertex_image (coherentNerveFunctor.map F) σ j hy)
  have ht := enriched_map_reindex F (congrArg (vertexOf C) hx) (congrArg (vertexOf C) hy)
  exact (congrArg (fun t => t ≫ F.map (vertexOf C x) (vertexOf C y)) hc).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun t => σ.map i j ≫ t) ht).trans
        ((Category.assoc _ _ _).symm.trans hd.symm)))

/-- The evaluation counit is natural on the enriched category carrier. -/
theorem counit_naturality {C D : Carrier.{u}} (F : C ⟶ D) :
    realizationMap (coherentNerveFunctor.map F) ≫ counit D = counit C ≫ F := by
  refine CoherentRealization.hom_ext rfl ?_
  intro x y
  ext q a
  cases a with
  | mk n σ i j hx hy a =>
      have hmap := realizationMap_simplexHom (coherentNerveFunctor.map F) σ i j hx hy
      have hnat := counit_simplex_naturality F σ i j hx hy
      have h := (congrArg (fun t => t ≫ (counit D).map
        ((coherentNerveFunctor.map F).app (op ⦋0⦌) x)
        ((coherentNerveFunctor.map F).app (op ⦋0⦌) y)) hmap).trans hnat.symm
      exact congr($(h).app q a)

/-- The evaluation counit natural transformation. -/
def counitNatTrans : coherentNerveFunctor ⋙ realizationFunctor ⟶ 𝟭 Carrier.{u} where
  app := counit
  naturality _ _ F := counit_naturality F

end CategoryTheory.CoherentRealization
