/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentMaps

/-!
# Genuine coherent realization functor and unit naturality

Identity and composition are proved on the actual original coherent
generators and then on whole enriched maps. The unit is natural for
every original simplicial map, with its exact endpoint transports.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization
open SimplicialEnrichment SimplicialQuiver

/-- The actual realization of an identity map is the whole enriched identity. -/
theorem realizationMap_id (K : SSet.{u}) : realizationMap (𝟙 K) = 𝟙 (realization K) := by
  refine CoherentRealization.hom_ext rfl ?_
  intro x y
  ext q a
  cases a with
  | mk n σ i j hx hy a =>
      change (mapInterpretation (𝟙 K)).evalPath q (arrowPath K σ i j hx hy a) =
        _root_.Quotient.mk (congruence (relations K) q x y) (arrowPath K σ i j hx hy a)
      exact map_eval_arrow (𝟙 K) σ i j hx hy a

/-- The actual realization preserves composition on all whole original enriched Hom paths. -/
theorem realizationMap_comp {K L N : SSet.{u}} (f : K ⟶ L) (g : L ⟶ N) :
    realizationMap (f ≫ g) = realizationMap f ≫ realizationMap g := by
  refine CoherentRealization.hom_ext rfl ?_
  intro x y
  ext q a
  cases a with
  | mk n σ i j hx hy a =>
      change (mapInterpretation (f ≫ g)).evalPath q (arrowPath K σ i j hx hy a) =
        ((realizationMap g).map (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y)).app q
          ((mapInterpretation f).evalPath q (arrowPath K σ i j hx hy a))
      have hf := map_eval_arrow f σ i j hx hy a
      have hg := map_eval_arrow g (f.app (op n) σ) i j (vertex_image f σ i hx)
        (vertex_image f σ j hy) a
      have hfg := map_eval_arrow (f ≫ g) σ i j hx hy a
      exact hfg.trans (hg.symm.trans (congrArg
        (fun t => ((realizationMap g).map (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y)).app q t) hf.symm))

/-- The genuine original coherent realization functor, with proved identity and composition. -/
def realizationFunctor : SSet.{u} ⥤ Carrier.{u} where
  obj := realization
  map f := realizationMap f
  map_id := realizationMap_id
  map_comp := realizationMap_comp

/-- The whole original unit simplex is natural for every actual input simplicial map. -/
theorem unit_simplex_naturality {K L : SSet.{u}} (f : K ⟶ L) {n : SimplexCategory}
    (σ : K.obj (op n)) :
    simplexInto K σ ≫ realizationMap f = simplexInto L (f.app (op n) σ) := by
  refine EnrichedFunctor.ext SSet.{u}
    (F := (simplexInto K σ).comp SSet.{u} (realizationMap f))
    (G := simplexInto L (f.app (op n) σ)) (fun i => (vertex_map f σ i).symm) ?_
  intro i j
  change (simplexHom K σ i j rfl rfl ≫ (realizationMap f).map (vertex K σ i) (vertex K σ j)) ≫
    eqToHom (congrArg₂ (hom L) (vertex_map f σ i).symm (vertex_map f σ j).symm) =
      simplexHom L (f.app (op n) σ) i j rfl rfl
  exact (congrArg (fun t => t ≫ eqToHom (congrArg₂ (hom L)
    (vertex_map f σ i).symm (vertex_map f σ j).symm))
      (realizationMap_simplexHom f σ i j rfl rfl)).trans
        (simplexHom_reindex_comp L (f.app (op n) σ) i j
          (vertex_image f σ i rfl) (vertex_image f σ j rfl)
          (vertex_map f σ i).symm (vertex_map f σ j).symm)

/-- The unit is a genuine natural transformation on the actual simplicial and enriched carriers. -/
def unitNatTrans : 𝟭 SSet.{u} ⟶ realizationFunctor ⋙ coherentNerveFunctor where
  app := unit
  naturality K L f := by
    ext n σ
    exact (unit_simplex_naturality f σ).symm

end CategoryTheory.CoherentRealization
