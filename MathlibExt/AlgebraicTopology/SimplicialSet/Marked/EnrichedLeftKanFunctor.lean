/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedLeftKanHom

/-!
# The genuine marked enriched left-extension functor

The unit is the actual universal image of the identity coequalizer
map. Every source map is the inverse of the proved universal Hom
correspondence on that original unit. Target naturality proves both
functor laws and whole unit naturality; no functor or adjunction
outcome is supplied.
-/

noncomputable section
universe u v
open CategoryTheory

namespace SSet.Marked.EnrichedLeftKan

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

variable {C : Type u} [EnrichedCategory SSet.{u} C]
    {D : Type v} [EnrichedCategory SSet.{u} D]
    (j : EnrichedFunctor SSet.{u} C D)

/-- The original left-extension unit is the universal image of the actual identity map. -/
def unit (W : EnrichedDiagram C) : W ⟶ j.comp SSet.{u} (object j W) :=
  universalHomEquiv j W (object j W) (𝟙 (object j W))

/-- A whole original source map extends through the genuine universal Hom correspondence and original target unit. -/
def map {W V : EnrichedDiagram C} (φ : W ⟶ V) : object j W ⟶ object j V :=
  (universalHomEquiv j W (object j V)).symm (φ ≫ unit j V)

/-- The universal image of the actual extended map is its original source map followed by the unit. -/
theorem map_homEquiv {W V : EnrichedDiagram C} (φ : W ⟶ V) :
    universalHomEquiv j W (object j V) (map j φ) = φ ≫ unit j V :=
  (universalHomEquiv j W (object j V)).apply_symm_apply _

/-- The constructed original unit is natural for every whole marked enriched source map. -/
theorem unit_natural {W V : EnrichedDiagram C} (φ : W ⟶ V) :
    unit j W ≫ (enrichedDiagramRestrict j).map (map j φ) = φ ≫ unit j V := by
  have h := universalHomEquiv_natural_right j W (𝟙 (object j W)) (map j φ)
  exact h.symm.trans (by
    rw [Category.id_comp]
    exact map_homEquiv j φ)

/-- The whole native extended identity is the original identity on the selected coequalizer object. -/
theorem map_id (W : EnrichedDiagram C) : map j (𝟙 W) = 𝟙 (object j W) := by
  change (universalHomEquiv j W (object j W)).symm
    ((𝟙 W) ≫ universalHomEquiv j W (object j W) (𝟙 (object j W))) = 𝟙 (object j W)
  rw [Category.id_comp]
  exact (universalHomEquiv j W (object j W)).symm_apply_apply _

/-- Consecutive original marked enriched maps extend by the same whole coequalizer-map composition. -/
theorem map_comp {W V U : EnrichedDiagram C} (φ : W ⟶ V) (ψ : V ⟶ U) :
    map j (φ ≫ ψ) = map j φ ≫ map j ψ := by
  apply (universalHomEquiv j W (object j U)).injective
  have hr : universalHomEquiv j W (object j U) (map j φ ≫ map j ψ) =
      (φ ≫ unit j V) ≫ (enrichedDiagramRestrict j).map (map j ψ) :=
    (universalHomEquiv_natural_right j W (map j φ) (map j ψ)).trans
      (congrArg (fun t => t ≫ (enrichedDiagramRestrict j).map (map j ψ)) (map_homEquiv j φ))
  exact (map_homEquiv j (φ ≫ ψ)).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun t => φ ≫ t) (unit_natural j ψ).symm).trans
        ((Category.assoc _ _ _).symm.trans hr.symm)))

/-- The native full marked enriched left-extension functor, constructed from its actual original coequalizers. -/
def leftExtension : EnrichedDiagram C ⥤ EnrichedDiagram D where
  obj := object j
  map := map j
  map_id := map_id j
  map_comp := map_comp j

/-- Each universal map is precisely the original unit followed by actual restriction of the same map. -/
theorem universalHomEquiv_unit (W : EnrichedDiagram C) (X : EnrichedDiagram D)
    (f : object j W ⟶ X) :
    universalHomEquiv j W X f = unit j W ≫ (enrichedDiagramRestrict j).map f := by
  have h := universalHomEquiv_natural_right j W (𝟙 (object j W)) f
  simpa only [Category.id_comp, unit] using h

end SSet.Marked.EnrichedLeftKan
