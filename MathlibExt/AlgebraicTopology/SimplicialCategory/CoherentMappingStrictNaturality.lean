/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomStrictMaps

/-!
# Whole strict enriched-map naturality of coherent right mapping spaces

The target mapping-space map is actual postcomposition by the same
strict enriched map on the coherent nerve. Its individual original
vertex labels and its identity and composition laws are exact. The
original Hom comparison commutes as an entire simplicial map.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.MappingStrictNaturality
open SimplicialEnrichment HomSimplex HomSimplexEndpoints HomMapping HomStrictMaps
variable {C D E : Carrier.{u}} (F : C ⟶ D) (x y : C)

/-- The genuine right-mapping-space map induced by the same strict original enriched functor at the supplied
  vertex labels. -/
def map : SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (vertex x) (vertex y) ⟶
    SSet.mappingSpaceRight (coherentNerveFunctor.obj D) (vertex (F.obj x)) (vertex (F.obj y)) where
  app q := ↾fun σ => ⟨σ.val ≫ coherentNerveFunctor.map F, by
    constructor
    · exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun g => g ≫ coherentNerveFunctor.map F) σ.2.1).trans
          ((Category.assoc _ _ _).trans (congrArg (fun g => SSet.toDeltaZero _ ≫ g) (vertex_map F x))))
    · exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun g => g ≫ coherentNerveFunctor.map F) σ.2.2).trans (vertex_map F y))⟩
  naturality q r θ := by
    apply ConcreteCategory.hom_ext
    intro σ
    apply Subtype.ext
    exact Category.assoc _ _ _

/-- The original entire right-mapping simplex is postcomposed by the literal coherent-nerve map. -/
theorem map_val (q : SimplexCategoryᵒᵖ)
    (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (vertex x) (vertex y)).obj q) :
    ((map F x y).app q σ).val = σ.val ≫ coherentNerveFunctor.map F := rfl

/-- The actual entire original Hom comparison commutes with every same strict enriched map and the genuine
  right-mapping postcomposition. -/
theorem homComparison_naturality : HomMapping.map x y ≫ map F x y =
    F.map x y ≫ HomMapping.map (F.obj x) (F.obj y) := by
  apply SSet.hom_ext
  intro q
  induction q using Opposite.rec with
  | _ q =>
    induction q using SimplexCategory.rec with
    | _ n =>
      apply ConcreteCategory.hom_ext
      intro τ
      apply Subtype.ext
      let J := (SSet.joinStdSimplexIso.{u} n 0).hom
      let T := (SSet.yonedaEquiv (X := coherentNerveFunctor.obj C) (n := ⦋n + 1⦌)).symm
        (simplex x y (SSet.yonedaEquiv.symm τ))
      let U := (SSet.yonedaEquiv (X := coherentNerveFunctor.obj D) (n := ⦋n + 1⦌)).symm
        (simplex (F.obj x) (F.obj y) (SSet.yonedaEquiv.symm ((F.map x y).app (op ⦋n⦌) τ)))
      have hA := SSet.yonedaEquiv_symm_comp τ (F.map x y)
      have hS := simplex_postcompose F x y (SSet.yonedaEquiv.symm τ)
      have hE : simplex x y (SSet.yonedaEquiv.symm τ) ≫ F =
          simplex (F.obj x) (F.obj y) (SSet.yonedaEquiv.symm ((F.map x y).app (op ⦋n⦌) τ)) :=
        hS.trans (congrArg (fun t => simplex (F.obj x) (F.obj y) t) hA)
      have hY := SSet.yonedaEquiv_symm_comp (X := coherentNerveFunctor.obj C)
        (simplex x y (SSet.yonedaEquiv.symm τ)) (coherentNerveFunctor.map F)
      have hT : T ≫ coherentNerveFunctor.map F = U := hY.trans
        (congrArg (fun σ => (SSet.yonedaEquiv (X := coherentNerveFunctor.obj D) (n := ⦋n + 1⦌)).symm σ) hE)
      change (J ≫ T) ≫ coherentNerveFunctor.map F = J ≫ U
      exact (Category.assoc _ _ _).trans (congrArg (fun t => J ≫ t) hT)

/-- Actual right-mapping postcomposition preserves the same original identity enriched map. -/
theorem map_id : map (𝟙 C) x y = 𝟙 (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (vertex x) (vertex y)) := by
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  intro σ
  apply Subtype.ext
  exact Category.comp_id _

/-- Actual right-mapping postcomposition preserves the same composite of original strict enriched maps. -/
theorem map_comp (G : D ⟶ E) : map (F ≫ G) x y = map F x y ≫ map G (F.obj x) (F.obj y) := by
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  intro σ
  apply Subtype.ext
  exact (congrArg (fun f => σ.val ≫ f) (coherentNerveFunctor.map_comp F G)).trans
    (Category.assoc σ.val (coherentNerveFunctor.map F) (coherentNerveFunctor.map G)).symm

end CategoryTheory.CoherentRealization.MappingStrictNaturality
