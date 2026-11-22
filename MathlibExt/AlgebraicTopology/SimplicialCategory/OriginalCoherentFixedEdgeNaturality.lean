/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedEdgeReadback
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomStrictMaps
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornMapNaturality

/-!
# Exact original fixed-edge postcomposition

The existing whole fixed-edge construction and readback follow the
same original enriched functor and retain both individual objects.
These formulas allow genuine full-Hom vertex lifts to construct
original coherent one-simplex lifts.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFixedEdgeNaturality
open SimplicialEnrichment HomMappingCells

variable {C D : Carrier.{u}} (F : C ⟶ D) (x y : C)

/-- The same whole original fixed edge postcomposed by the original enriched functor. -/
def map (σ : FixedSimplex x y (n := 0)) :
    FixedSimplex (F.obj x) (F.obj y) (n := 0) :=
  ⟨σ.val ≫ F, congrArg F.obj σ.property.1, congrArg F.obj σ.property.2⟩

/-- The literal whole enriched-functor value of the same fixed-edge map. -/
theorem map_val (σ : FixedSimplex x y (n := 0)) : (map F x y σ).val = σ.val ≫ F := rfl

/-- The full original fixed-edge flag readback follows the exact original Hom map. -/
theorem read_postcompose (σ : FixedSimplex x y (n := 0)) :
    read x y σ ≫ F.map x y = read (F.obj x) (F.obj y) (map F x y σ) := by
  have h := HornMapNaturality.retargetMap_postcompose σ.val F
    (.mk (ULift.up (0 : Fin 2))) (.mk (ULift.up (Fin.last 1)))
    σ.property.1 σ.property.2
  exact (Category.assoc _ _ _).trans
    (congrArg (fun q => HomFlagEvaluation.flagMap.{u} (n := 0) ≫ q) h)

/-- The actual original Hom vertex of the whole fixed edge is natural for the same enriched map. -/
theorem readVertex_postcompose (σ : FixedSimplex x y (n := 0)) :
    (F.map x y).app (op ⦋0⦌) (FixedEdgeReadback.readVertex x y σ) =
      FixedEdgeReadback.readVertex (F.obj x) (F.obj y) (map F x y σ) := by
  exact (SSet.yonedaEquiv_comp (read x y σ) (F.map x y)).symm.trans
    (congrArg SSet.yonedaEquiv (read_postcompose F x y σ))

/-- The SAME existing whole fixed-edge construction is natural, with both original object images retained. -/
theorem construct_postcompose (τ : (x ⟶[SSet.{u}] y) _⦋0⦌) :
    map F x y (construct x y τ) =
      construct (F.obj x) (F.obj y) ((F.map x y).app (op ⦋0⦌) τ) := by
  apply Subtype.ext
  exact (HomStrictMaps.simplex_postcompose F x y (SSet.yonedaEquiv.symm τ)).trans
    (congrArg (fun q => HomSimplex.simplex (F.obj x) (F.obj y) q)
      (SSet.yonedaEquiv_symm_comp τ (F.map x y)))

/-- Equal original endpoint labels transport the SAME whole fixed edge, preserving its enriched functor. -/
def reindex {x' y' : D} (hx : F.obj x = x') (hy : F.obj y = y')
    (σ : FixedSimplex x' y' (n := 0)) :
    FixedSimplex (F.obj x) (F.obj y) (n := 0) :=
  ⟨σ.val, σ.property.1.trans hx.symm, σ.property.2.trans hy.symm⟩

/-- The actual whole fixed-edge value is unchanged under its true endpoint equalities. -/
theorem reindex_val {x' y' : D} (hx : F.obj x = x') (hy : F.obj y = y')
    (σ : FixedSimplex x' y' (n := 0)) :
    (reindex F x y hx hy σ).val = σ.val := rfl

end CategoryTheory.CoherentRealization.OriginalFixedEdgeNaturality
