/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentMappingFlagVertices

/-!
# Literal endpoint paths of original coherent mapping vertices

Degree-zero flag evaluation uses precisely the original two-endpoint
path. Its image under any right-join operator is the same original
endpoint path at the supplied image labels. These equations retain the
actual path carriers and individual objects.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.MappingEndpointPaths
open SimplicialEnrichment AdjacentHom PathLastMaximum PathMaximumFlags PathMaximumOperators MappingFlagVertices

/-- The original zero-front flag is exactly the original adjacent zero-to-one endpoint path. -/
theorem zero_flag : flag.{u} (0 : Fin 1) = endpointPath (ULift.up.{u} (0 : Fin 2)) (ULift.up (1 : Fin 2)) (by decide) :=
  path_eq _ _ (by decide) (fun k _ _ => finTwo_vertices k) _

/-- Every actual right-join operator sends the original zero flag to the literal endpoint path with the same
  supplied image source and last target. -/
theorem image_zero_flag {m : ℕ} (θ : ⦋0⦌ ⟶ ⦋m⦌) :
    PathMaximumOperators.image θ (0 : Fin 1) (flag.{u} (0 : Fin 1)) =
      endpointPath (ULift.up.{u} (θ.toOrderHom 0).castSucc) (ULift.up (Fin.last (m + 1))) (Fin.le_last _) := by
  apply SimplicialThickening.Path.ext
  change (extension θ).toOrderHom.uliftMap '' (flag.{u} (0 : Fin 1)).I = {_, _}
  have hI := congrArg SimplicialThickening.Path.I (zero_flag.{u})
  rw [hI]
  change (extension θ).toOrderHom.uliftMap '' {ULift.up.{u} (0 : Fin 2), ULift.up (1 : Fin 2)} = _
  rw [Set.image_insert_eq, Set.image_singleton]
  exact congrArg₂ (fun a b => ({a, b} : Set (ULift.{u} (Fin (m + 2))))) (lifted_front θ (0 : Fin 1)) (lifted_last θ)

/-- The actual original right-mapping vertex is read at its literal two-endpoint path, retaining the exact
  original object equalities. -/
theorem read_zero (C : Carrier.{u}) (x y : C)
    (σ : (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (HomSimplexEndpoints.vertex x)
      (HomSimplexEndpoints.vertex y)) _⦋0⦌) :
    MappingVertices.read x y σ =
      (EqualityTransport.hom (RightMappingSimplex.front_obj x y σ 0) (RightMappingSimplex.last_obj x y σ)).app (op ⦋0⦌)
        (((RightMappingSimplex.toEnriched x y σ).map (.mk (ULift.up (0 : Fin 2))) (.mk (ULift.up (1 : Fin
          2)))).app (op ⦋0⦌)
          (ComposableArrows.mk₀ (endpointPath (ULift.up.{u} (0 : Fin 2)) (ULift.up (1 : Fin 2)) (by decide)))) := by
  have h := evaluate_vertex x y (RightMappingSimplex.toEnriched x y σ)
    (RightMappingSimplex.front_obj x y σ 0) (RightMappingSimplex.last_obj x y σ) (0 : Fin 1)
  have hId : (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0) = 𝟙 ⦋0⦌ := by
    ext i : 3
    exact (Fin.eq_zero i).symm
  have hV : standardVertex.{u} (0 : Fin 1) = SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by
    change SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0) = _
    exact congrArg (fun f => SSet.stdSimplex.objEquiv.symm f) hId
  have hR : MappingVertices.read x y σ =
      (HomFlagEvaluation.evaluate x y (RightMappingSimplex.toEnriched x y σ)
        (RightMappingSimplex.front_obj x y σ 0) (RightMappingSimplex.last_obj x y σ)).app (op ⦋0⦌)
          (standardVertex.{u} (0 : Fin 1)) := by
    rw [hV]
    rfl
  rw [← zero_flag]
  exact hR.trans h

end CategoryTheory.CoherentRealization.MappingEndpointPaths
