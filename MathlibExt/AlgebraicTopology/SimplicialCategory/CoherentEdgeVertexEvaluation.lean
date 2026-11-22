/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentMappingEndpointPaths

/-!
# Literal original vertex evaluation and endpoint retargeting

A fixed original coherent edge is read at its actual two-endpoint path.
Changing an endpoint by its supplied equality retains the entire
original Hom map and the literal cell evaluation. No transport or
mapping-equivalence outcome is an input.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.EdgeVertexEvaluation
open SimplicialEnrichment HomMappingCells HomFlagEvaluation MappingFlagVertices MappingEndpointPaths
variable {C : Carrier.{u}} (x y : C)

/-- The original fixed coherent edge reads the same literal two-endpoint Hom path under its exact supplied
  object boundaries. -/
theorem read_fixed (σ : FixedSimplex x y (n := 0)) :
    FixedEdgeReadback.readVertex x y σ =
      (EqualityTransport.hom σ.2.1 σ.2.2).app (op ⦋0⦌)
        ((σ.val.map (.mk (ULift.up (0 : Fin 2))) (.mk (ULift.up (1 : Fin 2)))).app (op ⦋0⦌)
          (ComposableArrows.mk₀ (AdjacentHom.endpointPath (ULift.up.{u} (0 : Fin 2)) (ULift.up (1 : Fin 2))
            (by decide)))) := by
  have h := evaluate_vertex x y σ.val σ.2.1 σ.2.2 (0 : Fin 1)
  have hId : (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0) = 𝟙 ⦋0⦌ := by
    ext i : 3
    exact (Fin.eq_zero i).symm
  have hV : standardVertex.{u} (0 : Fin 1) = SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) :=
    congrArg (fun f => SSet.stdSimplex.objEquiv.symm f) hId
  have hR : FixedEdgeReadback.readVertex x y σ =
      (evaluate x y σ.val σ.2.1 σ.2.2).app (op ⦋0⦌) (standardVertex.{u} (0 : Fin 1)) := by
    rw [hV]
    rfl
  rw [← zero_flag]
  exact hR.trans h

/-- The entire original enriched Hom map follows exact equality retargeting of its supplied source pair and
  original target objects. -/
theorem map_retarget {A : Carrier.{u}} (F : A ⟶ C) {a a' b b' : A} (ha : a = a') (hb : b = b')
    (hx : F.obj a' = x) (hy : F.obj b' = y) :
    F.map a b ≫ EqualityTransport.hom ((congrArg F.obj ha).trans hx) ((congrArg F.obj hb).trans hy) =
      EqualityTransport.hom ha hb ≫ F.map a' b' ≫ EqualityTransport.hom hx hy := by
  subst a'
  subst b'
  simp only [EqualityTransport.hom, eqToHom_refl, Category.id_comp]

end CategoryTheory.CoherentRealization.EdgeVertexEvaluation
