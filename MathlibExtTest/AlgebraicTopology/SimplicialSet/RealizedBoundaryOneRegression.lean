/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.Subcomplex
import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationDeltaGenerated

/-!
# Realized boundary of the standard 1-simplex

Test the actual boundary inclusion and both of its endpoints.
-/

set_option autoImplicit false

open CategoryTheory Convexity Simplicial

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet

example : DeltaGeneratedSpace (SSet.toTop.obj (SSet.boundary 1 : SSet.{0})) :=
  inferInstance

/-- The realized boundary inclusion of the standard 1-simplex is a closed embedding,
and under the standard simplex homeomorphism its image is exactly the two vertices. -/
theorem realizedBoundaryOne_closedEmbedding_range :
    Topology.IsClosedEmbedding (SSet.toTop.{0}.map (SSet.boundary 1).ι) ∧
      Set.range (⇑(⦋1⦌.toTopHomeo.{0}) ∘ ⇑(SSet.toTop.{0}.map (SSet.boundary 1).ι)) =
        Set.range (StdSimplex.single (R := ℝ) (X := Fin 2)) := by
  refine ⟨(SSet.Subcomplex.closedT1Embeddings_toTop_map_ι (SSet.boundary 1)).1, ?_⟩
  have finTwo (index : Fin 2) : index = 0 ∨ index = 1 := by omega
  apply Set.Subset.antisymm
  · rintro _ ⟨point, rfl⟩
    let realized := SSet.toTop.{0}.map (SSet.boundary 1).ι point
    let coord := ⦋1⦌.toTopHomeo.{0} realized
    change coord ∈ Set.range _
    obtain ⟨index, hZero⟩ :=
      SSet.boundary.mem_zeroCoord_of_mem_realizedBoundaryRange 1 realized ⟨point, rfl⟩
    change coord.weights index = 0 at hZero
    rcases finTwo index with rfl | rfl
    · have hOne : coord.weights 1 = 1 := by
        simpa only [hZero, zero_add] using coord.total_fin_two
      refine ⟨1, StdSimplex.ext (Finsupp.ext fun vertex ↦ ?_)⟩
      rcases finTwo vertex with rfl | rfl <;> simp [hZero, hOne]
    · have hOne : coord.weights 0 = 1 := by
        simpa only [hZero, add_zero] using coord.total_fin_two
      refine ⟨0, StdSimplex.ext (Finsupp.ext fun vertex ↦ ?_)⟩
      rcases finTwo vertex with rfl | rfl <;> simp [hZero, hOne]
  · rintro _ ⟨vertex, rfl⟩
    -- Each endpoint comes from the actual 0-simplex mapping into the boundary.
    have endpoint (index : Fin 2) :
        StdSimplex.single (R := ℝ) ((SimplexCategory.δ (n := 0) index) 0) ∈
          Set.range (⇑(⦋1⦌.toTopHomeo.{0}) ∘ ⇑(SSet.toTop.{0}.map (SSet.boundary 1).ι)) := by
      let origin := ⦋0⦌.toTopHomeo.{0}.symm (StdSimplex.single (R := ℝ) 0)
      refine ⟨SSet.toTop.{0}.map (SSet.boundary.ι index) origin, ?_⟩
      have face := ConcreteCategory.congr_hom
        (by
          rw [← Functor.map_comp, SSet.boundary.ι_ι]
          rfl :
          SSet.toTop.{0}.map (SSet.boundary.ι index) ≫
            SSet.toTop.{0}.map (SSet.boundary 1).ι =
            SSet.toTop.{0}.map (SSet.stdSimplex.map (SimplexCategory.δ (n := 0) index))) origin
      simp only [ConcreteCategory.comp_apply] at face
      change ⦋1⦌.toTopHomeo.{0}
        (SSet.toTop.{0}.map (SSet.boundary 1).ι
          (SSet.toTop.{0}.map (SSet.boundary.ι index) origin)) = _
      rw [face, SimplexCategory.toTopHomeo_naturality_apply]
      simp only [origin, Homeomorph.apply_symm_apply, StdSimplex.map_single]
    rcases finTwo vertex with rfl | rfl
    · exact endpoint 1
    · exact endpoint 0

end MathlibExtTest.AlgebraicTopology.SimplicialSet
