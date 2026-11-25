/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.RightHornLifting
import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
# Original critical edges in the two- and three-dimensional right horns

The same last edge is read through the original zeroth face. These finite
characteristic equations connect the strict right-horn lifting API to
the existing edge and triangle constructors without changing endpoints.
-/

noncomputable section
universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.CartesianEdge

private theorem critical_two : yonedaEquiv (horn₂₂.ι₁₂.{u}) = rightHornEdgeSimplex.{u} 0 := by
  apply Subtype.ext
  change yonedaEquiv (horn.ι (Fin.last 2) (0 : Fin 3) (by decide) ≫
    (horn 2 (Fin.last 2)).ι) = _
  rw [horn.ι_ι]
  change yonedaEquiv (stdSimplex.map (SimplexCategory.δ (0 : Fin 3))) = _
  rw [SSet.yonedaEquiv_map]
  apply stdSimplex.ext
  intro i
  rw [stdSimplex.objEquiv_symm_apply]
  apply Fin.ext
  fin_cases i <;> rfl

private theorem critical_three :
    yonedaEquiv ((stdSimplex.δ (0 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]) ≫
      horn.ι (Fin.last 3) (0 : Fin 4) (by decide)) = rightHornEdgeSimplex.{u} 1 := by
  apply Subtype.ext
  change yonedaEquiv (((stdSimplex.δ (0 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]) ≫
    horn.ι (Fin.last 3) (0 : Fin 4) (by decide)) ≫ (horn 3 (Fin.last 3)).ι) = _
  rw [Category.assoc, horn.ι_ι]
  change yonedaEquiv (stdSimplex.map (SimplexCategory.δ (0 : Fin 3)) ≫
    stdSimplex.map (SimplexCategory.δ (0 : Fin 4))) = _
  rw [← stdSimplex.map_comp, SSet.yonedaEquiv_map]
  apply stdSimplex.ext
  intro i
  rw [stdSimplex.objEquiv_symm_apply]
  apply Fin.ext
  fin_cases i <;> rfl

/-- In the right two-horn the critical edge is the whole original zeroth face. -/
theorem rightHornEdge_two {X : SSet.{u}} (σ₀ : (Λ[2, Fin.last 2] : SSet.{u}) ⟶ X) :
    (rightHornEdge σ₀).edge = yonedaEquiv (horn₂₂.ι₁₂ ≫ σ₀) := by
  rw [yonedaEquiv_comp, critical_two, rightHornEdge_edge]

/-- In the right three-horn the critical edge is the zeroth edge of the original zeroth triangle. -/
theorem rightHornEdge_three {X : SSet.{u}} (σ₀ : (Λ[3, Fin.last 3] : SSet.{u}) ⟶ X) :
    (rightHornEdge σ₀).edge = X.δ (0 : Fin 3)
      (yonedaEquiv (horn.ι (Fin.last 3) (0 : Fin 4) (by decide) ≫ σ₀)) := by
  rw [← stdSimplex.yonedaEquiv_δ_comp]
  rw [← Category.assoc, yonedaEquiv_comp, critical_three, rightHornEdge_edge]

end SSet.CartesianEdge
