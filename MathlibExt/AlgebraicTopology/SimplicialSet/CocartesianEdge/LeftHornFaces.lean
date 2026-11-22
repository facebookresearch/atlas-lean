/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.CocartesianEdge.LeftHornLifting
import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
# Original critical edges in the two- and three-dimensional left horns

The same first edge is read through the original last face. These finite
characteristic equations connect the strict left-horn lifting API to
the existing edge and triangle constructors without changing endpoints.
-/

noncomputable section
universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.CocartesianEdge

private theorem critical_two : yonedaEquiv (horn₂₀.ι₀₁.{u}) = leftHornEdgeSimplex.{u} 0 := by
  apply Subtype.ext
  change yonedaEquiv (horn.ι (0 : Fin 3) (2 : Fin 3) (by decide) ≫
    (horn 2 (0 : Fin 3)).ι) = _
  rw [horn.ι_ι]
  change yonedaEquiv (SSet.stdSimplex.map (SimplexCategory.δ (2 : Fin 3))) = _
  rw [SSet.yonedaEquiv_map]
  apply SSet.stdSimplex.ext
  intro i
  rw [SSet.stdSimplex.objEquiv_symm_apply]
  apply Fin.ext
  fin_cases i <;> rfl

private theorem critical_three :
    yonedaEquiv ((SSet.stdSimplex.δ (2 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]) ≫
      horn.ι (0 : Fin 4) (3 : Fin 4) (by decide)) = leftHornEdgeSimplex.{u} 1 := by
  apply Subtype.ext
  change yonedaEquiv (((SSet.stdSimplex.δ (2 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]) ≫
    horn.ι (0 : Fin 4) (3 : Fin 4) (by decide)) ≫ (horn 3 (0 : Fin 4)).ι) = _
  rw [Category.assoc, horn.ι_ι]
  change yonedaEquiv (SSet.stdSimplex.map (SimplexCategory.δ (2 : Fin 3)) ≫
    SSet.stdSimplex.map (SimplexCategory.δ (3 : Fin 4))) = _
  rw [← SSet.stdSimplex.map_comp, SSet.yonedaEquiv_map]
  apply SSet.stdSimplex.ext
  intro i
  rw [SSet.stdSimplex.objEquiv_symm_apply]
  apply Fin.ext
  fin_cases i <;> rfl

/-- In the left two-horn the critical edge is the whole original last face. -/
theorem leftHornEdge_two {X : SSet.{u}} (σ₀ : (Λ[2, (0 : Fin 3)] : SSet.{u}) ⟶ X) :
    (leftHornEdge σ₀).edge = yonedaEquiv (horn₂₀.ι₀₁ ≫ σ₀) := by
  rw [yonedaEquiv_comp, critical_two, leftHornEdge_edge]

/-- In the left three-horn the critical edge is the first edge of the original last triangle. -/
theorem leftHornEdge_three {X : SSet.{u}} (σ₀ : (Λ[3, (0 : Fin 4)] : SSet.{u}) ⟶ X) :
    (leftHornEdge σ₀).edge = X.δ (2 : Fin 3)
      (yonedaEquiv (horn.ι (0 : Fin 4) (3 : Fin 4) (by decide) ≫ σ₀)) := by
  rw [← SSet.stdSimplex.yonedaEquiv_δ_comp]
  rw [← Category.assoc, yonedaEquiv_comp, critical_three, leftHornEdge_edge]

end SSet.CocartesianEdge
