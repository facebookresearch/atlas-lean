/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.ODE.PlanarShooting.InvariantRegion

@[expose] public section

open Real Filter Topology Set
open MathlibExt.Analysis.ODE.PlanarShooting

namespace MathlibExtTest.Analysis.ODE.PlanarShooting.InvariantRegion

/-! ### The triangle -/

/-- Non-vacuity: `(1/2, -1/4)` lies in the triangle for `D = 1`, `c = 2` (slope `μ = 1`). -/
example : ((1 / 2 : ℝ), (-1 / 4 : ℝ)) ∈ trappingTriangle 1 2 :=
  ⟨by norm_num, by norm_num, by norm_num⟩

/-- Boundary: the saddle `(1, 0)` is not in the open triangle. -/
example : ((1 : ℝ), (0 : ℝ)) ∉ trappingTriangle 1 2 := fun h => lt_irrefl _ h.1

/-- Boundary: the node `(0, 0)` is not in the open triangle. -/
example : ((0 : ℝ), (0 : ℝ)) ∉ trappingTriangle 1 2 := fun h => lt_irrefl _ h.2.1

/-- Boundary: the point `(1/2, -1/2)` of the slanted edge `V = -μ U` is excluded. -/
example : ((1 / 2 : ℝ), (-1 / 2 : ℝ)) ∉ trappingTriangle 1 2 := fun h => by
  have := h.2.2; norm_num at this

/-- The a-priori bounds at `(1/2, -1/4)`, `D = r = 1`, `c = 2`. -/
example : -(2 / (2 * 1)) < (-1 / 4 : ℝ) :=
  (bounds_of_mem_trappingTriangle one_pos one_pos two_pos
    (p := ((1 / 2 : ℝ), (-1 / 4 : ℝ))) ⟨by norm_num, by norm_num, by norm_num⟩).2.2.1

/-! ### Boundary cases in the speed -/

/-- The critical speed `c = 2 √(r D) = 2` (`D = r = 1`) satisfies the speed hypothesis. -/
example : 2 * √((1 : ℝ) * 1) ≤ 2 := by simp

/-- At the critical speed the hypothesis gives `c² = 4 r D` with equality. -/
example : 4 * 1 * 1 ≤ (2 : ℝ) ^ 2 :=
  (pos_and_sq_of_two_sqrt_le one_pos one_pos (by simp : 2 * √((1 : ℝ) * 1) ≤ 2)).2

/-- Critical eigenvalue collision: for `D = r = 1`, `c = 2`, the slope `-1` is the double root
of `λ² + 2 λ + 1`. -/
example : (1 : ℝ) * (-(2 / (2 * 1))) ^ 2 + 2 * (-(2 / (2 * 1))) + 1 = 0 :=
  (node_charPoly_neg_slope_eq_zero_iff one_pos).2 (by norm_num)

/-- Above the critical speed (`c = 3`) the slope is not an eigenvalue. -/
example : (1 : ℝ) * (-(3 / (2 * 1))) ^ 2 + 3 * (-(3 / (2 * 1))) + 1 ≠ 0 := fun h => by
  have := (node_charPoly_neg_slope_eq_zero_iff one_pos).1 h
  norm_num at this

/-- Below the critical speed (`c = 1 < 2`) the field points out of the triangle somewhere on the
slanted edge, so the speed hypothesis cannot be dropped. -/
example : ∃ u ∈ Ioo (0 : ℝ) 1, (u, -(1 / (2 * 1)) * u) ∈ frontier (trappingTriangle 1 1) ∧
    (-(1 * (-(1 / (2 * 1)) * u)) - 1 * u * (1 - u)) / 1 + 1 / (2 * 1) * (-(1 / (2 * 1)) * u)
      < 0 :=
  exists_outward_of_sq_lt one_pos one_pos one_pos (by norm_num)

/-- Speed limits: constant points of the triangle stay in the closed triangle at the limit. -/
example : ((1 / 2 : ℝ), (-1 / 4 : ℝ)).2 ≤ 0 :=
  (closedTriangle_of_tendsto (D := 1) (cs := fun _ => 2) (ps := fun _ => (1 / 2, -1 / 4))
    tendsto_const_nhds tendsto_const_nhds
    fun _ => ⟨by norm_num, by norm_num, by norm_num⟩).2.1

end MathlibExtTest.Analysis.ODE.PlanarShooting.InvariantRegion
