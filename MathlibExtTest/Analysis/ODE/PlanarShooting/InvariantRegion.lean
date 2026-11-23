/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.ODE.PlanarShooting.InvariantRegion
import MathlibExt.Analysis.ODE.PlanarShooting.Lemma

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

/-! ### Invariance and entry of the unstable branch -/

example {D r c a : ℝ} {U V : ℝ → ℝ} (hD : 0 < D) (hr : 0 < r) (hc : 2 * √(r * D) ≤ c)
    (hode : ∀ z ∈ Set.Ici a, HasDerivAt U (V z) z ∧
      HasDerivAt V ((-(c * V z) - r * U z * (1 - U z)) / D) z)
    (ha : (U a, V a) ∈ trappingTriangle D c) :
    ∀ t ∈ Set.Ici a, (U t, V t) ∈ trappingTriangle D c :=
  mapsTo_trappingTriangle_Ici hD hr hc hode ha

/-- Acceptance 1b, the three edge inequalities of the triangle, stated pointwise for the vector
field `(V, (-(c V) - r U (1 - U)) / D)`: on the edge `V = 0` with `0 < U < 1` the field points
down, and on the slanted edge `V = -c U / (2 D)` with `0 < U` the derivative of `V + c U / (2 D)`
is positive when `c² ≥ 4 r D`. (On the edge `U = 1` the field is `U' = V < 0`.) -/
example {D r c u : ℝ} (hD : 0 < D) (hr : 0 < r) (hu0 : 0 < u) (hu1 : u < 1) :
    (-(c * 0) - r * u * (1 - u)) / D < 0 := by
  have : 0 < r * u * (1 - u) := mul_pos (mul_pos hr hu0) (sub_pos.2 hu1)
  rw [div_neg_iff]; right; constructor <;> linarith

example {D r c u : ℝ} (hD : 0 < D) (hr : 0 < r) (hc2 : 4 * r * D ≤ c ^ 2) (hu0 : 0 < u) :
    0 < (-(c * (-(c / (2 * D)) * u)) - r * u * (1 - u)) / D + c / (2 * D) * (-(c / (2 * D)) * u) := by
  have hk : 0 ≤ c ^ 2 / (4 * D) - r := by
    rw [sub_nonneg, le_div_iff₀ (by positivity)]; linarith
  have hpos : 0 < c ^ 2 / (4 * D) - r + r * u := by nlinarith [mul_pos hr hu0]
  have key : (-(c * (-(c / (2 * D)) * u)) - r * u * (1 - u)) / D +
      c / (2 * D) * (-(c / (2 * D)) * u) = u * (c ^ 2 / (4 * D) - r + r * u) / D := by
    field_simp
    ring
  rw [key]
  exact div_pos (mul_pos hu0 hpos) hD

/-- Acceptance 2, the unstable manifold of `(1, 0)` enters the region: the unstable branch
(Atlas `PlanarShooting.exists_unstableBranch`) solves the planar system on `z < 0`, tends to the
saddle `(1, 0)` at `-∞`, and eventually lies in the open trapping triangle
(`PlanarShooting.eventually_mem_trappingTriangle_atBot`). -/
example {D r c : ℝ} (hD : 0 < D) (hr : 0 < r) (hc0 : 0 < c) :
    ∃ U V : ℝ → ℝ, (∀ z < 0, HasDerivAt U (V z) z ∧
        HasDerivAt V ((-(c * V z) - r * U z * (1 - U z)) / D) z) ∧
      Tendsto U atBot (𝓝 1) ∧ Tendsto V atBot (𝓝 0) ∧
      ∀ᶠ z in atBot, (U z, V z) ∈ trappingTriangle D c := by
  obtain ⟨U, V, hode, hq, hU, hV, -⟩ := exists_unstableBranch hD hr c
  exact ⟨U, V, hode, hU, hV, eventually_mem_trappingTriangle_atBot hD hc0
    (fun z hz => ⟨(hq z hz).2.1, (hq z hz).2.2⟩) hU hV⟩

/-- Boundary: for `0 < c` with `c² < 4 r D` the vector field crosses the slanted edge of the
triangle outward, so the speed hypothesis of the invariance cannot be dropped (Atlas
`PlanarShooting.exists_outward_of_sq_lt`). -/
example {D r c : ℝ} (hD : 0 < D) (hr : 0 < r) (hc0 : 0 < c) (hc : c ^ 2 < 4 * r * D) :
    ∃ u ∈ Set.Ioo (0 : ℝ) 1, (u, -(c / (2 * D)) * u) ∈ frontier (trappingTriangle D c) ∧
      (-(c * (-(c / (2 * D)) * u)) - r * u * (1 - u)) / D + c / (2 * D) * (-(c / (2 * D)) * u)
        < 0 :=
  exists_outward_of_sq_lt hD hr hc0 hc

end MathlibExtTest.Analysis.ODE.PlanarShooting.InvariantRegion
