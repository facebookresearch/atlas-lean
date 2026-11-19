/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.FisherKPPExistence
import MathlibExt.Biology.Dynamics.FisherKPPClassification
import MathlibExt.Analysis.ODE.PlanarShooting.InvariantRegion
import MathlibExt.Analysis.ODE.PlanarShooting.Lemma

@[expose] public section

open Real Filter Topology
open MathlibExt.Biology.Dynamics.FisherKPP

namespace MathlibExtTest.Biology.Dynamics.FisherKPPExistence

open MathlibExt.Analysis.ODE.PlanarShooting

/-! ### Minimal-speed boundary -/

/-- The critical speed for `D = r = 1` is `c = 2`, and a strictly decreasing front exists
there. -/
example : ∃ U U' : ℝ → ℝ, IsFront 1 1 2 U U' ∧ StrictAnti U := by
  simpa using exists_isFront_two_mul_sqrt (D := 1) (r := 1) one_pos one_pos

/-- The critical speed through the general theorem, with `D = 4`, `r = 1`: `2 √(1 · 4) = 4`. -/
example : ∃ U U' : ℝ → ℝ, IsFront 4 1 4 U U' ∧ StrictAnti U :=
  exists_isFront_of_le (by norm_num) one_pos (by
    rw [show (1 : ℝ) * 4 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]; norm_num)

/-- Squared form exactly at the boundary: `4 r D = c²` for `D = r = 1`, `c = 2`. -/
example : ∃ U U' : ℝ → ℝ, IsFront 1 1 2 U U' ∧ StrictAnti U :=
  exists_isFront_of_sq_le one_pos one_pos (by norm_num) (by norm_num)

/-! ### Supercritical speeds -/

/-- A supercritical speed `c = 3 > 2` for `D = r = 1`. -/
example : ∃ U U' : ℝ → ℝ, IsFront 1 1 3 U U' ∧ StrictAnti U :=
  exists_isFront_of_sq_le one_pos one_pos (by norm_num) (by norm_num)

/-- Anisotropic parameters: `D = 1/2`, `r = 2`, `c = 2` is critical (`4 r D = 4 = c²`). -/
example : ∃ U U' : ℝ → ℝ, IsFront (1 / 2) 2 2 U U' ∧ StrictAnti U :=
  exists_isFront_of_sq_le (by norm_num) two_pos (by norm_num) (by norm_num)

/-! ### Non-vacuity of the conclusion -/

/-- The produced front is a genuine transition: it is strictly between the equilibria, decreases,
and connects `1` at `-∞` to `0` at `+∞`. -/
example : ∃ U : ℝ → ℝ, 0 < U 0 ∧ U 1 < U 0 ∧ U 0 < 1 ∧ Tendsto U atBot (𝓝 1) ∧
    Tendsto U atTop (𝓝 0) := by
  obtain ⟨U, U', ⟨-, hb, h1, h0⟩, hanti⟩ :=
    exists_isFront_of_sq_le (D := 1) (r := 1) (c := 2) one_pos one_pos (by norm_num)
      (by norm_num)
  exact ⟨U, (hb 0).1, hanti one_pos, (hb 0).2, h1, h0⟩

/-- `c = 2` is the minimal nonnegative front speed for `D = r = 1`: a front exists at `2`, and
none exists at any `0 ≤ c < 2`. -/
example : (∃ U U' : ℝ → ℝ, IsFront 1 1 2 U U' ∧ StrictAnti U) ∧
    ∀ c : ℝ, 0 ≤ c → c < 2 → ∀ U U' : ℝ → ℝ, ¬ IsFront 1 1 c U U' :=
  ⟨exists_isFront_of_sq_le one_pos one_pos (by norm_num) (by norm_num),
    fun c hc0 hc2 _ _ => not_isFront_of_sq_lt one_pos one_pos (by nlinarith)⟩

/-! ### Heteroclinic limits of fronts -/

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

/-! ### Boundary and non-vacuity checks -/

/-- Boundary: below the minimal speed there is no front, hence no heteroclinic orbit of the
frozen kind (Atlas `not_isFront_of_lt`). -/
example {D r c : ℝ} (hD : 0 < D) (hr : 0 < r) (hc : c < 2 * √(r * D)) :
    ¬ ∃ U V : ℝ → ℝ, IsFront D r c U V :=
  fun ⟨_, _, h⟩ => not_isFront_of_lt hD hr hc h

/-- Boundary: for `0 < c` with `c² < 4 r D` the vector field crosses the slanted edge of the
triangle outward, so the speed hypothesis of the invariance cannot be dropped (Atlas
`PlanarShooting.exists_outward_of_sq_lt`). -/
example {D r c : ℝ} (hD : 0 < D) (hr : 0 < r) (hc0 : 0 < c) (hc : c ^ 2 < 4 * r * D) :
    ∃ u ∈ Set.Ioo (0 : ℝ) 1, (u, -(c / (2 * D)) * u) ∈ frontier (trappingTriangle D c) ∧
      (-(c * (-(c / (2 * D)) * u)) - r * u * (1 - u)) / D + c / (2 * D) * (-(c / (2 * D)) * u)
        < 0 :=
  exists_outward_of_sq_lt hD hr hc0 hc

/-- Boundary: the critical speed `c = 2 √(r D)` is covered by the frozen existence theorem. -/
example {D r : ℝ} (hD : 0 < D) (hr : 0 < r) :
    ∃ U V : ℝ → ℝ, IsWaveProfile D r (2 * √(r * D)) U V ∧
      Tendsto (fun z => (U z, V z)) atBot (𝓝 (1, 0)) ∧
      Tendsto (fun z => (U z, V z)) atTop (𝓝 (0, 0)) ∧
      (∀ z, (U z, V z) ∈ trappingTriangle D (2 * √(r * D))) ∧
      (∀ z, 0 < U z ∧ U z < 1) ∧ StrictAnti U :=
  exists_heteroclinic_of_le hD hr le_rfl

/-- Non-vacuity on an explicit orbit: the Ablowitz–Zeppetella front lies in the trapping
triangle at every point and is heteroclinic (Atlas `isFront_azWave`,
`two_mul_sqrt_lt_azSpeed`). -/
example {D r C : ℝ} (hD : 0 < D) (hr : 0 < r) (hC : 0 < C) :
    (∀ z, (azWave D r C z, azWaveDeriv D r C z) ∈ trappingTriangle D (azSpeed D r)) ∧
      Tendsto (fun z => (azWave D r C z, azWaveDeriv D r C z)) atBot (𝓝 (1, 0)) ∧
      Tendsto (fun z => (azWave D r C z, azWaveDeriv D r C z)) atTop (𝓝 (0, 0)) :=
  ⟨mem_trappingTriangle_of_isFront hD hr (two_mul_sqrt_lt_azSpeed hD hr).le
      (isFront_azWave hD hr hC),
    tendsto_heteroclinic_of_isFront hD hr (isFront_azWave hD hr hC)⟩


open MathlibExt.Biology.Dynamics.FisherKPP

end MathlibExtTest.Biology.Dynamics.FisherKPPExistence
