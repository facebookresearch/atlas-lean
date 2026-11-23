/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.ODE.PlanarShooting.Lemma

@[expose] public section

open Real Filter Topology
open MathlibExt.Analysis.ODE.PlanarShooting

namespace MathlibExtTest.Analysis.ODE.PlanarShooting

/-- The first nonlinear coefficient: `a₂ = -ρ / (2 κ + ρ)`; with `κ = ρ = 1` it is `-1/3`. -/
example : branchCoeff 1 1 2 = -1 / 3 := by
  simp [branchCoeff]; norm_num

/-- The recursion in Cauchy-product form at `n = 2`. -/
example : ((2 : ℕ) - 1 : ℝ) * (1 * (2 : ℕ) + 1) * branchCoeff 1 1 2 =
    -1 * ∑ p ∈ Finset.antidiagonal 2, branchCoeff 1 1 p.1 * branchCoeff 1 1 p.2 :=
  branchCoeff_rec zero_le_one one_pos 2

/-- Boundary `κ = 0` (no diffusion term in the coefficient recursion): still `|aₙ| ≤ 1`. -/
example (n : ℕ) : |branchCoeff 0 1 n| ≤ 1 := abs_branchCoeff_le_one le_rfl one_pos n

/-- With `D = r = 1` and the standing speed `c = 0` the eigenvalues are `±1`. -/
example : unstableRate 1 1 0 = 1 := by
  norm_num [unstableRate, show √(4 : ℝ) = 2 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]

example : stableRate 1 1 0 = -1 := by
  norm_num [stableRate, show √(4 : ℝ) = 2 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]

/-- Degenerate boundary `D = 0`: the formula collapses to `0` (division by zero), which is why
every branch theorem assumes `0 < D`. -/
example : unstableRate 0 1 1 = 0 := by simp [unstableRate]

/-- Non-vacuity at the critical KPP speed `c = 2 √(r D) = 2` (`D = r = 1`). -/
example : ∃ U U' : ℝ → ℝ,
    (∀ z < 0, HasDerivAt U (U' z) z ∧
      HasDerivAt U' ((-(2 * U' z) - 1 * U z * (1 - U z)) / 1) z) ∧
    (∀ z < 0, 0 < U z ∧ U z < 1 ∧ U' z < 0) ∧
    Tendsto U atBot (𝓝 1) ∧ Tendsto U' atBot (𝓝 0) ∧
    Tendsto (fun z => U' z / (U z - 1)) atBot (𝓝 (unstableRate 1 1 2)) :=
  exists_unstableBranch one_pos one_pos 2

/-- The branch exists below the minimal speed too (here a negative speed `c = -3`); the speed
threshold is not part of this lemma. -/
example : 0 < branch 1 1 (-3) (-1) ∧ branch 1 1 (-3) (-1) < 1 ∧ branchDeriv 1 1 (-3) (-1) < 0 :=
  branch_mem_quadrant one_pos one_pos (-3) (by norm_num)

/-- The departure rate is positive for any speed, so the branch genuinely leaves the saddle. -/
example (c : ℝ) : 0 < unstableRate 2 3 c := unstableRate_pos (by norm_num) (by norm_num) c

/-- The amplitude normalization `(1 - U) e^{-λ z} → 1/4`. -/
example : Tendsto (fun z => (1 - branch 1 1 0 z) / exp (unstableRate 1 1 0 * z)) atBot
    (𝓝 (1 / 4)) :=
  tendsto_one_sub_branch_div_exp one_pos one_pos 0

end MathlibExtTest.Analysis.ODE.PlanarShooting
