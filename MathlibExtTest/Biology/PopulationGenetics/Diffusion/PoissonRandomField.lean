/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.PopulationGenetics.Diffusion.PoissonRandomField

/-! Tests for the Poisson random field: the explicit density, the neutral reduction `θ / i` of
the expected spectrum (and the separate sample-monomorphic class `i = n`), the forward
equation, its constant probability current and boundary normalizations, and the ODE
characterization applied to the density itself. -/

open Real Set Filter
open scoped Topology

namespace MathlibExtTest.Biology.PopulationGenetics.Diffusion.PoissonRandomField

open MathlibExt.Biology.PopulationGenetics.Diffusion

example : prfDensity 2 0 (1 / 4) = 8 := by
  rw [prfDensity_zero 2 (by norm_num)]
  norm_num

/-- Junk value outside the domain: at `x = 1` the formula divides by `0`, giving `0` rather
than the continuous extension `θ`. -/
example : prfDensity 1 0 1 = 0 := by simp [prfDensity]

example : prfDensity 1 1 (1 / 2) = (1 - exp (-1)) / ((1 - exp (-2)) * (1 / 4)) := by
  rw [prfDensity_of_ne_zero 1 one_ne_zero]
  norm_num
  ring

/-- Neutral spectrum: in a sample of `10`, the expected number of sites with `3` derived copies
is `θ / 3`. -/
example (θ : ℝ) : expectedSFS θ 0 10 3 = θ / 3 := by
  simpa using expectedSFS_neutral θ (n := 10) (i := 3) (by norm_num) (by norm_num)

/-- Singletons: `E ξ₁ = θ` in a sample of at least two copies. -/
example (θ : ℝ) (n : ℕ) (hn : 2 ≤ n) : expectedSFS θ 0 n 1 = θ := by
  simpa using expectedSFS_neutral θ one_pos hn

/-- Sites where all `5` sampled copies are derived (monomorphic in the sample, outside the
spectrum): `θ / 5`. -/
example (θ : ℝ) : expectedSFS θ 0 5 5 = θ / 5 := by
  simpa using expectedSFS_neutral_self θ (n := 5) (by norm_num)

/-- The neutral density as the Green's function of mutations entering at frequency `1/10`. -/
example (θ : ℝ) : prfDensity θ 0 (1 / 2) = θ / (2 * (1 / 10)) * neutralGreen (1 / 10) (1 / 2) :=
  prfDensity_zero_eq_neutralGreen θ (by norm_num) (by norm_num) (by norm_num)

example (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    deriv (deriv fun y => y * (1 - y) * prfDensity 3 (-2) y) x / 2 -
      (-2) * deriv (fun y => y * (1 - y) * prfDensity 3 (-2) y) x = 0 :=
  forward_prfDensity 3 (-2) hx

example : Tendsto (fun y => y * (1 - y) * prfDensity 3 5 y) (𝓝[>] 0) (𝓝 3) :=
  tendsto_weighted_prfDensity_zero 3 5

example : Tendsto (fun y => y * (1 - y) * prfDensity 3 5 y) (𝓝[<] 1) (𝓝 0) :=
  tendsto_weighted_prfDensity_one 3 5

/-- The neutral probability current is `θ / 2`, not the boundary value `θ` of the weighted
density. -/
example (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 * (x * (1 - x) * prfDensity 3 0 x) -
      deriv (fun y => y * (1 - y) * prfDensity 3 0 y) x / 2 = 3 / 2 := by
  rw [current_prfDensity 3 0 hx]
  simp [kimuraSlope]

/-- With selection the current is `θ σ / (1 - e^{-2σ})`. -/
example (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    5 * (x * (1 - x) * prfDensity 3 5 x) -
      deriv (fun y => y * (1 - y) * prfDensity 3 5 y) x / 2 = 3 * 5 / (1 - exp (-2 * 5)) := by
  rw [current_prfDensity 3 5 hx]
  simp only [kimuraSlope, show (5 : ℝ) ≠ 0 by norm_num, ↓reduceIte]
  ring

/-- The ODE characterization pins down the neutral density: a density whose weighted density
is the line
`F(x) = θ (1 - x)` is `θ / x`. -/
example (θ : ℝ) (hθ : θ ≠ 0) (φ : ℝ → ℝ) (hφ : ∀ x ∈ Ioo (0 : ℝ) 1, θ * (1 - x) = x * (1 - x) * φ x)
    (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : φ x = θ / x := by
  have hd : ∀ y, HasDerivAt (fun y : ℝ => θ * (1 - y)) (-θ) y := fun y => by
    simpa using ((hasDerivAt_id' y).const_sub 1).const_mul θ
  have hD : deriv (fun y : ℝ => θ * (1 - y)) = fun _ => -θ := funext fun y => (hd y).deriv
  rw [eq_prfDensity_of_forward (σ := 0) hθ hφ (by fun_prop)
    (fun y _ => (hd y).differentiableAt.differentiableWithinAt)
    (by rw [hD]; exact differentiableOn_const _) (fun y _ => by simp [hD]) (by simp) (by simp)
    x hx, prfDensity_zero θ hx.2.ne]

end MathlibExtTest.Biology.PopulationGenetics.Diffusion.PoissonRandomField
