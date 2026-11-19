/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.ODE.ContinuumBalances
import MathlibExt.Analysis.ODE.GreensOperator
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Drained consolidation sine mode

## i. Overview

The fundamental drained mode of one-dimensional Terzaghi
consolidation in a saturated layer of full thickness `H` (not a
drainage-path length; for double drainage the drainage path is
`H / 2`), with constant consolidation coefficient `cv` and a
sine initial excess pore-pressure profile of amplitude `u0`. It
is the first canonical unit-interval heat mode
(`MathlibExt.Analysis.ODE.ContinuumBalances.heatMode`) under the
depth rescaling `z / H` and diffusivity rescaling `cv / H^2`,
with the sine-basis normalization divided out:
`u(z, t) = u0 * exp (-cv * (π / H)^2 * t) * sin (π * z / H)`.
Depth `z` runs from one drained face (`z = 0`) to the other
(`z = H`). No arbitrary initial data, Fourier-series
completeness, or general consolidation existence theorem is
included.

## ii. Key results

- `EarthScience.consolidationMode`: the rescaled first heat mode.
- `EarthScience.consolidationMode_eq`: its explicit physical form.
- `EarthScience.consolidationMode_pde`: it satisfies
  `∂u/∂t = cv * ∂²u/∂z²` at every time and depth.
- `EarthScience.consolidationMode_zero_left` and
  `consolidationMode_zero_right`: the drained face values.
- `EarthScience.consolidationMode_time_zero` and
  `consolidationMode_midpoint_time_zero`: the sine initial
  profile, peaking at mid-depth.

## iii. Table of contents

- A. Definition and explicit form
- B. PDE, drained faces, and initial profile

## iv. References

- `MathlibExt.Analysis.ODE.ContinuumBalances` for the canonical
  unit-interval heat mode and its heat-equation witnesses.
- Terzaghi one-dimensional consolidation: excess pore pressure
  diffuses with coefficient `cv` between drained faces.
-/

@[expose] public section

open Real
open MathlibExt.Analysis.ODE.ContinuumBalances (heatMode)
open MathlibExt.Analysis.ODE.GreensOperator (sineBasisFun)
open MathlibExt.Analysis.ODE.DirichletSineEigenfunctions
  (dirichletLaplacianEigenvalue)

namespace EarthScience

/-! ## A. Definition and explicit form -/

/-- Fundamental drained consolidation mode in a layer of full
thickness `H` (not a drainage-path length), consolidation
coefficient `cv`, and initial excess pore-pressure amplitude `u0`:
the first canonical heat mode under the depth rescaling `z / H`
and diffusivity rescaling `cv / H^2`, with the basis normalization
divided out. Depth `z` runs from one drained face (`z = 0`) to the
other (`z = H`). -/
noncomputable def consolidationMode (u0 H cv t z : ℝ) : ℝ :=
  (u0 / Real.sqrt 2) * heatMode (cv / H ^ 2) 1 t (z / H)

/-- Explicit physical form of the consolidation mode:
`u0 * exp (-cv * (π / H)^2 * t) * sin (π * z / H)`. -/
theorem consolidationMode_eq {u0 H cv t z : ℝ} (hH : H ≠ 0) :
    consolidationMode u0 H cv t z
      = u0 * Real.exp (-cv * (Real.pi / H) ^ 2 * t)
        * Real.sin (Real.pi * z / H) := by
  have h1 : ((1 : ℕ+) : ℝ) = 1 := by norm_num
  have hsqrt : Real.sqrt 2 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num))
  have hH2 : H ^ 2 ≠ 0 := pow_ne_zero 2 hH
  have hexp : -(cv / H ^ 2) * ((1 : ℝ) * Real.pi) ^ 2 * t
      = -cv * (Real.pi / H) ^ 2 * t := by
    field_simp
  have hsin : (1 : ℝ) * Real.pi * (z / H) = Real.pi * z / H := by
    field_simp
  unfold consolidationMode heatMode sineBasisFun dirichletLaplacianEigenvalue
  rw [h1, hexp, hsin]
  field_simp

/-! ## B. PDE, drained faces, and initial profile -/

/-- The mode satisfies the one-dimensional Terzaghi consolidation
equation `∂u/∂t = cv * ∂²u/∂z²` at every time and depth. -/
theorem consolidationMode_pde {u0 H cv : ℝ} (hH : H ≠ 0) (t z : ℝ) :
    deriv (fun τ => consolidationMode u0 H cv τ z) t
      = cv * iteratedDeriv 2 (consolidationMode u0 H cv t) z := by
  have hH2 : H ^ 2 ≠ 0 := pow_ne_zero 2 hH
  have hfun_t : (fun τ => consolidationMode u0 H cv τ z)
      = fun τ => u0 * Real.exp (-cv * (Real.pi / H) ^ 2 * τ)
        * Real.sin (Real.pi * z / H) :=
    funext fun τ => consolidationMode_eq hH
  have hfun_z : consolidationMode u0 H cv t
      = fun z => u0 * Real.exp (-cv * (Real.pi / H) ^ 2 * t)
        * Real.sin (Real.pi * z / H) :=
    funext fun z => consolidationMode_eq hH
  have hshape_t : (fun τ => u0 * Real.exp (-cv * (Real.pi / H) ^ 2 * τ)
        * Real.sin (Real.pi * z / H))
      = fun τ => (u0 * Real.sin (Real.pi * z / H))
        * Real.exp (-cv * (Real.pi / H) ^ 2 * τ) := by
    funext τ
    ring
  have hlin_t : HasDerivAt (fun τ => -cv * (Real.pi / H) ^ 2 * τ)
      (-cv * (Real.pi / H) ^ 2) t :=
    hasDerivAt_const_mul _
  have hexp_t : HasDerivAt (fun τ => Real.exp (-cv * (Real.pi / H) ^ 2 * τ))
      (Real.exp (-cv * (Real.pi / H) ^ 2 * t) * (-cv * (Real.pi / H) ^ 2)) t :=
    hlin_t.exp
  have htime : deriv (fun τ => (u0 * Real.sin (Real.pi * z / H))
        * Real.exp (-cv * (Real.pi / H) ^ 2 * τ)) t
      = (u0 * Real.sin (Real.pi * z / H))
        * (Real.exp (-cv * (Real.pi / H) ^ 2 * t) * (-cv * (Real.pi / H) ^ 2)) :=
    (hexp_t.const_mul _).deriv
  have hiter : ∀ (G : ℝ → ℝ) (w : ℝ),
      iteratedDeriv 2 G w = deriv (deriv G) w := by
    intro G w
    have h2 : (2 : ℕ) = 1 + 1 := rfl
    have h10 : (1 : ℕ) = 0 + 1 := rfl
    rw [h2, iteratedDeriv_succ, h10, iteratedDeriv_succ, iteratedDeriv_zero]
  have hshape_z : (fun w => u0 * Real.exp (-cv * (Real.pi / H) ^ 2 * t)
        * Real.sin (Real.pi * w / H))
      = fun w => (u0 * Real.exp (-cv * (Real.pi / H) ^ 2 * t))
        * Real.sin (Real.pi / H * w) := by
    funext w
    have harg : Real.pi * w / H = Real.pi / H * w := by
      field_simp
    rw [harg]
  have hlin_z : ∀ (w : ℝ),
      HasDerivAt (fun w => Real.pi / H * w) (Real.pi / H) w :=
    fun w => hasDerivAt_const_mul _
  have hsin_z : ∀ (w : ℝ), HasDerivAt
      (fun w => Real.sin (Real.pi / H * w))
      (Real.cos (Real.pi / H * w) * (Real.pi / H)) w :=
    fun w => (hlin_z w).sin
  have hderiv1 : deriv (fun w => (u0 * Real.exp (-cv * (Real.pi / H) ^ 2 * t))
        * Real.sin (Real.pi / H * w))
      = fun w => (u0 * Real.exp (-cv * (Real.pi / H) ^ 2 * t))
        * (Real.cos (Real.pi / H * w) * (Real.pi / H)) :=
    funext fun w => ((hsin_z w).const_mul _).deriv
  have hshape2 : (fun w => (u0 * Real.exp (-cv * (Real.pi / H) ^ 2 * t))
        * (Real.cos (Real.pi / H * w) * (Real.pi / H)))
      = fun w => ((u0 * Real.exp (-cv * (Real.pi / H) ^ 2 * t)) * (Real.pi / H))
        * Real.cos (Real.pi / H * w) := by
    funext w
    ring
  have hcos_z : HasDerivAt (fun w => Real.cos (Real.pi / H * w))
      (-Real.sin (Real.pi / H * z) * (Real.pi / H)) z :=
    (hlin_z z).cos
  have hderiv2 : deriv (fun w => ((u0 * Real.exp (-cv * (Real.pi / H) ^ 2 * t))
        * (Real.pi / H)) * Real.cos (Real.pi / H * w)) z
      = ((u0 * Real.exp (-cv * (Real.pi / H) ^ 2 * t)) * (Real.pi / H))
        * (-Real.sin (Real.pi / H * z) * (Real.pi / H)) :=
    (hcos_z.const_mul _).deriv
  rw [hfun_t, hshape_t, htime, hfun_z, hiter, hshape_z, hderiv1, hshape2, hderiv2]
  have hsinarg : Real.pi / H * z = Real.pi * z / H := by
    field_simp
  rw [hsinarg]
  field_simp

/-- Drained face value at `z = 0`. -/
theorem consolidationMode_zero_left (u0 H cv t : ℝ) :
    consolidationMode u0 H cv t 0 = 0 := by
  unfold consolidationMode heatMode sineBasisFun
  simp

/-- Drained face value at `z = H`. -/
theorem consolidationMode_zero_right {u0 H cv t : ℝ} (hH : H ≠ 0) :
    consolidationMode u0 H cv t H = 0 := by
  rw [consolidationMode_eq hH]
  have harg : Real.pi * H / H = Real.pi := by
    field_simp
  rw [harg, Real.sin_pi, mul_zero]

/-- At `t = 0` the mode recovers the sine initial profile. -/
theorem consolidationMode_time_zero {u0 H cv z : ℝ} (hH : H ≠ 0) :
    consolidationMode u0 H cv 0 z = u0 * Real.sin (Real.pi * z / H) := by
  rw [consolidationMode_eq hH]
  simp

/-- At `t = 0` the mid-depth value is the full initial amplitude:
`H` is the full layer thickness, so the mode peaks at `H / 2`. -/
theorem consolidationMode_midpoint_time_zero {u0 H cv : ℝ} (hH : H ≠ 0) :
    consolidationMode u0 H cv 0 (H / 2) = u0 := by
  rw [consolidationMode_time_zero hH]
  have harg : Real.pi * (H / 2) / H = Real.pi / 2 := by
    field_simp
  rw [harg, Real.sin_pi_div_two, mul_one]

end EarthScience
