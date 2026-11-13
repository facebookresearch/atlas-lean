/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Surface gravity waves and wave energetics

A specified linear irrotational finite-depth wave ansatz satisfies the
dispersion relation `ω^2 = g k tanh (k H)`. The linearized free-surface
conditions give a kinematic relation `ω a = k tanh (kH) b` and a dynamic
relation `ω b = g a` between the surface amplitude `a` and the
velocity-potential amplitude `b`; eliminating `a` and `b` gives the
dispersion relation.

## i. Overview

For `g, k, H > 0`, `tanh (kH) > 0`, so the dispersion relation forces
`ω^2 > 0`. Deep and shallow limits are asymptotic only and are not proved
here; phase speed `ω / k` is distinct from group speed.

## ii. Key results

- `EarthScience.dispersion_from_surface_conditions`: the dispersion
  relation from the two surface conditions.
- `EarthScience.dispersion_positive`: `0 < ω^2` for `g, k, H > 0`.

## iii. Table of contents

- A. Dispersion from the surface conditions

## iv. References

- `Real.tanh_eq_sinh_div_cosh` in
  `Mathlib/Analysis/Complex/Trigonometric.lean`
  (Mathlib).

## A. Dispersion from the surface conditions
-/

@[expose] public section

namespace EarthScience

/-- Finite-depth surface-gravity-wave dispersion from the linearized
free-surface conditions. For a wave of (nonzero) surface amplitude `a`,
frequency `ω`, wavenumber `k`, depth `H`, the kinematic condition
`ω a = k tanh (kH) b` and the dynamic condition `ω b = g a` (with `b` the
velocity-potential amplitude) eliminate `a, b` and give
`ω² = g k tanh (kH)`. -/
theorem dispersion_from_surface_conditions (ω g k H a b : ℝ) (ha : a ≠ 0)
    (hkin : ω * a = k * Real.tanh (k * H) * b)
    (hdyn : ω * b = g * a) :
    ω ^ 2 = g * k * Real.tanh (k * H) := by
  have h1 : ω * (ω * a) = ω * (k * Real.tanh (k * H) * b) := by rw [hkin]
  have h2 : ω * (ω * a) = ω ^ 2 * a := by ring
  have h3 : ω * (k * Real.tanh (k * H) * b)
      = (g * k * Real.tanh (k * H)) * a := by
    calc ω * (k * Real.tanh (k * H) * b)
        = k * Real.tanh (k * H) * (ω * b) := by ring
      _ = k * Real.tanh (k * H) * (g * a) := by rw [hdyn]
      _ = (g * k * Real.tanh (k * H)) * a := by ring
  have h4 : ω ^ 2 * a = (g * k * Real.tanh (k * H)) * a := by
    rw [← h2, h1, h3]
  exact mul_right_cancel₀ ha h4

/-- The dispersion relation forces a positive `ω²` for `g, k, H > 0`,
and hence `ω ≠ 0`: with the same surface conditions, `0 < ω ^ 2`. -/
theorem dispersion_positive (ω g k H a b : ℝ) (hg : 0 < g) (hk : 0 < k)
    (hH : 0 < H) (ha : a ≠ 0)
    (hkin : ω * a = k * Real.tanh (k * H) * b)
    (hdyn : ω * b = g * a) :
    0 < ω ^ 2 := by
  have hdisp := dispersion_from_surface_conditions ω g k H a b ha hkin hdyn
  rw [hdisp]
  have hkH : 0 < k * H := mul_pos hk hH
  have htanh : 0 < Real.tanh (k * H) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hkH) (Real.cosh_pos _)
  exact mul_pos (mul_pos hg hk) htanh

end EarthScience
