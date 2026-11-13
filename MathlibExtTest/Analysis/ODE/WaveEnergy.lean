/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.ODE.WaveEnergy

open MeasureTheory intervalIntegral

/-!
# Wave-mode energy checks

Concrete consumers of `MathlibExt.Analysis.ODE.WaveEnergy`: the wave
equation at a numeric point, zero boundary flux at a numeric time, the
energy at two distinct times (both equal to `c² * π / 4`), and the
degenerate zero-speed boundary case `c = 0`, where the mode is constant
and the energy is `0`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Wave equation and boundary flux at a numeric point
- B. Energy at two times and conservation
- C. Zero speed

## iv. References

- `MathlibExt.Analysis.ODE.WaveEnergy`
-/

/-- Wave equation at `c = 2, t = 0.5, x = 1`: both sides are
`-4 * cos 1 * cos 1`. -/
example :
    iteratedDeriv 2 (fun t => Real.cos (2 * t) * Real.cos (1 : ℝ)) (0.5 : ℝ)
      = (2 : ℝ) ^ 2 * iteratedDeriv 2 (fun x => Real.cos (2 * (0.5 : ℝ)) * Real.cos x) (1 : ℝ) :=
  EarthScience.wave_mode_satisfies_wave_eq 2 0.5 1

/-- Zero boundary flux at `c = 2, t = 0.5`. -/
example :
    deriv (fun x => Real.cos (2 * (0.5 : ℝ)) * Real.cos x) 0 = 0 ∧
    deriv (fun x => Real.cos (2 * (0.5 : ℝ)) * Real.cos x) Real.pi = 0 :=
  EarthScience.wave_mode_neumann_boundary 2 0.5

/-- Energy at `c = 2, t = 0.5` and at `c = 2, t = 1.7` is `π` in both
cases, so the energy is conserved between them. -/
example :
    (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..Real.pi,
        (deriv (fun t => Real.cos (2 * t) * Real.cos x) (0.5 : ℝ)) ^ 2
          + (2 : ℝ) ^ 2 * (deriv (fun x => Real.cos (2 * (0.5 : ℝ)) * Real.cos x) x) ^ 2
      = Real.pi ∧
    (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..Real.pi,
        (deriv (fun t => Real.cos (2 * t) * Real.cos x) (1.7 : ℝ)) ^ 2
          + (2 : ℝ) ^ 2 * (deriv (fun x => Real.cos (2 * (1.7 : ℝ)) * Real.cos x) x) ^ 2
      = Real.pi := by
  have e1 := EarthScience.wave_mode_energy 2 (0.5 : ℝ)
  have e2 := EarthScience.wave_mode_energy 2 (1.7 : ℝ)
  refine ⟨?_, ?_⟩
  · rw [e1]; norm_num
  · rw [e2]; norm_num

/-- Zero speed: the mode is constant in time, the energy is `0`, and
conservation is trivial. -/
example :
    (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..Real.pi,
        (deriv (fun t => Real.cos (0 * t) * Real.cos x) (0.5 : ℝ)) ^ 2
          + (0 : ℝ) ^ 2 * (deriv (fun x => Real.cos (0 * (0.5 : ℝ)) * Real.cos x) x) ^ 2
      = 0 := by
  have e := EarthScience.wave_mode_energy 0 (0.5 : ℝ)
  rw [e]; norm_num
