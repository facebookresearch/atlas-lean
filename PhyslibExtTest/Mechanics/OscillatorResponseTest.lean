/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Mechanics.OscillatorResponse

/-!
# Oscillator parameter correspondence checks

Concrete consumers of `PhyslibExt.Mechanics.OscillatorResponse`: the critically damped
mass-spring-damper `m = 1`, `c = 2`, `k = 1` with initial data `x₀ = v₀ = 1`, and the boundary
cases of the parameter map.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Critical damping and conventions

## iv. References

None.

## A. Critical damping and conventions

-/

open ClassicalMechanics Time ContDiff PhyslibExt.Mechanics.OscillatorResponse

/-- Critical damping with nonzero initial data: `m = 1`, `c = 2`, `k = 1` (`c ^ 2 = 4 m k`),
`x₀ = v₀ = 1`. Both conventions give the rate `1`, and the free trajectory is
`exp (-t) (1 + 2 t)`. -/
example :
    (massSpringDamper 1 2 1 one_pos zero_le_two one_pos).IsCriticallyDamped ∧
      atlasDamping 1 2 = 1 ∧ atlasNaturalFrequency 1 1 = 1 ∧
      ∀ t : Time, (massSpringDamper 1 2 1 one_pos zero_le_two one_pos).trajectory
          (initialConditions 1 1) t =
        Real.exp (-(t : ℝ)) • EuclideanSpace.single 0 (1 + 2 * (t : ℝ)) := by
  set S := massSpringDamper 1 2 1 one_pos zero_le_two one_pos
  have hcrit : S.IsCriticallyDamped := by
    change (2 : ℝ) ^ 2 - 4 * 1 * 1 = 0
    norm_num
  refine ⟨hcrit, by norm_num [atlasDamping], by norm_num [atlasNaturalFrequency], fun t => ?_⟩
  rw [S.trajectory_eq_of_criticallyDamped _ hcrit]
  have hd : S.decayRate = 1 := by
    change (2 : ℝ) / (2 * 1) = 1
    norm_num
  simp only [DampedHarmonicOscillator.criticallyDampedBase, initialConditions, hd]
  ext i
  fin_cases i
  simp
  ring

/-- Boundary cases: no Physlib oscillator has `k = 0`; for `m = 1`, `c = 2` the Physlib damping
coefficient is `2` while the convention's damping rate is `1` (the factor `2 m`); a force
amplitude `4` on mass `2` is the acceleration amplitude `2`. -/
example :
    (¬ ∃ S : DampedHarmonicOscillator, S.k = 0) ∧
      (massSpringDamper 1 2 1 one_pos zero_le_two one_pos).γ = 2 ∧ atlasDamping 1 2 = 1 ∧
      atlasForcing 2 4 = 2 := by
  exact ⟨fun ⟨S, hS⟩ => S.k_ne_zero hS, rfl, by norm_num [atlasDamping],
    by norm_num [atlasForcing]⟩
