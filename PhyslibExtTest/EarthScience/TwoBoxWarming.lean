/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.TwoBoxWarming

/-!
# Two-box warming capstone checks

Concrete consumers of `PhyslibExt.EarthScience.TwoBoxWarming`:
equilibrium `(1, 1)`, the combined budget and energy identities at
`Ts = Td = 0` (where `Ts' = 1, Td' = 0, E = 1, E' = -1`),
`E 0 = 1`, and the exponential energy bound for an abstract solution.

## i. Overview

These are elaboration and non-vacuity checks, not new results. The
exponential bound is applied through the public API to an arbitrary
solution of the two-box ODE; no closed-form solution is introduced.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Equilibrium, budget, energy
- B. Initial energy
- C. Exponential energy bound

## iv. References

- `PhyslibExt.EarthScience.TwoBoxWarming`
-/

/-- Equilibrium `(1, 1)`. -/
example : (1 : ℝ) - 1 - (1 - 1) = 0 ∧ (1 : ℝ) - 1 = 0 :=
  EarthScience.two_box_warming_equilibrium

/-- Combined budget at `Ts = Td = 0`: `Ts' + Td' = 1 - Ts` with `Ts' = 1, Td' = 0`. -/
example : (1 : ℝ) + 0 = 1 - 0 :=
  EarthScience.two_box_combined_budget (Ts := 0) (Td := 0) (Ts' := 1) (Td' := 0)
    (by norm_num) (by norm_num)

/-- Energy derivative at `Ts = Td = 0`: `E' = -1`. -/
example : (0 - 1 : ℝ) * 1 + (0 - 1) * 0
    = -((0 - 1 : ℝ) ^ 2 + (0 - 0 : ℝ) ^ 2) :=
  EarthScience.two_box_energy_derivative (Ts := 0) (Td := 0) (Ts' := 1) (Td' := 0)
    (by norm_num) (by norm_num)

/-- Differential inequality at `Ts = Td = 0`: `-1 ≤ -(2 / 3) * 1`. -/
example : (0 - 1 : ℝ) * 1 + (0 - 1) * 0
    ≤ -(2 / 3) * (((0 - 1 : ℝ) ^ 2 + (0 - 1 : ℝ) ^ 2) / 2) :=
  EarthScience.two_box_energy_differential_inequality (Ts := 0) (Td := 0)
    (Ts' := 1) (Td' := 0) (by norm_num) (by norm_num)

/-- Initial energy `E 0 = 1` at `Ts = Td = 0`. -/
example : ((0 - 1 : ℝ) ^ 2 + (0 - 1 : ℝ) ^ 2) / 2 = 1 := by norm_num

/-- Exponential energy bound for any solution of the two-box ODE from
`Ts 0 = Td 0 = 0`, at any `t ≥ 0`. -/
example {Ts Td : ℝ → ℝ}
    (hODE : ∀ t : ℝ, HasDerivAt Ts (1 - Ts t - (Ts t - Td t)) t ∧
      HasDerivAt Td (Ts t - Td t) t)
    (hTs0 : Ts 0 = 0) (hTd0 : Td 0 = 0) (t : ℝ) (ht : 0 ≤ t) :
    ((Ts t - 1) ^ 2 + (Td t - 1) ^ 2) / 2 ≤ Real.exp (-(2 / 3) * t) :=
  EarthScience.two_box_energy_bound hODE hTs0 hTd0 t ht
