 /-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.EarthScience.K02ClimateFeedback

/-!
# Climate feedback and two-box response checks

Concrete consumers of `PhyslibExt.EarthScience.K02ClimateFeedback`:
scalar relaxation with `C = 1, F = 0, lambda = 1, T0 = 1`,
two-box equilibrium at `F = 2, lambda = 1`, the anomaly-energy
derivative for trivial anomalies, and the decay bound at
`xs = 1, xd = 0` with `Cs = Cd = lambda = gamma = 1`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Concrete checks

## iv. References

- `PhyslibExt.EarthScience.K02ClimateFeedback`
-/

/-- Scalar relaxation: `C = 1, F = 0, lambda = 1, T0 = 1` at `t = 0` gives `T(0) = 1`. -/
example :
    HasDerivAt (fun t => (0:ℝ) / 1 + (1 - (0:ℝ) / 1) * Real.exp (-(1:ℝ) * t / 1))
      (((0:ℝ) - 1 * ((0:ℝ) / 1 + (1 - (0:ℝ) / 1) * Real.exp (-(1:ℝ) * 0 / 1))) / 1) 0
    ∧ ((0:ℝ) / 1 + (1 - (0:ℝ) / 1) * Real.exp (-(1:ℝ) * 0 / 1) = 1) :=
  EarthScience.k02_scalar_relaxation (by norm_num) (by norm_num) 0

/-- Two-box equilibrium: `F = 2, lambda = 1, gamma = 3` gives `Ts = Td = 2`. -/
example : (2:ℝ) = (2:ℝ) / 1 ∧ (2:ℝ) = (2:ℝ) / 1 :=
  EarthScience.k02_two_box_equilibrium (gam := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Anomaly energy: trivial anomalies give derivative `0`. -/
example :
    HasDerivAt (fun (t : ℝ) => ((1:ℝ) * ((fun (_ : ℝ) => (0:ℝ)) t) ^ 2 + 1 * ((fun (_ : ℝ) => (0:ℝ)) t) ^ 2) / 2)
      (-(1:ℝ) * ((fun (_ : ℝ) => (0:ℝ)) 0) ^ 2 - 1 * ((fun (_ : ℝ) => (0:ℝ)) 0 - (fun (_ : ℝ) => (0:ℝ)) 0) ^ 2) 0 :=
  EarthScience.k02_anomaly_energy_hasDerivAt (Cs := 1) (Cd := 1) (lam := 1) (gam := 1)
    (xs := fun (_ : ℝ) => 0) (xd := fun (_ : ℝ) => 0) (by norm_num) (by norm_num) 0
    (by simpa using hasDerivAt_const (0:ℝ) (0:ℝ)) (by simpa using hasDerivAt_const (0:ℝ) (0:ℝ))

/-- Decay bound: at `xs = 1, xd = 0` with unit parameters, `-1 <= -c * 1/2` for `c = 1/3`. -/
example :
    0 < min (2 * (1:ℝ) / (1 + 2 * 1)) ((1:ℝ) / 1) ∧
    -(1:ℝ) * (1:ℝ) ^ 2 - 1 * ((1:ℝ) - 0) ^ 2
      ≤ -(min (2 * (1:ℝ) / (1 + 2 * 1)) ((1:ℝ) / 1)) * (1 * (1:ℝ) ^ 2 + 1 * (0:ℝ) ^ 2) / 2 :=
  EarthScience.k02_anomaly_energy_decay (by norm_num) (by norm_num) (by norm_num) (by norm_num)

