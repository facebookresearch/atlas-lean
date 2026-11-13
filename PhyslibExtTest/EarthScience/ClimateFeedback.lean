/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.EarthScience.ClimateFeedback

/-!
# Climate feedback and two-box response checks

Concrete consumers of `PhyslibExt.EarthScience.ClimateFeedback`:
scalar relaxation with `C = 1, F = 0, lambda = 1, T0 = 1`,
two-box equilibrium at `F = 2, lambda = 1`, the anomaly-energy
derivative for trivial anomalies, the dissipation bound at
`xs = 1, xd = 0` with `Cs = Cd = lambda = gamma = 1` (where
`c = min (2/3) 1 = 2/3` and the bound reads `-2 <= -1/3`), the
energy decay `E' <= -(2/3)*E` along unit-parameter anomaly solutions,
and the exponential energy bound for an abstract anomaly solution with
arbitrary positive parameters.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Concrete checks

## iv. References

- `PhyslibExt.EarthScience.ClimateFeedback`
-/

/-- Scalar relaxation: `C = 1, F = 0, lambda = 1, T0 = 1` at `t = 0` gives `T(0) = 1`. -/
example :
    HasDerivAt (fun t => (0:ℝ) / 1 + (1 - (0:ℝ) / 1) * Real.exp (-(1:ℝ) * t / 1))
      (((0:ℝ) - 1 * ((0:ℝ) / 1 + (1 - (0:ℝ) / 1) * Real.exp (-(1:ℝ) * 0 / 1))) / 1) 0
    ∧ ((0:ℝ) / 1 + (1 - (0:ℝ) / 1) * Real.exp (-(1:ℝ) * 0 / 1) = 1) :=
  EarthScience.scalar_relaxation (by norm_num) (by norm_num) 0

/-- Two-box equilibrium: `F = 2, lambda = 1, gamma = 3` gives `Ts = Td = 2`. -/
example : (2:ℝ) = (2:ℝ) / 1 ∧ (2:ℝ) = (2:ℝ) / 1 :=
  EarthScience.two_box_equilibrium (gam := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Anomaly energy: trivial anomalies give derivative `0`. -/
example :
    HasDerivAt (fun (t : ℝ) => ((1:ℝ) * ((fun (_ : ℝ) => (0:ℝ)) t) ^ 2 + 1 * ((fun (_ : ℝ) => (0:ℝ)) t) ^ 2) / 2)
      (-(1:ℝ) * ((fun (_ : ℝ) => (0:ℝ)) 0) ^ 2 - 1 * ((fun (_ : ℝ) => (0:ℝ)) 0 - (fun (_ : ℝ) => (0:ℝ)) 0) ^ 2) 0 :=
  EarthScience.anomaly_energy_hasDerivAt (Cs := 1) (Cd := 1) (lam := 1) (gam := 1)
    (xs := fun (_ : ℝ) => 0) (xd := fun (_ : ℝ) => 0) (by norm_num) (by norm_num) 0
    (by simpa using hasDerivAt_const (0:ℝ) (0:ℝ)) (by simpa using hasDerivAt_const (0:ℝ) (0:ℝ))

/-- Dissipation bound: at `xs = 1, xd = 0` with unit parameters, `c = min (2/3) 1 = 2/3` and
the bound reads `-2 <= -(2/3) * 1 / 2 = -1/3`. -/
example :
    0 < min (2 * (1:ℝ) / (1 + 2 * 1)) ((1:ℝ) / 1) ∧
    -(1:ℝ) * (1:ℝ) ^ 2 - 1 * ((1:ℝ) - 0) ^ 2
      ≤ -(min (2 * (1:ℝ) / (1 + 2 * 1)) ((1:ℝ) / 1)) * (1 * (1:ℝ) ^ 2 + 1 * (0:ℝ) ^ 2) / 2 :=
  EarthScience.anomaly_energy_dissipation_bound (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- Normalized values of that check: `c = 2/3`, the dissipation is `-2`, and `-c * E = -1/3`. -/
example :
    min (2 * (1:ℝ) / (1 + 2 * 1)) ((1:ℝ) / 1) = 2 / 3 ∧
      -(1:ℝ) * (1:ℝ) ^ 2 - 1 * ((1:ℝ) - 0) ^ 2 = -2 ∧
      -(min (2 * (1:ℝ) / (1 + 2 * 1)) ((1:ℝ) / 1)) * (1 * (1:ℝ) ^ 2 + 1 * (0:ℝ) ^ 2) / 2
        = -1 / 3 := by
  norm_num [min_def]

/-- Energy decay along any unit-parameter anomaly solution: `E'(t) <= -(2/3) * E(t)`. -/
example (xs xd : ℝ → ℝ) (t : ℝ)
    (hxs : HasDerivAt xs ((-1 * xs t - 1 * (xs t - xd t)) / 1) t)
    (hxd : HasDerivAt xd ((1 * (xs t - xd t)) / 1) t) :
    deriv (fun t => (1 * (xs t) ^ 2 + 1 * (xd t) ^ 2) / 2) t ≤
      -(2 / 3) * ((1 * (xs t) ^ 2 + 1 * (xd t) ^ 2) / 2) := by
  have h := (EarthScience.anomaly_energy_decay (Cs := 1) (Cd := 1) (lam := 1) (gam := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) xs xd t hxs hxd).2
  have hc : min (2 * (1:ℝ) / (1 + 2 * 1)) ((1:ℝ) / 1) = 2 / 3 := by norm_num [min_def]
  rwa [hc] at h

/-- Exponential energy bound along any anomaly solution on `[0, ∞)`, for arbitrary positive
parameters: `E(t) <= exp(-c*t) * E(0)` for `t >= 0`. -/
example {Cs Cd lam gam : ℝ} (hCs : 0 < Cs) (hCd : 0 < Cd) (hlam : 0 < lam) (hgam : 0 < gam)
    (xs xd : ℝ → ℝ)
    (hxs : ∀ t, 0 ≤ t → HasDerivAt xs ((-lam * xs t - gam * (xs t - xd t)) / Cs) t)
    (hxd : ∀ t, 0 ≤ t → HasDerivAt xd ((gam * (xs t - xd t)) / Cd) t) (t : ℝ) (ht : 0 ≤ t) :
    (Cs * (xs t) ^ 2 + Cd * (xd t) ^ 2) / 2 ≤
      Real.exp (-(min (2 * lam / (Cs + 2 * Cd)) (gam / Cd)) * t) *
        ((Cs * (xs 0) ^ 2 + Cd * (xd 0) ^ 2) / 2) :=
  EarthScience.anomaly_energy_exp_bound hCs hCd hlam hgam xs xd hxs hxd ht
