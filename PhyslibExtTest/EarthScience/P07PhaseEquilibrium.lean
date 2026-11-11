/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.EarthScience.P07PhaseEquilibrium

/-!
# Clapeyron checks

Concrete consumers of `PhyslibExt.EarthScience.P07PhaseEquilibrium`:
the public shape of the Clapeyron theorem, the latent-heat form at
`T = 300` with `s2 - s1 = 10`, `v2 - v1 = 2` (so `dp / dT = 5`), and
the equal-entropy boundary `s2 = s1`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Clapeyron shape
- B. Latent-heat form and equal-entropy boundary

## iv. References

- `PhyslibExt.EarthScience.P07PhaseEquilibrium`
-/

/-- Public shape of the Clapeyron theorem. -/
example {mu1 mu2 : ℝ → ℝ} {v1 v2 s1 s2 dp dT : ℝ} {t : ℝ}
    (hv : v2 - v1 ≠ 0) (hdT : dT ≠ 0)
    (hmu1 : HasDerivAt mu1 (v1 * dp - s1 * dT) t)
    (hmu2 : HasDerivAt mu2 (v2 * dp - s2 * dT) t)
    (heq : HasDerivAt (fun t => mu1 t - mu2 t) 0 t) :
    dp / dT = (s2 - s1) / (v2 - v1) :=
  EarthScience.clapeyron_dp_dT hv hdT hmu1 hmu2 heq

/-- Latent-heat form, numeric: `10 / 2 = 300 * 10 / (300 * 2) = 5`. -/
example : (12 - 2 : ℝ) / (3 - 1) = (300 * (12 - 2)) / (300 * (3 - 1)) :=
  EarthScience.clapeyron_latentHeat_form (T := 300) (s1 := 2) (s2 := 12) (v1 := 1) (v2 := 3) (by norm_num)

/-- Equal-entropy boundary: `s2 = s1` gives `dp / dT = 0` in latent-heat form. -/
example : ((5 : ℝ) - 5) / (3 - 1) = (300 * ((5 : ℝ) - 5)) / (300 * (3 - 1)) :=
  EarthScience.clapeyron_latentHeat_form (T := 300) (s1 := 5) (s2 := 5) (v1 := 1) (v2 := 3) (by norm_num)
