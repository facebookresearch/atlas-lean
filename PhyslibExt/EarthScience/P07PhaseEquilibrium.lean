/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Clapeyron relation along a coexistence curve

## i. Overview

Along a `C1` coexistence curve with chemical potentials `μ1 = μ2`
and `dμᵢ = vᵢ dp - sᵢ dT`, the Clapeyron relation is
`dp / dT = (s2 - s1) / (v2 - v1)` when `v2 ≠ v1`. The curve's existence
is hypothesised through the derivative data, not derived here.
`T` is absolute, `v`, `s` consistently molar or mass-specific, and the
critical point (where `v2 = v1`) is excluded. The latent-heat form
`dp / dT = L / (T * (v2 - v1))` with `L = T * (s2 - s1)` is also recorded.

## ii. Key results

- `EarthScience.clapeyron_dp_dT`: `dp / dT = (s2 - s1) / (v2 - v1)`.
- `EarthScience.clapeyron_latentHeat_form`: the latent-heat form.

## iii. Table of contents

- A. Clapeyron relation
- B. Latent-heat form

## iv. References

- `HasDerivAt.sub` / `HasDerivAt.unique` in Mathlib.
-/

@[expose] public section

namespace EarthScience

/-- Clapeyron relation along a coexistence curve: with
`dμᵢ = vᵢ dp - sᵢ dT`, equal chemical potentials along the curve
(`μ1 - μ2` has derivative `0`), `dp/dT = (s2 - s1) / (v2 - v1)`
when `v2 ≠ v1` and `dT ≠ 0`. Here `dp`, `dT` are the derivatives of
the pressure and temperature along the curve at the point. -/
theorem clapeyron_dp_dT {mu1 mu2 : ℝ → ℝ} {v1 v2 s1 s2 dp dT : ℝ} {t : ℝ}
    (hv : v2 - v1 ≠ 0) (hdT : dT ≠ 0)
    (hmu1 : HasDerivAt mu1 (v1 * dp - s1 * dT) t)
    (hmu2 : HasDerivAt mu2 (v2 * dp - s2 * dT) t)
    (heq : HasDerivAt (fun t => mu1 t - mu2 t) 0 t) :
    dp / dT = (s2 - s1) / (v2 - v1) := by
  have hsub := hmu1.sub hmu2
  have heq' : HasDerivAt (mu1 - mu2) 0 t := heq
  have hzero := hsub.unique heq'
  have hlin : dp * (v2 - v1) = (s2 - s1) * dT := by linear_combination -hzero
  rw [div_eq_div_iff hdT hv]
  exact hlin

/-- Latent-heat form: with `L = T * (s2 - s1)` and `T ≠ 0`,
`(s2 - s1) / (v2 - v1) = L / (T * (v2 - v1))`. -/
theorem clapeyron_latentHeat_form {s1 s2 v1 v2 T : ℝ} (hT : T ≠ 0) :
    (s2 - s1) / (v2 - v1) = (T * (s2 - s1)) / (T * (v2 - v1)) := by
  exact (mul_div_mul_left _ _ hT).symm

end EarthScience
