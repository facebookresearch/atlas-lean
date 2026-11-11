/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
/-!
# Streeter-Phelps river oxygen deficit

`L` is the oxygen demand and `D` the oxygen deficit, in the same
concentration unit, with rates inverse time. `L' = -kd*L` and
`D' = kd*L - ka*D` have the closed-form solutions below, with a separate
proved branch for equal rates.

## i. Overview

Fixed temperature/saturation and plug-flow travel time; no
photosynthesis or sediment demand unless explicitly added. The
unequal-rate branch requires `ka ≠ kd`; the equal-rate branch sets
`ka = kd = k > 0` explicitly and is a separate proved branch, not a
limit argument and not excluded permanently.

## ii. Key results

- `EarthScience.bod_decay_hasDerivAt`: `L(t) = L0*exp(-kd*t)` solves `L' = -kd*L`.
- `EarthScience.oxygen_deficit_hasDerivAt`: the unequal-rate deficit
  solution solves `D' = kd*L - ka*D`.
- `EarthScience.oxygen_deficit_equalRate_hasDerivAt`: the equal-rate
  deficit solution solves `D' = k*L - k*D`.

## iii. References

- `Real.hasDerivAt_exp` in `Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean`.
-/

@[expose] public section

namespace EarthScience

/-- Streeter-Phelps BOD: with `L' = -kd*L`, `L(t) = L0*exp(-kd*t)` solves it. -/
theorem bod_decay_hasDerivAt (kd L0 t : ℝ) :
    HasDerivAt (fun t => L0 * Real.exp (-kd * t))
      (-kd * (L0 * Real.exp (-kd * t))) t := by
  have hid : HasDerivAt (fun t : ℝ => t) 1 t := hasDerivAt_id t
  have hlin : HasDerivAt (fun t : ℝ => -kd * t) (-kd * 1) t := hid.const_mul (-kd)
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-kd * t))
      (Real.exp (-kd * t) * (-kd * 1)) t := hlin.exp
  have hmul : HasDerivAt (fun t : ℝ => L0 * Real.exp (-kd * t))
      (L0 * (Real.exp (-kd * t) * (-kd * 1))) t := hexp.const_mul L0
  convert hmul using 1
  ring

set_option linter.unusedVariables false in
/-- Streeter-Phelps oxygen deficit, unequal rates (`ka ≠ kd`):
`D(t) = D0*exp(-ka*t) + kd*L0*(exp(-kd*t)-exp(-ka*t))/(ka-kd)`
solves `D' = kd*L - ka*D`. -/
theorem oxygen_deficit_hasDerivAt (ka kd L0 D0 t : ℝ)
    (hka : 0 < ka) (hkd : 0 < kd) (hne : ka ≠ kd) :
    HasDerivAt (fun t => D0 * Real.exp (-ka * t) +
        kd * L0 * (Real.exp (-kd * t) - Real.exp (-ka * t)) / (ka - kd))
      (kd * (L0 * Real.exp (-kd * t)) -
        ka * (D0 * Real.exp (-ka * t) +
        kd * L0 * (Real.exp (-kd * t) - Real.exp (-ka * t)) / (ka - kd))) t := by
  have hid : HasDerivAt (fun t : ℝ => t) 1 t := hasDerivAt_id t
  have hlin_a : HasDerivAt (fun t : ℝ => -ka * t) (-ka * 1) t := hid.const_mul (-ka)
  have hlin_d : HasDerivAt (fun t : ℝ => -kd * t) (-kd * 1) t := hid.const_mul (-kd)
  have hexp_a : HasDerivAt (fun t : ℝ => Real.exp (-ka * t))
      (Real.exp (-ka * t) * (-ka * 1)) t := hlin_a.exp
  have hexp_d : HasDerivAt (fun t : ℝ => Real.exp (-kd * t))
      (Real.exp (-kd * t) * (-kd * 1)) t := hlin_d.exp
  have h1 : HasDerivAt (fun t : ℝ => D0 * Real.exp (-ka * t))
      (D0 * (Real.exp (-ka * t) * (-ka * 1))) t := hexp_a.const_mul D0
  have hsub : HasDerivAt (fun t : ℝ => Real.exp (-kd * t) - Real.exp (-ka * t))
      ((Real.exp (-kd * t) * (-kd * 1)) - (Real.exp (-ka * t) * (-ka * 1))) t :=
    hexp_d.sub hexp_a
  have hmul : HasDerivAt (fun t : ℝ => kd * L0 * (Real.exp (-kd * t) - Real.exp (-ka * t)))
      ((kd * L0) * ((Real.exp (-kd * t) * (-kd * 1)) - (Real.exp (-ka * t) * (-ka * 1)))) t :=
    hsub.const_mul (kd * L0)
  have hdiv : HasDerivAt
      (fun t : ℝ => kd * L0 * (Real.exp (-kd * t) - Real.exp (-ka * t)) / (ka - kd))
      (((kd * L0) * ((Real.exp (-kd * t) * (-kd * 1)) - (Real.exp (-ka * t) * (-ka * 1)))) /
        (ka - kd)) t :=
    hmul.div_const (ka - kd)
  have hsum : HasDerivAt (fun t : ℝ => D0 * Real.exp (-ka * t) +
        kd * L0 * (Real.exp (-kd * t) - Real.exp (-ka * t)) / (ka - kd))
      ((D0 * (Real.exp (-ka * t) * (-ka * 1))) +
        (((kd * L0) * ((Real.exp (-kd * t) * (-kd * 1)) - (Real.exp (-ka * t) * (-ka * 1)))) /
          (ka - kd))) t :=
    h1.add hdiv
  have hne' : ka - kd ≠ 0 := sub_ne_zero.mpr hne
  convert hsum using 1
  field_simp
  ring

set_option linter.unusedVariables false in
/-- Streeter-Phelps oxygen deficit, equal rates (`ka = kd = k`):
`D(t) = (D0 + k*L0*t)*exp(-k*t)` solves `D' = k*L - k*D`
with `L(t) = L0*exp(-k*t)`. -/
theorem oxygen_deficit_equalRate_hasDerivAt (k L0 D0 t : ℝ) (hk : 0 < k) :
    HasDerivAt (fun t => (D0 + k * L0 * t) * Real.exp (-k * t))
      (k * (L0 * Real.exp (-k * t)) -
        k * ((D0 + k * L0 * t) * Real.exp (-k * t))) t := by
  have hid : HasDerivAt (fun t : ℝ => t) 1 t := hasDerivAt_id t
  have hlin : HasDerivAt (fun t : ℝ => k * L0 * t) ((k * L0) * 1) t :=
    hid.const_mul (k * L0)
  have hadd : HasDerivAt (fun t : ℝ => D0 + k * L0 * t) ((k * L0) * 1) t :=
    hlin.const_add D0
  have hexplin : HasDerivAt (fun t : ℝ => -k * t) (-k * 1) t := hid.const_mul (-k)
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-k * t))
      (Real.exp (-k * t) * (-k * 1)) t := hexplin.exp
  have hmul : HasDerivAt (fun t : ℝ => (D0 + k * L0 * t) * Real.exp (-k * t))
      (((k * L0) * 1) * Real.exp (-k * t) + (D0 + k * L0 * t) * (Real.exp (-k * t) * (-k * 1))) t :=
    hadd.mul hexp
  convert hmul using 1
  ring

end EarthScience
