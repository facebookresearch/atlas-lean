/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A positive admissible isochron slope inverts to an age

For decay constant `λ > 0` and admissible slope `m > 0`, the age
`log (1 + m) / λ` is nonnegative and its slope
`exp (λ * age) - 1` recovers `m`.

## i. Overview

This is the forward direction of the slope-age inversion: given an
admissible slope, the age built from it reproduces that slope
(`Real.exp_log` with `1 + m > 0`). The parent isochron theorem in
`PhyslibExt.EarthScience.Isochrons` proves the reverse direction,
from a slope built from two samples to its age; it does not state
this direction, in which the slope is taken as given.

## ii. Key results

- `EarthScience.isochron_age_inverts_slope`: the age from a
  positive slope inverts the slope-age relation, and is nonnegative.

## iii. References

- `Real.exp_log`, `Real.log_nonneg` (Mathlib).
-/

@[expose] public section

namespace EarthScience

/-- Invert a positive admissible slope to an age: for decay constant
`λ > 0` and admissible slope `m > 0`, the age `log (1 + m) / λ` is
nonnegative and its slope `exp (λ * age) - 1` recovers `m`. This is the
forward direction of the slope-age inversion (the parent isochron
theorem proves the reverse direction, from a slope built from samples
to its age). -/
theorem isochron_age_inverts_slope {lam m : ℝ} (hlam : 0 < lam) (hm : 0 < m) :
    Real.exp (lam * (Real.log (1 + m) / lam)) - 1 = m
      ∧ 0 ≤ Real.log (1 + m) / lam := by
  have hlam' : lam ≠ 0 := ne_of_gt hlam
  have h1m : (0 : ℝ) < 1 + m := by linarith
  have hmul : lam * (Real.log (1 + m) / lam) = Real.log (1 + m) := by
    field_simp
  constructor
  · rw [hmul, Real.exp_log h1m]
    ring
  · apply div_nonneg _ (le_of_lt hlam)
    apply Real.log_nonneg
    linarith

end EarthScience
