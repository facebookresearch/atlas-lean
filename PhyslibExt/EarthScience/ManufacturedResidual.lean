/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Manufactured-solution residual order

The method of manufactured solutions checks a discrete scheme against a
chosen exact solution. For the manufactured solution `u(x) = x⁴`, whose
exact second derivative is `u''(x) = 12 x²`, the central second difference
`D²u(x) = (u(x + h) - 2 u(x) + u(x - h)) / h²` satisfies
`D²u(x) = 12 x² + 2 h²`. The residual is therefore exactly `2 h²`:
second order in `h`, with explicit constant `2`.

## i. Overview

Expanding `(x + h)⁴ - 2 x⁴ + (x - h)⁴ = 12 x² h² + 2 h⁴` and dividing by
`h²` gives the difference quotient; subtracting the exact derivative gives
the residual, and the absolute bound follows from nonnegativity of `2 h²`.

## ii. Key results

- `EarthScience.manufactured_central_second_diff`: the difference quotient.
- `EarthScience.manufactured_central_second_diff_residual`: the residual
  is exactly `2 h²`.
- `EarthScience.manufactured_central_second_diff_residual_le`: the
  residual order bound `|residual| ≤ 2 h²`.

## iii. Table of contents

- A. Central second difference on the manufactured solution

## iv. References

- `div_eq_iff`, `pow_ne_zero` in Mathlib.

## A. Central second difference on the manufactured solution
-/

@[expose] public section

namespace EarthScience

/-- Manufactured solution `u(x) = x⁴` for the central second difference:
the difference quotient equals `12 x² + 2 h²`. -/
theorem manufactured_central_second_diff {x h : ℝ} (hh : h ≠ 0) :
    ((x + h) ^ 4 - 2 * x ^ 4 + (x - h) ^ 4) / h ^ 2 = 12 * x ^ 2 + 2 * h ^ 2 := by
  have h2 : h ^ 2 ≠ 0 := pow_ne_zero 2 hh
  rw [div_eq_iff h2]
  ring

/-- Residual of the central second difference on the manufactured solution
`u(x) = x⁴`: the residual `D²u - u''(x)` is exactly `2 h²`, i.e. second
order in `h`. -/
theorem manufactured_central_second_diff_residual {x h : ℝ} (hh : h ≠ 0) :
    ((x + h) ^ 4 - 2 * x ^ 4 + (x - h) ^ 4) / h ^ 2 - 12 * x ^ 2 = 2 * h ^ 2 := by
  rw [manufactured_central_second_diff hh]
  ring

/-- Residual order bound: `|D²u - u''(x)| ≤ 2 h²` for the manufactured
solution `u(x) = x⁴`. -/
theorem manufactured_central_second_diff_residual_le {x h : ℝ} (hh : h ≠ 0) :
    |((x + h) ^ 4 - 2 * x ^ 4 + (x - h) ^ 4) / h ^ 2 - 12 * x ^ 2| ≤ 2 * h ^ 2 := by
  rw [manufactured_central_second_diff_residual hh]
  have hnn : 0 ≤ 2 * h ^ 2 := by positivity
  rw [abs_of_nonneg hnn]

end EarthScience
