/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Basic.Real.Basic

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
/-!
# Positive heat capacity yields monotonic internal energy

In the restricted model `U(T) = U0 + C * (T - T0)` with constant heat
capacity `C > 0`, the internal energy is strictly increasing in `T` and
has derivative `C` at every `T`.

## i. Overview

Both facts are the affine structure: `C * (T - T0)` is strictly
increasing when `C > 0`, and its derivative is `C`. No claim is made
about temperature-dependent heat capacity, phase change, or work.

## ii. Key results

- `EarthScience.internalEnergy_strictMono`: `U` is strictly monotone in `T`.
- `EarthScience.internalEnergy_hasDerivAt`: `U` has derivative `C` at every `T`.

## iii. References

- `mul_lt_mul_of_pos_left`, `hasDerivAt_id`, `HasDerivAt.sub_const`,
  `HasDerivAt.const_mul`, `HasDerivAt.const_add` in Mathlib.
-/

@[expose] public section

namespace EarthScience

/-- In the restricted model `U(T) = U0 + C * (T - T0)` with heat capacity
`C > 0`, the internal energy is strictly increasing in `T`. -/
theorem internalEnergy_strictMono {C U0 T0 : ℝ} (hC : 0 < C) :
    StrictMono (fun T : ℝ => U0 + C * (T - T0)) := by
  intro a b hab
  have hsub : a - T0 < b - T0 := by linarith
  have hmul : C * (a - T0) < C * (b - T0) :=
    mul_lt_mul_of_pos_left hsub hC
  linarith

/-- The internal energy `U(T) = U0 + C * (T - T0)` has derivative `C` at every `T`. -/
theorem internalEnergy_hasDerivAt {C U0 T0 : ℝ} (T : ℝ) :
    HasDerivAt (fun T : ℝ => U0 + C * (T - T0)) C T := by
  have h1 : HasDerivAt (fun T : ℝ => T - T0) 1 T :=
    (hasDerivAt_id T).sub_const T0
  have h2 : HasDerivAt (fun T : ℝ => C * (T - T0)) (C * 1) T :=
    h1.const_mul C
  have h3 : HasDerivAt (fun T : ℝ => U0 + C * (T - T0)) (C * 1) T :=
    h2.const_add U0
  simpa using h3

end EarthScience
