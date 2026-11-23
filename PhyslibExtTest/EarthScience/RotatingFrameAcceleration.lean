/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.RotatingFrameAcceleration
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

open scoped Matrix

/-!
# Rotating-frame acceleration checks

Concrete consumers of
`PhyslibExt.EarthScience.RotatingFrameAcceleration`: the decomposition
with `Ω = (0, 0, 1)`, `v = (1, 0, 0)`, `a = (0, 1, 0)`, `r = (1, 1, 0)`,
where both sides are `(-1, 2, 0)`, the derivative version applied to
abstract position/velocity data, and the derivative version on uniform
rotating-frame motion, where the inertial acceleration given by the frame
transport law is `(-1, 1, 0)`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Decomposition with numbers
- B. Decomposition with derivatives, abstract and concrete data

## iv. References

- `PhyslibExt.EarthScience.RotatingFrameAcceleration`
-/

/-- Decomposition with numbers: both sides equal `(-1, 2, 0)`. -/
example : (![0, 1, 0] : Fin 3 → ℝ) + ![0, 0, 1] ⨯₃ ![1, 0, 0] +
      ![0, 0, 1] ⨯₃ (![1, 0, 0] + ![0, 0, 1] ⨯₃ ![1, 1, 0]) =
    (![0, 1, 0] : Fin 3 → ℝ) + 2 • (![0, 0, 1] ⨯₃ ![1, 0, 0]) +
      ![0, 0, 1] ⨯₃ (![0, 0, 1] ⨯₃ ![1, 1, 0]) := by
  have h := EarthScience.rotating_acceleration_decomposition
    ![0, 0, 1] ![1, 0, 0] ![0, 1, 0] ![1, 1, 0]
  exact h

/-- The left side of the numeric instance evaluates to `(-1, 2, 0)`. -/
example : (![0, 1, 0] : Fin 3 → ℝ) + ![0, 0, 1] ⨯₃ ![1, 0, 0] +
      ![0, 0, 1] ⨯₃ (![1, 0, 0] + ![0, 0, 1] ⨯₃ ![1, 1, 0]) = ![-1, 2, 0] := by
  ext i
  fin_cases i <;> norm_num [cross_apply]

/-- The right side evaluates to `(-1, 2, 0)`: rotating-frame acceleration
`(0, 1, 0)`, Coriolis term `2 • (0, 1, 0)`, centripetal term `(-1, -1, 0)`. -/
example : (![0, 1, 0] : Fin 3 → ℝ) + 2 • (![0, 0, 1] ⨯₃ ![1, 0, 0]) +
      ![0, 0, 1] ⨯₃ (![0, 0, 1] ⨯₃ ![1, 1, 0]) = ![-1, 2, 0] := by
  ext i
  fin_cases i <;> simp [cross_apply]

/-- The centripetal term points toward the rotation axis: for `Ω = (0, 0, 1)`
and `r = (1, 1, 0)`, `Ω × (Ω × r) = (-1, -1, 0)`. -/
example : (![0, 0, 1] : Fin 3 → ℝ) ⨯₃ (![0, 0, 1] ⨯₃ ![1, 1, 0]) = ![-1, -1, 0] := by
  ext i
  fin_cases i <;> simp [cross_apply]

/-- Derivative version applied to abstract data: the inertial acceleration
given by the frame transport law decomposes. -/
example (Ω : Fin 3 → ℝ) (r v : ℝ → Fin 3 → ℝ) (a aInertial : Fin 3 → ℝ) (t : ℝ)
    (hr : HasDerivAt (fun t : ℝ => r t) (v t) t)
    (hv : HasDerivAt (fun t : ℝ => v t) a t)
    (htransport : aInertial =
      deriv (fun t : ℝ => v t + Ω ⨯₃ r t) t + Ω ⨯₃ (v t + Ω ⨯₃ r t)) :
    HasDerivAt (fun t : ℝ => v t + Ω ⨯₃ r t) (a + Ω ⨯₃ v t) t ∧
      aInertial = a + 2 • (Ω ⨯₃ v t) + Ω ⨯₃ (Ω ⨯₃ r t) :=
  EarthScience.rotating_acceleration_hasDerivAt Ω r v a aInertial t hr hv htransport

/-- Derivative version on a concrete trajectory: uniform rotating-frame motion
`r t = t • (1, 0, 0) + (1, 1, 0)` with `Ω = (0, 0, 1)`, so `v = (1, 0, 0)` and
`a = 0`. The inertial acceleration at `t = 0` given by the frame transport law
is `2 • (Ω × v) + Ω × (Ω × r) = (0, 2, 0) + (-1, -1, 0) = (-1, 1, 0)`. -/
example :
    deriv (fun t : ℝ => (![1, 0, 0] : Fin 3 → ℝ) +
        ![0, 0, 1] ⨯₃ (t • ![1, 0, 0] + ![1, 1, 0])) 0 +
      ![0, 0, 1] ⨯₃ ((![1, 0, 0] : Fin 3 → ℝ) +
        ![0, 0, 1] ⨯₃ ((0 : ℝ) • ![1, 0, 0] + ![1, 1, 0])) = ![-1, 1, 0] := by
  have hr : HasDerivAt (fun t : ℝ => t • (![1, 0, 0] : Fin 3 → ℝ) + ![1, 1, 0])
      ![1, 0, 0] 0 := by
    simpa only [one_smul] using
      ((hasDerivAt_id' (x := (0 : ℝ))).smul_const (![1, 0, 0] : Fin 3 → ℝ)).add_const
        (![1, 1, 0] : Fin 3 → ℝ)
  refine Eq.trans (EarthScience.rotating_acceleration_hasDerivAt ![0, 0, 1]
    (fun t => t • ![1, 0, 0] + ![1, 1, 0]) (fun _ => ![1, 0, 0]) 0 _ 0 hr
    (hasDerivAt_const 0 _) rfl).2 ?_
  ext i
  fin_cases i <;> norm_num [cross_apply]
