/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.ConservativeAdvectiveForms
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Conservative/advective form checks

Concrete consumers of
`PhyslibExt.EarthScience.ConservativeAdvectiveForms`: with constant
carrier velocity `U = 3` (so `U_x = 0`), concentration `c(x) = x ^ 2`,
and diffusivity `D = 1 / 2`, the flux divergence and the advective
operator at `x = 2` are both `11`; without continuity the forms
differ (`U(x) = x`, `c(x) = x ^ 2` at `x = 2` gives `12` versus `8`).

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Constant-velocity agreement and the no-continuity counterexample

## iv. References

- `PhyslibExt.EarthScience.ConservativeAdvectiveForms`
-/

/-- Derivative of `y ^ 2` at every `x`: `2 * x`. -/
example : ∀ x : ℝ, deriv (fun y : ℝ => y ^ 2) x = 2 * x := fun x => by
  rw [(hasDerivAt_pow 2 x).deriv]
  ring

/-- First derivative `c'(2) = 4` for `c(x) = x ^ 2`. -/
example : deriv (fun x : ℝ => x ^ 2) 2 = 4 := by
  rw [(hasDerivAt_pow 2 (2 : ℝ)).deriv]
  norm_num

/-- Second derivative `(c')'(2) = 2` for `c(x) = x ^ 2`. -/
example : deriv (fun x : ℝ => deriv (fun y : ℝ => y ^ 2) x) 2 = 2 := by
  have hfun : (fun x : ℝ => deriv (fun y : ℝ => y ^ 2) x) = fun x => 2 * x := by
    funext x
    rw [(hasDerivAt_pow 2 x).deriv]
    ring
  rw [hfun]
  simp

/-- Constant velocity `U = 3`, `c(x) = x ^ 2`, `D = 1 / 2` at `x = 2`:
the flux divergence is `11`. -/
example : deriv (fun x : ℝ => 3 * x ^ 2 - (1 / 2) * deriv (fun y : ℝ => y ^ 2) x)
    2 = 11 := by
  have hc1 : HasDerivAt (fun x : ℝ => x ^ 2) (deriv (fun x : ℝ => x ^ 2) 2) 2 :=
    ((hasDerivAt_pow 2 (2 : ℝ)).differentiableAt).hasDerivAt
  have hc2 : HasDerivAt (fun x : ℝ => deriv (fun y : ℝ => y ^ 2) x)
      (deriv (fun x : ℝ => deriv (fun y : ℝ => y ^ 2) x) 2) 2 := by
    have hfun : (fun x : ℝ => deriv (fun y : ℝ => y ^ 2) x) = fun x => 2 * x := by
      funext x
      rw [(hasDerivAt_pow 2 x).deriv]
      ring
    have hdiff : DifferentiableAt ℝ (fun x : ℝ => deriv (fun y : ℝ => y ^ 2) x) 2 := by
      rw [hfun]
      simpa using (differentiableAt_id (x := (2 : ℝ))).const_mul (2 : ℝ)
    exact hdiff.hasDerivAt
  have h := EarthScience.flux_divergence_eq_advective (fun _ : ℝ => (3 : ℝ))
    (fun x : ℝ => x ^ 2) (1 / 2 : ℝ) 2 (hasDerivAt_const _ _) hc1 hc2
  have h1 : deriv (fun x : ℝ => x ^ 2) 2 = 4 := by
    rw [(hasDerivAt_pow 2 (2 : ℝ)).deriv]
    norm_num
  have h2 : deriv (fun x : ℝ => deriv (fun y : ℝ => y ^ 2) x) 2 = 2 := by
    have hfun : (fun x : ℝ => deriv (fun y : ℝ => y ^ 2) x) = fun x => 2 * x := by
      funext x
      rw [(hasDerivAt_pow 2 x).deriv]
      ring
    rw [hfun]
    simp
  rw [h, h1, h2]
  norm_num

/-- Without continuity the forms differ: for `U(x) = x`, `c(x) = x ^ 2`
at `x = 2`, `d/dx (U * c) = 12` but `U * c_x = 8`. -/
example : deriv (fun x : ℝ => x * x ^ 2) 2 ≠
    (fun x : ℝ => x) 2 * deriv (fun y : ℝ => y ^ 2) 2 := by
  have h1 : deriv (fun x : ℝ => x * x ^ 2) 2 = 12 := by
    have hfun : (fun x : ℝ => x * x ^ 2) = fun x => x ^ 3 := by
      funext x
      ring
    rw [hfun, (hasDerivAt_pow 3 (2 : ℝ)).deriv]
    norm_num
  have h2 : deriv (fun y : ℝ => y ^ 2) 2 = 4 := by
    rw [(hasDerivAt_pow 2 (2 : ℝ)).deriv]
    norm_num
  rw [h1, h2]
  norm_num

/-- PDE-form equivalence as a consumer: under continuity, the
conservative and advective equations are equivalent. -/
example (U : ℝ → ℝ) (C : ℝ → ℝ → ℝ) (D k t x : ℝ)
    (hU : HasDerivAt U 0 x)
    (hc1 : ∀ t, HasDerivAt (fun x => C t x) (deriv (fun x => C t x) x) x)
    (hc2 : ∀ t, HasDerivAt (fun x => deriv (fun x => C t x) x)
      (deriv (fun x => deriv (fun x => C t x) x) x) x) :
    (deriv (fun t => C t x) t +
        deriv (fun x => U x * C t x - D * deriv (fun x => C t x) x) x =
          -k * C t x) ↔
    (deriv (fun t => C t x) t + U x * deriv (fun x => C t x) x -
        D * deriv (fun x => deriv (fun x => C t x) x) x = -k * C t x) :=
  EarthScience.conservative_advective_pde_equiv U C D k t x hU hc1 hc2
