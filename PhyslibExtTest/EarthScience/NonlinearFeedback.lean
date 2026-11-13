/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.EarthScience.NonlinearFeedback

/-!
# Nonlinear feedback checks

Concrete consumers of `PhyslibExt.EarthScience.NonlinearFeedback`:
linear attracting and repelling models at `Tstar = 1, T = 3`, the cubic
boundary case `F(T) = -(T - 1)^3` (derivative `0` at the equilibrium), and
Lyapunov decay for `F(T) = -(T - 1)`, `C = 1`, `T = 3`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Concrete checks

## iv. References

- `PhyslibExt.EarthScience.NonlinearFeedback`
-/

/-- Linear attracting model: `(T - Tstar) * F(T) < 0` at `Tstar = 1, T = 3, k = 2`. -/
example : ((3:ℝ) - 1) * (-(2:ℝ) * ((3:ℝ) - 1)) < 0 :=
  EarthScience.linear_witness (by norm_num) (by norm_num)

/-- Linear repelling model: `(T - Tstar) * F(T) > 0` at `Tstar = 1, T = 3, k = 2`. -/
example : 0 < ((3:ℝ) - 1) * ((2:ℝ) * ((3:ℝ) - 1)) :=
  EarthScience.unstable_witness (by norm_num) (by norm_num)

/-- Local sign theorem as an elaboration check (hypotheses as premises). -/
example {F : ℝ → ℝ} {Tstar δ : ℝ} (hδ : 0 < δ) (hF : F Tstar = 0)
    (hdiff : ∀ T ∈ Set.Ioo (Tstar - δ) (Tstar + δ), DifferentiableAt ℝ F T)
    (hneg : ∀ T ∈ Set.Ioo (Tstar - δ) (Tstar + δ), T ≠ Tstar → deriv F T < 0)
    {T : ℝ} (hT : T ∈ Set.Ioo (Tstar - δ) (Tstar + δ)) (hne : T ≠ Tstar) :
    (T - Tstar) * F T < 0 :=
  EarthScience.local_sign hδ hF hdiff hneg hT hne

/-- Cubic boundary case: `F(T) = -(T - 1)^3` has derivative `0` at the
equilibrium `Tstar = 1`. -/
example : deriv (fun x : ℝ => -(x - 1) ^ 3) 1 = 0 := by
  have h : HasDerivAt (fun x : ℝ => -(x - 1) ^ 3)
      (-((3 : ℕ) * ((1 : ℝ) - 1) ^ (3 - 1) * 1)) 1 :=
    (((hasDerivAt_id' (1 : ℝ)).sub_const 1).pow 3).neg
  rw [h.deriv]
  norm_num

/-- Cubic boundary case: the derivative of `F(T) = -(T - 1)^3` is negative
only away from `Tstar = 1`, which suffices for the local sign condition at
`T = 3 / 2` with `δ = 1`. -/
example : ((3 : ℝ) / 2 - 1) * (-((3 : ℝ) / 2 - 1) ^ 3) < 0 := by
  refine EarthScience.local_sign (F := fun x : ℝ => -(x - 1) ^ 3) (Tstar := 1) (δ := 1)
    (by norm_num) (by norm_num) (fun T _ => ?_) (fun T _ hT => ?_)
    (T := 3 / 2) (by norm_num) (by norm_num)
  · exact (((hasDerivAt_id' T).sub_const 1).pow 3).neg.differentiableAt
  · have h : HasDerivAt (fun x : ℝ => -(x - 1) ^ 3) (-((3 : ℕ) * (T - 1) ^ (3 - 1) * 1)) T :=
      (((hasDerivAt_id' T).sub_const 1).pow 3).neg
    rw [h.deriv, neg_lt_zero]
    exact mul_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero (sub_ne_zero.mpr hT))) one_pos

/-- Lyapunov decay as an elaboration check (hypotheses as premises). -/
example {F : ℝ → ℝ} {C Tstar : ℝ} (hC : 0 < C) (T : ℝ → ℝ) (t : ℝ)
    (hne : T t ≠ Tstar) (hODE : HasDerivAt T (F (T t) / C) t)
    (hsign : (T t - Tstar) * F (T t) < 0) :
    HasDerivAt (fun t => (T t - Tstar) ^ 2 / 2) ((T t - Tstar) * F (T t) / C) t
    ∧ (T t - Tstar) * F (T t) / C < 0 :=
  EarthScience.lyapunov_decay hC T t hne hODE hsign
