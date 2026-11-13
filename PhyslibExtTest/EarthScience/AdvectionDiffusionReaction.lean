/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.AdvectionDiffusionReaction

/-!
# Advection-diffusion-reaction checks

Concrete consumers of `PhyslibExt.EarthScience.AdvectionDiffusionReaction`:
the linear-profile tracer `c(t, x) = t - x` with `U = 1`, `D = 2`, `k = 0`
on `[0, 1]` at `t = 5`, for which the balance is `1 = 1`, and the public
shape of the mass-balance theorem.

## i. Overview

These are elaboration and non-vacuity checks, not new results. For
`c(t, x) = t - x`: `c_t = 1`, `c_x = -1`, `c_xx = 0`, so the PDE
`1 + 1 * (-1) = 2 * 0 - 0 * c` holds; the flux is
`J = U c - D c_x = (t - x) + 2`, and `J(5, 0) - J(5, 1) = 1 = ∫₀¹ c_t`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Linear-profile balance
- B. Shape of the mass-balance theorem

## iv. References

- `PhyslibExt.EarthScience.AdvectionDiffusionReaction`
-/

/-- Linear profile `c(t, x) = t - x`, `U = 1, D = 2, k = 0` on `[0, 1]`:
the integrated balance `∫ c_t = J(a) - J(b)` holds, both sides `1`. -/
example : (∫ x in (0:ℝ)..1, deriv (fun t => t - x) 5) =
    (1 * (5 - 0) - 2 * deriv (fun x => 5 - x) 0) -
      (1 * (5 - 1) - 2 * deriv (fun x => 5 - x) 1) - 0 * ∫ x in (0:ℝ)..1, (5 - x) := by
  have h_t : ∀ x : ℝ, deriv (fun t : ℝ => t - x) 5 = 1 := by
    intro x
    exact ((hasDerivAt_id 5).sub_const x).deriv
  have h_x : ∀ x : ℝ, deriv (fun x : ℝ => (5 : ℝ) - x) x = -1 := by
    intro x
    exact ((hasDerivAt_id x).const_sub 5).deriv
  have h_xx : ∀ x : ℝ, deriv (fun x : ℝ => deriv (fun x' : ℝ => (5 : ℝ) - x') x) x = 0 := by
    intro x
    have hfun : (fun x : ℝ => deriv (fun x' : ℝ => (5 : ℝ) - x') x) = fun _ => (-1 : ℝ) :=
      funext h_x
    rw [hfun]
    simp
  have hpde : ∀ x : ℝ, deriv (fun t => t - x) 5 + 1 * deriv (fun x => 5 - x) x =
      2 * deriv (fun x => deriv (fun x' => 5 - x') x) x - 0 * (5 - x) := by
    intro x
    rw [h_t, h_x, h_xx]
    norm_num
  have hxx_int : IntervalIntegrable
      (fun x => deriv (fun x => deriv (fun x' : ℝ => 5 - x') x) x)
      MeasureTheory.volume 0 1 := by
    have hfun : (fun x : ℝ => deriv (fun x => deriv (fun x' : ℝ => 5 - x') x) x)
        = fun _ => (0 : ℝ) := funext h_xx
    rw [hfun]
    exact intervalIntegrable_const
  have hx_int : IntervalIntegrable (fun x => deriv (fun x : ℝ => (5 : ℝ) - x) x)
      MeasureTheory.volume 0 1 := by
    have hfun : (fun x : ℝ => deriv (fun x : ℝ => (5 : ℝ) - x) x) = fun _ => (-1 : ℝ) :=
      funext h_x
    rw [hfun]
    exact intervalIntegrable_const
  have hc_int : IntervalIntegrable (fun x => (5 : ℝ) - x) MeasureTheory.volume 0 1 :=
    (continuous_const.sub continuous_id').intervalIntegrable 0 1
  have hxx_deriv : ∀ x : ℝ, HasDerivAt (fun x => deriv (fun x' : ℝ => 5 - x') x)
      (deriv (fun x => deriv (fun x' : ℝ => 5 - x') x) x) x := by
    intro x
    have hfun : (fun x : ℝ => deriv (fun x' : ℝ => 5 - x') x) = fun _ => (-1 : ℝ) :=
      funext h_x
    rw [hfun]
    simpa using hasDerivAt_const x (-1 : ℝ)
  have hx_deriv : ∀ x : ℝ, HasDerivAt (fun x => (5 : ℝ) - x)
      (deriv (fun x => (5 : ℝ) - x) x) x := by
    intro x
    rw [h_x]
    exact (hasDerivAt_id x).const_sub 5
  exact EarthScience.integrated_advection_diffusion_reaction (fun t x => t - x) 1 2 0 0 1 5
    (fun x _ => hpde x) hxx_int hx_int hc_int (fun x _ => hxx_deriv x) (fun x _ => hx_deriv x)

/-- The public statement shape of the mass-balance theorem. -/
example (c : ℝ → ℝ → ℝ) (U D k a b t : ℝ)
    (hpde : ∀ x ∈ Set.uIcc a b,
      deriv (fun t => c t x) t + U * deriv (fun x => c t x) x =
        D * deriv (fun x => deriv (fun x' => c t x') x) x - k * c t x)
    (hxx_int : IntervalIntegrable
      (fun x => deriv (fun x => deriv (fun x' => c t x') x) x) MeasureTheory.volume a b)
    (hx_int : IntervalIntegrable (fun x => deriv (fun x => c t x) x)
      MeasureTheory.volume a b)
    (hc_int : IntervalIntegrable (fun x => c t x) MeasureTheory.volume a b)
    (hxx_deriv : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun x => deriv (fun x' => c t x') x)
      (deriv (fun x => deriv (fun x' => c t x') x) x) x)
    (hx_deriv : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun x => c t x)
      (deriv (fun x => c t x) x) x)
    (hswap : HasDerivAt (fun t => ∫ x in a..b, c t x)
      (∫ x in a..b, deriv (fun t => c t x) t) t) :
    HasDerivAt (fun t => ∫ x in a..b, c t x)
      ((U * c t a - D * deriv (fun x => c t x) a) -
        (U * c t b - D * deriv (fun x => c t x) b) - k * ∫ x in a..b, c t x) t :=
  EarthScience.mass_balance_advection_diffusion_reaction c U D k a b t hpde hxx_int
    hx_int hc_int hxx_deriv hx_deriv hswap
