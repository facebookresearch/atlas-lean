/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.NormNum

import PhyslibExt.FluidDynamics.Traffic.ShockOrdering

/-!
# Shock-ordering checks

Focused checks for `PhyslibExt.FluidDynamics.Traffic.ShockOrdering`:
the shock speed of the quadratic flux `q(k) = k * (1 - k)` between
densities `0` and `1 / 2` is `1 / 2` by computation, and the public
ordering theorems apply to it (concavity of the quadratic on `ℝ` is
standard; here the checked content is the secant value and that the
theorem's hypotheses are the ones used).

These are elaboration and non-vacuity checks, not new results.
-/

open FluidDynamics.Traffic.ShockOrdering

/-- The secant value on the quadratic flux, by computation. -/
example : shockSpeed (fun k : ℝ => k * (1 - k)) 0 (1 / 2) = 1 / 2 := by
  rw [shockSpeed]
  norm_num

/-- Concrete witness: the quadratic flux on `[0, 1/2]`, with its
strict concavity proved directly and endpoint derivatives computed,
gives the strict ordering through the public strict theorem. -/
example : deriv (fun k : ℝ => k * (1 - k)) (1 / 2)
      < shockSpeed (fun k : ℝ => k * (1 - k)) 0 (1 / 2)
    ∧ shockSpeed (fun k : ℝ => k * (1 - k)) 0 (1 / 2)
      < deriv (fun k : ℝ => k * (1 - k)) 0 := by
  have hconc : StrictConcaveOn ℝ (Set.Icc 0 (1 / 2))
      (fun k : ℝ => k * (1 - k)) := by
    refine ⟨convex_Icc 0 _, fun x _ y _ hxy a b ha hb hab => ?_⟩
    simp only [smul_eq_mul]
    have h : a * (x * (1 - x)) + b * (y * (1 - y)) + a * b * (x - y) ^ 2
        = (a * x + b * y) * (1 - (a * x + b * y)) := by
      have hb1 : b = 1 - a := by linarith
      subst hb1
      ring
    rw [← h]
    have hpos : 0 < a * b * (x - y) ^ 2 :=
      mul_pos (mul_pos ha hb) (pow_two_pos_of_ne_zero (sub_ne_zero.mpr hxy))
    linarith
  have hfun : (fun k : ℝ => k * (1 - k)) = fun k => k - k ^ 2 := by
    funext k
    ring
  have hd0v : HasDerivAt (fun k : ℝ => k * (1 - k)) 1 0 := by
    rw [hfun]
    convert HasDerivAt.sub (hasDerivAt_id (0 : ℝ))
      (hasDerivAt_pow 2 (0 : ℝ)) using 1
    · ext k
      simp [Pi.sub_apply]
    · norm_num
  have hd1v : HasDerivAt (fun k : ℝ => k * (1 - k)) 0 (1 / 2) := by
    rw [hfun]
    convert HasDerivAt.sub (hasDerivAt_id (1 / 2 : ℝ))
      (hasDerivAt_pow 2 (1 / 2 : ℝ)) using 1
    · ext k
      simp [Pi.sub_apply]
    · norm_num
  have hd0 : HasDerivAt (fun k : ℝ => k * (1 - k))
      (deriv (fun k : ℝ => k * (1 - k)) 0) 0 := by
    rw [hd0v.deriv]
    exact hd0v
  have hd1 : HasDerivAt (fun k : ℝ => k * (1 - k))
      (deriv (fun k : ℝ => k * (1 - k)) (1 / 2)) (1 / 2) := by
    rw [hd1v.deriv]
    exact hd1v
  exact shockSpeed_strict_between_of_strictConcave hconc hd0 hd1 (by norm_num)
