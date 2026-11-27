/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.NormNum

import MathlibExt.Analysis.Calculus.NonminimumWitness

/-!
# Nonminimum-witness checks

Focused checks for `MathlibExt.Analysis.Calculus.NonminimumWitness`:
for `Pi = fun x : ℝ => -x^2` at `x0 = 0`, `v = 1`, every `ε > 0`
admits a lower point, through the public theorem.

These are elaboration and non-vacuity checks, not new results.
-/

open NonminimumWitness

/-- The `-x^2` witness: lower points within any `ε`. -/
example (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℝ, t ≠ 0 ∧ |t| * ‖(1 : ℝ)‖ < ε
      ∧ (fun x : ℝ => -x^2) ((0 : ℝ) + t • (1 : ℝ)) < (fun x : ℝ => -x^2) 0 := by
  have hfun : (fun t : ℝ => (fun x : ℝ => -x^2) ((0 : ℝ) + t • (1 : ℝ)))
      = fun t => -(t ^ 2) := by
    funext t
    simp
  have hg0 : deriv (fun t : ℝ => (fun x : ℝ => -x^2) ((0 : ℝ) + t • (1 : ℝ))) 0
      = 0 := by
    rw [hfun]
    have e : (fun t : ℝ => -(t ^ 2)) = -(fun t : ℝ => t ^ 2) := by
      funext t
      rfl
    rw [e, deriv.neg, deriv_pow_field]
    norm_num
  have hg2 : deriv (deriv (fun t : ℝ => (fun x : ℝ => -x^2)
        ((0 : ℝ) + t • (1 : ℝ)))) 0 < 0 := by
    rw [hfun]
    have h1 : deriv (fun t : ℝ => -(t ^ 2)) = fun t => -(2 * t) := by
      funext x
      have e : (fun t : ℝ => -(t ^ 2)) = -(fun t : ℝ => t ^ 2) := by
        funext t
        rfl
      rw [e, deriv.neg, deriv_pow_field]
      ring
    rw [h1]
    have e2 : (fun t : ℝ => -(2 * t)) = fun t => (-2 : ℝ) * t := by
      funext t
      ring
    rw [e2]
    have h := HasDerivAt.deriv
      (HasDerivAt.const_mul (-2 : ℝ) (hasDerivAt_id (0 : ℝ)))
    simpa using h
  exact exists_lower_arbitrarily_close (fun x : ℝ => -x^2) 0 1 (by norm_num)
    (by fun_prop) hg0 hg2 ε hε
