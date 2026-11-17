/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import MathlibExt.Algebra.AffineRecurrence

/-!
# Periodic dose recurrence

Post-dose amounts under a fixed-spacing schedule obey `x (n+1) = q x n + D` with closed
form `q^n x0 + D ∑_{j<n} q^j`; without elimination they grow linearly.
-/

@[expose] public section

open Finset

namespace MathlibExt.Biology.Biophysics.CompartmentKinetics.DoseRecurrence

/-- **Post-dose recurrence closed form.** With `x n` the amount
just after the `n`-th periodic dose, `x (n+1) = q * x n + D` where
`q = exp (-k * tau)`, the post-dose amounts are
`x n = q^n * x 0 + D * ∑ j ∈ range n, q^j`. At `k = 0` (`q = 1`)
this is `x n = x 0 + n * D`. -/
lemma post_dose_closed_form {D q x0 : ℝ} (x : ℕ → ℝ)
    (h0 : x 0 = x0) (hstep : ∀ n, x (n + 1) = q * x n + D) (n : ℕ) :
    x n = q ^ n * x0 + D * ∑ j ∈ Finset.range n, q ^ j := by
  have h := MathlibExt.AffineRecurrence.IsAffineRecurrence.eq_pow_mul_add_geom_sum
    (x := x) (a := q) (b := D) hstep n
  rwa [h0] at h

/-- At `q = 1` (no elimination) amounts grow linearly. -/
lemma post_dose_no_elimination {D x0 : ℝ} (x : ℕ → ℝ)
    (h0 : x 0 = x0) (hstep : ∀ n, x (n + 1) = 1 * x n + D) (n : ℕ) :
    x n = x0 + n * D := by
  have h := MathlibExt.AffineRecurrence.IsAffineRecurrence.eq_add_nsmul_of_one
    (x := x) (b := D) hstep n
  rw [h0] at h
  simpa using h

end MathlibExt.Biology.Biophysics.CompartmentKinetics.DoseRecurrence
