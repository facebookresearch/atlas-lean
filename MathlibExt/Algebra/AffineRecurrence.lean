/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# First-order affine recurrences

Closed forms for sequences with `x (n + 1) = a * x n + b` over a field, including the unit-root
branch `a = 1`.

## i. Overview

Every solution is the propagated initial value plus the accumulated forcing,
`x n = a ^ n * x 0 + b * ∑ i ∈ range n, a ^ i`. Off the unit root the forcing sum has Mathlib's
closed form `geom_sum_eq`, which gives the fixed-point form
`x n = b / (1 - a) + a ^ n * (x 0 - b / (1 - a))`; at `a = 1` Mathlib's `one_geom_sum` gives the
linear drift `x n = x 0 + n * b`. No stability or convergence statement is made.

## ii. Main results

* `MathlibExt.AffineRecurrence.IsAffineRecurrence.eq_pow_mul_add_geom_sum`
* `MathlibExt.AffineRecurrence.IsAffineRecurrence.eq_fixedPoint_add` (`a ≠ 1`)
* `MathlibExt.AffineRecurrence.IsAffineRecurrence.eq_add_nsmul_of_one` (`a = 1`)

## iii. References

* K. Sydsæter, P. Hammond, *Essential Mathematics for Economic Analysis*, chapter on difference
  equations.
-/

@[expose] public section

namespace MathlibExt.AffineRecurrence

/-- `x` solves the first-order affine recurrence with slope `a` and intercept `b`:
`x (n + 1) = a * x n + b` for every `n`. The initial value `x 0` is free. -/
def IsAffineRecurrence {K : Type*} [Field K] (a b : K) (x : ℕ → K) : Prop :=
  ∀ n, x (n + 1) = a * x n + b

/-- Every solution is the propagated initial value plus the accumulated forcing:
`x n = a ^ n * x 0 + b * ∑ i ∈ range n, a ^ i`, for every slope. -/
theorem IsAffineRecurrence.eq_pow_mul_add_geom_sum {K : Type*} [Field K] {a b : K}
    {x : ℕ → K} (h : IsAffineRecurrence a b x) (n : ℕ) :
    x n = a ^ n * x 0 + b * ∑ i ∈ Finset.range n, a ^ i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [h n, ih, geom_sum_succ, pow_succ]
      ring

/-- **Closed form off the unit root.** If `a ≠ 1`, with fixed point `b / (1 - a)`,
`x n = b / (1 - a) + a ^ n * (x 0 - b / (1 - a))`. -/
theorem IsAffineRecurrence.eq_fixedPoint_add {K : Type*} [Field K] {a b : K}
    {x : ℕ → K} (h : IsAffineRecurrence a b x) (ha : a ≠ 1) (n : ℕ) :
    x n = b / (1 - a) + a ^ n * (x 0 - b / (1 - a)) := by
  have h1 : (1 : K) - a ≠ 0 := sub_ne_zero.mpr ha.symm
  have h2 : a - 1 ≠ 0 := sub_ne_zero.mpr ha
  rw [h.eq_pow_mul_add_geom_sum n, geom_sum_eq ha n]
  field_simp
  ring

/-- **Unit-root branch.** If `a = 1` the solution drifts linearly: `x n = x 0 + n * b`. -/
theorem IsAffineRecurrence.eq_add_nsmul_of_one {K : Type*} [Field K] {b : K}
    {x : ℕ → K} (h : IsAffineRecurrence 1 b x) (n : ℕ) :
    x n = x 0 + n * b := by
  rw [h.eq_pow_mul_add_geom_sum n, one_geom_sum, one_pow, one_mul, mul_comm b]

end MathlibExt.AffineRecurrence
