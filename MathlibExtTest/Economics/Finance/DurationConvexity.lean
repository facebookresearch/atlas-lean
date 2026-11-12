/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.DurationConvexity
import Mathlib.Tactic

/-!
# Tests for duration, convexity, and the tangent-line approximation

A single payment of 100 at `t = 1` has price 50 at yield 1, derivative -100
at yield 0, and satisfies the tangent inequality at `r₀ = 0, r = 1` (the true
price 50 sits strictly above the tangent line value 0).
-/

@[expose] public section

namespace MathlibExtTest.Economics.Finance.DurationConvexity

open _root_.MathlibExt.Economics.Finance.DurationConvexity

theorem test_price :
    bondPrice (fun t => if t = 1 then (100 : ℝ) else 0) {1} 1 = 50 := by
  simp only [bondPrice, Finset.sum_singleton, ite_true, Nat.cast_one]
  rw [zpow_neg, zpow_one]
  norm_num

theorem test_deriv :
    deriv (bondPrice (fun t => if t = 1 then (100 : ℝ) else 0) {1}) 0 = -100 := by
  have h : HasDerivAt (bondPrice (fun t => if t = 1 then (100 : ℝ) else 0) {1}) _ 0 :=
    hasDerivAt_bondPrice (by norm_num)
  rw [h.deriv]
  simp only [Finset.sum_singleton, ite_true, Nat.cast_one, add_zero,
    one_zpow, mul_one]
  norm_num

theorem test_tangent :
    bondPrice (fun t => if t = 1 then (100 : ℝ) else 0) {1} 1 ≥
      bondPrice (fun t => if t = 1 then (100 : ℝ) else 0) {1} 0 +
        deriv (bondPrice (fun t => if t = 1 then (100 : ℝ) else 0) {1}) 0 * (1 - 0) := by
  have hc : ∀ t ∈ ({1} : Finset ℕ), 0 ≤ (if t = 1 then (100 : ℝ) else 0) := by
    intro t ht
    simp only [Finset.mem_singleton] at ht
    subst ht
    simp only [ite_true]
    norm_num
  exact bondPrice_ge_tangent hc (by norm_num) (by norm_num)

end MathlibExtTest.Economics.Finance.DurationConvexity
