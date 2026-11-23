/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Field.GeomSum

/-!
# Roots-of-unity filter

For a `k`-th root of unity `ζ`, the geometric sum `∑ j ∈ range k, (ζ ^ m) ^ j` over one
period is `k` when `ζ ^ m = 1` and `0` otherwise. Order finding is not included here.
-/

@[expose] public section

namespace MathlibExt.Quantum.RootsFilter

/-- Roots-of-unity filter: for a `k`-th root of unity `ζ`, the geometric sum
`∑ j ∈ range k, (ζ ^ m) ^ j` over one period is `k` when `ζ ^ m = 1` and `0` otherwise. -/
theorem roots_filter {k : ℕ} (ζ : ℂ) (hk : 0 < k)
    (hζ : ζ ^ k = 1) (m : ℕ) :
    (∑ j ∈ Finset.range k, (ζ ^ m) ^ j)
      = if ζ ^ m = 1 then (k : ℂ) else 0 := by
  by_cases h : ζ ^ m = 1
  · rw [ite_eq_left h]
    simp only [h, one_pow]
    rw [Finset.sum_const, Finset.card_range]
    simp
  · rw [ite_eq_right h]
    rw [geom_sum_eq h k]
    have hxk : (ζ ^ m) ^ k = 1 := by
      calc (ζ ^ m) ^ k = ζ ^ (m * k) := by rw [← pow_mul]
        _ = ζ ^ (k * m) := by rw [mul_comm m k]
        _ = (ζ ^ k) ^ m := by rw [pow_mul]
        _ = 1 ^ m := by rw [hζ]
        _ = 1 := one_pow m
    rw [hxk]
    simp

end MathlibExt.Quantum.RootsFilter

end
