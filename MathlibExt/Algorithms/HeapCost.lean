/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# BUILD-HEAP cost accounting

The linear-time analysis of bottom-up heap construction charges
`h / 2 ^ (h + 1)` work per node at height `h`. This module proves
the accounting bound behind that analysis: the weights
`h / 2 ^ (h + 1)` sum to at most `1`, so the charged cost over
`range n` is at most `n`. The heap algorithms themselves are not
formalized here.
-/

@[expose] public section

private theorem geom_weight_sum_eq (k : ℕ) :
    ∑ h ∈ Finset.range k, (h : ℝ) / 2 ^ (h + 1) = 1 - (k + 1 : ℝ) / 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have h2k : (2 : ℝ) ^ k ≠ 0 := by positivity
    field_simp
    push_cast
    ring

private theorem geom_weight_sum_le_aux (k : ℕ) :
    ∑ h ∈ Finset.range k, (h : ℝ) / 2 ^ (h + 1) ≤ 1 := by
  rw [geom_weight_sum_eq]
  have hnonneg : 0 ≤ (k + 1 : ℝ) / 2 ^ k := by positivity
  linarith

/-- BUILD-HEAP cost accounting (core of ALG-32): the standard
bound `sum_h (n / 2^(h+1)) * h <= n` over the reals, since
`sum_h h / 2^(h+1) = 1`. The heap algorithms themselves are
downstream parts of the roadmap package. -/
theorem build_heap_cost_bound (n : ℕ) :
    ∑ h ∈ Finset.range n, ((n : ℝ) / 2 ^ (h + 1)) * h ≤ n := by
  have hcongr : (∑ h ∈ Finset.range n, ((n : ℝ) / 2 ^ (h + 1)) * (h : ℝ))
      = ∑ h ∈ Finset.range n, (n : ℝ) * ((h : ℝ) / 2 ^ (h + 1)) := by
    apply Finset.sum_congr rfl
    intro h _
    ring
  rw [hcongr, ← Finset.mul_sum]
  have hle : ∑ h ∈ Finset.range n, (h : ℝ) / 2 ^ (h + 1) ≤ 1 :=
    geom_weight_sum_le_aux n
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  calc (n : ℝ) * ∑ h ∈ Finset.range n, (h : ℝ) / 2 ^ (h + 1)
      ≤ (n : ℝ) * 1 := mul_le_mul_of_nonneg_left hle hn
    _ = (n : ℝ) := mul_one _

/-- The finite geometric-weight sum behind the bound:
`sum_{h<k} h / 2^(h+1) <= 1` for all `k`. -/
theorem geom_weight_sum_le (k : ℕ) :
    ∑ h ∈ Finset.range k, (h : ℝ) / 2 ^ (h + 1) ≤ 1 := by
  exact geom_weight_sum_le_aux k

end
