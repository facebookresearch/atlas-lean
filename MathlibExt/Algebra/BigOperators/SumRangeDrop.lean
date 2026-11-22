/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Drops along a finite series chain

If successive real potentials satisfy `P i - P (i + 1) = q * R i` along a
finite chain, each potential is reconstructed from the initial one by
partial sums of the `R i`, the total drop is `q` times the total sum, and
for positive `R i` over a nonempty chain the factor `q` is recovered as the
total drop divided by the total sum. These are the shared scalar identities
behind series-resistance calculations (roadmap task F17_U10_T00); the
physical readings of `R`, `P`, and `q` belong to consumers.

## Main results

* `MathlibExt.apply_eq_sub_mul_sum_range`: reconstruction of `P j` from partial sums.
* `MathlibExt.sub_eq_mul_sum_range`: the total drop.
* `MathlibExt.eq_div_sum_range`: recovery of the common factor.
-/

@[expose] public section

namespace MathlibExt

/-- Reconstruction along a finite series chain: if successive drops are
`P i - P (i + 1) = q * R i` for `i < n`, then every intermediate potential
`P j` with `j ≤ n` equals the initial potential minus `q` times the partial
resistance sum. (Shared scalar identity for series networks; physical
meanings of `R`, `P`, and `q` are supplied by consumers.) -/
theorem apply_eq_sub_mul_sum_range {R P : ℕ → ℝ} {q : ℝ} {n j : ℕ}
    (hj : j ≤ n) (hdrop : ∀ i < n, P i - P (i + 1) = q * R i) :
    P j = P 0 - q * ∑ i ∈ Finset.range j, R i := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hjn : j < n := by omega
    have hj' : j ≤ n := by omega
    have hd := hdrop j hjn
    have ih' := ih hj'
    rw [Finset.sum_range_succ]
    linarith

/-- Total drop along a finite series chain: `P 0 - P n` is the common flow
`q` times the total resistance. -/
theorem sub_eq_mul_sum_range {R P : ℕ → ℝ} {q : ℝ} {n : ℕ}
    (hdrop : ∀ i < n, P i - P (i + 1) = q * R i) :
    P 0 - P n = q * ∑ i ∈ Finset.range n, R i := by
  have h := apply_eq_sub_mul_sum_range (le_refl n) hdrop
  linarith

/-- Flow recovery for a positive series chain: with `n ≥ 1` positive
resistances, the common flow is the total drop divided by the total
resistance. -/
theorem eq_div_sum_range {R P : ℕ → ℝ} {q : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hR : ∀ i < n, 0 < R i)
    (hdrop : ∀ i < n, P i - P (i + 1) = q * R i) :
    q = (P 0 - P n) / ∑ i ∈ Finset.range n, R i := by
  have h2 := sub_eq_mul_sum_range hdrop
  have hS : 0 < ∑ i ∈ Finset.range n, R i := by
    apply Finset.sum_pos
    · intro i hi
      exact hR i (Finset.mem_range.mp hi)
    · refine ⟨0, Finset.mem_range.mpr ?_⟩
      omega
  have hSne : ∑ i ∈ Finset.range n, R i ≠ 0 := ne_of_gt hS
  field_simp
  linarith

end MathlibExt
