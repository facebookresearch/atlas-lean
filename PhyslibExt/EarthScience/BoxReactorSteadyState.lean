/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Tactic.Ring
/-!
# Box-reactor steady solutions satisfy elemental conservation

At steady state a well-mixed box reactor obeys, for every species `i`,
`(F / V) * (cIn i - c i) + ∑ j, S i j * r j = 0`, with flow `F > 0`
and volume `V > 0`. Every left-null vector `l` of the stoichiometric
matrix `S` then gives equal weighted totals:
`∑ i, l i * c i = ∑ i, l i * cIn i`.

## i. Overview

Multiply each steady equation by `l i` and sum over species. The
reaction term vanishes by the left-null property (after swapping the
sums), leaving `(F / V)` times the difference of the weighted totals;
since `F / V ≠ 0`, the totals are equal. No claim is made about
existence or stability of the steady state, or about time-dependent
solutions.

## ii. Key results

- `EarthScience.box_reactor_steady_elemental_conservation`: a steady
  solution's weighted total equals the inflow's weighted total.

## iii. References

- `Finset.sum_comm`, `Finset.mul_sum`, `Finset.sum_mul`,
  `Finset.sum_sub_distrib` in Mathlib (`Mathlib/Algebra/BigOperators/`).
-/

@[expose] public section

namespace EarthScience

/-- A box-reactor steady solution satisfies elemental conservation: at steady
state `(F / V) * (cIn i - c i) + ∑ j, S i j * r j = 0` for every species `i`,
with flow `F > 0` and volume `V > 0`, every left-null vector `l` of `S` gives
equal weighted totals, `∑ i, l i * c i = ∑ i, l i * cIn i`. -/
theorem box_reactor_steady_elemental_conservation {n m : ℕ}
    (S : Fin n → Fin m → ℝ) (l : Fin n → ℝ)
    (c cIn : Fin n → ℝ) (r : Fin m → ℝ) {F V : ℝ} (hF : 0 < F) (hV : 0 < V)
    (hnull : ∀ j, ∑ i, l i * S i j = 0)
    (hsteady : ∀ i, (F / V) * (cIn i - c i) + ∑ j, S i j * r j = 0) :
    ∑ i, l i * c i = ∑ i, l i * cIn i := by
  have hFV : F / V ≠ 0 := div_ne_zero (ne_of_gt hF) (ne_of_gt hV)
  have hsum : ∑ i, l i * ((F / V) * (cIn i - c i) + ∑ j, S i j * r j) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [hsteady i, mul_zero]
  have hsplit : ∑ i, l i * ((F / V) * (cIn i - c i) + ∑ j, S i j * r j)
      = ∑ i, l i * ((F / V) * (cIn i - c i)) + ∑ i, l i * (∑ j, S i j * r j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_add]
  have hR : ∑ i, l i * (∑ j, S i j * r j) = 0 := by
    calc ∑ i, l i * (∑ j, S i j * r j)
        = ∑ i, ∑ j, l i * (S i j * r j) := by simp only [Finset.mul_sum]
      _ = ∑ i, ∑ j, (l i * S i j) * r j := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact (mul_assoc _ _ _).symm
      _ = ∑ j, ∑ i, (l i * S i j) * r j := Finset.sum_comm
      _ = ∑ j, (∑ i, l i * S i j) * r j := by simp only [← Finset.sum_mul]
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        rw [hnull j, zero_mul]
  have hC : ∑ i, l i * ((F / V) * (cIn i - c i))
      = (F / V) * (∑ i, l i * cIn i - ∑ i, l i * c i) := by
    have hfac : ∑ i, l i * ((F / V) * (cIn i - c i))
        = (F / V) * ∑ i, (l i * cIn i - l i * c i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hfac, Finset.sum_sub_distrib]
  rw [hsplit, hR, add_zero, hC] at hsum
  have hdiff : ∑ i, l i * cIn i - ∑ i, l i * c i = 0 :=
    (mul_eq_zero.mp hsum).resolve_left hFV
  exact (sub_eq_zero.mp hdiff).symm

end EarthScience
