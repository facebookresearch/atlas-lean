/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Dual certificate for the assignment problem

For a real cost matrix, the cost of a permutation minus the sum of the row and column
potentials is exactly the sum of the slacks on its assigned entries. Under dual feasibility,
this gap is nonnegative and vanishes precisely when every assigned entry is tight.

T. Ralphs, [*Introduction to Mathematical Programming*, IE406 Lecture 19](https://coral.ise.lehigh.edu/~ted/files/ie406/lectures/Lecture19.pdf),
slides 2, 3 and 5, maximises value `c` with `r i + p j ≥ c i j` and gives equality on used
entries under complementary slackness. Negating `c`, `r` and `p` gives the minimum-cost sign
convention below. The gap formula follows by summing along a permutation, which uses each
column once.
-/

public section

namespace AssignmentDual

variable {n : ℕ} (w : Fin n → Fin n → ℝ) (u v : Fin n → ℝ)

/-- The cost of an assignment minus the sum of the potentials is the sum of its chosen-entry
slacks. This identity does not require feasible potentials. -/
theorem cost_sub_dual_eq_sum_slack (τ : Equiv.Perm (Fin n)) :
    (∑ i, w i (τ i)) - ((∑ i, u i) + ∑ j, v j) = ∑ i, (w i (τ i) - (u i + v (τ i))) := by
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Equiv.sum_comp τ v]

/-- Feasible row and column potentials give a lower bound on the cost of every permutation. -/
theorem dual_le_cost (hfeas : ∀ i j, u i + v j ≤ w i j) (τ : Equiv.Perm (Fin n)) :
    (∑ i, u i) + ∑ j, v j ≤ ∑ i, w i (τ i) := by
  apply sub_nonneg.mp
  rw [cost_sub_dual_eq_sum_slack]
  exact Finset.sum_nonneg fun i _ ↦ sub_nonneg.mpr (hfeas i (τ i))

/-- For feasible potentials, an assignment attains the dual lower bound if and only if the
potential inequality is tight at every entry it uses. -/
theorem cost_eq_dual_iff (hfeas : ∀ i j, u i + v j ≤ w i j) (σ : Equiv.Perm (Fin n)) :
    (∑ i, w i (σ i)) = (∑ i, u i) + ∑ j, v j ↔ ∀ i, u i + v (σ i) = w i (σ i) := by
  rw [← sub_eq_zero, cost_sub_dual_eq_sum_slack,
    Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ sub_nonneg.mpr (hfeas i (σ i)))]
  simp only [Finset.mem_univ, forall_const, sub_eq_zero]
  exact forall_congr' fun _ ↦ eq_comm

/-- For a real cost matrix, feasible row and column potentials tight along `σ` certify that
`σ` costs no more than any competing permutation `τ`. -/
theorem optimal_of_tight (σ : Equiv.Perm (Fin n)) (hfeas : ∀ i j, u i + v j ≤ w i j)
    (htight : ∀ i, u i + v (σ i) = w i (σ i)) (τ : Equiv.Perm (Fin n)) :
    ∑ i, w i (σ i) ≤ ∑ i, w i (τ i) :=
  ((cost_eq_dual_iff w u v hfeas σ).2 htight).trans_le (dual_le_cost w u v hfeas τ)

end AssignmentDual
