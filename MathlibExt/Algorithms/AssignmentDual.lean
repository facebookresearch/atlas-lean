/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Rat

/-!
# Assignment optimality from a dual certificate

If potentials `u, v` satisfy `u i + v j ≤ w i j` for all
`i, j` and equality holds along a permutation `σ`, then
`σ` is a minimum-cost perfect assignment. The Hungarian
algorithm is not included here.
-/

@[expose] public section

/-- Assignment-problem dual certificate: if potentials `u v`
satisfy `u i + v j ≤ w i j` everywhere and equality holds on
the edges of a permutation `σ`, then `σ` is a minimum-cost
perfect assignment. Costs over `ℚ`. -/
theorem assignment_optimal_of_dual {n : ℕ}
    (w : Fin n → Fin n → ℚ) (u v : Fin n → ℚ)
    (σ : Equiv.Perm (Fin n))
    (hfeas : ∀ i j, u i + v j ≤ w i j)
    (htight : ∀ i, u i + v (σ i) = w i (σ i))
    (τ : Equiv.Perm (Fin n)) :
    ∑ i, w i (σ i) ≤ ∑ i, w i (τ i) := by
  have hle : ∑ i, (u i + v (τ i)) ≤ ∑ i, w i (τ i) := by
    apply Finset.sum_le_sum
    intro i _
    exact hfeas i (τ i)
  have hsplit : ∀ σ' : Equiv.Perm (Fin n),
      ∑ i, (u i + v (σ' i)) = ∑ i, u i + ∑ j, v j := by
    intro σ'
    rw [Finset.sum_add_distrib, Equiv.sum_comp σ' v]
  have hσ : ∑ i, w i (σ i) = ∑ i, u i + ∑ j, v j := by
    have hcongr : ∑ i, w i (σ i) = ∑ i, (u i + v (σ i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (htight i).symm
    rw [hcongr, hsplit σ]
  rw [hσ, ← hsplit τ]
  exact hle

end
