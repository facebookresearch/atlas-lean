/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.BalancedSignsInfiniteFamilyErdosProblem178
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Order.Monotone.Defs

/-! # Tests for `MathlibExt.Combinatorics.BalancedSignsInfiniteFamilyErdosProblem178` -/

namespace MathlibExtTest.BalancedSignsInfiniteFamilyErdosProblem178

open MathlibExt.Combinatorics.BalancedSignsInfiniteFamilyErdosProblem178Wanted

-- The theorem applies to the arithmetic progressions `0, d, 2d, …` for `d = 1, 2, 3, …`: one
-- choice of signs has bounded partial sums along each of them, with a bound depending on `d`.
example : ∃ f : ℕ → ℤ, (∀ n, f n = 1 ∨ f n = -1) ∧
    ∀ d : ℕ, ∃ C : ℕ, ∀ i < d, ∀ m : ℕ, |∑ j ∈ Finset.range m, f ((i + 1) * j)| ≤ C :=
  boundedDiscrepancyInfiniteFamily_holds (fun i j => (i + 1) * j)
    fun i _ _ h => Nat.mul_lt_mul_of_pos_left h (Nat.succ_pos i)

-- One sequence: the signs given for the family whose sequences all enumerate `ℕ` have bounded
-- partial sums along `ℕ` itself.
example : ∃ f : ℕ → ℤ, (∀ n, f n = 1 ∨ f n = -1) ∧
    ∃ C : ℕ, ∀ m : ℕ, |∑ n ∈ Finset.range m, f n| ≤ C := by
  obtain ⟨f, hf, h⟩ := boundedDiscrepancyInfiniteFamily_holds (fun _ j => j) fun _ => strictMono_id
  obtain ⟨C, hC⟩ := h 1
  exact ⟨f, hf, C, hC 0 Nat.one_pos⟩

-- Edge case: the signs must balance. The constant sign `1` takes the values allowed for `f` but
-- its partial sums along `ℕ` are not bounded, so it is not a witness for the identity family.
example : ¬ ∃ C : ℕ, ∀ m : ℕ, |∑ _n ∈ Finset.range m, (1 : ℤ)| ≤ C := by
  rintro ⟨C, hC⟩
  have h := hC (C + 1)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    abs_of_nonneg (Nat.cast_nonneg _)] at h
  exact absurd h (by push_cast; exact not_le.2 (lt_add_one _))

-- The proposition is the statement of the theorem.
example : boundedDiscrepancyInfiniteFamily := boundedDiscrepancyInfiniteFamily_holds

end MathlibExtTest.BalancedSignsInfiniteFamilyErdosProblem178
