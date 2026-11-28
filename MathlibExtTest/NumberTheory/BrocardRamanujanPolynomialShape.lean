/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.BrocardRamanujanPolynomialShape

/-! # Tests for Brocard–Ramanujan solutions of polynomial shape -/

open Nat MvPolynomial MetaMathlibExt

private def solutions (P : MvPolynomial (Fin 2) ℤ) : Set (ℕ × ℤ) :=
  {p | ((p.1 ! : ℕ) : ℤ) + 1 = p.2 ^ 2 ∧
    ∃ xs : Fin 2 → ℕ, (∀ i, ∃ y z : ℕ, xs i = y * z ∧ y.IsPowerFree 2 ∧ 0 < z ∧
        z.primeFactors.card < 2) ∧
      (p.2 = (∏ i, (xs i : ℤ)) * eval (fun i => (xs i : ℤ)) P + 1 ∨
        p.2 = (∏ i, (xs i : ℤ)) * eval (fun i => (xs i : ℤ)) P - 1)}

-- The zero polynomial gives no solutions: both candidate values of x square to 1.
example : solutions 0 = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr ?_
  rintro ⟨n, x⟩ ⟨hsol, _, _, hx⟩
  change ((n ! : ℕ) : ℤ) + 1 = x ^ 2 at hsol
  simp only [map_zero, mul_zero, zero_add, zero_sub] at hx
  change x = 1 ∨ x = -1 at hx
  have hpos : (0 : ℤ) < (n ! : ℕ) := by exact_mod_cast Nat.factorial_pos n
  rcases hx with rfl | rfl <;> norm_num at hsol <;> omega

private theorem one_decomposition :
    ∃ y z : ℕ, 1 = y * z ∧ y.IsPowerFree 2 ∧ 0 < z ∧ z.primeFactors.card < 2 :=
  ⟨1, 1, rfl, Nat.isPowerFree_two.mpr squarefree_one, by decide, by simp⟩

private theorem four_decomposition :
    ∃ y z : ℕ, 4 = y * z ∧ y.IsPowerFree 2 ∧ 0 < z ∧ z.primeFactors.card < 2 :=
  ⟨2, 2, rfl, Nat.isPowerFree_two.mpr Nat.squarefree_two, by decide,
    by simp [Nat.prime_two.primeFactors]⟩

-- The same polynomial produces -11 via addition and 11 via subtraction.
-- In each case the input 4 uses the nontrivial decomposition 2 * 2.
example : ((5, -11) : ℕ × ℤ) ∈ solutions (X 0 - X 1) := by
  refine ⟨by decide, ![1, 4], ?_, Or.inl ?_⟩
  · intro i
    fin_cases i
    · exact one_decomposition
    · exact four_decomposition
  · norm_num [Fin.prod_univ_two, map_sub, eval_X]

example : ((5, 11) : ℕ × ℤ) ∈ solutions (X 0 - X 1) := by
  refine ⟨by decide, ![4, 1], ?_, Or.inr ?_⟩
  · intro i
    fin_cases i
    · exact four_decomposition
    · exact one_decomposition
  · norm_num [Fin.prod_univ_two, map_sub, eval_X]

-- Public API client, with the same parameters as the independently checked instances.
example : (solutions (X 0 - X 1)).Finite :=
  brocardRamanujan_polynomial_powerFree_mul_fewPrimeFactors_finite
    (k := 2) (l := 2) (m := 2) (by decide) (by decide) (by decide) (X 0 - X 1)
