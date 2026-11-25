/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Tactic.Ring

/-!
# Carlitz Bernoulli identity

Formalizes the symmetric Bernoulli-number sum identity from Claudio de J.
Pita Ruiz V., “Carlitz-Type and Other Bernoulli Identities”
(`https://cs.uwaterloo.ca/journals/JIS/VOL19/Pita/pita23.tex`),
concept `jis_grounded_fce2b7cab59026f60915e28f__carlitz_bernoulli_sum_symm`,
grounded in source file SHA-256
`9afd712145cc635f43c1d169b86bd08516c3ace3223a0763f2538204790e4087`,
exact lines 203–233 SHA-256
`1dac4569ed610222ad9901fde13d7081d71e9072b9c4e9496fd78cfe78dac5bd`.
The identity goes back to the original L. Carlitz, Problem 795,
Mathematics Magazine 44 (1971), p. 107.
-/

namespace MetaMathlibExt

@[expose] public section

open Nat Finset

private noncomputable def S (m n : ℕ) : ℚ :=
  ∑ k ∈ range (m + 1), (choose m k : ℚ) * bernoulli (n + k)

private noncomputable def A (m n : ℕ) : ℚ := (-1 : ℚ) ^ m * S m n

private lemma S_succ (m n : ℕ) : S (m + 1) n = S m n + S m (n + 1) := by
  simp only [S]
  rw [sum_range_succ']
  simp only [choose_zero_right, Nat.cast_one, one_mul, add_zero]
  simp_rw [choose_succ_succ, Nat.cast_add, add_mul]
  rw [sum_add_distrib]
  have hfirst :
      (∑ x ∈ range (m + 1), (m.choose x : ℚ) * bernoulli (n + (x + 1))) =
        ∑ x ∈ range (m + 1), (m.choose x : ℚ) * bernoulli (n + 1 + x) := by
    apply sum_congr rfl
    intro x hx
    rw [Nat.add_comm x 1, ← Nat.add_assoc]
  have hshift :
      (∑ x ∈ range (m + 1), (m.choose x.succ : ℚ) * bernoulli (n + (x + 1))) +
          bernoulli n =
        ∑ x ∈ range (m + 1), (m.choose x : ℚ) * bernoulli (n + x) := by
    rw [sum_range_succ, sum_range_succ']
    simp [add_comm, add_left_comm]
  rw [hfirst, ← hshift]
  ring

private lemma A_zero_left (n : ℕ) : A 0 n = bernoulli n := by
  simp [A, S]

private lemma A_zero_right (n : ℕ) : A n 0 = bernoulli n := by
  rw [A]
  have h := Polynomial.bernoulli_eval_one n
  rw [Polynomial.bernoulli] at h
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial, one_pow, mul_one] at h
  rw [show S n 0 = bernoulli' n by simpa [S, mul_comm] using h]
  simp [bernoulli'_eq_bernoulli, ← mul_assoc, ← sq, ← pow_mul, mul_comm n 2]

private lemma A_succ (m n : ℕ) :
    A (m + 1) n = -A m n - A m (n + 1) := by
  simp only [A, S_succ, pow_succ]
  ring

private lemma A_symm (m n : ℕ) : A m n = A n m := by
  induction m generalizing n with
  | zero => rw [A_zero_left, A_zero_right]
  | succ m ih =>
      rw [A_succ, ih n, ih (n + 1), A_succ]
      ring

/-- **Carlitz's Bernoulli identity.** Let $B_j$ denote the $j$-th Bernoulli number, with
$B_1 = -1/2$. For all natural numbers $m$ and $n$,
$$(-1)^m \sum_{k=0}^{m} \binom{m}{k} B_{n+k} = (-1)^n \sum_{k=0}^{n} \binom{n}{k} B_{m+k}.$$

Source: Pita Ruiz, “Carlitz-Type and Other Bernoulli Identities”, concept
`jis_grounded_fce2b7cab59026f60915e28f__carlitz_bernoulli_sum_symm`; original L. Carlitz,
Problem 795, Mathematics Magazine 44 (1971), p. 107. -/
theorem carlitz_bernoulli_sum_symm (m n : ℕ) :
    (-1 : ℚ) ^ m * (Finset.range (m + 1)).sum
      (fun k => (Nat.choose m k : ℚ) * bernoulli (n + k)) =
    (-1 : ℚ) ^ n * (Finset.range (n + 1)).sum
      (fun k => (Nat.choose n k : ℚ) * bernoulli (m + k)) := by
  exact A_symm m n

end

end MetaMathlibExt
