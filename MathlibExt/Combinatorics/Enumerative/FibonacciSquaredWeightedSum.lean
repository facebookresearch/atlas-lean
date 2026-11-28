/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Fib.Basic
import MathlibExt.Combinatorics.Enumerative.FibonacciSquaredAddition

/-!
# Squared Fibonacci numbers as weighted sums of squares

`fib_succ_sq_sub_parity_eq_sum` expresses the parity-corrected square of a Fibonacci number
as a weighted sum of earlier squares in both orders.
-/

namespace MetaMathlibExt

open Finset

namespace fib_succ_sq_sub_parity_eq_sum

private def weightedSum (n : ℕ) : ℤ :=
  ∑ k ∈ Icc 1 n, ((n - k + 1 : ℕ) : ℤ) * (Nat.fib k : ℤ) ^ 2

-- Each old weight increases by one, and the new square has weight one.
private theorem weightedSum_succ (n : ℕ) :
    weightedSum (n + 1) = weightedSum n + ∑ k ∈ Icc 1 (n + 1), (Nat.fib k : ℤ) ^ 2 := by
  simp only [weightedSum, sum_Icc_succ_top (show 1 ≤ n + 1 by omega), Nat.sub_self, Nat.zero_add,
    Nat.cast_one, one_mul]
  rw [← add_assoc, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun k hk => ?_
  have hk' := (mem_Icc.mp hk).2
  rw [show n + 1 - k + 1 = (n - k + 1) + 1 by omega, Nat.cast_add_one, add_one_mul]

private theorem weightedSum_eq {n : ℕ} (hn : 1 ≤ n) :
    weightedSum n = (Nat.fib (n + 1) : ℤ) ^ 2 - ((n + 1) % 2 : ℕ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  clear hn
  induction m using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more m ih _ =>
    -- Two successive increments give twice the earlier sum of squares and one final square.
    rw [weightedSum_succ (m + 2), weightedSum_succ (m + 1), ih,
      sum_Icc_succ_top (show 1 ≤ m + 2 + 1 by omega)]
    have h := two_mul_sum_fib_sq (n := m + 4) (by omega)
    rw [show m + 4 - 2 = m + 2 by omega, show m + 4 - 1 = m + 3 by omega] at h
    simp only [Nat.add_assoc, Nat.reduceAdd]
    omega

end fib_succ_sq_sub_parity_eq_sum

open fib_succ_sq_sub_parity_eq_sum in
/-- **Squared Fibonacci numbers as weighted sums of squares.** Let $F_k$ denote the Fibonacci
numbers ($F_0 = 0$, $F_1 = 1$) and let $\xi(m) = m \bmod 2$. For every natural number $n \ge 1$,
$$
F_{n+1}^2 - \xi(n+1) = \sum_{k=1}^{n} (n-k+1) F_k^2 = \sum_{k=1}^{n} k F_{n-k+1}^2.
$$

Source: Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic
Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024,
Corollary 3.10 (`fq-2024-belaggoun01132024-cor-3.10`). -/
public theorem fib_succ_sq_sub_parity_eq_sum {n : ℕ} (hn : 1 ≤ n) :
    (Nat.fib (n + 1) : ℤ) ^ 2 - ((n + 1) % 2 : ℕ) =
        ∑ k ∈ Icc 1 n, ((n - k + 1 : ℕ) : ℤ) * (Nat.fib k : ℤ) ^ 2 ∧
      (Nat.fib (n + 1) : ℤ) ^ 2 - ((n + 1) % 2 : ℕ) =
        ∑ k ∈ Icc 1 n, (k : ℤ) * (Nat.fib (n - k + 1) : ℤ) ^ 2 := by
  have h := (weightedSum_eq hn).symm
  refine ⟨h, h.trans ?_⟩
  have maps : ∀ k ∈ Icc 1 n, n - k + 1 ∈ Icc 1 n := by
    simp only [mem_Icc]
    omega
  have inv : ∀ k ∈ Icc 1 n, n - (n - k + 1) + 1 = k := by
    simp only [mem_Icc]
    omega
  exact sum_nbij' (fun k => n - k + 1) (fun k => n - k + 1) maps maps inv inv
    (fun k hk => by dsimp; rw [inv k hk])

end MetaMathlibExt
