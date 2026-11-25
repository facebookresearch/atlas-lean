/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.HyperFibonacciLogConcave
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open MetaMathlibExt

/-- The theorem specializes to the hyper Fibonacci numbers of order two (`p = 1`). -/
example : ∃ N : ℕ, ∀ n ≥ N, generalizedHyperFibonacci 1 0 1 2 n *
    generalizedHyperFibonacci 1 0 1 2 (n + 2) ≤ generalizedHyperFibonacci 1 0 1 2 (n + 1) ^ 2 := by
  obtain ⟨N, hN⟩ := (hyperPFibonacci_hyperPLucas_eventually_logConcave 1 le_rfl 2 (by norm_num)).1
  exact ⟨N, fun n hn => (hN n hn).2⟩

/-- The hyper `1`-Lucas numbers of order one begin `2, 3, 6, 10, 17`. -/
example : (List.range 5).map (generalizedHyperFibonacci 1 2 1 1) = [2, 3, 6, 10, 17] := by
  decide

/-- Log-concavity of the hyper `1`-Lucas numbers of order one fails at `n = 2`
(`6 * 17 > 10 ^ 2`), so the threshold `N` is needed. -/
example : generalizedHyperFibonacci 1 2 1 1 3 ^ 2 <
    generalizedHyperFibonacci 1 2 1 1 2 * generalizedHyperFibonacci 1 2 1 1 4 := by
  decide

/-- Cassini's identity for the Lucas numbers `L_n = W_{1,n}` with `(a, b) = (2, 1)`. -/
private theorem lucas_cassini (n : ℕ) :
    generalizedPFibonacci 1 2 1 (n + 1) ^ 2 -
        generalizedPFibonacci 1 2 1 n * generalizedPFibonacci 1 2 1 (n + 2) =
      (-1) ^ n * (-5) := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h1 : generalizedPFibonacci 1 2 1 (n + 2) =
        1 * generalizedPFibonacci 1 2 1 (n + 1) + generalizedPFibonacci 1 2 1 n := rfl
    have h2 : generalizedPFibonacci 1 2 1 (n + 3) =
        1 * generalizedPFibonacci 1 2 1 (n + 2) + generalizedPFibonacci 1 2 1 (n + 1) := rfl
    linear_combination (-1 : ℤ) * ih + generalizedPFibonacci 1 2 1 (n + 2) * h1 -
      generalizedPFibonacci 1 2 1 (n + 1) * h2

/-- The hypothesis `1 ≤ r` cannot be dropped: the Lucas numbers (order `r = 0`) are not
eventually log-concave, since `L_n L_{n+2} - L_{n+1} ^ 2 = 5` for every even `n`. -/
example : ¬ ∃ N : ℕ, ∀ n ≥ N, generalizedHyperFibonacci 1 2 1 0 n *
    generalizedHyperFibonacci 1 2 1 0 (n + 2) ≤ generalizedHyperFibonacci 1 2 1 0 (n + 1) ^ 2 := by
  rintro ⟨N, hN⟩
  have h := hN (2 * N) (by omega)
  have hc := lucas_cassini (2 * N)
  rw [pow_mul, neg_one_sq, one_pow] at hc
  change generalizedPFibonacci 1 2 1 (2 * N) * generalizedPFibonacci 1 2 1 (2 * N + 2) ≤
    generalizedPFibonacci 1 2 1 (2 * N + 1) ^ 2 at h
  linarith
