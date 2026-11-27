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

/-- For `(p, a, b) = (1, 5, 1)` the generalized hyper-Fibonacci numbers of order one begin
`5, 6, 12, 19, 32, 52, 85`. -/
example : (List.range 7).map (generalizedHyperFibonacci 1 5 1 1) =
    [5, 6, 12, 19, 32, 52, 85] := by
  decide

/-- The general theorem covers initial values that are neither the hyper `p`-Fibonacci nor the
hyper `p`-Lucas case, here `(p, a, b) = (1, 5, 1)` with `r = 1`. Log-concavity fails at `n = 4`
(`32 * 85 > 52 ^ 2`), so the threshold the theorem provides exceeds `4`. -/
example : ∃ N : ℕ, 4 < N ∧ ∀ n ≥ N, 0 < generalizedHyperFibonacci 1 5 1 1 n ∧
    generalizedHyperFibonacci 1 5 1 1 n * generalizedHyperFibonacci 1 5 1 1 (n + 2) ≤
      generalizedHyperFibonacci 1 5 1 1 (n + 1) ^ 2 := by
  obtain ⟨N, hN⟩ := generalizedHyperFibonacci_eventually_logConcave 1 5 1 le_rfl
    (by norm_num) one_pos 1 le_rfl
  refine ⟨N, ?_, hN⟩
  by_contra hN4
  have hfail : generalizedHyperFibonacci 1 5 1 1 (4 + 1) ^ 2 <
      generalizedHyperFibonacci 1 5 1 1 4 * generalizedHyperFibonacci 1 5 1 1 (4 + 2) := by
    decide
  exact absurd (hN 4 (by omega)).2 (not_le.mpr hfail)

/-- With `a = b = 0` every generalized hyper-Fibonacci number vanishes. -/
private theorem generalizedHyperFibonacci_zero_zero (p : ℤ) (r n : ℕ) :
    generalizedHyperFibonacci p 0 0 r n = 0 := by
  induction r generalizing n with
  | zero =>
    induction n using Nat.twoStepInduction with
    | zero => rfl
    | one => rfl
    | more n ih1 ih2 =>
      change p * generalizedHyperFibonacci p 0 0 0 (n + 1) +
        generalizedHyperFibonacci p 0 0 0 n = 0
      rw [ih1, ih2, mul_zero, add_zero]
  | succ r ih =>
    change ∑ k ∈ Finset.range (n + 1), p ^ (n - k) * generalizedHyperFibonacci p 0 0 r k = 0
    simp only [ih, mul_zero, Finset.sum_const_zero]

/-- The hypothesis `0 < b` cannot be dropped: for `a = b = 0` no term is positive. -/
example : ¬ ∃ N : ℕ, ∀ n ≥ N, 0 < generalizedHyperFibonacci 1 0 0 1 n := by
  rintro ⟨N, hN⟩
  have h := hN N le_rfl
  rw [generalizedHyperFibonacci_zero_zero] at h
  exact lt_irrefl 0 h
