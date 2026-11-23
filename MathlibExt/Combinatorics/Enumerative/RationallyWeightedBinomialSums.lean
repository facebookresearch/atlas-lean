/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import MathlibExt.Analysis.MonotonePowerSumInequalities
import MathlibExt.NumberTheory.DilcherFiniteMultipleHarmonic

/-!
# Rationally weighted binomial sums

For every natural number `n`, `∑_{k=0}^n binom(n, k) / (k + 1) = (2^{n+1} - 1) / (n + 1)` in `ℚ`
(`MetaMathlibExt.sum_choose_div_succ`).

The alternating binomial sum with inverse-square weights equals the sum of the harmonic
numbers divided by their indices. This follows from Dilcher's identity at exponent two by
grouping the weakly increasing pairs by their second entry.

The first four power-weighted binomial sums of Fibonacci numbers follow by expanding each
power in falling factorials and evaluating the shifted binomial sums.

## Proof of Epsteen's identity

The absorption identity `(n + 1) binom(n, k) = binom(n + 1, k + 1) (k + 1)`
(`Nat.add_one_mul_choose_eq`) turns each term into `binom(n + 1, k + 1) / (n + 1)`. The remaining
sum `∑_{k=0}^n binom(n + 1, k + 1)` is the row sum `∑_{j=0}^{n+1} binom(n + 1, j) = 2^{n+1}`
(`Nat.sum_range_choose`) without its term `binom(n + 1, 0) = 1`.

## Implementation notes

`sum_choose_div_succ` keeps the full name and the statement it had as a wanted theorem in
`WantedExt.Combinatorics.Enumerative.RationallyWeightedBinomialSumsWanted`.
-/

namespace MetaMathlibExt

/-- **Epsteen's identity.** For every natural number $n$,

$$\sum_{k=0}^{n} \frac{1}{k+1} \binom{n}{k} = \frac{2^{n+1} - 1}{n+1}.$$

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Corollary 3.2. -/
public theorem sum_choose_div_succ (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) / (k + 1) = (2 ^ (n + 1) - 1) / (n + 1) := by
  -- Absorption: each term is `binom(n + 1, k + 1) / (n + 1)`.
  have hterm : ∀ k ∈ Finset.range (n + 1),
      (n.choose k : ℚ) / (k + 1) = ((n + 1).choose (k + 1) : ℚ) / (n + 1) := by
    intro k _
    rw [div_eq_div_iff (by positivity) (by positivity)]
    have h : ((n : ℚ) + 1) * n.choose k = (n + 1).choose (k + 1) * ((k : ℚ) + 1) := by
      exact_mod_cast Nat.add_one_mul_choose_eq n k
    linarith
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
  congr 1
  -- Row `n + 1` of Pascal's triangle sums to `2 ^ (n + 1)`; drop its first entry `1`.
  have hrow := Nat.sum_range_choose (n + 1)
  rw [Finset.sum_range_succ', Nat.choose_zero_right] at hrow
  have hrow' : (∑ k ∈ Finset.range (n + 1), ((n + 1).choose (k + 1) : ℚ)) + 1 = 2 ^ (n + 1) := by
    exact_mod_cast hrow
  linarith

/-- **Alternating binomial sum with inverse-square weights.** For every natural number $n$, with
$H_k = \sum_{j=1}^{k} 1/j$ the $k$-th harmonic number,

$$\sum_{k=1}^{n} (-1)^{k-1} \frac{1}{k^2} \binom{n}{k} = \sum_{k=1}^{n} \frac{H_k}{k}.$$

This is the case $x = -1$ of identity (3.6) of the source.

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Corollary 3.2. -/
public theorem sum_neg_one_pow_choose_div_sq_eq_sum_harmonic (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (-1 : ℚ) ^ (k - 1) * n.choose k / (k : ℚ) ^ 2 =
      ∑ k ∈ Finset.Icc 1 n, harmonic k / k := by
  classical
  obtain rfl | hn := Nat.eq_zero_or_pos n
  · simp
  let pairWeight (i j : ℕ) : ℚ := if i ≤ j then (↑(i + 1) : ℚ)⁻¹ / ↑(j + 1) else 0
  have inner (j : Fin n) :
      (∑ i : Fin n, pairWeight i j) = harmonic (j.val + 1) / ↑(j.val + 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => pairWeight i j), harmonic, Finset.sum_div]
    simp only [pairWeight, ← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  calc
    _ = ∑ js ∈ Finset.univ.filter (fun js : Fin 2 → Fin n => Monotone (fun i => (js i).val)),
          (∏ i, ((js i).val + 1 : ℚ))⁻¹ := by
      simpa only [mul_comm] using dilcher_finite_multiple_harmonic_identity_general 2 n hn
    _ = ∑ p : Fin n × Fin n, pairWeight p.1 p.2 := by
      rw [Finset.sum_filter]
      refine Fintype.sum_equiv (finTwoArrowEquiv (Fin n)) _ _ fun js => ?_
      simp [pairWeight, Fin.monotone_iff_le_succ, Fin.forall_fin_one, Fin.prod_univ_two,
        finTwoArrowEquiv_apply, div_eq_mul_inv, mul_comm]
    _ = ∑ j : Fin n, harmonic (j.val + 1) / ↑(j.val + 1) := by
      rw [Fintype.sum_prod_type_right]
      exact Finset.sum_congr rfl fun j _ => inner j
    _ = _ := by
      rw [Fin.sum_univ_eq_sum_range (fun j => harmonic (j + 1) / ↑(j + 1)),
        ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
      simp [Nat.add_comm]

-- Absorbing one falling-factorial factor lowers the binomial row and shifts the Fibonacci index.
private theorem sum_descFactorial_mul_choose_mul_fib_add (n i m : ℕ) :
    ∑ k ∈ Finset.range (n + 1), k.descFactorial i * n.choose k * Nat.fib (k + m) =
      n.descFactorial i * Nat.fib (2 * n + m - i) := by
  induction i generalizing n m with
  | zero => simpa using Nat.sum_range_choose_mul_fib_add n m
  | succ i ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [Finset.sum_range_succ', Nat.zero_descFactorial_succ, zero_mul, zero_mul, add_zero,
        Nat.succ_descFactorial_succ, mul_assoc,
        show 2 * (n + 1) + m - (i + 1) = 2 * n + (m + 1) - i by omega,
        ← ih n (m + 1), Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Nat.succ_descFactorial_succ, show k + 1 + m = k + (m + 1) by omega]
      calc
        _ = ((n + 1).choose (k + 1) * (k + 1)) * k.descFactorial i *
            Nat.fib (k + (m + 1)) := by ac_rfl
        _ = _ := by
          rw [← Nat.add_one_mul_choose_eq]
          ac_rfl

/-- **Weighted binomial Fibonacci sums for the powers one to four.** Let $F_n$ denote the Fibonacci
numbers. For every natural number $N$,
$$\sum_{k=1}^{N} k \binom{N}{k} F_k = N F_{2N-1},$$
$$\sum_{k=1}^{N} k^2 \binom{N}{k} F_k = N F_{2N-1} + N(N-1) F_{2N-2},$$
$$\sum_{k=1}^{N} k^3 \binom{N}{k} F_k = N F_{2N-1} + 3N(N-1) F_{2N-2} + N(N-1)(N-2) F_{2N-3},$$
$$\sum_{k=1}^{N} k^4 \binom{N}{k} F_k = N F_{2N-1} + 7N(N-1) F_{2N-2} +
6N(N-1)(N-2) F_{2N-3} + N(N-1)(N-2)(N-3) F_{2N-4}.$$

Every term with a negative Fibonacci index has coefficient zero.

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Corollary 2.6. -/
public theorem sum_pow_mul_choose_mul_fib_small (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, k * N.choose k * Nat.fib k = N * Nat.fib (2 * N - 1)) ∧
    (∑ k ∈ Finset.Icc 1 N, k ^ 2 * N.choose k * Nat.fib k =
      N * Nat.fib (2 * N - 1) + N * (N - 1) * Nat.fib (2 * N - 2)) ∧
    (∑ k ∈ Finset.Icc 1 N, k ^ 3 * N.choose k * Nat.fib k =
      N * Nat.fib (2 * N - 1) + 3 * N * (N - 1) * Nat.fib (2 * N - 2) +
        N * (N - 1) * (N - 2) * Nat.fib (2 * N - 3)) ∧
    ∑ k ∈ Finset.Icc 1 N, k ^ 4 * N.choose k * Nat.fib k =
      N * Nat.fib (2 * N - 1) + 7 * N * (N - 1) * Nat.fib (2 * N - 2) +
        6 * N * (N - 1) * (N - 2) * Nat.fib (2 * N - 3) +
        N * (N - 1) * (N - 2) * (N - 3) * Nat.fib (2 * N - 4) := by
  -- Expand the power in falling factorials, then evaluate the inner sum at each order.
  have moment (r : ℕ) :
      ∑ k ∈ Finset.Icc 1 N, k ^ r * N.choose k * Nat.fib k =
        ∑ i ∈ Finset.range (r + 1),
          Nat.stirlingSecond r i * (N.descFactorial i * Nat.fib (2 * N - i)) := by
    calc
      _ = ∑ k ∈ Finset.range (N + 1), k ^ r * N.choose k * Nat.fib k := by
        rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos N)]
        simp [Finset.Ico_add_one_right_eq_Icc]
      _ = _ := by
        simp_rw [Nat.pow_eq_sum_stirlingSecond_mul_descFactorial, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        simpa only [Finset.mul_sum, mul_assoc, Nat.add_zero] using
          congrArg (Nat.stirlingSecond r i * ·) (sum_descFactorial_mul_choose_mul_fib_add N i 0)
  simpa [Finset.sum_range_succ, Nat.stirlingSecond, Nat.descFactorial, mul_assoc, mul_comm,
    mul_left_comm] using (show _ ∧ _ ∧ _ ∧ _ from ⟨moment 1, moment 2, moment 3, moment 4⟩)

end MetaMathlibExt
