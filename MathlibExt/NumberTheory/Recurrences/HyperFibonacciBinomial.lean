/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.HyperLeonardo
public import MathlibExt.NumberTheory.Recurrences.GeneralizedHyperFibonacci
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Hyper-Fibonacci binomial-sum formulas

## References

* Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
  INTEGERS 24 (2024), Article A70, pp. 1–31, Theorem 3, Equation (2.8).
* Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of Toeplitz
  Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer Sequences 29
  (2026), Article 26.2.5, pp. 1–16, Lemma 5, Equation (8), citing Ait-Amrane and Behloul.
* Lyes Ait-Amrane and Djilali Behloul, *Cassini-Like Formula for Generalized Hyper-Fibonacci
  Numbers*, Journal of Integer Sequences 25 (2022), Article 22.3.2, pp. 1–16, Proposition 2,
  Equation (9).
-/

namespace MetaMathlibExt

@[expose] public section

private def hyperFibonacciCorrection (p a b : ℤ) (r m : ℕ) : ℤ :=
  ∑ k ∈ Finset.range r,
    ((m + (r - 1 - k)).choose (r - 1 - k) : ℤ) * generalizedPFibonacci p a b (2 * k + 1)

private theorem hyperFibonacciCorrection_zero (p a b : ℤ) (r : ℕ) :
    hyperFibonacciCorrection p a b r 0 =
      ∑ k ∈ Finset.range r, generalizedPFibonacci p a b (2 * k + 1) := by
  simp only [hyperFibonacciCorrection, zero_add, Nat.choose_self, Nat.cast_one, one_mul]

private theorem hyperFibonacciCorrection_step (p a b : ℤ) (r m : ℕ) :
    hyperFibonacciCorrection p a b (r + 1) (m + 1) =
      hyperFibonacciCorrection p a b (r + 1) m + hyperFibonacciCorrection p a b r (m + 1) := by
  unfold hyperFibonacciCorrection
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [Nat.add_sub_cancel, Nat.sub_self, Nat.choose_zero_right, Nat.cast_one, one_mul]
  rw [add_right_comm, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkr := Finset.mem_range.mp hk
  have hdiff : r - k = (r - 1 - k) + 1 := by omega
  rw [hdiff, show m + 1 + (r - 1 - k + 1) = (m + 1 + (r - 1 - k)) + 1 by omega,
    Nat.choose_succ_succ', Nat.cast_add]
  rw [show m + (r - 1 - k + 1) = m + 1 + (r - 1 - k) by omega]
  ring

private theorem generalizedPFibonacci_even (p a b : ℤ) (r : ℕ) :
    generalizedPFibonacci p a b (2 * r) =
      a + p * ∑ k ∈ Finset.range r, generalizedPFibonacci p a b (2 * k + 1) := by
  induction r with
  | zero => simp [generalizedPFibonacci]
  | succ r ih =>
    rw [show 2 * (r + 1) = 2 * r + 2 by omega, generalizedPFibonacci, ih, Finset.sum_range_succ]
    ring

private theorem hyperFibonacci_integer_formula (p a b : ℤ) (r m : ℕ) :
    generalizedHyperFibonacci p a b r m = generalizedPFibonacci p a b (m + 2 * r) -
      p ^ (m + 1) * hyperFibonacciCorrection p a b r m := by
  induction r generalizing m with
  | zero => simp [hyperFibonacciCorrection, generalizedHyperFibonacci]
  | succ r hr =>
    induction m with
    | zero =>
      rw [(generalizedHyperFibonacci_zero_one p a b (r + 1)).1,
        hyperFibonacciCorrection_zero, zero_add, pow_one, generalizedPFibonacci_even]
      ring
    | succ m hm =>
      rw [generalizedHyperFibonacci_succ_succ, hm, hr (m + 1), hyperFibonacciCorrection_step,
        show m + 1 + 2 * (r + 1) = (m + 1 + 2 * r) + 2 by omega, generalizedPFibonacci,
        show m + 1 + 2 * r + 1 = m + 2 * (r + 1) by omega, pow_succ]
      ring

/-- **A binomial-sum formula for generalized hyper-Fibonacci numbers.** Let $p, a, b$ be integers
with $p \ne 0$, let $W_{p,n}$ denote the generalized Fibonacci sequence and $W^{(r)}_{p,n}$ the
generalized hyper-Fibonacci numbers. For all natural numbers $r$ and $n$ with $1 \le r \le n$, the
following identity of rational numbers holds:
$$
W^{(r)}_{p,n-r} = W_{p,n+r} - \frac{p^n}{p^{r-1}} \sum_{k=0}^{r-1} \binom{n-k-1}{r-k-1} W_{p,2k+1}.
$$

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of
Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer
Sequences 29 (2026), Article 26.2.5, Lemma 5, equation (8), quoting Ait-Amrane et al.
(`jis-2026-26.2.5-lem-5`). -/
public theorem generalizedHyperFibonacci_sub_eq_sub (p a b : ℤ) (hp : p ≠ 0) (r n : ℕ)
    (hr : 1 ≤ r) (hrn : r ≤ n) :
    (generalizedHyperFibonacci p a b r (n - r) : ℚ) =
      generalizedPFibonacci p a b (n + r) -
        (p : ℚ) ^ n * (∑ k ∈ Finset.range r,
          ((n - k - 1).choose (r - k - 1) : ℚ) * generalizedPFibonacci p a b (2 * k + 1)) /
          (p : ℚ) ^ (r - 1) := by
  have he := congrArg (fun z : ℤ => (z : ℚ)) (hyperFibonacci_integer_formula p a b r (n - r))
  unfold hyperFibonacciCorrection at he
  push_cast at he
  rw [show n - r + 2 * r = n + r by omega] at he
  have hsum : (∑ k ∈ Finset.range r,
      (((n - r + (r - 1 - k)).choose (r - 1 - k) : ℕ) : ℚ) *
        (generalizedPFibonacci p a b (2 * k + 1) : ℚ)) =
      ∑ k ∈ Finset.range r,
        ((n - k - 1).choose (r - k - 1) : ℚ) * generalizedPFibonacci p a b (2 * k + 1) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkr := Finset.mem_range.mp hk
    rw [show n - r + (r - 1 - k) = n - k - 1 by omega,
      show r - 1 - k = r - k - 1 by omega]
  rw [hsum] at he
  have hpow : (p : ℚ) ^ n = (p : ℚ) ^ (n - r + 1) * (p : ℚ) ^ (r - 1) := by
    rw [← pow_add, show n - r + 1 + (r - 1) = n by omega]
  rw [he, hpow]
  have hp' : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  field_simp [hp']

open Finset in
private def hyperFibonacciEvenCorrection (r n : ℕ) : ℤ :=
  ∑ k ∈ range r, ((n + k - 1).choose k : ℤ) * Nat.fib (2 * (r - k))

private theorem hyperFibonacciEvenCorrection_zero (r : ℕ) :
    hyperFibonacciEvenCorrection (r + 1) 0 = Nat.fib (2 * (r + 1)) := by
  rw [hyperFibonacciEvenCorrection, Finset.sum_range_succ']
  simp only [zero_add, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
  rw [Finset.sum_eq_zero, zero_add]
  intro k _
  rw [Nat.choose_eq_zero_of_lt (by omega : k + 1 - 1 < k + 1), Nat.cast_zero, zero_mul]

private theorem hyperFibonacciEvenCorrection_step (r n : ℕ) :
    hyperFibonacciEvenCorrection (r + 1) (n + 1) =
      hyperFibonacciEvenCorrection (r + 1) n + hyperFibonacciEvenCorrection r (n + 1) := by
  unfold hyperFibonacciEvenCorrection
  -- Split off the constant term before applying Pascal's identity at positive indices.
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero, Nat.succ_sub_succ_eq_sub]
  rw [add_right_comm, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show n + 1 + (k + 1) - 1 = (n + k) + 1 by omega,
    show n + (k + 1) - 1 = n + k by omega, show n + 1 + k - 1 = n + k by omega,
    Nat.choose_succ_succ, Nat.cast_add, add_mul, add_comm]

open Finset in
/-- **Hyperfibonacci numbers in terms of Fibonacci numbers.** Let $F_k$ denote the $k$th Fibonacci
number and $F^{(r)}_n$ the hyperfibonacci numbers, given by $F^{(0)}_n = F_n$ and
$F^{(r+1)}_n = \sum_{k=0}^{n} F^{(r)}_k$. For all natural numbers $r$ and $n$,
$$F^{(r)}_n = F_{n+2r} - \sum_{k=0}^{r-1} \binom{n + k - 1}{k} F_{2(r-k)}.$$

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Theorem 3, Equation (2.8) (`integers-2024-A70-thm-3`). -/
public theorem hyperFibonacci_eq_fib_sub_sum (r n : ℕ) :
    (hyperFibonacci r n : ℤ) =
      Nat.fib (n + 2 * r) - ∑ k ∈ range r, ((n + k - 1).choose k * Nat.fib (2 * (r - k)) : ℕ) := by
  simp only [Nat.cast_sum, Nat.cast_mul]
  change (hyperFibonacci r n : ℤ) = _ - hyperFibonacciEvenCorrection r n
  have hzero (s : ℕ) : hyperFibonacci s 0 = 0 := by
    induction s with
    | zero => simp [hyperFibonacci_zero]
    | succ s ih => simpa only [hyperFibonacci_succ, Nat.zero_add, Finset.sum_range_one] using ih
  induction r generalizing n with
  | zero => simp [hyperFibonacci_zero, hyperFibonacciEvenCorrection]
  | succ r hr =>
    induction n with
    | zero => simp [hzero, hyperFibonacciEvenCorrection_zero]
    | succ n hn =>
      have hstep : (hyperFibonacci (r + 1) (n + 1) : ℤ) =
          (hyperFibonacci (r + 1) n : ℤ) + hyperFibonacci r (n + 1) := by
        rw [hyperFibonacci_succ, Finset.sum_range_succ, Nat.cast_add, ← hyperFibonacci_succ]
      rw [hstep, hn, hr (n + 1), hyperFibonacciEvenCorrection_step,
        show n + 1 + 2 * (r + 1) = (n + 1 + 2 * r) + 2 by omega, Nat.fib_add_two, Nat.cast_add,
        show n + 1 + 2 * r + 1 = n + 2 * (r + 1) by omega]
      ring

end

end MetaMathlibExt
