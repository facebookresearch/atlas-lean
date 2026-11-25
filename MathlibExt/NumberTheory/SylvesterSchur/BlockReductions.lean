/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Choose.Dvd
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.NumberTheory.Bertrand
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.NumberTheory.Primorial
public import Mathlib.NumberTheory.SmoothNumbers
public import MathlibExt.NumberTheory.SylvesterSchur.Conditional

/-!
# Block-level reductions for the Sylvester-Schur theorem

This file contains reusable block-product and binomial-coefficient lemmas for the
Sylvester-Schur proof.

## Bertrand base case
-/

@[expose] public section

namespace Nat.SylvesterSchur
namespace Internal

open Finset Nat

/-- **Bertrand's postulate in block form.** For every natural number $n \ge 1$ there are $i < n$
and a prime $p > n$ such that $p$ divides $n + 1 + i$. Thus one of the $n$ consecutive integers
$n + 1, \dots, 2n$ has a prime divisor greater than $n$. -/
lemma bertrand_base {n : ℕ} (hn : 1 ≤ n) :
    ∃ i < n, ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ n + 1 + i := by
  obtain ⟨p, hp_prime, hp_gt, hp_le⟩ :=
    Nat.exists_prime_lt_and_le_two_mul n (Nat.pos_iff_ne_zero.mp (by omega))
  refine ⟨p - (n + 1), ?_, p, hp_prime, hp_gt, ?_⟩
  · omega
  · rw [Nat.add_sub_cancel' (by omega : n + 1 ≤ p)]

/-!
### From block divisibility to binomial divisibility
-/

/-- **Prime divisors above $n$ of a block term divide the binomial coefficient.** Let $n$, $k$
and $j$ be natural numbers with $j < n$, and let $r$ be a prime with $r > n$. If $r$ divides
$k + j$, then $r$ divides $\binom{k+n-1}{n}$. -/
lemma prime_dvd_seq_implies_choose {n k r : ℕ} (hr : r.Prime) (hr_gt : n < r)
    (j : ℕ) (hj : j < n) (hdvd : r ∣ k + j) :
    r ∣ Nat.choose (k + n - 1) n :=
  prime_dvd_choose_of_dvd_consecutive hr hr_gt hj hdvd

/-- **Primes above $n$ in the block divide the block binomial coefficient.** Let $n$ and $k$
be natural numbers and let $p$ be a prime with $p > n$ and $k \le p \le k + n - 1$. Then $p$
divides $\binom{k+n-1}{n}$. -/
lemma prime_dvd_choose_of_mem_interval {n k p : ℕ} (hp : p.Prime) (hp_gt : n < p)
    (hp_ge : k ≤ p) (hp_le : p ≤ k + n - 1) :
    p ∣ Nat.choose (k + n - 1) n :=
  hp.dvd_choose hp_gt (by omega) hp_le

private lemma exists_prime_dvd_choose_of_large_prime_dvd_term {n k i p : ℕ}
    (hi : i < n) (hp : p.Prime) (hp_gt : n < p) (hp_dvd : p ∣ k + i) :
    ∃ q : ℕ, q.Prime ∧ n < q ∧ q ∣ Nat.choose (k + n - 1) n := by
  exact ⟨p, hp, hp_gt, prime_dvd_seq_implies_choose hp hp_gt i hi hp_dvd⟩

/-- **Large prime divisors pass from a block to its binomial coefficient.** Let $n$ and $k$ be
natural numbers. If some prime $p > n$ divides $k + i$ for some $i < n$, then some prime $q > n$
divides $\binom{k + n - 1}{n}$. -/
lemma exists_prime_dvd_choose_of_large_prime_dvd_block {n k : ℕ}
    (hblock : ∃ i < n, ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ k + i) :
    ∃ q : ℕ, q.Prime ∧ n < q ∧ q ∣ Nat.choose (k + n - 1) n := by
  obtain ⟨i, hi, p, hp, hp_gt, hp_dvd⟩ := hblock
  exact exists_prime_dvd_choose_of_large_prime_dvd_term hi hp hp_gt hp_dvd

private lemma block_term_prime_factors_le_of_no_large_prime_dvd_block {n k : ℕ}
    (hblock : ¬ ∃ i < n, ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ k + i)
    {i p : ℕ} (hi : i < n) (hp : p.Prime) (hp_dvd : p ∣ k + i) :
    p ≤ n := by
  by_contra hp_le
  push Not at hp_le
  exact hblock ⟨i, hi, p, hp, by omega, hp_dvd⟩

private lemma block_term_mem_smoothNumbers_succ_of_no_large_prime_dvd_block {n k i : ℕ}
    (hblock : ¬ ∃ i < n, ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ k + i)
    (hi : i < n) :
    k + i ∈ Nat.smoothNumbers (n + 1) := by
  rw [Nat.mem_smoothNumbers']
  intro p hp hp_dvd
  have hp_le :
      p ≤ n :=
    block_term_prime_factors_le_of_no_large_prime_dvd_block hblock hi hp hp_dvd
  omega

private lemma block_length_le_smoothNumbersUpTo_card_of_no_large_prime_dvd_block
    {n k : ℕ}
    (hblock : ¬ ∃ i < n, ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ k + i) :
    n ≤ (Nat.smoothNumbersUpTo (k + n - 1) (n + 1)).card := by
  apply Finset.le_card_of_inj_on_range (fun i => k + i)
  · intro i hi
    rw [Nat.mem_smoothNumbersUpTo]
    have hle_top : k + i ≤ k + n - 1 := by
      calc
        k + i ≤ k + (n - 1) := Nat.add_le_add_left (Nat.le_sub_one_of_lt hi) k
        _ = k + n - 1 := by omega
    exact ⟨hle_top, block_term_mem_smoothNumbers_succ_of_no_large_prime_dvd_block hblock hi⟩
  · intro a _ha b _hb hab
    exact Nat.add_left_cancel hab

private lemma block_length_le_smoothNumbersUpTo_bound_of_no_large_prime_dvd_block
    {n k : ℕ}
    (hblock : ¬ ∃ i < n, ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ k + i) :
    n ≤ 2 ^ Nat.primeCounting n * Nat.sqrt (k + n - 1) := by
  have h :=
    (block_length_le_smoothNumbersUpTo_card_of_no_large_prime_dvd_block hblock).trans
    (Nat.smoothNumbersUpTo_card_le (k + n - 1) (n + 1))
  rw [Nat.primeCounting, ← Nat.primesBelow_card_eq_primeCounting' (n + 1)]
  exact h

private lemma exists_dvd_block_or_dvd_recent_pred {n k p : ℕ} (hn : 0 < n) (hp_gt : n < p) :
    (∃ i < n, p ∣ k + i) ∨
      ∃ j : ℕ, 1 ≤ j ∧ j ≤ p - n ∧ p ∣ k - j := by
  have hp_pos : 0 < p := by omega
  by_cases hmod0 : k % p = 0
  · left
    exact ⟨0, hn, by
      rw [Nat.dvd_iff_mod_eq_zero]
      simp [hmod0]⟩
  · let r := k % p
    have hr_lt : r < p := Nat.mod_lt k hp_pos
    have hr_pos : 0 < r := Nat.pos_of_ne_zero hmod0
    by_cases hhit : p - r < n
    · left
      refine ⟨p - r, hhit, ?_⟩
      have hsum_mod : k + (p - r) ≡ r + (p - r) [MOD p] :=
        (Nat.mod_modEq k p).symm.add_right (p - r)
      have hsum_eq : r + (p - r) = p := by omega
      exact Nat.modEq_zero_iff_dvd.mp <| hsum_mod.trans <| by
        simp [hsum_eq]
    · right
      have hr_le_pred : r ≤ p - n := by omega
      have hr_le_k : r ≤ k := Nat.mod_le k p
      refine ⟨r, by omega, hr_le_pred, ?_⟩
      have hmodEq : r ≡ k [MOD p] := by
        simpa [r] using Nat.mod_modEq k p
      exact (Nat.modEq_iff_dvd' hr_le_k).mp hmodEq

/-- **A block term divisible by the block length plus two.** Let $n \ge 1$ and $k$ be natural
numbers and let $s = n + 2$. If $s$ divides neither $k - 1$ nor $k - 2$ (natural-number
differences, truncated at $0$), then $s$ divides $k + i$ for some $i < n$.

The number $s$ is not assumed to be prime. -/
lemma exists_dvd_block_of_succ_succ_prime_not_dvd_pred {n k s : ℕ} (hn : 0 < n)
    (hsn : s = n + 2) (hnot_one : ¬ s ∣ k - 1) (hnot_two : ¬ s ∣ k - 2) :
    ∃ i < n, s ∣ k + i := by
  rcases exists_dvd_block_or_dvd_recent_pred (n := n) (k := k) (p := s) hn (by omega)
      with hblock | hpred
  · exact hblock
  obtain ⟨j, hj1, hjle, hjdvd⟩ := hpred
  rcases (by omega : j = 1 ∨ j = 2) with rfl | rfl
  · exact (hnot_one hjdvd).elim
  · exact (hnot_two hjdvd).elim

/-! ### Binomial criteria from block estimates -/

/-- **Sylvester–Schur criterion for blocks with a large start.** Let $2 \le n < k$ be natural
numbers with $n! \cdot 2^{n-1} < k$. Then some prime $p > n$ divides $\binom{k + n - 1}{n}$. -/
lemma exists_prime_dvd_choose_of_large_start {n k : ℕ} (hn : 2 ≤ n) (hk : n < k)
    (hlarge : n ! * 2 ^ (n - 1) < k) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ Nat.choose (k + n - 1) n := by
  obtain ⟨i, hi, p, hp, hp_gt, hp_dvd⟩ := consecutive_of_large_start hn hk hlarge
  exact ⟨p, hp, by omega, prime_dvd_seq_implies_choose hp (by omega) i hi hp_dvd⟩

/-- **Sylvester–Schur criterion from the half-exponent bound.** Let $1 \le n < k$ be natural
numbers and put $N = k + n - 1$. If $n! \cdot N^{\lfloor n/2 \rfloor + 1} < k^n$, then some prime
$p > n$ divides $\binom{N}{n}$. -/
lemma exists_prime_dvd_choose_of_half_bound {n k : ℕ} (hn : 1 ≤ n) (hk : n < k)
    (hbound : n ! * (k + n - 1) ^ (n / 2 + 1) < k ^ n) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ Nat.choose (k + n - 1) n := by
  obtain ⟨i, hi, p, hp, hp_gt, hp_dvd⟩ :=
    consecutive_of_factorial_mul_top_pow_half_add_one_lt_start_pow hn hk hbound
  exact ⟨p, hp, by omega, prime_dvd_seq_implies_choose hp (by omega) i hi hp_dvd⟩

/-- **Blocks without large prime divisors start at most at $n^2$.** Let $n \ge 38$ and $k$ be
natural numbers. If none of the $n$ consecutive integers $k, k+1, \dots, k+n-1$ has a prime
divisor greater than $n$, then $k \le n^2$. -/
lemma start_le_quadratic_of_no_large_prime_dvd_block {n k : ℕ} (hn : 38 ≤ n)
    (hblock : ¬ ∃ i < n, ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ k + i) :
    k ≤ n ^ 2 := by
  by_contra hkquad
  push Not at hkquad
  obtain ⟨i, hi, p, hp, hp_gt, hp_dvd⟩ := consecutive_of_quadratic_start hn hkquad
  exact hblock ⟨i, hi, p, hp, by omega, hp_dvd⟩

/-- **Sylvester–Schur criterion from the prime-counting bound.** Let $1 \le n < k$ be natural
numbers, put $N = k + n - 1$, and let $\pi(n)$ be the number of primes at most $n$. If
$n! \cdot N^{\pi(n)} < k^n$, then some prime $p > n$ divides $\binom{N}{n}$. -/
lemma exists_prime_dvd_choose_of_primeCounting_bound {n k : ℕ} (hn : 1 ≤ n)
    (hk : n < k) (hbound : n ! * (k + n - 1) ^ Nat.primeCounting n < k ^ n) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ Nat.choose (k + n - 1) n := by
  obtain ⟨i, hi, p, hp, hp_gt, hp_dvd⟩ :=
    consecutive_of_factorial_mul_top_pow_primeCounting_lt_start_pow hn hk hbound
  exact ⟨p, hp, by omega, prime_dvd_seq_implies_choose hp (by omega) i hi hp_dvd⟩

/-- **Large prime divisor of the block binomial coefficient from the square-root primorial
bound.** Let $n \ge 1$ and $k > n$ be natural numbers, write $N = k + n - 1$, let
$\lfloor\sqrt{N}\rfloor$ be the integer square root of $N$ and let $P$ be the product of all
primes at most $n$. If $n! \cdot N^{\lfloor\sqrt{N}\rfloor + 1} \cdot P < k^n$, then some prime
$p > n$ divides $\binom{N}{n}$. -/
lemma exists_prime_dvd_choose_of_sqrt_primorial_bound {n k : ℕ} (hn : 1 ≤ n)
    (hk : n < k)
    (hbound :
      n ! * ((k + n - 1) ^ (Nat.sqrt (k + n - 1) + 1) * primorial n) < k ^ n) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ Nat.choose (k + n - 1) n := by
  obtain ⟨i, hi, p, hp, hp_gt, hp_dvd⟩ :=
    consecutive_of_factorial_mul_top_pow_sqrt_mul_primorial_lt_start_pow hn hk hbound
  exact ⟨p, hp, by omega, prime_dvd_seq_implies_choose hp (by omega) i hi hp_dvd⟩

/-- **Sylvester–Schur criterion from the Erdős layer bound.** Let $1 \le n < k$ be natural
numbers, put $N = k + n - 1$ and $L = \lfloor \log_2 N \rfloor$, and write $m\#$ for the product
of the primes at most $m$. If
$$n! \cdot n\# \cdot \prod_{i=2}^{L} \lfloor N^{1/i} \rfloor\# < k^n,$$
then some prime $p > n$ divides $\binom{N}{n}$. -/
lemma exists_prime_dvd_choose_of_erdos_layers_bound {n k : ℕ} (hn : 1 ≤ n)
    (hk : n < k)
    (hbound :
      n ! *
          (∏ j ∈ Finset.range (Nat.log 2 (k + n - 1)),
            if j = 0 then primorial n else primorial (Nat.nthRoot (j + 1) (k + n - 1))) <
        k ^ n) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ Nat.choose (k + n - 1) n := by
  obtain ⟨i, hi, p, hp, hp_gt, hp_dvd⟩ :=
    consecutive_of_factorial_mul_prod_erdos_layers_lt_start_pow hn hk hbound
  exact ⟨p, hp, by omega, prime_dvd_seq_implies_choose hp (by omega) i hi hp_dvd⟩

/-- **Sylvester–Schur criterion from the Erdős layer bound with a one-third first layer.** Let
$n < k$ be natural numbers, put $N = k + n - 1$ and $L = \lfloor \log_2 N \rfloor$, and assume
$N \ge 6$. Write $m\#$ for the product of the primes at most $m$. If
$$n! \cdot \lfloor N/3 \rfloor\# \cdot \prod_{i=2}^{L} \lfloor N^{1/i} \rfloor\# < k^n,$$
then some prime $p > n$ divides $\binom{N}{n}$. -/
lemma exists_prime_dvd_choose_of_erdos_div_three_layers_bound {n k : ℕ}
    (hk : n < k) (hN6 : 6 ≤ k + n - 1)
    (hbound :
      n ! *
          (∏ j ∈ Finset.range (Nat.log 2 (k + n - 1)),
            if j = 0 then primorial ((k + n - 1) / 3)
            else primorial (Nat.nthRoot (j + 1) (k + n - 1))) <
        k ^ n) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ Nat.choose (k + n - 1) n := by
  obtain ⟨i, hi, p, hp, hp_gt, hp_dvd⟩ :=
    consecutive_of_factorial_mul_prod_erdos_div_three_layers_lt_start_pow hk hN6 hbound
  exact ⟨p, hp, by omega, prime_dvd_seq_implies_choose hp (by omega) i hi hp_dvd⟩

/-- **Sylvester–Schur criterion from the coarse power-of-four Erdős bound.** Let $1 \le n < k$ be
natural numbers and put $N = k + n - 1$. If
$$n! \cdot 4^{n + \lfloor \sqrt N \rfloor \lfloor \log_2 N \rfloor} < k^n,$$
then some prime $p > n$ divides $\binom{N}{n}$. -/
lemma exists_prime_dvd_choose_of_erdos_layers_four_pow_bound {n k : ℕ}
    (hn : 1 ≤ n) (hk : n < k)
    (hbound :
      n ! *
          4 ^ (n + Nat.sqrt (k + n - 1) * Nat.log 2 (k + n - 1)) <
        k ^ n) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ Nat.choose (k + n - 1) n := by
  apply exists_prime_dvd_choose_of_erdos_layers_bound hn hk
  have hprod := erdos_layers_le_four_pow (k + n - 1) n
  exact (Nat.mul_le_mul_left (n !) hprod).trans_lt hbound

/-- **Sylvester–Schur criterion from the three-layer power-of-four Erdős bound.** Let
$1 \le n < k$ be natural numbers and put $N = k + n - 1$. If
$$n! \cdot 4^{n+\lfloor\sqrt N\rfloor+\lfloor N^{1/3}\rfloor\lfloor\log_2 N\rfloor} < k^n,$$
then some prime $p > n$ divides $\binom{N}{n}$. -/
lemma exists_prime_dvd_choose_of_erdos_layers_three_layers_bound {n k : ℕ}
    (hn : 1 ≤ n) (hk : n < k)
    (hbound :
      n ! *
          4 ^ (n + Nat.sqrt (k + n - 1) +
            Nat.nthRoot 3 (k + n - 1) * Nat.log 2 (k + n - 1)) <
        k ^ n) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ Nat.choose (k + n - 1) n := by
  apply exists_prime_dvd_choose_of_erdos_layers_bound hn hk
  have hprod := erdos_layers_le_four_pow_three_layers (k + n - 1) n
  exact (Nat.mul_le_mul_left (n !) hprod).trans_lt hbound

/-- **Large prime divisor of the block binomial coefficient from the smooth-number count.**
Let $n$ and $k$ be natural numbers, let $\pi(n)$ be the number of primes at most $n$, and let
$\lfloor\sqrt{k+n-1}\rfloor$ be the integer square root. If
$2^{\pi(n)} \lfloor\sqrt{k+n-1}\rfloor < n$, then some prime $p > n$ divides
$\binom{k+n-1}{n}$.

Otherwise all $n$ integers $k, \dots, k+n-1$ would be positive, at most $k+n-1$ and free of
prime factors greater than $n$, and there are at most $2^{\pi(n)} \lfloor\sqrt{k+n-1}\rfloor$
such integers. -/
lemma exists_prime_dvd_choose_of_smooth_count_bound {n k : ℕ}
    (hbound : 2 ^ Nat.primeCounting n * Nat.sqrt (k + n - 1) < n) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ Nat.choose (k + n - 1) n := by
  by_cases hblock : ∃ i < n, ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ k + i
  · exact exists_prime_dvd_choose_of_large_prime_dvd_block hblock
  · have hle :=
      block_length_le_smoothNumbersUpTo_bound_of_no_large_prime_dvd_block (n := n) (k := k)
        hblock
    omega


end Internal
end Nat.SylvesterSchur
