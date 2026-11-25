/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Factorization.Basic

/-!
# `k`-full numbers

Following Li–Wang–Wang–Yi ("Some ergodic theorems over squarefree numbers and
squarefull numbers", Acta Arith. 221 (2025), no. 2, 117-140): for an integer
`k ≥ 2`, a natural number `n` is `k`-full if `p ^ k ∣ n` for every prime factor
`p` of `n`.

The source works with positive naturals: `0` is excluded and `1` is `k`-full
vacuously (it has no prime factors). `Nat.IsKFull` below is total in `k`, so its
values at `k = 0` and `k = 1` are documented and proved explicitly
(`Nat.isKFull_k_eq_zero`, `Nat.isKFull_k_eq_one`); source-facing consequences
(such as `Nat.isKFull_of_two_le`) assume `2 ≤ k`. The `k = 2` specialization
(`Nat.isKFull_two`) is the squarefull/powerful case.

The function `Nat.powerfulPart` keeps exactly the prime-power factors whose
exponents are at least two.
-/

namespace Nat

@[expose]
public section

/-- **$k$-full numbers.** Let $k$ be a natural number. A natural number $n$ is $k$-full if
$n \ne 0$ and $p^k$ divides $n$ for every prime $p$ dividing $n$.

The definition makes sense for every $k$; the source considers only $k \ge 2$. -/
public def IsKFull (k n : ℕ) : Prop :=
  n ≠ 0 ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ k ∣ n

/-- **Powerful part of a natural number.** For a natural number $n \ge 1$ and a prime $p$, let
$v_p(n)$ be the exponent of $p$ in $n$. The powerful (or $2$-full) part of $n$ is the product of
the prime powers $p^{v_p(n)}$ over the primes $p$ dividing $n$ with $v_p(n) \ge 2$ (and $1$ if
there are none). The powerful part of $0$ is defined to be $1$. -/
public def powerfulPart (n : ℕ) : ℕ :=
  Finset.prod (n.primeFactors.filter (fun p => 2 ≤ n.factorization p))
    (fun p ↦ p ^ n.factorization p)

@[simp] public theorem powerfulPart_zero : powerfulPart 0 = 1 := by
  unfold powerfulPart
  simp

@[simp] public theorem powerfulPart_one : powerfulPart 1 = 1 := by
  unfold powerfulPart
  simp

/-- **Prime exponents of the powerful part.** For natural numbers $n$ and $p$, write $v_p(n)$ for
the exponent of $p$ in the prime factorization of $n$ (it is $0$ when $p$ is not a prime factor
of $n$). Then the exponent of $p$ in the powerful part of $n$ equals $v_p(n)$ if $v_p(n) \ge 2$,
and $0$ otherwise. -/
public theorem powerfulPart_factorization (n p : ℕ) :
    (powerfulPart n).factorization p =
      if 2 ≤ n.factorization p then n.factorization p else 0 := by
  unfold powerfulPart
  rw [Nat.factorization_prod_apply (fun q hq =>
    pow_ne_zero _ (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter q hq)).ne_zero)]
  have hterm : ∀ q : ℕ, q ∈ n.primeFactors.filter (fun q => 2 ≤ n.factorization q) →
      (q ^ n.factorization q).factorization p =
        if q = p then n.factorization q else 0 := by
    intro q hq
    have hqprime : q.Prime :=
      Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter q hq)
    by_cases hqp : q = p
    · subst hqp
      rw [if_pos rfl, Nat.factorization_pow_self hqprime]
    · rw [if_neg hqp, Nat.factorization_pow, Finsupp.smul_apply,
        hqprime.factorization, Finsupp.single_apply, if_neg hqp,
        smul_eq_mul, mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  by_cases hp2 : 2 ≤ n.factorization p
  · rw [if_pos hp2]
    have hn0 : n ≠ 0 := by
      rintro rfl
      simp at hp2
    have hprime : p.Prime := by
      by_contra hnp
      have h0 := Nat.factorization_eq_zero_of_not_prime n hnp
      omega
    have hdvd : p ∣ n := by
      by_contra hnd
      have h0 := Nat.factorization_eq_zero_of_not_dvd hnd
      omega
    have hpmem : p ∈ n.primeFactors.filter (fun q => 2 ≤ n.factorization q) := by
      rw [Finset.mem_filter]
      exact ⟨Nat.mem_primeFactors.mpr ⟨hprime, hdvd, hn0⟩, hp2⟩
    rw [if_pos hpmem]
  · rw [if_neg hp2]
    have hnotmem : p ∉ n.primeFactors.filter (fun q => 2 ≤ n.factorization q) :=
      fun h => hp2 (Finset.mem_filter.mp h).2
    rw [if_neg hnotmem]

/-- **The powerful part of $n$ divides $n$.** For every natural number $n$, the powerful part
of $n$ divides $n$. -/
public theorem powerfulPart_dvd (n : ℕ) : powerfulPart n ∣ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [powerfulPart_zero]
    exact one_dvd 0
  · have hpos : powerfulPart n ≠ 0 := by
      unfold powerfulPart
      exact Finset.prod_ne_zero_iff.mpr fun q hq =>
        pow_ne_zero _ (Nat.prime_of_mem_primeFactors
          (Finset.mem_of_mem_filter q hq)).ne_zero
    rw [← Nat.factorization_le_iff_dvd hpos hn]
    intro q
    rw [powerfulPart_factorization]
    split_ifs with h
    · exact le_rfl
    · exact zero_le _

/-- **Factorization criterion for $k$-full numbers.** Let $k$ and $n$ be natural numbers with
$n \ne 0$, and write $v_p(n)$ for the exponent of a prime $p$ in the prime factorization of
$n$. Then $n$ is $k$-full if and only if $k \le v_p(n)$ for every prime $p$ dividing $n$. -/
public theorem isKFull_iff_factorization {k n : ℕ} (hn : n ≠ 0) :
    IsKFull k n ↔ ∀ p : ℕ, p.Prime → p ∣ n → k ≤ n.factorization p := by
  constructor
  · intro h p hp hpn
    exact (hp.pow_dvd_iff_le_factorization hn).mp (h.2 p hp hpn)
  · intro h
    exact ⟨hn, fun p hp hpn => (hp.pow_dvd_iff_le_factorization hn).mpr (h p hp hpn)⟩

/-- **Zero is not $k$-full.** For every natural number $k$, the number $0$ is not $k$-full.

The source works with positive integers. -/
public theorem not_isKFull_zero (k : ℕ) : ¬ IsKFull k 0 := fun h => h.1 rfl

/-- **One is $k$-full.** For every natural number $k$, the number $1$ is $k$-full: it is nonzero
and has no prime divisors. -/
public theorem isKFull_one (k : ℕ) : IsKFull k 1 :=
  ⟨one_ne_zero, fun _p hp hpn => absurd (Nat.dvd_one.mp hpn) hp.ne_one⟩

/-- **The $0$-full numbers.** A natural number $n$ is $0$-full if and only if $n \ne 0$, since
$p^0 = 1$ divides $n$ for every prime $p$.

The source considers only $k$-full numbers with $k \ge 2$. -/
public theorem isKFull_k_eq_zero {n : ℕ} : IsKFull 0 n ↔ n ≠ 0 := by
  constructor
  · exact fun h => h.1
  · intro hn
    refine ⟨hn, fun p _ _ => ?_⟩
    rw [pow_zero]
    exact one_dvd n

/-- **The $1$-full numbers.** A natural number $n$ is $1$-full if and only if $n \ne 0$, since
$p^1 = p$ divides $n$ for every prime $p$ dividing $n$.

The source considers only $k$-full numbers with $k \ge 2$. -/
public theorem isKFull_k_eq_one {n : ℕ} : IsKFull 1 n ↔ n ≠ 0 := by
  constructor
  · exact fun h => h.1
  · intro hn
    exact ⟨hn, fun _ _ hpn => by simpa using hpn⟩

/-- **Monotonicity of $k$-fullness in $k$.** Let $j \le k$ be natural numbers. Every $k$-full
natural number is $j$-full. -/
public theorem isKFull_mono {j k n : ℕ} (hjk : j ≤ k) (h : IsKFull k n) :
    IsKFull j n :=
  ⟨h.1, fun p hp hpn => (pow_dvd_pow p hjk).trans (h.2 p hp hpn)⟩

/-- **For $k \ge 2$, $k$-full numbers are $2$-full.** Let $k \ge 2$ be a natural number. Every
$k$-full natural number is $2$-full. -/
public theorem isKFull_of_two_le {k n : ℕ} (hk : 2 ≤ k) (h : IsKFull k n) :
    IsKFull 2 n :=
  isKFull_mono hk h

/-- **The $2$-full numbers.** A natural number $n$ is $2$-full if and only if $n \ne 0$ and $p^2$
divides $n$ for every prime $p$ dividing $n$. These are the squarefull (also called powerful)
numbers. -/
public theorem isKFull_two {n : ℕ} :
    IsKFull 2 n ↔ n ≠ 0 ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n :=
  Iff.rfl

end
end Nat
