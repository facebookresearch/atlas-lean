/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.NumberTheory.Divisors

/-! # Odd primes and deficient-perfect numbers

A prime's only proper divisor is one. The deficient-perfect equation would then
make the prime divide two, which excludes every odd prime.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.FkPerfectWanted

/-- **$[k,\ell]$-deficient-perfect with a given divisor.** For natural numbers $k$, $\ell$, $n$
and $d$, the number $n$ is $[k,\ell]$-deficient-perfect with divisor $d$ when $d$ is a proper
divisor of $n$ ($d \mid n$ and $d < n$) and $\sigma_k(n) + d^k = n^k + \ell n$, where
$\sigma_k(n) = \sum_{e \mid n} e^k$ is the sum of the $k$-th powers of the divisors of $n$. -/
def KLDeficientPerfectWith (k l n d : ℕ) : Prop :=
  d ∣ n ∧ d < n ∧
    (∑ e ∈ n.divisors, e ^ k) + d ^ k = n ^ k + l * n

/-- **$[k,\ell]$-deficient-perfect numbers.** For natural numbers $k$, $\ell$ and $n$, write
$\sigma_k(n) = \sum_{e \mid n} e^k$. The number $n$ is $[k,\ell]$-deficient-perfect when there is a
divisor $d$ of $n$ with $d < n$ such that $\sigma_k(n) + d^k = n^k + \ell n$. -/
def IsKLDeficientPerfect (k l n : ℕ) : Prop :=
  ∃ d, KLDeficientPerfectWith k l n d

/-- **Odd primes are not $[k,\ell]$-deficient-perfect.** Let $p$ be an odd prime. Then for all
natural numbers $k$ and $\ell$, $p$ is not $[k,\ell]$-deficient-perfect.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Proposition 1. -/
theorem not_isKLDeficientPerfect_of_prime_odd
    (k l p : ℕ) (hp : p.Prime) (hpo : Odd p) :
    ¬ IsKLDeficientPerfect k l p := by
  rintro ⟨d, hd, hlt, hsum⟩
  have hdmem := Nat.mem_divisors.mpr ⟨hd, hp.ne_zero⟩
  rw [hp.divisors] at hdmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdmem
  have hd1 : d = 1 := hdmem.resolve_right fun he => (Nat.ne_of_lt hlt) he
  have h1 : (1 : ℕ) ∉ ({p} : Finset ℕ) := by
    simpa only [Finset.mem_singleton] using hp.ne_one.symm
  simp only [hd1, hp.divisors, Finset.sum_insert h1, Finset.sum_singleton, one_pow] at hsum
  have htwo : 2 = l * p := by omega
  have hd2 : p ∣ 2 := ⟨l, htwo.trans (Nat.mul_comm l p)⟩
  have hle := Nat.le_of_dvd (by decide : 0 < 2) hd2
  have hge := hp.odd_iff.mp hpo
  omega

end MathlibExt.NumberTheory.FkPerfectWanted
