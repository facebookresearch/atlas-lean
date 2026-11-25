/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Tactic.Ring

/-!
# Classical core of Shor's factoring algorithm

The quantum part of Shor's algorithm finds the multiplicative order `r` of a
number `a` modulo `N`. This file proves the classical post-processing step:
from such an order with `r` even and `a ^ (r / 2) ≢ ±1 (mod N)`, the greatest
common divisor `gcd (a ^ (r / 2) - 1) N` is a nontrivial factor of `N`.
-/

@[expose] public section

namespace Cslib.Shor

/-- **Shor's order-to-factor reduction.** Let $N$, $a$ and $r$ be natural numbers with $N > 1$ and
$a \ge 1$. Suppose $a^r \equiv 1 \pmod{N}$, $r$ is even, $a^{r/2} \not\equiv 1 \pmod{N}$ and
$a^{r/2} \not\equiv -1 \pmod{N}$. Then $d = \gcd(a^{r/2} - 1, N)$, the value computed by the
classical post-processing, is a nontrivial factor of $N$: $d$ divides $N$ and $1 < d < N$.

In the algorithm $r$ is the multiplicative order of $a$ modulo $N$, so the hypothesis
$a^{r/2} \not\equiv 1 \pmod{N}$ is the minimality of the order, and the hypothesis
$a^{r/2} \not\equiv -1 \pmod{N}$ is the "good unit" condition. This module assumes that
condition; it does not prove its prevalence among units.

Source: P. W. Shor, Polynomial-time algorithms for prime factorization and
discrete logarithms on a quantum computer, SIAM J. Comput. 26 (1997),
1484–1509, Section 5; M. A. Nielsen and I. L. Chuang, Quantum Computation and
Quantum Information, Cambridge University Press, 2000, Section 5.3. -/
theorem gcd_factor_of_order {N a r : ℕ} (hN : 1 < N) (ha : 1 ≤ a)
    (hord : N ∣ a ^ r - 1) (hr : Even r)
    (hne1 : ¬ N ∣ a ^ (r / 2) - 1) (hnem1 : ¬ N ∣ a ^ (r / 2) + 1) :
    Nat.gcd (a ^ (r / 2) - 1) N ∣ N ∧ 1 < Nat.gcd (a ^ (r / 2) - 1) N ∧
      Nat.gcd (a ^ (r / 2) - 1) N < N := by
  -- `b = a ^ (r / 2)` satisfies `b ^ 2 = a ^ r`.
  obtain ⟨k, hk⟩ := hr
  have hr2 : r / 2 = k := by omega
  have hbsq : (a ^ (r / 2)) ^ 2 = a ^ r := by
    rw [hr2, hk, pow_add, pow_two]
  -- `b ≥ 1`, so the truncated subtraction below is exact.
  have hb1 : 1 ≤ a ^ (r / 2) := Nat.one_le_pow _ _ ha
  -- Difference of squares: `(b - 1) * (b + 1) = b ^ 2 - 1`.
  have hsq : (a ^ (r / 2) - 1) * (a ^ (r / 2) + 1) =
      (a ^ (r / 2)) ^ 2 - 1 := by
    cases hb : a ^ (r / 2) with
    | zero => omega
    | succ c =>
      rw [pow_two]
      have key : (c + 1 - 1) * (c + 1 + 1) + 1 = (c + 1) * (c + 1) := by
        rw [Nat.add_sub_cancel]
        ring
      omega
  -- `N` divides the product `(b - 1) * (b + 1)`.
  have hNprod : N ∣ (a ^ (r / 2) - 1) * (a ^ (r / 2) + 1) := by
    rw [hsq, hbsq]
    exact hord
  -- The gcd is the factor.
  refine ⟨Nat.gcd_dvd_right _ _, ?_, ?_⟩
  · -- `1 < gcd`: it is neither `0` nor `1`.
    rw [Nat.one_lt_iff_ne_zero_and_ne_one]
    refine ⟨?_, ?_⟩
    · intro h0
      have hdvd : Nat.gcd (a ^ (r / 2) - 1) N ∣ N := Nat.gcd_dvd_right _ _
      rw [h0] at hdvd
      have hN0 : N = 0 := Nat.eq_zero_of_zero_dvd hdvd
      omega
    · intro h1
      have hcop : Nat.Coprime (a ^ (r / 2) - 1) N := h1
      exact hnem1 (hcop.symm.dvd_of_dvd_mul_left hNprod)
  · -- `gcd < N`: it divides `N` and is not `N`.
    have hle : Nat.gcd (a ^ (r / 2) - 1) N ≤ N :=
      Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right _ _)
    refine lt_of_le_of_ne hle ?_
    intro hN'
    have hdvd : Nat.gcd (a ^ (r / 2) - 1) N ∣ a ^ (r / 2) - 1 :=
      Nat.gcd_dvd_left _ _
    rw [hN'] at hdvd
    exact hne1 hdvd

/-- **Shor's order-to-factor reduction, existential form.** Let $N$, $a$ and $r$ be natural
numbers with $N > 1$ and $a \ge 1$. If $a^r \equiv 1 \pmod{N}$, $r$ is even,
$a^{r/2} \not\equiv 1 \pmod{N}$ and $a^{r/2} \not\equiv -1 \pmod{N}$, then $N$ has a nontrivial
factor: there is a natural number $d$ with $d \mid N$ and $1 < d < N$.

One such factor is $\gcd(a^{r/2} - 1, N)$. -/
theorem exists_factor_of_order {N a r : ℕ} (hN : 1 < N) (ha : 1 ≤ a)
    (hord : N ∣ a ^ r - 1) (hr : Even r)
    (hne1 : ¬ N ∣ a ^ (r / 2) - 1) (hnem1 : ¬ N ∣ a ^ (r / 2) + 1) :
    ∃ d, d ∣ N ∧ 1 < d ∧ d < N :=
  ⟨_, gcd_factor_of_order hN ha hord hr hne1 hnem1⟩

end Cslib.Shor
