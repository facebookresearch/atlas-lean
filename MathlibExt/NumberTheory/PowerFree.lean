/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Squarefree

@[expose] public section

/-!
# Power-free natural numbers

This file formalizes the classical notion of `k`-free natural number from
Dietmann–Marmon, *The density of twins of k-free numbers* (arXiv `1307.2481v2`):
for `k ≥ 2`, a positive integer is `k`-free when it is not divisible by the
`k`-th power of any prime.

We prove that divisors of a power-free number are power-free at the same level,
monotonicity in the exponent, and that `2`-free is exactly squarefree.
-/

namespace Nat

/-- **Power-free natural numbers.** Let $k$ be a natural number. A natural number $n$ is
$k$-free when $k \ge 2$, $n > 0$, and $p^k$ does not divide $n$ for any prime $p$. -/
def IsPowerFree (n k : ℕ) : Prop :=
  2 ≤ k ∧ 0 < n ∧ ∀ p : ℕ, p.Prime → ¬p ^ k ∣ n

/-- **Characterization of power-free numbers.** For natural numbers $n$ and $k$, $n$ is $k$-free
if and only if $k \ge 2$, $n > 0$, and $p^k$ does not divide $n$ for any prime $p$. -/
theorem isPowerFree_iff {n k : ℕ} :
    n.IsPowerFree k ↔ 2 ≤ k ∧ 0 < n ∧ ∀ p : ℕ, p.Prime → ¬p ^ k ∣ n :=
  Iff.rfl

/-- **The exponent of a power-free number is at least two.** If a natural number $n$ is $k$-free,
then $k \ge 2$. -/
theorem IsPowerFree.two_le {n k : ℕ} (h : n.IsPowerFree k) : 2 ≤ k :=
  h.1

/-- **Power-free numbers are positive.** If a natural number $n$ is $k$-free, then $n > 0$. -/
theorem IsPowerFree.pos {n k : ℕ} (h : n.IsPowerFree k) : 0 < n :=
  h.2.1

/-- **A k-free number has no prime k-th power divisor.** If a natural number $n$ is $k$-free and
$p$ is a prime, then $p^k$ does not divide $n$. -/
theorem IsPowerFree.not_dvd {n k p : ℕ} (h : n.IsPowerFree k)
    (hp : p.Prime) : ¬p ^ k ∣ n :=
  h.2.2 p hp

/-- **Divisors of k-free numbers are k-free.** If a natural number $n$ is $k$-free and $m$ divides
$n$, then $m$ is $k$-free. -/
theorem IsPowerFree.of_dvd {m n k : ℕ} (h : n.IsPowerFree k)
    (hmn : m ∣ n) : m.IsPowerFree k :=
  ⟨h.two_le, Nat.pos_of_dvd_of_pos hmn h.pos,
    fun _ hp hdiv => h.not_dvd hp (hdiv.trans hmn)⟩

/-- **Power-freeness is monotone in the exponent.** If a natural number $n$ is $k$-free and
$k \le l$, then $n$ is $l$-free. -/
theorem IsPowerFree.mono {n k l : ℕ} (h : n.IsPowerFree k)
    (hkl : k ≤ l) : n.IsPowerFree l := by
  refine ⟨le_trans h.two_le hkl, h.pos, fun p hp hdiv => ?_⟩
  have hpk : p ^ k ∣ p ^ l := by
    obtain ⟨d, rfl⟩ := Nat.le.dest hkl
    rw [pow_add]
    exact dvd_mul_right _ _
  exact h.not_dvd hp (hpk.trans hdiv)

/-- **A natural number is 2-free if and only if it is squarefree.** For every natural number $n$,
$n$ is $2$-free if and only if $n$ is squarefree, that is, $d^2$ divides $n$ only for $d = 1$. -/
theorem isPowerFree_two {n : ℕ} : n.IsPowerFree 2 ↔ Squarefree n := by
  constructor
  · intro h
    rw [squarefree_iff_prime_squarefree]
    intro x hx hdiv
    exact h.not_dvd hx (by rwa [pow_two])
  · intro h
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [squarefree_iff_prime_squarefree] at h
      exact h 2 prime_two (dvd_zero _)
    refine ⟨le_refl 2, Nat.pos_of_ne_zero hn0, fun p hp hdiv => ?_⟩
    rw [squarefree_iff_prime_squarefree] at h
    exact h p hp (by rw [← pow_two]; exact hdiv)

end Nat
