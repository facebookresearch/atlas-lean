/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.SmoothNumbers

/-!
# Rough natural numbers

This file defines the source-faithful notion of `z`-rough natural number used in
Mayank Pandey, *Numbers with at most 2 prime factors in short arithmetic
progressions* (arXiv `2307.14890v1`): footnote on line 91 of `hybrid.tex` says
that by a `z`-rough number, one means a number with no prime factors `≤ z`.

The candidate number and the roughness bound are both natural numbers. Zero is
not rough. The unit `1` is rough for every bound by vacuity; this agrees with
Fred B. Holt, *On the counts of p-rough numbers* (arXiv `2308.07570`), which
explicitly includes `1` as a `p`-rough number.

Mathlib's `Nat.roughNumbersUpTo N k` is only the positive complement of
`k`-smoothness below `N` (a number with at least one prime factor `≥ k`); it is
not the source predicate, which demands that *every* prime factor exceed the
bound. We bridge to it below without conflating the two notions.
-/

@[expose] public section

namespace Nat

/-- **Rough numbers.** Let $n$ and $k$ be natural numbers. Then $n$ is $k$-rough if $n \neq 0$
and every prime $p$ dividing $n$ satisfies $k < p$; that is, $n$ is positive and has no prime
factor at most $k$.

In particular $0$ is not rough, and $1$ is $k$-rough for every $k$ by vacuity.

Source: Pandey, arXiv 2307.14890v1, footnote definition (`hybrid.tex` line 91). -/
def IsRough (n k : ℕ) : Prop :=
  n ≠ 0 ∧ ∀ p : ℕ, p.Prime → p ∣ n → k < p

/-- **Characterization of rough numbers.** For natural numbers $n$ and $k$, $n$ is $k$-rough
if and only if $n \neq 0$ and every prime $p$ dividing $n$ satisfies $k < p$. -/
theorem isRough_iff {n k : ℕ} :
    n.IsRough k ↔ n ≠ 0 ∧ ∀ p : ℕ, p.Prime → p ∣ n → k < p :=
  Iff.rfl

/-- **Rough numbers are nonzero.** For every natural number $k$, every $k$-rough natural number $n$
satisfies $n \ne 0$. -/
theorem IsRough.ne_zero {n k : ℕ} (h : n.IsRough k) : n ≠ 0 :=
  h.1

/-- **Rough numbers are positive.** For every natural number $k$, every $k$-rough natural number
$n$ satisfies $n > 0$. -/
theorem IsRough.pos {n k : ℕ} (h : n.IsRough k) : 0 < n :=
  Nat.pos_of_ne_zero h.ne_zero

/-- **Prime divisors of a rough number exceed the bound.** Let $n$, $k$ and $p$ be natural
numbers. If $n$ is $k$-rough and $p$ is a prime dividing $n$, then $k < p$. -/
theorem IsRough.lt_of_prime_dvd {n k p : ℕ} (h : n.IsRough k) (hp : p.Prime)
    (hdvd : p ∣ n) : k < p :=
  h.2 p hp hdvd

/-- **Roughness through the list of prime factors.** For natural numbers $n$ and $k$, $n$ is
$k$-rough if and only if $n \neq 0$ and every prime in the list of prime factors of $n$
(with multiplicity) is greater than $k$. -/
theorem isRough_iff_primeFactorsList {n k : ℕ} :
    n.IsRough k ↔ n ≠ 0 ∧ ∀ p ∈ primeFactorsList n, k < p := by
  constructor
  · intro h
    refine ⟨h.ne_zero, fun p hp => ?_⟩
    exact h.lt_of_prime_dvd (prime_of_mem_primeFactorsList hp)
      (dvd_of_mem_primeFactorsList hp)
  · intro h
    refine ⟨h.1, fun p hp hdvd => ?_⟩
    exact h.2 p ((mem_primeFactorsList h.1).mpr ⟨hp, hdvd⟩)

/-- Roughness is decidable via the finite prime-factor characterization. -/
instance decidableIsRough (n k : ℕ) : Decidable (n.IsRough k) :=
  decidable_of_iff _ (isRough_iff_primeFactorsList (n := n) (k := k)).symm

/-- **The number $1$ is rough.** For every natural number $k$, the number $1$ is $k$-rough.

This holds vacuously, since $1$ has no prime divisors. -/
theorem isRough_one (k : ℕ) : (1 : ℕ).IsRough k :=
  ⟨one_ne_zero, fun _ hp hdvd => (hp.ne_one (Nat.dvd_one.mp hdvd)).elim⟩

/-- **A prime is rough exactly above the bound.** For natural numbers $p$ and $k$ with $p$
prime, $p$ is $k$-rough if and only if $k < p$. -/
theorem Prime.isRough_iff {p k : ℕ} (hp : p.Prime) : p.IsRough k ↔ k < p := by
  constructor
  · intro h
    exact h.lt_of_prime_dvd hp dvd_rfl
  · intro hk
    refine ⟨hp.ne_zero, fun q hq hdvd => ?_⟩
    have heq : q = p := (prime_dvd_prime_iff_eq hq hp).mp hdvd
    rw [heq]
    exact hk

/-- **Divisors of rough numbers are rough.** Let $k$ be a natural number. If a natural number $m$
is $k$-rough and $d$ is a nonzero divisor of $m$, then $d$ is $k$-rough. -/
theorem IsRough.of_dvd {m d k : ℕ} (h : m.IsRough k) (hdvd : d ∣ m) (hd : d ≠ 0) :
    d.IsRough k :=
  ⟨hd, fun _ hp hpd => h.lt_of_prime_dvd hp (hpd.trans hdvd)⟩

/-- **A product is rough exactly when both factors are.** For natural numbers $m$, $n$ and
$k$, the product $mn$ is $k$-rough if and only if both $m$ and $n$ are $k$-rough. -/
theorem isRough_mul {m n k : ℕ} : (m * n).IsRough k ↔ m.IsRough k ∧ n.IsRough k := by
  constructor
  · intro h
    refine ⟨h.of_dvd (Nat.dvd_mul_right m n) ?_,
      h.of_dvd (Nat.dvd_mul_left n m) ?_⟩
    · intro hm
      exact h.ne_zero (by rw [hm, zero_mul])
    · intro hn
      exact h.ne_zero (by rw [hn, mul_zero])
  · rintro ⟨hm, hn⟩
    refine ⟨mul_ne_zero hm.ne_zero hn.ne_zero, fun _ hp hdvd => ?_⟩
    rw [hp.dvd_mul] at hdvd
    exact hdvd.elim (hm.lt_of_prime_dvd hp) (hn.lt_of_prime_dvd hp)

/-- **Products of rough numbers are rough.** For natural numbers $m$, $n$ and $k$, if $m$ and
$n$ are both $k$-rough, then $mn$ is $k$-rough. -/
theorem IsRough.mul {m n k : ℕ} (hm : m.IsRough k) (hn : n.IsRough k) :
    (m * n).IsRough k :=
  isRough_mul.mpr ⟨hm, hn⟩

/-- **Roughness is antitone in the bound.** Let $k$ and $l$ be natural numbers with $l \le k$.
Every $k$-rough natural number is $l$-rough. -/
theorem IsRough.of_le {n k l : ℕ} (h : n.IsRough k) (hle : l ≤ k) : n.IsRough l :=
  ⟨h.ne_zero, fun _ hp hdvd => lt_of_le_of_lt hle (h.lt_of_prime_dvd hp hdvd)⟩

/-- **Only $1$ is rough and smooth at the same bound.** Let $n$ and $k$ be natural
numbers. If $n$ is $k$-rough and $n$ is positive with every prime factor less than
$k + 1$, then $n = 1$. -/
theorem IsRough.eq_one_of_mem_smoothNumbers {n k : ℕ}
    (hrough : n.IsRough k) (hsmooth : n ∈ smoothNumbers (k + 1)) : n = 1 := by
  by_contra hn1
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hn1
  have hlt1 : k < p := hrough.lt_of_prime_dvd hp hpdvd
  rw [Nat.mem_smoothNumbers] at hsmooth
  have hmem : p ∈ Nat.primeFactorsList n :=
    (Nat.mem_primeFactorsList hrough.ne_zero).mpr ⟨hp, hpdvd⟩
  have hlt2 : p < k + 1 := hsmooth.2 p hmem
  omega

/-- **Rough numbers other than $1$ lie in Mathlib's rough numbers up to a bound.** Let $n$,
$N$ and $k$ be natural numbers. If $n$ is $k$-rough, $n \le N$ and $n \ne 1$, then $n$ belongs
to the set of natural numbers $m$ with $1 \le m \le N$ that are not $(k+1)$-smooth, where $m$ is
$(k+1)$-smooth when $m > 0$ and every prime factor of $m$ is less than $k + 1$; for $m \ge 1$,
not being $(k+1)$-smooth means having a prime factor $p \ge k + 1$.

This set is Mathlib's set of rough numbers up to $N$ at bound $k + 1$. It asks only for some
prime factor $p \ge k + 1$, while $k$-roughness asks that every prime factor exceed $k$. -/
theorem IsRough.mem_roughNumbersUpTo {n N k : ℕ}
    (h : n.IsRough k) (hle : n ≤ N) (hn1 : n ≠ 1) :
    n ∈ roughNumbersUpTo N (k + 1) := by
  rw [roughNumbersUpTo, Finset.mem_filter, Finset.mem_range]
  refine ⟨by omega, h.ne_zero, ?_⟩
  intro hsmooth
  exact hn1 (h.eq_one_of_mem_smoothNumbers hsmooth)

end Nat
