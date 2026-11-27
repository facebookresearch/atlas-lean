/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Factorial

@[expose] public section

namespace MetaMathlibExt

/-! # Prime gaps near n!
-/

/-- **Prime gaps near $n!$, general form.** Let $n$, $p$ and $r$ be natural numbers such that
every prime $q > n$ satisfies $q \ge r$. If $p$ is a prime with $n! + 1 < p < n! + r^2$, then
$p - n!$ is prime. -/
theorem prime_gap_factorial_general
    (n p r : ℕ) (hrmin : ∀ q : ℕ, q.Prime → n < q → r ≤ q)
    (hp : p.Prime) (hlo : Nat.factorial n + 1 < p)
    (hhi : p < Nat.factorial n + r ^ 2) :
    (p - Nat.factorial n).Prime := by
  have hNpos : 0 < Nat.factorial n := Nat.factorial_pos n
  have hNle : Nat.factorial n ≤ p := by omega
  have hd2 : 2 ≤ p - Nat.factorial n := by omega
  have hdpos : 0 < p - Nat.factorial n := by omega
  have hdp : p - Nat.factorial n + Nat.factorial n = p :=
    Nat.sub_add_cancel hNle
  have hdr2 : p - Nat.factorial n < r ^ 2 := by omega
  -- Key claim: every prime divisor of the difference is at least `r`.
  have key : ∀ m : ℕ, m.Prime → m ∣ (p - Nat.factorial n) → r ≤ m := by
    intro m hm hmd
    by_contra hlt
    have hlt' : m < r := Nat.lt_of_not_ge hlt
    have hmn : m ≤ n := by
      by_contra hcon
      have hcon' : n < m := Nat.lt_of_not_ge hcon
      have hle := hrmin m hm hcon'
      omega
    have hmN : m ∣ Nat.factorial n := hm.dvd_factorial.mpr hmn
    have hmp : m ∣ p := by
      rw [← hdp]
      exact Nat.dvd_add hmd hmN
    have hpm : p = m := (hp.dvd_iff_eq hm.ne_one).mp hmp
    have hmle : m ≤ p - Nat.factorial n := Nat.le_of_dvd hdpos hmd
    omega
  by_contra hcon
  have hmin : (p - Nat.factorial n).minFac.Prime :=
    Nat.minFac_prime (by omega)
  have hdvd : (p - Nat.factorial n).minFac ∣ (p - Nat.factorial n) :=
    Nat.minFac_dvd _
  have hrle : r ≤ (p - Nat.factorial n).minFac := key _ hmin hdvd
  have hsq : (p - Nat.factorial n).minFac ^ 2 ≤ p - Nat.factorial n :=
    Nat.minFac_sq_le_self hdpos hcon
  have hrr : r ^ 2 ≤ p - Nat.factorial n :=
    le_trans (Nat.pow_le_pow_left hrle 2) hsq
  omega

set_option linter.unusedVariables false in
/--
**Prime gaps near $n!$.** Let $n$ be a natural number and let $r$ be the smallest prime greater
than $n$. If $p$ is a prime with $n! + 1 < p < n! + r^2$, then $p - n!$ is prime.

The source's proof: if $p - n!$ were composite, its least prime factor $m$ would satisfy
$m^2 \le p - n! < r^2$, so $m < r$ and hence $m \le n$. Then $m$ divides $n!$ and therefore $p$,
contradicting $p > n! + 1$.

Source: Antonín Čejchan, Michal Křížek, and Lawrence Somer,
"On Remarkable Properties of Primes Near Factorials and Primorials,"
Journal of Integer Sequences 25 (2022), Article 22.1.4,
Theorem (label T1), lines 153–159,
https://cs.uwaterloo.ca/journals/JIS/VOL25/Krizek/krizek3.tex
-/
theorem prime_gap_factorial
    (n p r : ℕ)
    (hr : r.Prime) (hrn : n < r) (hrmin : ∀ q : ℕ, q.Prime → n < q → r ≤ q)
    (hp : p.Prime) (hlo : Nat.factorial n + 1 < p)
    (hhi : p < Nat.factorial n + r ^ 2) :
    (p - Nat.factorial n).Prime := by
  exact prime_gap_factorial_general n p r hrmin hp hlo hhi

end MetaMathlibExt
