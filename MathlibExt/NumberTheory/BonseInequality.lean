/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.NumberTheory.Bertrand
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

open Finset

/-- **Infinitely many primes.** The set of prime natural numbers is infinite.

Here a natural number $p$ is prime in the sense of prime elements of a commutative monoid with
zero: $p$ is neither $0$ nor a unit, and $p \mid ab$ implies $p \mid a$ or $p \mid b$. For natural
numbers this agrees with the usual notion of a prime number. -/
theorem bonse_primes_infinite : (Set.ofPred fun p : ℕ => Prime p).Infinite := by
  have h := Nat.infinite_setOfPred_prime
  have heq : Set.ofPred (fun p : ℕ => Prime p) = Set.ofPred Nat.Prime := by
    ext x
    exact Nat.prime_iff.symm
  rwa [heq]

/-- **The enumeration of the primes is strictly increasing.** For $k \ge 1$ let $p_k$ be the
$k$-th smallest prime number. If $i < j$, then $p_i < p_j$. -/
theorem bonse_nth_strictMono : StrictMono (Nat.nth Prime) :=
  Nat.nth_strictMono bonse_primes_infinite

/-- **The enumeration of the primes takes prime values.** For every $k \ge 1$, the $k$-th
smallest prime number exists and is prime. -/
theorem bonse_nth_prime (k : ℕ) : Prime (Nat.nth Prime k) :=
  Nat.nth_mem_of_infinite bonse_primes_infinite k

/-- **The sixth prime is thirteen.** The sixth prime number, counting $2$ as the first, is $13$. -/
theorem bonse_nth_five : Nat.nth Prime 5 = 13 := by
  have c13 : Nat.count Prime 13 = 5 := by decide
  have h13 : Prime 13 := by decide
  have h := Nat.nth_count h13
  rwa [c13] at h

/-- **Bertrand's postulate for consecutive primes.** Let $p_1 < p_2 < p_3 < \cdots$ be the prime
numbers in increasing order. For every $k \ge 1$, $p_{k+1} < 2 p_k$. -/
theorem bonse_nth_succ_lt (k : ℕ) :
    Nat.nth Prime (k + 1) < 2 * Nat.nth Prime k := by
  have hne0 : Nat.nth Prime k ≠ 0 := by
    have h2 := (Nat.prime_iff.mpr (bonse_nth_prime k)).two_le
    omega
  obtain ⟨p, hpNat, hlt, hle⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (Nat.nth Prime k) hne0
  have hp : Prime p := Nat.prime_iff.mp hpNat
  have hcount : k + 1 ≤ Nat.count Prime p := by
    by_contra h
    have hle' : Nat.count Prime p ≤ k := by omega
    have hmono := bonse_nth_strictMono.monotone hle'
    rw [Nat.nth_count hp] at hmono
    omega
  have hle_nth : Nat.nth Prime (k + 1) ≤ p :=
    le_trans (bonse_nth_strictMono.monotone hcount) (le_of_eq (Nat.nth_count hp))
  have hne : p ≠ 2 * Nat.nth Prime k := by
    intro h
    have hdvd : Nat.nth Prime k ∣ p := ⟨2, by omega⟩
    rcases hpNat.eq_one_or_self_of_dvd (Nat.nth Prime k) hdvd with h1 | hpk
    · have h2 := (Nat.prime_iff.mpr (bonse_nth_prime k)).two_le
      omega
    · omega
  omega

/-- **Bonse's inequality.** Let $p_1 = 2, p_2 = 3, p_3 = 5, \dots$ be the prime numbers in
increasing order. For every natural number $k > 4$, the square of the $(k+1)$-st prime is
smaller than the product of the first $k$ primes: $p_{k+1}^2 < p_1 p_2 \cdots p_k$.

Source: Robert J. Betts, "Using Bonse's Inequality to Find Upper Bounds on
Prime Gaps," Journal of Integer Sequences 10 (2007), Article 07.3.8,
Proposition [Bonse's inequality] (label prop1), lines 142–148,
<https://cs.uwaterloo.ca/journals/JIS/VOL10/Betts/betts7.tex>.
Proves `Wanted` entry `bonse_inequality`. -/
theorem bonse_inequality
    (k : ℕ) (hk : 4 < k) :
    (Nat.nth Prime k) ^ 2 < ∏ i ∈ Finset.range k, Nat.nth Prime i := by
  have key : ∀ m : ℕ, 5 ≤ m →
      (Nat.nth Prime m) ^ 2 < ∏ i ∈ Finset.range m, Nat.nth Prime i := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
      have c2 : Nat.count Prime 2 = 0 := by decide
      have c3 : Nat.count Prime 3 = 1 := by decide
      have c5 : Nat.count Prime 5 = 2 := by decide
      have c7 : Nat.count Prime 7 = 3 := by decide
      have c11 : Nat.count Prime 11 = 4 := by decide
      have c13 : Nat.count Prime 13 = 5 := by decide
      have n0 : Nat.nth Prime 0 = 2 := by
        have h2 : Prime 2 := by decide
        have h := Nat.nth_count h2
        rwa [c2] at h
      have n1 : Nat.nth Prime 1 = 3 := by
        have h3 : Prime 3 := by decide
        have h := Nat.nth_count h3
        rwa [c3] at h
      have n2 : Nat.nth Prime 2 = 5 := by
        have h5 : Prime 5 := by decide
        have h := Nat.nth_count h5
        rwa [c5] at h
      have n3 : Nat.nth Prime 3 = 7 := by
        have h7 : Prime 7 := by decide
        have h := Nat.nth_count h7
        rwa [c7] at h
      have n4 : Nat.nth Prime 4 = 11 := by
        have h11 : Prime 11 := by decide
        have h := Nat.nth_count h11
        rwa [c11] at h
      have n5 : Nat.nth Prime 5 = 13 := by
        have h13 : Prime 13 := by decide
        have h := Nat.nth_count h13
        rwa [c13] at h
      simp only [Finset.prod_range_succ, n0, n1, n2, n3, n4, n5]
      norm_num
    | succ n hn ih =>
      have hB := bonse_nth_succ_lt n
      have h4 : 4 ≤ Nat.nth Prime n := by
        have hmono := bonse_nth_strictMono.monotone hn
        rw [bonse_nth_five] at hmono
        omega
      have hpos : 0 < Nat.nth Prime n := by omega
      have hsq : (Nat.nth Prime (n + 1)) ^ 2 < 4 * (Nat.nth Prime n) ^ 2 := by
        nlinarith [hB, hpos]
      have hmul : 4 * (Nat.nth Prime n) ^ 2 ≤
          Nat.nth Prime n * (Nat.nth Prime n) ^ 2 :=
        Nat.mul_le_mul h4 le_rfl
      have hlt : Nat.nth Prime n * (Nat.nth Prime n) ^ 2 <
          Nat.nth Prime n * ∏ i ∈ Finset.range n, Nat.nth Prime i :=
        mul_lt_mul_of_pos_left ih hpos
      have hprod : ∏ i ∈ Finset.range (n + 1), Nat.nth Prime i =
          Nat.nth Prime n * ∏ i ∈ Finset.range n, Nat.nth Prime i := by
        rw [Finset.prod_range_succ, mul_comm]
      calc (Nat.nth Prime (n + 1)) ^ 2
          < 4 * (Nat.nth Prime n) ^ 2 := hsq
        _ ≤ Nat.nth Prime n * (Nat.nth Prime n) ^ 2 := hmul
        _ < Nat.nth Prime n * ∏ i ∈ Finset.range n, Nat.nth Prime i := hlt
        _ = ∏ i ∈ Finset.range (n + 1), Nat.nth Prime i := hprod.symm
  exact key k (by omega)

end MetaMathlibExt
