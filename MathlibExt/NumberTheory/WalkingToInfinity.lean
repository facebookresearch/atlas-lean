/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Ring

/-!
# Binary digit walks on primes

`MetaMathlibExt.two_pow_sub_succ_ne_two_pow` excludes powers of two obtained by
subtracting a sufficiently small positive number from a power of two.
`MetaMathlibExt.not_exists_binary_prime_walk_appending_at_most_two_digits` rules out
infinite prime walks that append one or two binary digits at each step.
-/

namespace MetaMathlibExt

/-- **A power of two minus a much smaller positive number is not a power of two.** Let $p$
and $k$ be natural numbers with $k \ge \lceil \log_2 (p + 1) \rceil + 2$. Then $2^k - (p + 1)$
is not a power of $2$: there is no natural number $m$ with $2^k - (p + 1) = 2^m$.

Under this hypothesis $2^k > p + 1$, so the subtraction is exact. The source assumes $p$ is
prime; the statement holds without that assumption.

Source: Steven J. Miller, Fei Peng, Tudor Popescu, Joshua M. Siktar, and Nawapan
Wattanawanichkul, *Walking to Infinity Along Some Number Theory Sequences*, INTEGERS 24 (2024),
Article A78, Lemma 2.5. -/
public theorem two_pow_sub_succ_ne_two_pow (p k : ℕ) (hk : Nat.clog 2 (p + 1) + 2 ≤ k) :
    ¬ ∃ m : ℕ, 2 ^ k - (p + 1) = 2 ^ m := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hsmall : p + 1 < 2 ^ j :=
    (Nat.le_pow_clog Nat.one_lt_two (p + 1)).trans_lt (Nat.pow_lt_pow_right Nat.one_lt_two
      (by omega))
  rintro ⟨m, hm⟩
  have hlt : 2 ^ m < 2 ^ (j + 1) := by
    rw [← hm]
    exact Nat.sub_lt (Nat.two_pow_pos _) (Nat.succ_pos _)
  have hmj : m ≤ j := Nat.le_of_lt_succ ((Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp hlt)
  have hle := Nat.pow_le_pow_right (by decide : 0 < 2) hmj
  rw [Nat.pow_succ] at hm
  omega

namespace not_exists_binary_prime_walk_appending_at_most_two_digits

-- Every prime successor is odd, so its appended block must be 1, 01 or 11.
private theorem prime_step {a b : ℕ} (ha : a.Prime) (hb : b.Prime)
    (h : ∃ n k : ℕ, 1 ≤ n ∧ n ≤ 2 ∧ k < 2 ^ n ∧ b = 2 ^ n * a + k) :
    3 < b ∧ (b = 2 * a + 1 ∨ b = 4 * a + 1 ∨ b = 4 * a + 3) := by
  obtain ⟨n, k, hn, hn', hk, rfl⟩ := h
  have := ha.two_le
  have := hb.eq_two_or_odd
  rcases (by omega : n = 1 ∨ n = 2) with rfl | rfl <;> simp_all only [Nat.reducePow] <;> omega

-- Modulo 3, appending 01 takes residue 1 to 2, and residue 2 can never be left.
private theorem all_ones_tail (p : ℕ → ℕ) (hp : ∀ i, (p i).Prime) (hgt : ∀ i, 3 < p i)
    (hs : ∀ i, p (i + 1) = 2 * p i + 1 ∨ p (i + 1) = 4 * p i + 1 ∨
      p (i + 1) = 4 * p i + 3) :
    ∃ a, ∀ j, p (a + j + 1) = 2 * p (a + j) + 1 ∨ p (a + j + 1) = 4 * p (a + j) + 3 := by
  have hmod (i) : p i % 3 ≠ 0 := fun h =>
    Nat.not_prime_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero h) (by decide) (hgt i) (hp i)
  by_cases h : ∃ a, p a % 3 = 2
  · obtain ⟨a, ha⟩ := h
    have htwo (j) : p (a + j) % 3 = 2 := by
      induction j with
      | zero => exact ha
      | succ j ih =>
        have := hs (a + j)
        have := hmod (a + j + 1)
        change p (a + j + 1) % 3 = 2
        omega
    refine ⟨a, fun j => ?_⟩
    have := htwo j
    have := hmod (a + j + 1)
    rcases hs (a + j) with h | h | h <;> omega
  · refine ⟨0, fun j => ?_⟩
    simp only [Nat.zero_add]
    have := hmod j
    rw [not_exists] at h
    have := h j
    have := h (j + 1)
    rcases hs j with h | h | h <;> omega

-- A walk appending only ones crosses every pair of consecutive bit lengths.
private theorem reaches_length_pair (p : ℕ → ℕ)
    (hs : ∀ j, p (j + 1) = 2 * p j + 1 ∨ p (j + 1) = 4 * p j + 3) (k : ℕ) :
    ∃ i, p i + 1 = 2 ^ k * (p 0 + 1) ∨ p i + 1 = 2 * (2 ^ k * (p 0 + 1)) := by
  induction k with
  | zero => exact ⟨0, Or.inl (by simp)⟩
  | succ k ih =>
    rw [pow_succ', Nat.mul_assoc]
    obtain ⟨i, hi | hi⟩ := ih
    · refine ⟨i + 1, ?_⟩
      rcases hs i with h | h <;> omega
    · exact ⟨i, Or.inl hi⟩

-- Euler's theorem repeats the initial two residues, giving two consecutive composite terms.
private theorem no_all_ones_walk (p : ℕ → ℕ) (hp : ∀ i, (p i).Prime) (hodd : Odd (p 0))
    (hs : ∀ j, p (j + 1) = 2 * p j + 1 ∨ p (j + 1) = 4 * p j + 3) : False := by
  let a := p 0
  let m := a * (2 * a + 1)
  let k := m.totient
  have ha : 1 < a := (hp 0).one_lt
  have hm : Odd m := hodd.mul (show Odd (2 * a + 1) from ⟨a, rfl⟩)
  have hperiod : 2 ^ k ≡ 1 [MOD m] := Nat.ModEq.pow_totient hm.coprime_two_left
  have hk : 0 < k := Nat.totient_pos.mpr (Nat.mul_pos (by omega) (by omega))
  have hpow : 1 < 2 ^ k := Nat.one_lt_pow hk.ne' (by decide)
  have composite {b q : ℕ} (hb : 1 < b) (hd : b ∣ m) (heq : q + 1 = 2 ^ k * (b + 1)) :
      ¬ q.Prime := by
    have hcong : q + 1 ≡ b + 1 [MOD b] := by
      rw [heq]
      simpa using (hperiod.of_dvd hd).mul_right (b + 1)
    have hqb := Nat.ModEq.add_right_cancel' 1 hcong
    have hdq : b ∣ q := by simpa [Nat.ModEq, Nat.dvd_iff_mod_eq_zero] using hqb
    have : b + 1 < 2 ^ k * (b + 1) := lt_mul_of_one_lt_left (Nat.succ_pos b) hpow
    exact Nat.not_prime_of_dvd_of_lt hdq hb (by omega)
  obtain ⟨i, hi | hi⟩ := reaches_length_pair p hs k
  · exact composite ha (dvd_mul_right a _) hi (hp i)
  · apply composite (b := 2 * a + 1) (by omega) (dvd_mul_left _ a) _ (hp i)
    change p i + 1 = 2 * (2 ^ k * (a + 1)) at hi
    rw [hi]
    ring

end not_exists_binary_prime_walk_appending_at_most_two_digits

open not_exists_binary_prime_walk_appending_at_most_two_digits in
/-- **No binary prime walk to infinity in steps of one or two digits.** There is no sequence of
primes $p_0, p_1, p_2, \ldots$ such that for every $i \ge 0$ there are $n \in \{1, 2\}$ and a
natural number $k < 2^n$ with $p_{i+1} = 2^n p_i + k$. That is, starting from any prime, one
cannot walk to infinity on primes by appending one or two binary digits at a time on the right.

The appended blocks are the paper's $0, 1, 00, 01, 10, 11$ (a block may begin with $0$).

Source: Steven J. Miller, Fei Peng, Tudor Popescu, Joshua M. Siktar, and Nawapan
Wattanawanichkul, *Walking to Infinity Along Some Number Theory Sequences*, INTEGERS 24 (2024),
Article A78, Theorem 2.7. -/
public theorem not_exists_binary_prime_walk_appending_at_most_two_digits :
    ¬ ∃ p : ℕ → ℕ, (∀ i, (p i).Prime) ∧
      ∀ i, ∃ n k : ℕ, 1 ≤ n ∧ n ≤ 2 ∧ k < 2 ^ n ∧ p (i + 1) = 2 ^ n * p i + k := by
  rintro ⟨p, hp, h⟩
  have hs (i) := prime_step (hp i) (hp (i + 1)) (h i)
  -- Drop the initial prime so that every term exceeds 3.
  let q (i : ℕ) := p (i + 1)
  obtain ⟨a, ha⟩ := all_ones_tail q (fun i => hp (i + 1)) (fun i => (hs i).1)
    (fun i => (hs (i + 1)).2)
  have hodd : Odd (q a) := (hp (a + 1)).odd_of_ne_two (by have := (hs a).1; omega)
  exact no_all_ones_walk (fun j => q (a + j)) (fun j => hp (a + j + 1)) hodd ha

end MetaMathlibExt
