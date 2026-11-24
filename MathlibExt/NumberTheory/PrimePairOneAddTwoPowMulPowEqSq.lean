/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linarith

/-!
# Squares of the form `1 + (2 ^ k * (2 * p - 1)) ^ y`

For primes `p` and `2 * p - 1` with `p` odd and `k ≥ 1`, the unique solution has
`k = 4`, `p = 3`, `y = 1` and square root `9`.
Factoring the difference of squares gives consecutive factors that are powers of two and of
`2 * p - 1`. Their residues modulo three, four and eight determine the solution.
-/

namespace MetaMathlibExt

namespace one_add_two_pow_mul_pow_eq_sq_iff

/-- If the entire odd prime power divides one factor, the other factor is a power of two.
Since that power exceeds one, coprimality forces the first factor to be odd. -/
private theorem split_factors {m n a b : ℕ} (hcop : m.Coprime n) (hn : 1 < n)
    (hb : 0 < b) (hd : b ∣ m) (h : 4 * (m * n) = 2 ^ a * b) :
    m = b ∧ ∃ j : ℕ, n = 2 ^ j := by
  obtain ⟨c, hc⟩ := hd
  have hcancel : (4 * c) * n = 2 ^ a := by
    apply Nat.eq_of_mul_eq_mul_right hb
    calc
      (4 * c * n) * b = 4 * (m * n) := by rw [hc]; ac_rfl
      _ = 2 ^ a * b := h
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Dvd.intro_left _ hcancel)
  have hj0 : j ≠ 0 := by rintro rfl; simp_all
  have h2n : 2 ∣ n := hj ▸ dvd_pow_self 2 hj0
  have hm : m ∣ 2 ^ a * b := h ▸ dvd_mul_of_dvd_right (dvd_mul_right m n) 4
  exact ⟨Nat.dvd_antisymm
    (((hcop.coprime_dvd_right h2n).pow_right a).dvd_of_dvd_mul_left hm) ⟨c, hc⟩, j, hj⟩

/-- The power of the odd prime is one greater than the power of two. Modulo three this forces
the prime pair to be `(3, 5)` and the exponent of five to be odd. -/
private theorem classify_neighbors {p y j : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : (2 * p - 1).Prime) (hy : y ≠ 0)
    (hadj : (2 * p - 1) ^ y + 1 = 2 ^ j ∨ 2 ^ j + 1 = (2 * p - 1) ^ y) :
    p = 3 ∧ y = 1 ∧ j = 2 := by
  have hpmin := hp.two_le
  have hqmin := Nat.le_self_pow hy (2 * p - 1)
  have hj : 2 ≤ j := by
    by_contra! h
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl <;> norm_num at hadj <;> omega
  have h4 : 4 ∣ 2 ^ j := pow_dvd_pow 2 hj
  have hpodd := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have hq4 : 2 * p - 1 ≡ 1 [MOD 4] := by unfold Nat.ModEq; omega
  have hpow4 : (2 * p - 1) ^ y ≡ 1 [MOD 4] := by simpa using hq4.pow y
  have h : 2 ^ j + 1 = (2 * p - 1) ^ y := by
    unfold Nat.ModEq at hpow4
    omega
  have h3 : ¬3 ∣ 2 ^ j := fun hd => (by decide : ¬3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  have hp3 : p = 3 := by
    by_contra hne
    have hpd : ¬3 ∣ p := by simpa [Nat.dvd_prime hp, eq_comm] using hne
    have hqd : ¬3 ∣ 2 * p - 1 := by
      intro hd
      rcases (Nat.dvd_prime hq).mp hd with h1 | hq3 <;> omega
    have hq3 : 2 * p - 1 ≡ 1 [MOD 3] := by unfold Nat.ModEq; omega
    have hpow3 : (2 * p - 1) ^ y ≡ 1 [MOD 3] := by simpa using hq3.pow y
    unfold Nat.ModEq at hpow3
    omega
  subst p
  change 2 ^ j + 1 = 5 ^ y at h
  obtain ⟨s, rfl⟩ | ⟨s, rfl⟩ := Nat.even_or_odd y
  · have hpow3 := (show 5 ^ 2 ≡ 1 [MOD 3] by decide).pow s
    rw [show s + s = 2 * s by omega, pow_mul] at h
    simp only [one_pow, Nat.ModEq] at hpow3
    omega
  · have hpow8 := ((show 5 ^ 2 ≡ 1 [MOD 8] by decide).pow s).mul
      (Nat.ModEq.refl 5)
    have hodd := h
    rw [pow_succ, pow_mul] at hodd
    simp only [one_pow, one_mul, Nat.ModEq] at hpow8
    have hj2 : j = 2 := by
      by_contra hne
      have h8 : 8 ∣ 2 ^ j := pow_dvd_pow 2 (show 3 ≤ j by omega)
      omega
    subst j
    have hy1 := Nat.pow_right_injective (by decide : 2 ≤ 5)
      (show 5 ^ (2 * s + 1) = 5 ^ 1 from h.symm)
    exact ⟨rfl, hy1, rfl⟩

end one_add_two_pow_mul_pow_eq_sq_iff

open one_add_two_pow_mul_pow_eq_sq_iff

/-- **Squares of the form $1 + (2^k(2p - 1))^y$ for prime pairs.** Let $p$ be an odd prime such
that $2p - 1$ is prime, and let $k \ge 1$ be an integer. Then non-negative integers $y$ and $z$
satisfy $1 + (2^k(2p - 1))^y = z^2$ if and only if $k = 4$, $p = 3$, $y = 1$ and $z = 9$.

Source: Jing Zhang and Yuan Li, *On the Equation (-1)^α p^x + (-1)^β (2^k(2p - 1))^y = z^2 for
Prime Pairs (p, 2p - 1)*, INTEGERS 24 (2024), Article A64, Lemma 4. -/
public theorem one_add_two_pow_mul_pow_eq_sq_iff {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : (2 * p - 1).Prime) (hk : 1 ≤ k) (y z : ℕ) :
    1 + (2 ^ k * (2 * p - 1)) ^ y = z ^ 2 ↔ (k, p, y, z) = (4, 3, 1, 9) := by
  constructor
  · intro h
    have hpmin := hp.two_le
    have hy : y ≠ 0 := by
      rintro rfl
      simp only [pow_zero] at h
      exact (Nat.prime_iff.mp Nat.prime_two).not_isSquare ⟨z, by simpa [sq] using h⟩
    have hkmin := Nat.le_self_pow (by omega : k ≠ 0) 2
    have hbase := Nat.le_self_pow hy (2 ^ k * (2 * p - 1))
    have hzmin : 3 < z := by
      by_contra! hz
      have : 5 ≤ 2 * p - 1 := by omega
      nlinarith only [h, hbase, Nat.mul_le_mul hkmin this, Nat.pow_le_pow_left hz 2]
    rw [mul_pow, ← pow_mul] at h
    have hke : 2 ∣ 2 ^ (k * y) := dvd_pow_self 2 (by positivity)
    have he : 2 ∣ 2 ^ (k * y) * (2 * p - 1) ^ y := dvd_mul_of_dvd_left hke _
    have hzodd : Odd z := by
      by_contra hz
      have hz2 : 2 ∣ z := by rw [Nat.odd_iff] at hz; omega
      have := hz2.trans (dvd_pow_self z two_ne_zero)
      omega
    obtain ⟨t, rfl⟩ := hzodd
    have ht : 1 < t := by omega
    have hfac : 4 * (t * (t + 1)) = 2 ^ (k * y) * (2 * p - 1) ^ y := by
      nlinarith only [h]
    have hcop : t.Coprime (t + 1) := by simp
    have hqpos : 0 < (2 * p - 1) ^ y := Nat.pow_pos (by omega)
    have hqodd := hq.odd_of_ne_two (by omega)
    have hcop4 : ((2 * p - 1) ^ y).Coprime 4 :=
      hqodd.coprime_two_right.pow y 2
    have hd : (2 * p - 1) ^ y ∣ t * (t + 1) :=
      hcop4.dvd_of_dvd_mul_left (hfac ▸ dvd_mul_left _ _)
    have hqpow := (isPrimePow_pow_iff hy).2 hq.isPrimePow
    obtain ⟨j, hj⟩ : ∃ j : ℕ,
        (t = (2 * p - 1) ^ y ∧ t + 1 = 2 ^ j) ∨
        (t + 1 = (2 * p - 1) ^ y ∧ t = 2 ^ j) := by
      rcases (hcop.isPrimePow_dvd_mul hqpow).mp hd with hd | hd
      · obtain ⟨hm, j, hn⟩ := split_factors hcop (by omega) hqpos hd hfac
        exact ⟨j, Or.inl ⟨hm, hn⟩⟩
      · rw [Nat.mul_comm t (t + 1)] at hfac
        obtain ⟨hm, j, hn⟩ := split_factors hcop.symm ht hqpos hd hfac
        exact ⟨j, Or.inr ⟨hm, hn⟩⟩
    obtain ⟨rfl, rfl, rfl⟩ := classify_neighbors hp hp2 hq hy (by omega :
      (2 * p - 1) ^ y + 1 = 2 ^ j ∨ 2 ^ j + 1 = (2 * p - 1) ^ y)
    norm_num at hj
    obtain rfl : t = 4 := by omega
    have hk4 := Nat.pow_right_injective (by decide : 2 ≤ 2)
      (show 2 ^ k = 2 ^ 4 by norm_num at h ⊢; omega)
    simp [hk4]
  · simp only [Prod.mk.injEq]
    rintro ⟨rfl, rfl, rfl, rfl⟩
    decide

end MetaMathlibExt
