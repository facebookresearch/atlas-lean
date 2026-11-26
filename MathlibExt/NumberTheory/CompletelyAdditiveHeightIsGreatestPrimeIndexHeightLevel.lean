/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.CompletelyAdditiveHeight
import Mathlib.NumberTheory.Bertrand

/-!
# The largest integer at each height for the prime-index height

For the completely additive height with `H p` equal to the one-based index of the
prime `p`, `2 ^ n` is the largest positive integer of height `n`. Each prime is at
most two to its index by Bertrand's postulate, and complete additivity turns this
into the global bound `m ≤ 2 ^ H m`.

Statements from Hartosh Singh Bal, *Completely Additive Height Functions: Profile
Laws, Matula Bounds, and Inverse Growth*, INTEGERS 26 (2026), Article A116.
-/

namespace MetaMathlibExt

@[expose] public section

private theorem count_prime_two : Nat.count Nat.Prime 2 = 0 := by
  rw [Nat.count_eq_zero ⟨2, Nat.prime_two⟩, Nat.nth_prime_zero_eq_two]

private theorem nth_prime_le_two_pow_succ (k : ℕ) :
    Nat.nth Nat.Prime k ≤ 2 ^ (k + 1) := by
  induction k with
  | zero => simp [Nat.nth_prime_zero_eq_two]
  | succ k ih =>
    have hnth : (Nat.nth Nat.Prime k).Prime :=
      Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime k
    obtain ⟨q, hq, hlt, hle⟩ :=
      Nat.exists_prime_lt_and_le_two_mul _ (ne_of_gt hnth.pos)
    have hle' : Nat.nth Nat.Prime (k + 1) ≤ q :=
      (Nat.nth_add_one_le_iff Nat.infinite_setOfPred_prime hq).mpr hlt
    calc Nat.nth Nat.Prime (k + 1) ≤ q := hle'
      _ ≤ 2 * Nat.nth Nat.Prime k := hle
      _ ≤ 2 * 2 ^ (k + 1) := by gcongr
      _ = 2 ^ (k + 1 + 1) := (pow_succ' 2 (k + 1)).symm

private theorem prime_le_two_pow_count_succ (p : ℕ) (hp : p.Prime) :
    p ≤ 2 ^ (Nat.count Nat.Prime p + 1) := by
  have h := nth_prime_le_two_pow_succ (Nat.count Nat.Prime p)
  rwa [Nat.nth_count hp] at h

private theorem le_two_pow_additiveOfPrimeValues (v : ℕ → ℕ)
    (hv : ∀ p, p.Prime → p ≤ 2 ^ v p) (m : ℕ) (hm : 0 < m) :
    m ≤ 2 ^ additiveOfPrimeValues v m := by
  revert hm
  refine Nat.strong_induction_on m (fun m ih hm => ?_)
  by_cases h1 : m = 1
  · subst h1
    simp [additiveOfPrimeValues_one]
  · have hq : m.minFac.Prime := Nat.minFac_prime h1
    have hqdvd : m.minFac ∣ m := Nat.minFac_dvd m
    have hqpos : 0 < m.minFac := hq.pos
    have hkpos : 0 < m / m.minFac := Nat.div_pos (Nat.le_of_dvd hm hqdvd) hqpos
    have hkm : m / m.minFac < m := Nat.div_lt_self hm hq.one_lt
    have ihk := ih (m / m.minFac) hkm hkpos
    have hmul := isCompletelyAdditiveNat_additiveOfPrimeValues v m.minFac (m / m.minFac)
      hqpos hkpos
    rw [Nat.mul_div_cancel' hqdvd] at hmul
    have hqH := additiveOfPrimeValues_prime v hq
    calc m = m.minFac * (m / m.minFac) := (Nat.mul_div_cancel' hqdvd).symm
      _ ≤ 2 ^ v m.minFac * 2 ^ additiveOfPrimeValues v (m / m.minFac) :=
        Nat.mul_le_mul (hv m.minFac hq) ihk
      _ = 2 ^ (v m.minFac + additiveOfPrimeValues v (m / m.minFac)) := (pow_add 2 _ _).symm
      _ = 2 ^ additiveOfPrimeValues v m := by rw [hmul, hqH]

private theorem additiveOfPrimeValues_two_pow (n : ℕ) :
    additiveOfPrimeValues (fun p => Nat.count Nat.Prime p + 1) (2 ^ n) = n := by
  induction n with
  | zero => rw [pow_zero, additiveOfPrimeValues_one]
  | succ n ih =>
    have h2 : additiveOfPrimeValues (fun p => Nat.count Nat.Prime p + 1) 2 = 1 := by
      simp only [additiveOfPrimeValues_prime _ Nat.prime_two, count_prime_two, zero_add]
    have h2pos : 0 < (2 : ℕ) := by norm_num
    have hpos : 0 < (2 : ℕ) ^ n := pow_pos h2pos n
    have hadd := isCompletelyAdditiveNat_additiveOfPrimeValues
      (fun p => Nat.count Nat.Prime p + 1) (2 ^ n) 2 hpos h2pos
    rw [pow_succ, hadd, ih, h2]

/-- **The largest integer at each height for the prime-index height.** Let $H$ be the completely
additive function on the positive integers with $H(p) = i$ when $p$ is the $i$-th prime, so that
$H(2) = 1$, $H(3) = 2$ and $H(5) = 3$. For every natural number $n$, $2^n$ is the largest integer
$m \ge 1$ with $H(m) = n$.

Source: Hartosh Singh Bal, *Completely Additive Height Functions: Profile Laws, Matula Bounds,
and Inverse Growth*, INTEGERS 26 (2026), Article A116, Proposition 4
(`integers-2026-A116-prop-4`). -/
public theorem isGreatest_primeIndexHeight_level (n : ℕ) :
    IsGreatest
      {m : ℕ | 0 < m ∧ additiveOfPrimeValues (fun p => Nat.count Nat.Prime p + 1) m = n} (2 ^ n)
    := by
  have h2 : (0 : ℕ) < 2 := by norm_num
  refine ⟨⟨pow_pos h2 n, additiveOfPrimeValues_two_pow n⟩, ?_⟩
  intro m hm
  obtain ⟨hmpos, hmn⟩ := hm
  calc m ≤ 2 ^ additiveOfPrimeValues (fun p => Nat.count Nat.Prime p + 1) m :=
        le_two_pow_additiveOfPrimeValues _ prime_le_two_pow_count_succ m hmpos
    _ = 2 ^ n := by rw [hmn]

end

end MetaMathlibExt
