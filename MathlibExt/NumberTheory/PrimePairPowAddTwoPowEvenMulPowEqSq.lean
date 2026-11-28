/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic.Linarith
import MathlibExt.NumberTheory.PrimePairOneAddTwoPowMulPowEqSq
import MathlibExt.NumberTheory.PrimePairPowAddPowEqSq

/-!
# Squares of the form `p ^ x + (2 ^ (2 * k) * (2 * p - 1)) ^ y`

For positive exponents, reduction modulo `p` forces `y` to be even. Factoring the resulting
difference of squares and reducing modulo four then forces `x` to be even. A second
factorization gives consecutive factors, whose residues rule out all possible allocations
of the powers of two and `2 * p - 1`.
-/

namespace MetaMathlibExt

namespace prime_pair_pow_add_two_pow_even_mul_pow_eq_sq_iff

private theorem prime_pair_cast {p : ℕ} (hp : p.Prime) :
    ((2 * p - 1 : ℕ) : ZMod p) = -1 := by
  have hp2 := hp.two_le
  rw [Nat.cast_sub (by omega : 1 ≤ 2 * p), Nat.cast_mul, ZMod.natCast_self, mul_zero,
    Nat.cast_one, zero_sub]

private theorem even_second_exponent {p k x y z : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3)
    (hx : x ≠ 0) (h : p ^ x + (2 ^ (2 * k) * (2 * p - 1)) ^ y = z ^ 2) : Even y := by
  let _ : Fact p.Prime := ⟨hp⟩
  rcases Nat.even_or_odd y with he | ho
  · exact he
  have htwo : (2 : ZMod p) ≠ 0 := fun h0 =>
    Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) (by omega)
      ((ZMod.natCast_eq_zero_iff 2 p).mp h0)
  have hz : (z : ZMod p) ^ 2 = ((2 : ZMod p) ^ (2 * k) * (-1)) ^ y := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ZMod.natCast_self,
      zero_pow hx, zero_add, prime_pair_cast hp] using
      congrArg (Nat.cast : ℕ → ZMod p) h.symm
  rw [mul_pow, ho.neg_one_pow, mul_neg_one, ← pow_mul,
    show 2 * k * y = (k * y) * 2 by ring, pow_mul] at hz
  exact False.elim ((ZMod.mod_four_ne_three_of_sq_eq_neg_sq' (pow_ne_zero _ htwo) hz) hp4)

/-- The two factors cannot both be divisible by `p`, since they differ by `2 * a`. -/
private theorem prime_pow_eq_twice_add_one {p x a z : ℕ} (hp : p.Prime)
    (ha : 0 < a) (hndvd : ¬p ∣ 2 * a) (h : p ^ x + a ^ 2 = z ^ 2) :
    p ^ x = 2 * a + 1 := by
  have hsq : a ^ 2 < z ^ 2 := by
    rw [← h]
    exact Nat.lt_add_of_pos_left (pow_pos hp.pos _)
  have haz : a < z := lt_of_not_ge fun hza => hsq.not_ge (Nat.pow_le_pow_left hza 2)
  obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le haz.le
  have hu0 : 0 < u := by omega
  rw [hu] at h
  have hfac : u * (u + 2 * a) = p ^ x := by nlinarith only [h]
  have hu1 : u = 1 := by
    by_contra hne
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).mp (hfac ▸ dvd_mul_right u (u + 2 * a))
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (hfac ▸ dvd_mul_left (u + 2 * a) u)
    have hdi : p ∣ u := hi ▸ dvd_pow_self p (by rintro rfl; simp_all)
    have hdj : p ∣ u + 2 * a := hj ▸ dvd_pow_self p (by rintro rfl; simp at hj; omega)
    exact hndvd ((Nat.dvd_add_iff_right hdi).mpr hdj)
  simpa [hu1, add_comm 1] using hfac.symm

private theorem modEq_pow_of_odd {a b d n : ℕ} (hab : a ≡ b [MOD d])
    (hb : b ^ 2 ≡ 1 [MOD d]) (hn : Odd n) : a ^ n ≡ b [MOD d] := by
  obtain ⟨m, hm⟩ := hn
  rw [hm, pow_succ, pow_mul]
  simpa only [one_pow, one_mul] using ((((hab.pow 2).trans hb).pow m).mul hab)

/-- If one coprime factor contains the entire odd prime power, the other is a power of two.
If the latter factor exceeds one, coprimality puts the entire power of two in that factor. -/
private theorem split_factors {a b q t n : ℕ} (hc : a.Coprime b) (hb : 1 < b)
    (hq : 0 < q) (h : a * b = 2 ^ t * q ^ n) (hd : q ^ n ∣ a) :
    a = q ^ n ∧ b = 2 ^ t := by
  obtain ⟨c, hc'⟩ := hd
  have hcancel : c * b = 2 ^ t := by
    apply Nat.eq_of_mul_eq_mul_right (pow_pos hq n)
    calc
      c * b * q ^ n = a * b := by rw [hc']; ac_rfl
      _ = 2 ^ t * q ^ n := h
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (hcancel ▸ dvd_mul_left b c)
  have h2b : 2 ∣ b := hj ▸ dvd_pow_self 2 (by rintro rfl; simp_all)
  have had : a ∣ 2 ^ t * q ^ n := h ▸ dvd_mul_right a b
  have ha : a = q ^ n := Nat.dvd_antisymm
    (((hc.coprime_dvd_right h2b).pow_right t).dvd_of_dvd_mul_left had) ⟨c, hc'⟩
  rw [ha, mul_comm _ (q ^ n)] at h
  exact ⟨ha, Nat.eq_of_mul_eq_mul_left (pow_pos hq n) h⟩

private theorem no_consecutive_factors {p k m n u : ℕ} (hp : p.Prime)
    (hq : (2 * p - 1).Prime) (hp4 : p % 4 = 3) (hk : 1 ≤ k) (hm : m ≠ 0) (hn : n ≠ 0)
    (hu : p ^ m = 2 * u + 1) (h : u * (u + 1) = 2 ^ (2 * (k * n) - 1) * (2 * p - 1) ^ n) :
    False := by
  let q := 2 * p - 1
  let t := 2 * (k * n) - 1
  change q.Prime at hq
  change u * (u + 1) = 2 ^ t * q ^ n at h
  have hkn : 1 ≤ k * n := Nat.mul_pos (by omega) (by omega)
  have ht : 1 ≤ t := by dsimp [t]; omega
  have hq5 : 5 ≤ q := by dsimp [q]; omega
  have hqn : 5 ≤ q ^ n := hq5.trans (Nat.le_self_pow hn q)
  have ht2 : 2 ≤ 2 ^ t := Nat.le_self_pow (by omega) 2
  have hprod : 10 ≤ 2 ^ t * q ^ n := Nat.mul_le_mul ht2 hqn
  have hu1 : 1 < u := by
    by_contra! hu1
    have hle := Nat.mul_le_mul hu1 (show u + 1 ≤ 2 by omega)
    omega
  have hcop : u.Coprime (u + 1) := by simp
  have hqd : q ^ n ∣ u * (u + 1) := h ▸ dvd_mul_left (q ^ n) (2 ^ t)
  have hqp := (isPrimePow_pow_iff hn).2 hq.isPrimePow
  have hs : (u = q ^ n ∧ u + 1 = 2 ^ t) ∨ (u + 1 = q ^ n ∧ u = 2 ^ t) := by
    rcases (hcop.isPrimePow_dvd_mul hqp).mp hqd with hd | hd
    · exact Or.inl (split_factors hcop (by omega) hq.pos h hd)
    · exact Or.inr (split_factors hcop.symm hu1 hq.pos (by rwa [mul_comm (u + 1) u]) hd)
  have ht3 : 3 ≤ t := by
    by_contra! hlt
    have ht1 : t = 1 := by dsimp [t] at *; omega
    rw [ht1, pow_one] at hs
    omega
  rcases hs with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · have hq4 : q ≡ 1 [MOD 4] := by dsimp [q, Nat.ModEq]; omega
    have h4 : 2 ^ t ≡ 0 [MOD 4] := Nat.modEq_zero_iff_dvd.mpr (pow_dvd_pow 2 (by omega : 2 ≤ t))
    have hmod := (hq4.pow n).add_right 1
    rw [one_pow, ← h₁, h₂] at hmod
    exact (by decide : ¬(0 ≡ 1 + 1 [MOD 4])) (h4.symm.trans hmod)
  · have h8 : 2 ^ t ≡ 0 [MOD 8] := Nat.modEq_zero_iff_dvd.mpr (pow_dvd_pow 2 ht3)
    have hq8 : q ≡ 5 [MOD 8] := by dsimp [q, Nat.ModEq]; omega
    have hqn8 : q ^ n ≡ 1 [MOD 8] := by rw [← h₁, h₂]; exact h8.add_right 1
    have he : Even n := by
      rcases Nat.even_or_odd n with he | ho
      · exact he
      · have hmod := modEq_pow_of_odd hq8 (by decide : 5 ^ 2 ≡ 1 [MOD 8]) ho
        exact False.elim ((by decide : ¬(5 ≡ 1 [MOD 8])) (hmod.symm.trans hqn8))
    -- Then `p ^ m + 1 = 2 * q ^ n` reduces to `1 = 2` modulo `p`.
    let _ : Fact p.Prime := ⟨hp⟩
    have hupper : p ^ m + 1 = 2 * q ^ n := by omega
    have hcast := congrArg (Nat.cast : ℕ → ZMod p) hupper
    have hqc : (q : ZMod p) = -1 := prime_pair_cast hp
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
      ZMod.natCast_self, zero_pow hm, zero_add, hqc, he.neg_one_pow, mul_one] at hcast
    rw [← one_add_one_eq_two] at hcast
    exact one_ne_zero (add_left_cancel (hcast.symm.trans (add_zero 1).symm))

private theorem no_positive_exponents {p k x y z : ℕ} (hp : p.Prime)
    (hq : (2 * p - 1).Prime) (hp4 : p % 4 = 3) (hk : 1 ≤ k) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : p ^ x + (2 ^ (2 * k) * (2 * p - 1)) ^ y = z ^ 2) : False := by
  obtain ⟨n, hn'⟩ := even_second_exponent hp hp4 hx h
  have hn : n ≠ 0 := by omega
  let q := 2 * p - 1
  let a := 2 ^ (2 * (k * n)) * q ^ n
  have haz : p ^ x + a ^ 2 = z ^ 2 := by
    rw [hn', ← two_mul, mul_comm 2 n, pow_mul, mul_pow, ← pow_mul,
      show 2 * k * n = 2 * (k * n) by ring] at h
    exact h
  have hpa : ¬p ∣ 2 * a := by
    have h2 : ¬p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
    have hq' : ¬p ∣ q := by
      let _ : Fact p.Prime := ⟨hp⟩
      rw [← ZMod.natCast_eq_zero_iff, show (q : ZMod p) = -1 from prime_pair_cast hp]
      exact neg_ne_zero.mpr one_ne_zero
    exact hp.not_dvd_mul h2 (hp.not_dvd_mul (h2 ∘ hp.dvd_of_dvd_pow) (hq' ∘ hp.dvd_of_dvd_pow))
  have ha : 0 < a := Nat.mul_pos (pow_pos (by decide) _) (pow_pos hq.pos _)
  have hpx := prime_pow_eq_twice_add_one hp ha hpa haz
  have h2a : 2 ∣ a := dvd_mul_of_dvd_left (dvd_pow_self 2 (by positivity)) _
  have hpx4 : p ^ x ≡ 1 [MOD 4] := by
    obtain ⟨s, hs⟩ := h2a
    unfold Nat.ModEq
    omega
  have hxe : Even x := by
    rcases Nat.even_or_odd x with he | ho
    · exact he
    · have hp' : p ≡ 3 [MOD 4] := by exact hp4
      have hmod := modEq_pow_of_odd hp' (by decide : 3 ^ 2 ≡ 1 [MOD 4]) ho
      exact False.elim ((by decide : ¬(3 ≡ 1 [MOD 4])) (hmod.symm.trans hpx4))
  obtain ⟨m, hm'⟩ := hxe
  have hm : m ≠ 0 := by omega
  obtain ⟨u, hu⟩ := (hp.odd_of_ne_two (by omega)).pow (n := m)
  have hpow : p ^ x = (2 * u + 1) ^ 2 := by rw [hm', ← two_mul, mul_comm 2 m, pow_mul, hu]
  have hkn : 0 < k * n := Nat.mul_pos (by omega) (by omega)
  have ha' : a = 2 * (2 ^ (2 * (k * n) - 1) * q ^ n) := by
    dsimp [a]
    conv_lhs => rw [show 2 * (k * n) = (2 * (k * n) - 1) + 1 by omega, pow_succ]
    ac_rfl
  have hfac : u * (u + 1) = 2 ^ (2 * (k * n) - 1) * q ^ n := by
    rw [hpow, ha'] at hpx
    nlinarith only [hpx]
  exact no_consecutive_factors hp hq hp4 hk hm hn hu hfac

end prime_pair_pow_add_two_pow_even_mul_pow_eq_sq_iff

open prime_pair_pow_add_two_pow_even_mul_pow_eq_sq_iff

/-- **Squares of the form $p^x + (2^{2k}(2p - 1))^y$ for prime pairs.** Let $p$ be a prime with
$p \equiv 3 \pmod 4$ such that $2p - 1$ is prime, and let $k \ge 1$ be an integer. Then
non-negative integers $x$, $y$ and $z$ satisfy $p^x + (2^{2k}(2p - 1))^y = z^2$ if and only if
either $p = 3$ and $(x, y, z) = (1, 0, 2)$, or $p = 3$, $k = 2$ and $(x, y, z) = (0, 1, 9)$.

Source: Jing Zhang and Yuan Li, *On the Equation (-1)^α p^x + (-1)^β (2^k(2p - 1))^y = z^2 for
Prime Pairs (p, 2p - 1)*, INTEGERS 24 (2024), Article A64, Theorem 3. -/
public theorem prime_pair_pow_add_two_pow_even_mul_pow_eq_sq_iff {p k : ℕ} (hp : p.Prime)
    (hq : (2 * p - 1).Prime) (hp4 : p % 4 = 3) (hk : 1 ≤ k) (x y z : ℕ) :
    p ^ x + (2 ^ (2 * k) * (2 * p - 1)) ^ y = z ^ 2 ↔
      (p, x, y, z) = (3, 1, 0, 2) ∨ (p, k, x, y, z) = (3, 2, 0, 1, 9) := by
  constructor
  · intro h
    by_cases hy : y = 0
    · subst y
      exact Or.inl ((prime_pair_pow_add_pow_eq_sq_iff hp (by omega) hq x 0 z).mp (by simpa using h))
    by_cases hx : x = 0
    · subst x
      have he := (one_add_two_pow_mul_pow_eq_sq_iff hp (by omega) hq (k := 2 * k)
        (by omega) y z).mp (by simpa using h)
      simp only [Prod.mk.injEq] at he ⊢
      exact Or.inr ⟨he.2.1, by omega, trivial, he.2.2.1, he.2.2.2⟩
    exact (no_positive_exponents hp hq hp4 hk hx hy h).elim
  · simp only [Prod.mk.injEq]
    rintro (⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩)
    · simp
    · decide

end MetaMathlibExt
