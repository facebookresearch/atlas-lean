/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Sums of two squares modulo prime powers

Every positive integer is a sum of two positive squares modulo any positive power of a prime
congruent to one modulo four, with the second coordinate not divisible by the prime.

Source: Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and Polygonal
Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1, Lemma 8
(arXiv:2403.13533, Lemma 4.3).
-/

namespace MetaMathlibExt

private theorem base (p n : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1) :
    ∃ x y : ℕ, x ^ 2 + y ^ 2 ≡ n [MOD p] ∧ ¬ p ∣ y := by
  have : Fact p.Prime := ⟨hp⟩
  have h : ∃ a b : ZMod p, a ^ 2 + b ^ 2 = n ∧ b ≠ 0 := by
    by_cases hn : (n : ZMod p) = 0
    · obtain ⟨a, ha⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mpr (by omega)
      refine ⟨a, 1, ?_, one_ne_zero⟩
      rw [pow_two, ← ha, one_pow, neg_add_cancel, hn]
    · obtain ⟨a, b, hab⟩ := ZMod.sq_add_sq p (n : ZMod p)
      by_cases hb : b = 0
      · refine ⟨b, a, by rw [add_comm]; exact hab, ?_⟩
        intro ha
        apply hn
        simpa [ha, hb] using hab.symm
      · exact ⟨a, b, hab, hb⟩
  obtain ⟨a, b, hab, hb⟩ := h
  refine ⟨a.val, b.val, (ZMod.natCast_eq_natCast_iff ..).mp ?_, ?_⟩
  · simpa only [Nat.cast_add, Nat.cast_pow, ZMod.natCast_zmod_val] using hab
  · rwa [← ZMod.natCast_eq_zero_iff, ZMod.natCast_zmod_val]

private theorem lift_solution (p n x y j : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hj : 0 < j) (h : x ^ 2 + y ^ 2 ≡ n [MOD p ^ j]) (hy : ¬ p ∣ y) :
    ∃ z : ℕ, x ^ 2 + z ^ 2 ≡ n [MOD p ^ (j + 1)] ∧ ¬ p ∣ z := by
  have : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    exact (ZMod.natCast_eq_zero_iff 2 p).not.mpr
      ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).not.mpr hp2)
  have hy0 : (y : ZMod p) ≠ 0 := (ZMod.natCast_eq_zero_iff ..).not.mpr hy
  obtain ⟨c, hc⟩ := Nat.modEq_iff_dvd.mp h
  have hc' : (n : ℤ) - ((x : ℤ) ^ 2 + (y : ℤ) ^ 2) = (p : ℤ) ^ j * c := by
    simpa only [Nat.cast_add, Nat.cast_pow] using hc
  let t := ((c : ZMod p) / (2 * y)).val
  have ht : (2 : ZMod p) * y * t = c := by
    dsimp [t]
    rw [ZMod.natCast_zmod_val]
    exact mul_div_cancel₀ _ (mul_ne_zero h2 hy0)
  have hd : (p : ℤ) ∣ c - 2 * (y : ℤ) * t := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp
    push_cast
    exact sub_eq_zero.mpr ht.symm
  obtain ⟨d, hd⟩ := hd
  have hjpow : (p : ℤ) ^ j = (p : ℤ) * p ^ (j - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hj]
  refine ⟨y + t * p ^ j, Nat.modEq_iff_dvd.mpr ⟨d - (t : ℤ) ^ 2 * p ^ (j - 1), ?_⟩, ?_⟩
  · push_cast
    rw [pow_succ]
    linear_combination hc' + (p : ℤ) ^ j * hd - (t : ℤ) ^ 2 * (p : ℤ) ^ j * hjpow
  · rw [← ZMod.natCast_eq_zero_iff]
    simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, hj.ne'] using hy0

/-- **Sums of two squares modulo prime powers.** Let $p$ be a prime with $p \equiv 1 \pmod{4}$.
For all natural numbers $n > 0$ and $k > 0$ there are natural numbers $x, y > 0$ with
$x^2 + y^2 \equiv n \pmod{p^k}$ and $p \nmid y$.

Source: Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and Polygonal
Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1, Lemma 8
(arXiv Lemma 4.3; `jis-2024-24.5.1-lem-8`). -/
public theorem exists_sq_add_sq_modEq_prime_pow (p n k : ℕ) (hp : p.Prime)
    (hp4 : p % 4 = 1) (hn : 0 < n) (hk : 0 < k) :
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x ^ 2 + y ^ 2 ≡ n [MOD p ^ k] ∧ ¬ p ∣ y := by
  have hp2 : p ≠ 2 := by omega
  have solutions (j : ℕ) : ∃ x y : ℕ,
      x ^ 2 + y ^ 2 ≡ n [MOD p ^ (j + 1)] ∧ ¬ p ∣ y := by
    induction j with
    | zero => simpa using base p n hp hp4
    | succ j ih =>
      obtain ⟨x, y, h, hy⟩ := ih
      obtain ⟨z, hz, hzp⟩ := lift_solution p n x y (j + 1) hp hp2 (by omega) h hy
      exact ⟨x, z, hz, hzp⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  obtain ⟨x, y, h, hy⟩ := solutions j
  have hpow : 0 < p ^ (j + 1) := pow_pos hp.pos _
  have hx : x + n * p ^ (j + 1) ≡ x [MOD p ^ (j + 1)] := by simp [Nat.ModEq]
  have hy' : y + p ^ (j + 1) ≡ y [MOD p ^ (j + 1)] := by simp [Nat.ModEq]
  refine ⟨x + n * p ^ (j + 1), y + p ^ (j + 1),
    Nat.add_pos_right _ (Nat.mul_pos hn hpow), Nat.add_pos_right _ hpow,
    ((hx.pow 2).add (hy'.pow 2)).trans h, ?_⟩
  exact fun hd => hy ((Nat.dvd_add_iff_left (dvd_pow_self p (by omega))).mpr hd)

end MetaMathlibExt
