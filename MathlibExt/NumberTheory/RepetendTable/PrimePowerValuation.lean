/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Nat.PadicValNat
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Basic
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# Prime-power valuations for repetend tables

For a base of order `6 * p ^ j` modulo `p ^ i`, the sixth cyclotomic factor has
`p`-adic valuation `i - j`.
-/

namespace MetaMathlibExt

private theorem pow_eq_one_iff_dvd_sub {B n k : ℕ} (hk : 1 ≤ B ^ k) :
    (B : ZMod n) ^ k = 1 ↔ n ∣ B ^ k - 1 := by
  rw [← sub_eq_zero, ← Nat.cast_one, ← Nat.cast_pow, ← Nat.cast_sub hk,
    ZMod.natCast_eq_zero_iff]

/-- **The $p$-adic valuation of $B^2 - B + 1$ for a base of order $6p^j$.** Let $p$ be a prime
with $p \equiv 1 \pmod 6$, let $i$ and $j$ be natural numbers with $j \ge 1$ and $i \ge 2j$, and
let $B$ be a natural number whose multiplicative order modulo $p^i$ is $6p^j$. Then the $p$-adic
valuation of $B^2 - B + 1$ is exactly $i - j$.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 8 (`integers-2025-A26-lem-8`). -/
public theorem padicValNat_sq_sub_add_one_of_orderOf_eq (p i j B : ℕ) (hp : p.Prime)
    (hp6 : p % 6 = 1)
    (hj : 0 < j) (hij : 2 * j ≤ i) (hB : orderOf (B : ZMod (p ^ i)) = 6 * p ^ j) :
    padicValNat p (B ^ 2 - B + 1) = i - j := by
  have : Fact p.Prime := ⟨hp⟩
  have hi : 0 < i := by omega
  have : Fact (1 < p ^ i) := ⟨Nat.one_lt_pow hi.ne' hp.one_lt⟩
  have hpgt : 6 < p := by have := hp.two_le; omega
  have hpg : p.Coprime 6 := hp.coprime_iff_not_dvd.mpr fun h =>
    (not_le_of_gt hpgt) (Nat.le_of_dvd (by decide) h)
  have hbase : 1 < B := by
    by_contra! h
    have horder : 1 < 6 * p ^ j := by have := pow_pos hp.pos j; omega
    obtain rfl | rfl : B = 0 ∨ B = 1 := by omega
    all_goals
      simp at hB
      omega
  have hpos (k : ℕ) : 1 ≤ B ^ k := Nat.one_le_pow k B (by omega)
  -- Reduction modulo `p` removes the `p`-power from the exponent by Fermat's theorem.
  let d := orderOf (B : ZMod p)
  have hbig : (B : ZMod (p ^ i)) ^ (6 * p ^ j) = 1 := hB ▸ pow_orderOf_eq_one _
  have hsmall : (B : ZMod p) ^ 6 = 1 := by
    have h := congrArg (ZMod.castHom (dvd_pow_self p hi.ne') (ZMod p)) hbig
    simpa only [map_pow, map_natCast, map_one, pow_mul, ZMod.pow_card_pow] using h
  have hd6 : d ∣ 6 := orderOf_dvd_of_pow_eq_one hsmall
  -- A power that is one modulo `p` becomes one modulo `p ^ i` after raising to `p ^ (i - 1)`.
  have hpd : p ∣ B ^ d - 1 :=
    (pow_eq_one_iff_dvd_sub (hpos d)).mp (pow_orderOf_eq_one (B : ZMod p))
  have hpd' : (p : ℤ) ∣ (B : ℤ) ^ d - 1 := by
    simpa only [Nat.cast_sub (hpos d), Nat.cast_pow, Nat.cast_one] using
      (Int.natCast_dvd_natCast.mpr hpd)
  have hlift : (p : ℤ) ^ i ∣ (B : ℤ) ^ (d * p ^ (i - 1)) - 1 := by
    have h := dvd_sub_pow_of_dvd_sub hpd' (i - 1)
    rwa [Nat.sub_add_cancel hi, one_pow, ← pow_mul] at h
  have hlift' : p ^ i ∣ B ^ (d * p ^ (i - 1)) - 1 := by
    apply Int.natCast_dvd_natCast.mp
    simpa only [Nat.cast_sub (hpos _), Nat.cast_pow, Nat.cast_one] using hlift
  have hlarge := orderOf_dvd_of_pow_eq_one ((pow_eq_one_iff_dvd_sub (hpos _)).mpr hlift')
  rw [hB] at hlarge
  have h6d : 6 ∣ d := (hpg.symm.pow_right (i - 1)).dvd_of_dvd_mul_right
    (dvd_trans (dvd_mul_right 6 (p ^ j)) hlarge)
  have hmod : orderOf (B : ZMod p) = 6 := Nat.dvd_antisymm hd6 h6d
  -- LTE and the exact order determine the valuation of `B ^ 6 - 1`.
  have hlt6 : 1 < B ^ 6 := Nat.one_lt_pow (by decide) hbase
  have hdiv6 := (pow_eq_one_iff_dvd_sub (hpos 6)).mp hsmall
  have hndiv6 : ¬ p ∣ B ^ 6 := fun hdvd => one_ne_zero <|
    by simpa only [Nat.cast_pow, hsmall] using (ZMod.natCast_eq_zero_iff (B ^ 6) p).mpr hdvd
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have htest (k : ℕ) : (B : ZMod (p ^ i)) ^ (6 * p ^ k) = 1 ↔
      i ≤ multiplicity p (B ^ 6 - 1) + k := by
    have hne : p ^ k ≠ 0 := pow_ne_zero _ hp.ne_zero
    have hlt : 1 < (B ^ 6) ^ (p ^ k) := Nat.one_lt_pow hne hlt6
    rw [pow_mul, ← Nat.cast_pow, pow_eq_one_iff_dvd_sub hlt.le,
      multiplicity_dvd_iff_le (Nat.sub_ne_zero_of_lt hlt)]
    have hlte := Nat.multiplicity_pow_sub_pow hpodd hlt6 hdiv6 hndiv6 hne
    simp only [one_pow, Nat.multiplicity_prime_pow] at hlte
    rw [hlte]
  have hmin : (B : ZMod (p ^ i)) ^ (6 * p ^ (j - 1)) ≠ 1 := by
    apply ((orderOf_eq_iff (Nat.mul_pos (by decide) (pow_pos hp.pos _) : 0 < 6 * p ^ j)).mp hB).2
    · exact Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right hp.one_lt (by omega)) (by decide)
    · exact Nat.mul_pos (by decide) (pow_pos hp.pos _)
  have hval : multiplicity p (B ^ 6 - 1) = i - j := by
    have := (htest j).mp hbig
    have := (htest (j - 1)).not.mp hmin
    omega
  -- Of the three factors of `B ^ 6 - 1`, only `B ^ 2 - B + 1` can be divisible by `p`.
  have hlt3 : 1 < B ^ 3 := Nat.one_lt_pow (by decide) hbase
  have hn3 : ¬ p ∣ B ^ 3 - 1 := fun h =>
    ((orderOf_eq_iff (by decide : 0 < 6)).mp hmod).2 3 (by decide) (by decide)
      ((pow_eq_one_iff_dvd_sub hlt3.le).mpr h)
  have hn1 : ¬ p ∣ B + 1 := by
    intro h
    have hneg : (B : ZMod p) = -1 := by
      apply eq_neg_of_add_eq_zero_left
      simpa only [Nat.cast_add, Nat.cast_one] using (ZMod.natCast_eq_zero_iff (B + 1) p).mpr h
    exact ((orderOf_eq_iff (by decide : 0 < 6)).mp hmod).2 2 (by decide) (by decide)
      (by simp [hneg])
  have hsq : B ≤ B ^ 2 := by rw [pow_two]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hfac : B ^ 6 - 1 = (B ^ 3 - 1) * ((B + 1) * (B ^ 2 - B + 1)) := by
    zify [hlt3.le, hlt6.le, hsq]
    ring
  rw [hfac, Nat.multiplicity_mul (by omega) (by positivity),
    Nat.multiplicity_mul (by omega) (by omega), multiplicity_eq_zero_of_not_dvd hn3,
    multiplicity_eq_zero_of_not_dvd hn1, zero_add, zero_add] at hval
  simpa only [Nat.padicValNat_def] using hval

end MetaMathlibExt
