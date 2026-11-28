/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import MathlibExt.NumberTheory.PrimitiveDivisor
public import MathlibExt.NumberTheory.RieselRepdigit101
public import MathlibExt.NumberTheory.SierpinskiRepinteger18107
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring

/-!
# Infinitely many Riesel repunits in bases `b ≡ 16518444216571 [MOD 2 ^ 64 - 1]`

For a base `b` congruent to `16518444216571` modulo `2 ^ 64 - 1`, there are infinitely
many Riesel numbers among the `b`-repunits `(b ^ t - 1) / (b - 1)` with `t ≥ 1`. The proof
is the covering system method applied to the residue classes `2 ^ (j - 1)` modulo `2 ^ j`
for `1 ≤ j ≤ 6` together with `0` modulo `64`, using the prime divisors `3`, `5`, `17`,
`257`, `65537`, `641` and `6700417` of `2 ^ 64 - 1`, and combines the resulting
congruences on the repunit length with the Chinese remainder theorem.

## Main results

* `MetaMathlibExt.infinite_riesel_repunits_mod_two_pow_64_sub_one`

## References

* Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
  Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Corollary 3.14.
-/

namespace MetaMathlibExt

namespace infinite_riesel_repunits_mod_two_pow_64_sub_one

private theorem repunit_mul_sub {b t : ℕ} (hb2 : 2 ≤ b) :
    repstring b 1 0 t * (b - 1) = b ^ t - 1 := by
  simp only [repstring, Nat.digits_of_lt b 1 (by decide) (by omega),
    List.length_singleton, zero_add, one_mul, pow_one]
  exact Nat.div_mul_cancel (Nat.sub_one_dvd_pow_sub_one b t)

private theorem repunit_eq_sum {b t : ℕ} (hb2 : 2 ≤ b) :
    repstring b 1 0 t = ∑ i ∈ Finset.range t, b ^ i := by
  simp only [repstring, Nat.digits_of_lt b 1 (by decide) (by omega),
    List.length_singleton, zero_add, one_mul, pow_one]
  exact (Nat.geomSum_eq hb2 t).symm

private theorem repunit_ge_length {b t : ℕ} (hb2 : 2 ≤ b) :
    t ≤ repstring b 1 0 t := by
  rw [repunit_eq_sum hb2]
  calc t = ∑ i ∈ Finset.range t, 1 := by simp [Finset.sum_const, Finset.card_range]
    _ ≤ ∑ i ∈ Finset.range t, b ^ i :=
      Finset.sum_le_sum (fun i _ => Nat.one_le_pow i b (by omega))

private theorem modeq_of_cover {n m r : ℕ} (hcase : n % 64 % m = r) (hdiv : m ∣ 64)
    (hrm : r < m) : n ≡ r [MOD m] := by
  have h1 : n % m = n % 64 % m := (Nat.mod_mod_of_dvd n hdiv).symm
  have h2 : n % m = r % m := by rw [h1, hcase, Nat.mod_eq_of_lt hrm]
  exact h2

private theorem dvd_of_pclass {b t n p m r : ℕ} (hb2 : 2 ≤ b) (ht1 : 1 ≤ t)
    (hb1p : b ≡ 1 [MOD p]) (htmod : t % p = p - 1) (hn : n ≡ r [MOD m])
    (hrm : r < m) (hp2 : 2 ≤ p) (h2m : 2 ^ m ≡ 1 [MOD p])
    (h2r : 2 ^ r ≡ p - 1 [MOD p]) :
    p ∣ repstring b 1 0 t * 2 ^ n - 1 := by
  have hNmod : repstring b 1 0 t % p = t % p := by
    have hterm : ∀ i ∈ Finset.range t, b ^ i % p = 1 := by
      intro i _
      have hpow : b ^ i ≡ 1 [MOD p] := by simpa using hb1p.pow i
      have h : b ^ i % p = 1 % p := hpow
      rwa [Nat.mod_eq_of_lt (show (1 : ℕ) < p by omega)] at h
    rw [repunit_eq_sum hb2, Finset.sum_nat_mod, Finset.sum_congr rfl hterm]
    simp [Finset.sum_const, Finset.card_range]
  have hN : repstring b 1 0 t ≡ p - 1 [MOD p] := by
    have hmod : repstring b 1 0 t % p = (p - 1) % p := by
      rw [hNmod, htmod, Nat.mod_eq_of_lt (show p - 1 < p by omega)]
    exact hmod
  have hnm : n % m = r := by
    have h : n % m = r % m := hn
    rwa [Nat.mod_eq_of_lt hrm] at h
  have hndecomp : n = r + m * (n / m) := by
    have h := Nat.div_add_mod n m
    omega
  have h2nm : (2 : ℕ) ^ n = 2 ^ r * (2 ^ m) ^ (n / m) := by
    conv_lhs => rw [hndecomp]
    rw [pow_add, pow_mul]
  have h2n : (2 : ℕ) ^ n ≡ 2 ^ r [MOD p] := by
    rw [h2nm]
    simpa using (h2m.pow (n / m)).mul_left (2 ^ r)
  have hsq : (p - 1) * (p - 1) ≡ 1 [MOD p] := by
    obtain ⟨k, rfl⟩ : ∃ k, p = k + 2 := ⟨p - 2, by omega⟩
    have e1 : k + 2 - 1 = k + 1 := by omega
    have e : (k + 2 - 1) * (k + 2 - 1) = 1 + (k + 2) * k := by rw [e1]; ring
    have hmod : ((k + 2 - 1) * (k + 2 - 1)) % (k + 2) = 1 % (k + 2) := by
      rw [e, Nat.add_mul_mod_self_left]
    exact hmod
  have hfin : repstring b 1 0 t * 2 ^ n ≡ 1 [MOD p] :=
    (hN.mul (h2n.trans h2r)).trans hsq
  have h1N : (1 : ℕ) ≤ repstring b 1 0 t * 2 ^ n := by
    have hNt : t ≤ repstring b 1 0 t := repunit_ge_length hb2
    have hN1 : (1 : ℕ) ≤ repstring b 1 0 t := by omega
    have h2n1 : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_two_pow
    have hmul := Nat.mul_le_mul hN1 h2n1
    omega
  exact (Nat.modEq_iff_dvd' h1N).mp hfin.symm

private theorem dvd_of_qclass {b t n : ℕ} (hb2 : 2 ≤ b) (ht1 : 1 ≤ t)
    (htM : t % 2233472 = 1) (hn0 : n % 64 = 0)
    (hpowM : b ^ 2233472 ≡ 1 [MOD 6700417]) (hbq1 : ¬ b ≡ 1 [MOD 6700417]) :
    6700417 ∣ repstring b 1 0 t * 2 ^ n - 1 := by
  have h2q : (2 : ℕ) ^ 64 ≡ 1 [MOD 6700417] := by decide
  have hq : Nat.Prime 6700417 := by norm_num
  have htdecomp : t = 1 + 2233472 * (t / 2233472) := by
    have h := Nat.div_add_mod t 2233472
    omega
  have hbtm : b ^ t = b * (b ^ 2233472) ^ (t / 2233472) := by
    conv_lhs => rw [htdecomp]
    rw [pow_add, pow_one, pow_mul]
  have hbt : b ^ t ≡ b [MOD 6700417] := by
    rw [hbtm]
    simpa using (hpowM.pow (t / 2233472)).mul_left b
  have h1b : (1 : ℕ) ≤ b := by omega
  have h1bt : (1 : ℕ) ≤ b ^ t := Nat.one_le_pow t b (by omega)
  have hsub : b ^ t - 1 ≡ b - 1 [MOD 6700417] := hbt.sub_right h1bt h1b
  have hmul : repstring b 1 0 t * (b - 1) ≡ 1 * (b - 1) [MOD 6700417] := by
    rw [repunit_mul_sub hb2]
    simpa using hsub
  have hcop : Nat.gcd 6700417 (b - 1) = 1 :=
    (hq.coprime_iff_not_dvd).mpr
      (fun hdvd => hbq1 (((Nat.modEq_iff_dvd' h1b).mpr hdvd).symm))
  have hN1 : repstring b 1 0 t ≡ 1 [MOD 6700417] :=
    Nat.ModEq.cancel_right_of_coprime hcop hmul
  have hndecomp : n = 64 * (n / 64) := by
    have h := Nat.div_add_mod n 64
    omega
  have h2nq : (2 : ℕ) ^ n ≡ 1 [MOD 6700417] := by
    have e : (2 : ℕ) ^ n = ((2 : ℕ) ^ 64) ^ (n / 64) := by
      conv_lhs => rw [hndecomp]
      rw [pow_mul]
    rw [e]
    simpa using h2q.pow (n / 64)
  have hfin : repstring b 1 0 t * 2 ^ n ≡ 1 [MOD 6700417] :=
    (hN1.mul h2nq).trans (by decide)
  have h1N : (1 : ℕ) ≤ repstring b 1 0 t * 2 ^ n := by
    have hNt : t ≤ repstring b 1 0 t := repunit_ge_length hb2
    have hNge : (1 : ℕ) ≤ repstring b 1 0 t := by omega
    have h2n1 : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_two_pow
    have hle := Nat.mul_le_mul hNge h2n1
    omega
  exact (Nat.modEq_iff_dvd' h1N).mp hfin.symm

private theorem pow_chain : 6692726 ^ 2233472 ≡ 1 [MOD 6700417] := by
  have h1 : 6692726 ^ 128 ≡ 3302943 [MOD 6700417] := by decide
  have h2 : 6692726 ^ 16384 ≡ 903215 [MOD 6700417] := by
    have earith : (128 : ℕ) * 128 = 16384 := by norm_num
    have e : 6692726 ^ 16384 = (6692726 ^ 128) ^ 128 := by
      rw [← earith, pow_mul]
    rw [e]
    exact (h1.pow 128).trans (by decide)
  have h3 : 6692726 ^ 2228224 ≡ 4131723 [MOD 6700417] := by
    have earith : (16384 : ℕ) * 136 = 2228224 := by norm_num
    have e : 6692726 ^ 2228224 = (6692726 ^ 16384) ^ 136 := by
      rw [← earith, pow_mul]
    rw [e]
    exact (h2.pow 136).trans (by decide)
  have h4 : 6692726 ^ 5248 ≡ 377034 [MOD 6700417] := by
    have earith : (128 : ℕ) * 41 = 5248 := by norm_num
    have e : 6692726 ^ 5248 = (6692726 ^ 128) ^ 41 := by
      rw [← earith, pow_mul]
    rw [e]
    exact (h1.pow 41).trans (by decide)
  have eM : 6692726 ^ 2233472 = 6692726 ^ 2228224 * 6692726 ^ 5248 := by
    have earith : (2228224 : ℕ) + 5248 = 2233472 := by norm_num
    rw [← earith, pow_add]
  rw [eM]
  exact (h3.mul h4).trans (by decide)

private theorem mod_two_of_modM {t : ℕ} (htM : t % 2233472 = 1) : t % 2 = 1 := by
  omega

private theorem one_le_of_modM {t : ℕ} (htM : t % 2233472 = 1) : 1 ≤ t := by
  omega

private theorem lo_of_modP {t : ℕ}
    (htP : t % 2753074036095 = 2753074036095 - 1) :
    2753074036095 - 1 ≤ t := by
  omega

private theorem mod_two_eq_zero_of_dvd {x : ℕ} (h : 2 ∣ x) : x % 2 = 0 := by
  omega

private theorem size_bound {N t n p : ℕ} (hNt : t ≤ N)
    (htlo : 2753074036095 - 1 ≤ t) (hNN : N * 2 ≤ N * 2 ^ n)
    (hp : p ≤ 6700417) : p < N * 2 ^ n - 1 := by
  omega

private theorem lt_of_eq_add_pos {a b d : ℕ} (h : b = a + d) (hpos : 1 ≤ d) :
    a < b := by
  omega

private theorem mod3_of_modP {t : ℕ}
    (htP : t % 2753074036095 = 2753074036095 - 1) : t % 3 = 2 := by
  omega

private theorem mod5_of_modP {t : ℕ}
    (htP : t % 2753074036095 = 2753074036095 - 1) : t % 5 = 4 := by
  omega

private theorem mod17_of_modP {t : ℕ}
    (htP : t % 2753074036095 = 2753074036095 - 1) : t % 17 = 16 := by
  omega

private theorem mod257_of_modP {t : ℕ}
    (htP : t % 2753074036095 = 2753074036095 - 1) : t % 257 = 256 := by
  omega

private theorem mod65537_of_modP {t : ℕ}
    (htP : t % 2753074036095 = 2753074036095 - 1) : t % 65537 = 65536 := by
  omega

private theorem mod641_of_modP {t : ℕ}
    (htP : t % 2753074036095 = 2753074036095 - 1) : t % 641 = 640 := by
  omega

private theorem isRiesel_of_residues {b t : ℕ} (hb2 : 2 ≤ b)
    (hbP : b ≡ 1 [MOD 2753074036095])
    (htP : t % 2753074036095 = 2753074036095 - 1) (htM : t % 2233472 = 1)
    (hpowM : b ^ 2233472 ≡ 1 [MOD 6700417])
    (hbq1 : ¬ b ≡ 1 [MOD 6700417]) :
    IsRieselNumber (repstring b 1 0 t) := by
  have ht1 : 1 ≤ t := one_le_of_modM htM
  have hNsum : repstring b 1 0 t = ∑ i ∈ Finset.range t, b ^ i :=
    repunit_eq_sum hb2
  have hoddN : Odd (repstring b 1 0 t) := by
    rcases Nat.even_or_odd b with heven | hodd
    · have hNmod2 : repstring b 1 0 t % 2 = 1 := by
        rw [hNsum, Finset.sum_nat_mod]
        have hterm0 : ∀ i ∈ Finset.range t, i ≠ 0 → b ^ i % 2 = 0 := by
          intro i _ hi0
          have hdvd : 2 ∣ b ^ i :=
            (even_iff_two_dvd.mp heven).trans (dvd_pow_self b hi0)
          exact mod_two_eq_zero_of_dvd hdvd
        have h0mem : (0 : ℕ) ∈ Finset.range t := Finset.mem_range.mpr ht1
        have hsum : (∑ i ∈ Finset.range t, b ^ i % 2) = 1 := by
          rw [Finset.sum_eq_single 0 hterm0 (fun h => (h h0mem).elim)]
          rw [pow_zero]
          decide
        rw [hsum]
      exact Nat.odd_iff.mpr hNmod2
    · have ht2 : t % 2 = 1 := mod_two_of_modM htM
      have hNmod2 : repstring b 1 0 t % 2 = 1 := by
        rw [hNsum, Finset.sum_nat_mod]
        have hterm : ∀ i ∈ Finset.range t, b ^ i % 2 = 1 :=
          fun i _ => Nat.odd_iff.mp hodd.pow
        have hsum1 : (∑ i ∈ Finset.range t, (1 : ℕ)) = t := by
          simp [Finset.sum_const, Finset.card_range]
        rw [Finset.sum_congr rfl hterm, hsum1]
        exact ht2
      exact Nat.odd_iff.mpr hNmod2
  refine ⟨hoddN, ?_⟩
  intro n hn1
  have h2n : (2 : ℕ) ≤ 2 ^ n := by
    have h := pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) hn1
    rwa [pow_one] at h
  have hNt : t ≤ repstring b 1 0 t := repunit_ge_length hb2
  have htlo : 2753074036095 - 1 ≤ t := lo_of_modP htP
  have hNN : repstring b 1 0 t * 2 ≤ repstring b 1 0 t * 2 ^ n :=
    Nat.mul_le_mul le_rfl h2n
  have hcover : ∀ c : Fin 64, (c : ℕ) % 64 = 0 ∨ (c : ℕ) % 2 = 1 ∨
      (c : ℕ) % 4 = 2 ∨ (c : ℕ) % 8 = 4 ∨ (c : ℕ) % 16 = 8 ∨
      (c : ℕ) % 32 = 16 ∨ (c : ℕ) % 64 = 32 := by decide
  rcases hcover ⟨n % 64, Nat.mod_lt _ (by decide)⟩ with
    h0 | h1 | h2 | h3 | h4 | h5 | h6
  · have h0' : n % 64 % 64 = 0 := h0
    have hn0 : n % 64 = 0 := by rwa [Nat.mod_mod] at h0'
    have hdvd : 6700417 ∣ repstring b 1 0 t * 2 ^ n - 1 :=
      dvd_of_qclass hb2 ht1 htM hn0 hpowM hbq1
    exact Nat.not_prime_of_dvd_of_lt hdvd (by decide)
      (size_bound hNt htlo hNN (by decide))
  · have h1' : n % 64 % 2 = 1 := h1
    have hn : n ≡ 1 [MOD 2] := modeq_of_cover h1' (by decide) (by decide)
    have htmod : t % 3 = 2 := mod3_of_modP htP
    have hb13 : b ≡ 1 [MOD 3] := hbP.of_dvd (by decide)
    have hdvd : 3 ∣ repstring b 1 0 t * 2 ^ n - 1 :=
      dvd_of_pclass hb2 ht1 hb13 htmod hn (by decide) (by decide) (by decide)
        (by decide)
    exact Nat.not_prime_of_dvd_of_lt hdvd (by decide)
      (size_bound hNt htlo hNN (by decide))
  · have h2' : n % 64 % 4 = 2 := h2
    have hn : n ≡ 2 [MOD 4] := modeq_of_cover h2' (by decide) (by decide)
    have htmod : t % 5 = 4 := mod5_of_modP htP
    have hb15 : b ≡ 1 [MOD 5] := hbP.of_dvd (by decide)
    have hdvd : 5 ∣ repstring b 1 0 t * 2 ^ n - 1 :=
      dvd_of_pclass hb2 ht1 hb15 htmod hn (by decide) (by decide) (by decide)
        (by decide)
    exact Nat.not_prime_of_dvd_of_lt hdvd (by decide)
      (size_bound hNt htlo hNN (by decide))
  · have h3' : n % 64 % 8 = 4 := h3
    have hn : n ≡ 4 [MOD 8] := modeq_of_cover h3' (by decide) (by decide)
    have htmod : t % 17 = 16 := mod17_of_modP htP
    have hb117 : b ≡ 1 [MOD 17] := hbP.of_dvd (by decide)
    have hdvd : 17 ∣ repstring b 1 0 t * 2 ^ n - 1 :=
      dvd_of_pclass hb2 ht1 hb117 htmod hn (by decide) (by decide) (by decide)
        (by decide)
    exact Nat.not_prime_of_dvd_of_lt hdvd (by decide)
      (size_bound hNt htlo hNN (by decide))
  · have h4' : n % 64 % 16 = 8 := h4
    have hn : n ≡ 8 [MOD 16] := modeq_of_cover h4' (by decide) (by decide)
    have htmod : t % 257 = 256 := mod257_of_modP htP
    have hb1257 : b ≡ 1 [MOD 257] := hbP.of_dvd (by decide)
    have hdvd : 257 ∣ repstring b 1 0 t * 2 ^ n - 1 :=
      dvd_of_pclass hb2 ht1 hb1257 htmod hn (by decide) (by decide) (by decide)
        (by decide)
    exact Nat.not_prime_of_dvd_of_lt hdvd (by decide)
      (size_bound hNt htlo hNN (by decide))
  · have h5' : n % 64 % 32 = 16 := h5
    have hn : n ≡ 16 [MOD 32] := modeq_of_cover h5' (by decide) (by decide)
    have htmod : t % 65537 = 65536 := mod65537_of_modP htP
    have hb165537 : b ≡ 1 [MOD 65537] := hbP.of_dvd (by decide)
    have hdvd : 65537 ∣ repstring b 1 0 t * 2 ^ n - 1 :=
      dvd_of_pclass hb2 ht1 hb165537 htmod hn (by decide) (by decide) (by decide)
        (by decide)
    exact Nat.not_prime_of_dvd_of_lt hdvd (by decide)
      (size_bound hNt htlo hNN (by decide))
  · have h6' : n % 64 % 64 = 32 := h6
    have hn : n ≡ 32 [MOD 64] := modeq_of_cover h6' (by decide) (by decide)
    have htmod : t % 641 = 640 := mod641_of_modP htP
    have hb1641 : b ≡ 1 [MOD 641] := hbP.of_dvd (by decide)
    have hdvd : 641 ∣ repstring b 1 0 t * 2 ^ n - 1 :=
      dvd_of_pclass hb2 ht1 hb1641 htmod hn (by decide) (by decide) (by decide)
        (by decide)
    exact Nat.not_prime_of_dvd_of_lt hdvd (by decide)
      (size_bound hNt htlo hNN (by decide))

end infinite_riesel_repunits_mod_two_pow_64_sub_one

/-- **Infinitely many Riesel repunits in bases $b \equiv 16518444216571 \pmod{2^{64} - 1}$.**
Let $b$ be a natural number with $b \equiv 16518444216571 \pmod{18446744073709551615}$, where
$18446744073709551615 = 2^{64} - 1$. Then there are infinitely many Riesel numbers among the
$b$-repunits $(b^t - 1)/(b - 1)$ with $t \ge 1$.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Corollary 3.14
(`integers-2026-A12-cor-3-14`). -/
public theorem infinite_riesel_repunits_mod_two_pow_64_sub_one {b : ℕ}
    (hb : b ≡ 16518444216571 [MOD 18446744073709551615]) :
    {N : ℕ | ∃ t : ℕ, 1 ≤ t ∧ N = repstring b 1 0 t ∧ IsRieselNumber N}.Infinite := by
  have hPq : 2753074036095 * 6700417 = 18446744073709551615 := by decide
  have hb2 : 2 ≤ b := by
    have hmod : b % 18446744073709551615 = 16518444216571 := by
      have h : b % 18446744073709551615
          = 16518444216571 % 18446744073709551615 := hb
      rwa [Nat.mod_eq_of_lt
        (by decide : 16518444216571 < 18446744073709551615)] at h
    have hle := Nat.mod_le b 18446744073709551615
    omega
  rw [← hPq] at hb
  have hbP : b ≡ 1 [MOD 2753074036095] :=
    (hb.of_dvd (Nat.dvd_mul_right 2753074036095 6700417)).trans (by decide)
  have hbq : b ≡ 6692726 [MOD 6700417] :=
    (hb.of_dvd (Nat.dvd_mul_left 6700417 2753074036095)).trans (by decide)
  have hpowM : b ^ 2233472 ≡ 1 [MOD 6700417] :=
    (hbq.pow 2233472).trans
      infinite_riesel_repunits_mod_two_pow_64_sub_one.pow_chain
  have hbq1 : ¬ b ≡ 1 [MOD 6700417] := by
    have hr1 : ¬ 6692726 ≡ 1 [MOD 6700417] := by decide
    exact fun h => hr1 (hbq.symm.trans h)
  obtain ⟨t0, ht0P, ht0M⟩ :=
    Nat.chineseRemainder (n := 2753074036095) (m := 2233472) (by decide)
      (2753074036095 - 1) 1
  have ht0P' : t0 % 2753074036095 = 2753074036095 - 1 := by
    have h : t0 % 2753074036095
        = (2753074036095 - 1) % 2753074036095 := ht0P
    rwa [Nat.mod_eq_of_lt
      (show 2753074036095 - 1 < 2753074036095 by decide)] at h
  have ht0M' : t0 % 2233472 = 1 := by
    have h : t0 % 2233472 = 1 % 2233472 := ht0M
    rwa [Nat.mod_eq_of_lt (show (1 : ℕ) < 2233472 by decide)] at h
  have hresP : ∀ k : ℕ, (t0 + 2753074036095 * 2233472 * k) % 2753074036095
      = 2753074036095 - 1 := by
    intro k
    have e : 2753074036095 * 2233472 * k
        = 2753074036095 * (2233472 * k) := by ring
    rw [e, Nat.add_mul_mod_self_left, ht0P']
  have hresM : ∀ k : ℕ, (t0 + 2753074036095 * 2233472 * k) % 2233472 = 1 := by
    intro k
    have e : 2753074036095 * 2233472 * k
        = 2233472 * (2753074036095 * k) := by ring
    rw [e, Nat.add_mul_mod_self_left, ht0M']
  have hmem : ∀ k : ℕ, repstring b 1 0 (t0 + 2753074036095 * 2233472 * k) ∈
      {N : ℕ | ∃ t : ℕ, 1 ≤ t ∧ N = repstring b 1 0 t ∧ IsRieselNumber N} := by
    intro k
    have ht1k : 1 ≤ t0 + 2753074036095 * 2233472 * k :=
      infinite_riesel_repunits_mod_two_pow_64_sub_one.one_le_of_modM (hresM k)
    exact ⟨t0 + 2753074036095 * 2233472 * k, ht1k, rfl,
      infinite_riesel_repunits_mod_two_pow_64_sub_one.isRiesel_of_residues hb2 hbP
        (hresP k) (hresM k) hpowM hbq1⟩
  have hNmono : StrictMono (fun t => repstring b 1 0 t) := by
    apply strictMono_nat_of_lt_succ
    intro t
    have hstep : repstring b 1 0 (t + 1) = repstring b 1 0 t + b ^ t := by
      simp only [infinite_riesel_repunits_mod_two_pow_64_sub_one.repunit_eq_sum hb2,
        Finset.sum_range_succ]
    have hpos : (1 : ℕ) ≤ b ^ t := Nat.one_le_pow t b (by omega)
    exact infinite_riesel_repunits_mod_two_pow_64_sub_one.lt_of_eq_add_pos hstep
      hpos
  have hmono : StrictMono
      (fun k => repstring b 1 0 (t0 + 2753074036095 * 2233472 * k)) := by
    apply strictMono_nat_of_lt_succ
    intro k
    have hlt : t0 + 2753074036095 * 2233472 * k
        < t0 + 2753074036095 * 2233472 * (k + 1) := by
      have hPM : (1 : ℕ) ≤ 2753074036095 * 2233472 := by decide
      have e : t0 + 2753074036095 * 2233472 * (k + 1)
          = (t0 + 2753074036095 * 2233472 * k)
            + 2753074036095 * 2233472 := by ring
      exact infinite_riesel_repunits_mod_two_pow_64_sub_one.lt_of_eq_add_pos e hPM
    exact hNmono hlt
  exact Set.infinite_of_injective_forall_mem hmono.injective hmem

end MetaMathlibExt
