/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SierpinskiRieselRepdigits
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# Infinitely many Riesel repdigits in every base $b > 509203$

For every base $b > 509203$, the repdigits with digit $509203$ whose lengths are
congruent to $1$ modulo $2684354400$ are all congruent to $509203$ modulo
$11184810$, and hence are Riesel numbers by the covering system with moduli
$2, 3, 4, 8, 12, 24$ and primes $3, 7, 5, 17, 13, 241$. This gives infinitely many
Riesel repdigits in every such base.
-/

namespace MetaMathlibExt

namespace infinite_riesel_repdigits

-- The repdigit with digit $509203$ is the geometric sum with that digit.
private theorem repstring_eq_sum {b t : ℕ} (hb : 509203 < b) :
    repstring b 509203 0 t = 509203 * ∑ i ∈ Finset.range t, b ^ i := by
  have hprod : repstring b 509203 0 t * (b - 1) = 509203 * (b ^ t - 1) := by
    simp only [repstring, Nat.digits_of_lt b 509203 (by decide) (by omega),
      List.length_singleton, zero_add, one_mul, pow_one]
    exact Nat.div_mul_cancel (dvd_mul_of_dvd_right (Nat.sub_one_dvd_pow_sub_one b t) 509203)
  have hgeom : (∑ i ∈ Finset.range t, (b : ℤ) ^ i) * ((b : ℤ) - 1) = (b : ℤ) ^ t - 1 :=
    geom_sum_mul (b : ℤ) t
  have hprod_int : (repstring b 509203 0 t : ℤ) * ((b : ℤ) - 1)
      = 509203 * ((b : ℤ) ^ t - 1) := by
    have h1 : (1 : ℕ) ≤ b ^ t := Nat.one_le_pow t b (by omega)
    have h2 : (1 : ℕ) ≤ b := by omega
    exact_mod_cast hprod
  have hcancel : (repstring b 509203 0 t : ℤ)
      = (509203 * ∑ i ∈ Finset.range t, b ^ i : ℕ) := by
    have hne : ((b : ℤ) - 1) ≠ 0 := by
      have h2z : (2 : ℤ) ≤ b := by exact_mod_cast (by omega : 2 ≤ b)
      linarith
    apply mul_right_cancel₀ hne
    rw [hprod_int]
    push_cast
    rw [mul_assoc, hgeom]
  exact_mod_cast hcancel

-- A repdigit with digit $509203$ and admissible length has the same residue
-- as $509203$ modulo a prime $p$, provided the length is $1$ modulo both $p$ and
-- $p - 1$.
private theorem repstring_modEq {b t p : ℕ} (hp : p.Prime) (hb : 509203 < b)
    (ht1 : p ∣ t - 1) (ht2 : p - 1 ∣ t - 1) (ht : 1 ≤ t) :
    repstring b 509203 0 t ≡ 509203 [MOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.natCast_eq_natCast_iff]
  have hcast : (repstring b 509203 0 t : ZMod p)
      = (509203 : ZMod p) * ∑ i ∈ Finset.range t, (b : ZMod p) ^ i := by
    rw [repstring_eq_sum hb]
    push_cast
    rfl
  rw [hcast]
  have hsum : ∑ i ∈ Finset.range t, (b : ZMod p) ^ i = 1 := by
    by_cases hB : (b : ZMod p) = 1
    · rw [hB]
      simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      have hmodeq : t ≡ 1 [MOD p] := ((Nat.modEq_iff_dvd' ht).2 ht1).symm
      have ht_cast : (t : ZMod p) = 1 := by
        rw [← Nat.cast_one]
        exact (ZMod.natCast_eq_natCast_iff t 1 p).mpr hmodeq
      simpa using ht_cast
    · have hBt : (b : ZMod p) ^ t = (b : ZMod p) := by
        by_cases hB0 : (b : ZMod p) = 0
        · rw [hB0, zero_pow (by omega : t ≠ 0)]
        · obtain ⟨q, hq⟩ := ht2
          have ht_eq : t = (p - 1) * q + 1 := by omega
          rw [ht_eq, pow_add, pow_mul, ZMod.pow_card_sub_one_eq_one hB0, one_pow, one_mul,
            pow_one]
      have hgeom : (∑ i ∈ Finset.range t, (b : ZMod p) ^ i) * ((b : ZMod p) - 1)
          = (b : ZMod p) ^ t - 1 := geom_sum_mul (b : ZMod p) t
      rw [hBt] at hgeom
      have hne : (b : ZMod p) - 1 ≠ 0 := sub_ne_zero.mpr hB
      apply mul_right_cancel₀ hne
      rw [hgeom]
      ring
  rw [hsum, mul_one]
  simp

-- A number congruent to $509203$ modulo $11184810$ is a Riesel number: one
-- of the six covering primes divides $N \cdot 2^n - 1$ for every $n \ge 1$, and
-- it is a proper divisor.
private theorem riesel_of_modEq {N : ℕ} (hN : N ≡ 509203 [MOD 11184810]) :
    IsRieselNumber N := by
  refine ⟨Nat.odd_iff.mpr (hN.of_dvd (by decide : 2 ∣ 11184810)), ?_⟩
  intro n hn
  have hcover : ∀ r : Fin 24, ∃ p ∈ [3, 7, 5, 17, 13, 241],
      2 ≤ p ∧ p ≤ 241 ∧ p ∣ 11184810 ∧ 2 ^ 24 ≡ 1 [MOD p] ∧
      509203 * 2 ^ (r : ℕ) ≡ 1 [MOD p] := by decide
  obtain ⟨p, _, hp, hple, hmod, hperiod, hr⟩ := hcover ⟨n % 24, Nat.mod_lt _ (by decide)⟩
  have hpow : 2 ^ n ≡ 2 ^ (n % 24) [MOD p] := by
    conv_lhs => rw [← Nat.mod_add_div n 24, pow_add, pow_mul]
    simpa only [one_pow, mul_one] using (hperiod.pow (n / 24)).mul_left (2 ^ (n % 24))
  have hfactor : p ∣ N * 2 ^ n - 1 :=
    (((hN.of_dvd hmod).mul hpow).trans hr).symm.dvd'
  have hN_le : 509203 ≤ N := calc
    509203 = N % 11184810 := hN.symm
    _ ≤ N := Nat.mod_le _ _
  have h2n : 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hn
  have hprod : 509203 * 2 ≤ N * 2 ^ n := Nat.mul_le_mul hN_le h2n
  exact Nat.not_prime_of_dvd_of_lt hfactor hp (by omega)

-- A repdigit with digit $509203$ whose length is $1$ modulo $2684354400 =
-- 11184810 \cdot 240$ is congruent to $509203$ modulo $11184810$: the period is
-- divisible by every covering prime and by one less than every covering prime.
private theorem repstring_modEq_11184810 {b t : ℕ} (hb : 509203 < b) (ht : 1 ≤ t)
    (htL : 2684354400 ∣ t - 1) :
    repstring b 509203 0 t ≡ 509203 [MOD 11184810] := by
  have h2 := repstring_modEq (p := 2) (by decide) hb (dvd_trans (by decide) htL)
    (dvd_trans (by decide) htL) ht
  have h3 := repstring_modEq (p := 3) (by decide) hb (dvd_trans (by decide) htL)
    (dvd_trans (by decide) htL) ht
  have h5 := repstring_modEq (p := 5) (by decide) hb (dvd_trans (by decide) htL)
    (dvd_trans (by decide) htL) ht
  have h7 := repstring_modEq (p := 7) (by decide) hb (dvd_trans (by decide) htL)
    (dvd_trans (by decide) htL) ht
  have h13 := repstring_modEq (p := 13) (by decide) hb (dvd_trans (by decide) htL)
    (dvd_trans (by decide) htL) ht
  have h17 := repstring_modEq (p := 17) (by decide) hb (dvd_trans (by decide) htL)
    (dvd_trans (by decide) htL) ht
  have h241 := repstring_modEq (p := 241) (by decide +kernel) hb
    (dvd_trans (by norm_num) htL) (dvd_trans (by norm_num) htL) ht
  have h23 := (Nat.modEq_and_modEq_iff_modEq_mul (by decide : Nat.Coprime 2 3)).mp ⟨h2, h3⟩
  have h235 :=
    (Nat.modEq_and_modEq_iff_modEq_mul (by decide : Nat.Coprime (2 * 3) 5)).mp ⟨h23, h5⟩
  have h2357 :=
    (Nat.modEq_and_modEq_iff_modEq_mul (by decide : Nat.Coprime (2 * 3 * 5) 7)).mp ⟨h235, h7⟩
  have h235713 :=
    (Nat.modEq_and_modEq_iff_modEq_mul (by decide : Nat.Coprime (2 * 3 * 5 * 7) 13)).mp
      ⟨h2357, h13⟩
  have h23571317 :=
    (Nat.modEq_and_modEq_iff_modEq_mul
      (by decide : Nat.Coprime (2 * 3 * 5 * 7 * 13) 17)).mp ⟨h235713, h17⟩
  have hfin :=
    (Nat.modEq_and_modEq_iff_modEq_mul
      (by decide : Nat.Coprime (2 * 3 * 5 * 7 * 13 * 17) 241)).mp ⟨h23571317, h241⟩
  rwa [show (2 * 3 * 5 * 7 * 13 * 17 * 241 : ℕ) = 11184810 from by norm_num] at hfin

end infinite_riesel_repdigits

/-- **Infinitely many Riesel repdigits in every base $b > 509203$.** Let $b > 509203$ be a
natural number. Then there are infinitely many Riesel numbers of the form $k(b^t - 1)/(b - 1)$ with
$1 \le k < b$ and $t \ge 1$, that is, $b$-repdigits: the digit $k$ written $t$ times in base $b$.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Corollary 3.8
(`integers-2026-A12-cor-3-8`). -/
public theorem infinite_riesel_repdigits {b : ℕ} (hb : 509203 < b) :
    {N : ℕ | ∃ k t : ℕ, 1 ≤ k ∧ k < b ∧ 1 ≤ t ∧ N = repstring b k 0 t ∧
      IsRieselNumber N}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro B
  set t := 1 + 2684354400 * B with ht_def
  refine ⟨repstring b 509203 0 t, ⟨509203, t, by norm_num, hb, by omega, rfl, ?_⟩, ?_⟩
  · exact infinite_riesel_repdigits.riesel_of_modEq
      (infinite_riesel_repdigits.repstring_modEq_11184810 hb (by omega) ⟨B, by omega⟩)
  · have hsum_ge : t ≤ ∑ i ∈ Finset.range t, b ^ i := by
      calc t = ∑ _i ∈ Finset.range t, 1 := by simp
        _ ≤ ∑ i ∈ Finset.range t, b ^ i :=
          Finset.sum_le_sum fun i _ => Nat.one_le_pow i b (by omega)
    have hle : B ≤ 2684354400 * B := Nat.le_mul_of_pos_left B (by norm_num)
    rw [infinite_riesel_repdigits.repstring_eq_sum hb]
    calc B < t := by omega
      _ ≤ ∑ i ∈ Finset.range t, b ^ i := hsum_ge
      _ ≤ 509203 * ∑ i ∈ Finset.range t, b ^ i := Nat.le_mul_of_pos_left _ (by norm_num)

end MetaMathlibExt
