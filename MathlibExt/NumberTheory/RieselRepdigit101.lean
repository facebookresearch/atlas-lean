/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SierpinskiRieselRepdigits
import Mathlib.Algebra.Ring.GeomSum

/-!
# Riesel repdigits with digit 101

The admissible repdigits have a common residue modulo twice the product of the six
covering primes. Checking one period of the exponent then supplies a proper divisor.
-/

namespace MetaMathlibExt

namespace isRieselNumber_repstring_101

private theorem repdigit_modEq {b t : ℕ} (hb : b ≡ 180 [MOD 11184810])
    (ht : t ≡ 171 [MOD 240]) : repstring b 101 0 t ≡ 762701 [MOD 11184810] := by
  have hb' : 180 ≤ b := calc
    180 = b % 11184810 := hb.symm
    _ ≤ b := Nat.mod_le _ _
  have hprod : repstring b 101 0 t * (b - 1) = 101 * (b ^ t - 1) := by
    simp only [repstring, Nat.digits_of_lt b 101 (by decide) (by omega),
      List.length_singleton, zero_add, one_mul, pow_one]
    exact Nat.div_mul_cancel (dvd_mul_of_dvd_right (Nat.sub_one_dvd_pow_sub_one b t) 101)
  -- At length 171 the residue of the power is fixed by a block of 240 more digits.
  have hcycle (q : ℕ) : 180 ^ (171 + 240 * q) ≡ 1573200 [MOD 11184810] := by
    induction q with
    | zero => decide
    | succ q ih =>
      rw [Nat.mul_succ, ← Nat.add_assoc, pow_add]
      exact (ih.mul_right (180 ^ 240)).trans (by decide)
  have hpow : b ^ t ≡ 1573200 [MOD 11184810] := by
    apply (hb.pow t).trans
    simpa only [← show t % 240 = 171 from ht, Nat.mod_add_div] using hcycle (t / 240)
  -- The denominator is congruent to 179, which is invertible modulo 11184810.
  apply Nat.ModEq.cancel_right_of_coprime (c := 179) (by decide)
  calc
    repstring b 101 0 t * 179 ≡ repstring b 101 0 t * (b - 1) [MOD 11184810] :=
      (hb.sub_right (by omega : 1 ≤ b) (by decide)).symm.mul_left _
    _ = 101 * (b ^ t - 1) := hprod
    _ ≡ 101 * (1573200 - 1) [MOD 11184810] :=
      (hpow.sub_right (Nat.one_le_pow _ _ (by omega)) (by decide)).mul_left _
    _ ≡ 762701 * 179 [MOD 11184810] := by decide

end isRieselNumber_repstring_101

/-- **Riesel repdigits with digit $101$ in bases $b \equiv 180 \pmod{11184810}$.** Let $b$ and $t$
be natural numbers with $b \equiv 180 \pmod{11184810}$ and $t \equiv 171 \pmod{240}$. Then the
$b$-repinteger $101_b^{(t)}$, which is the repdigit $101\,(b^t - 1)/(b - 1)$ because $101 < b$, is
a Riesel number.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Theorem 3.10
(`integers-2026-A12-thm-3-10`). -/
public theorem isRieselNumber_repstring_101 {b t : ℕ} (hb : b ≡ 180 [MOD 11184810])
    (ht : t ≡ 171 [MOD 240]) : IsRieselNumber (repstring b 101 0 t) := by
  let k := repstring b 101 0 t
  have hk : k ≡ 762701 [MOD 11184810] := isRieselNumber_repstring_101.repdigit_modEq hb ht
  refine ⟨Nat.odd_iff.mpr (hk.of_dvd (by decide : 2 ∣ 11184810)), ?_⟩
  intro n _
  change ¬ (k * 2 ^ n - 1).Prime
  -- One of the six covering primes works in each of the 24 exponent classes.
  have hcover : ∀ r : Fin 24, ∃ p ∈ [3, 7, 5, 17, 13, 241],
      2 ≤ p ∧ p ≤ 241 ∧ p ∣ 11184810 ∧ 2 ^ 24 ≡ 1 [MOD p] ∧
      762701 * 2 ^ (r : ℕ) ≡ 1 [MOD p] := by decide
  obtain ⟨p, _, hp, hple, hmod, hperiod, hr⟩ := hcover ⟨n % 24, Nat.mod_lt _ (by decide)⟩
  have hpow : 2 ^ n ≡ 2 ^ (n % 24) [MOD p] := by
    conv_lhs => rw [← Nat.mod_add_div n 24, pow_add, pow_mul]
    simpa only [one_pow, mul_one] using (hperiod.pow (n / 24)).mul_left (2 ^ (n % 24))
  have hfactor : p ∣ k * 2 ^ n - 1 := (((hk.of_dvd hmod).mul hpow).trans hr).symm.dvd'
  have hk_le : 762701 ≤ k := calc
    762701 = k % 11184810 := hk.symm
    _ ≤ k := Nat.mod_le _ _
  have := Nat.le_mul_of_pos_right k (by positivity : 0 < 2 ^ n)
  exact Nat.not_prime_of_dvd_of_lt hfactor hp (by omega)

end MetaMathlibExt
