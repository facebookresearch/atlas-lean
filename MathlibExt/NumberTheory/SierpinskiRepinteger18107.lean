/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SierpinskiRieselRepdigits

/-!
# Binary Sierpiński repintegers of 18107

Repeating the binary digits of 18107 a number of times congruent to 25 modulo 56
gives a Sierpiński number.
-/

namespace MetaMathlibExt

namespace isSierpinskiNumber_repstring_18107

private theorem repinteger_modEq {t : ℕ} (ht : t ≡ 25 [MOD 56]) :
    repstring 2 18107 0 t ≡ 8007257 [MOD 11184810] := by
  -- Include the denominator in the modulus so that division preserves the desired residue.
  have hcycle (q : ℕ) :
      2 ^ (15 * (25 + 56 * q)) ≡ 2 ^ (15 * 25) [MOD 32767 * 11184810] := by
    induction q with
    | zero => simp only [Nat.mul_zero, Nat.add_zero, Nat.ModEq.refl]
    | succ q ih =>
      rw [Nat.mul_succ 56 q, ← Nat.add_assoc, Nat.mul_add, pow_add]
      exact (ih.mul_right (2 ^ (15 * 56))).trans (by decide +kernel)
  have hpow : 2 ^ (15 * t) ≡ 2 ^ (15 * 25) [MOD 32767 * 11184810] := by
    simpa only [← show t % 56 = 25 from ht, Nat.mod_add_div] using hcycle (t / 56)
  have hnum := (hpow.sub_right Nat.one_le_two_pow Nat.one_le_two_pow).mul_left 18107
  change 18107 * (2 ^ (15 * t) - 1) / 32767 % 11184810 = _
  rw [← Nat.mod_mul_right_div_self]
  exact (congrArg (· / 32767) hnum).trans (by decide +kernel)

end isSierpinskiNumber_repstring_18107

/-- **Binary repintegers of 18107 that are Sierpiński numbers.** For every natural number
$t \equiv 25 \pmod{56}$, the binary repinteger $18107_2^{(t)} = 18107\,(2^{15t} - 1)/(2^{15} - 1)$,
whose binary expansion is that of $18107$ (fifteen binary digits) written $t$ times, is a
Sierpiński number.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Theorem 3.5
(`integers-2026-A12-thm-3-5`). -/
public theorem isSierpinskiNumber_repstring_18107 {t : ℕ} (ht : t ≡ 25 [MOD 56]) :
    IsSierpinskiNumber (repstring 2 18107 0 t) := by
  let k := repstring 2 18107 0 t
  have hk : k ≡ 8007257 [MOD 11184810] := isSierpinskiNumber_repstring_18107.repinteger_modEq ht
  refine ⟨Nat.odd_iff.mpr (hk.of_dvd (by decide : 2 ∣ 11184810)), ?_⟩
  intro n _
  change ¬ (k * 2 ^ n + 1).Prime
  -- Each exponent class modulo 24 has a divisor among the six covering primes.
  have hcover : ∀ r : Fin 24, ∃ p ∈ [3, 7, 5, 17, 13, 241],
      2 ≤ p ∧ p ≤ 241 ∧ p ∣ 11184810 ∧ 2 ^ 24 ≡ 1 [MOD p] ∧
      8007257 * 2 ^ (r : ℕ) + 1 ≡ 0 [MOD p] := by decide
  obtain ⟨p, _, hp, hple, hmod, hperiod, hr⟩ := hcover ⟨n % 24, Nat.mod_lt _ (by decide)⟩
  have hpow : 2 ^ n ≡ 2 ^ (n % 24) [MOD p] := by
    conv_lhs => rw [← Nat.mod_add_div n 24, pow_add, pow_mul]
    simpa only [one_pow, mul_one] using (hperiod.pow (n / 24)).mul_left (2 ^ (n % 24))
  have hdvd : p ∣ k * 2 ^ n + 1 :=
    Nat.modEq_zero_iff_dvd.mp ((((hk.of_dvd hmod).mul hpow).add_right 1).trans hr)
  have hk_le : 8007257 ≤ k := calc
    8007257 = k % 11184810 := hk.symm
    _ ≤ k := Nat.mod_le _ _
  have := Nat.le_mul_of_pos_right k (by positivity : 0 < 2 ^ n)
  exact Nat.not_prime_of_dvd_of_lt hdvd hp (by omega)

end MetaMathlibExt
