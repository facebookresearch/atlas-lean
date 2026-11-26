/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PalindromeAPCountOfDvdBase
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.List.GetD

/-!
# Palindromes up to a power of the base

The divisor-of-the-base formula specializes using the digits of the cutoff and its palindromic
half copy. For a divisor of the base minus one, we count the even-length and odd-length prefixes
separately. In the odd-length count we fill the gaps in `h + h / b` and subtract their contribution;
the resulting interval contains complete residue blocks.

## References

* K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam,
  *Exact Formulas for the Number of Palindromes in Certain Arithmetic Progressions*,
  Journal of Integer Sequences 27 (2024), Article 24.4.8, pp. 1–29, Theorem 7 and Corollary 11.
-/

namespace MetaMathlibExt

open Finset Int

private theorem basePow_digits {b k : ℕ} (hb : 2 ≤ b) :
    b.digits (b ^ k) = List.replicate k 0 ++ [1] := by
  simpa only [mul_one, Nat.digits_of_lt b 1 one_ne_zero hb] using
    Nat.digits_base_pow_mul (k := k) hb Nat.zero_lt_one

private theorem basePow_digit {b k i : ℕ} (hb : 2 ≤ b) (hi : i ≤ k) :
    (b.digits (b ^ k)).getD i 0 = if i = k then 1 else 0 := by
  rw [basePow_digits hb]
  rcases hi.lt_or_eq with hi | rfl
  · rw [List.getD_append _ _ _ _ (by simpa using hi), List.getD_replicate _ hi, ite_eq_right hi.ne]
  · rw [List.getD_append_right _ _ _ _ (by simp), List.length_replicate, Nat.sub_self,
      ite_eq_left rfl]
    rfl

private theorem halfCopy_basePow {b k : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k) :
    palindromicHalfCopy b (b ^ k) = 1 + b ^ k := by
  have hlen : (b.digits (b ^ k)).length = k + 1 := by simp [basePow_digits hb]
  rw [palindromicHalfCopy, hlen, Nat.add_sub_cancel]
  calc
    _ = ∑ i ∈ range (k + 1), ((if i = 0 then 1 else 0) + (if i = k then b ^ k else 0)) := by
      apply sum_congr rfl
      intro i hi
      have hi' := mem_range.mp hi
      rw [basePow_digit hb (by omega)]
      by_cases h0 : i = 0
      · subst i
        simp [show 0 ≠ k by omega]
      by_cases hiₖ : i = k
      · subst i
        simp [show k ≠ 0 by omega]
      have hmid : max i (k - i) ≠ k := by omega
      simp [h0, hiₖ, hmid]
    _ = _ := by simp [sum_add_distrib]

private theorem basePow_of_dvd {b k q r : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k)
    (hq : 1 ≤ q) (hr : r < q) (hqb : q ∣ b) :
    (palindromeAPCount b (b ^ k) q r : ℚ) =
      ((b : ℚ) / q - (if r = 0 then 1 else 0)) *
        (((b : ℚ) ^ ((k + 1) / 2) + (b : ℚ) ^ (k / 2) - 2) / ((b : ℚ) - 1)) := by
  have hlen : (b.digits (b ^ k)).length = k + 1 := by simp [basePow_digits hb]
  have hlead : (b.digits (b ^ k)).getD k 0 = 1 := by
    rw [basePow_digit hb le_rfl, ite_eq_left rfl]
  have htail : ∑ i ∈ Icc 1 (k / 2), ((b.digits (b ^ k)).getD (k - i) 0 : ℚ) *
      (b : ℚ) ^ (k / 2 - i) = 0 := by
    apply sum_eq_zero
    intro i hi
    have hi' := mem_Icc.mp hi
    rw [basePow_digit hb (by omega), ite_eq_right (by omega), Nat.cast_zero, zero_mul]
  have hno : ¬ palindromicHalfCopy b (b ^ k) ≤ b ^ k := by rw [halfCopy_basePow hb hk]; omega
  have H := palindromeAPCount_of_dvd_base hb (m := b ^ k) (Nat.one_le_pow _ _ (by omega)) hq hqb
  dsimp only at H
  simp only [hlen, Nat.add_sub_cancel, hlead, htail, hno, ite_false, add_zero, mul_zero] at H
  by_cases hz : r = 0
  · subst r
    simpa using H.1
  · have hceil : ⌈((1 : ℚ) - r) / q⌉ = 0 := by
      have hq' : (0 : ℚ) < q := by positivity
      rw [Int.ceil_eq_zero_iff, Set.mem_Ioc, lt_div_iff₀ hq', div_le_iff₀ hq']
      have hpos : (1 : ℚ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
      have hlt : (r : ℚ) < q := by exact_mod_cast hr
      constructor <;> linarith
    have J := H.2 r (by rw [Nat.mod_eq_of_lt hr]; omega)
    simp only [Nat.mod_eq_of_lt hr, Nat.cast_one, hceil, Int.cast_zero, zero_mul, add_zero] at J
    rw [J, ite_eq_right hz, sub_zero]
    ring

-- A positive interval of length divisible by q contains only complete residue blocks.
private theorem card_residue {n q : ℕ} (hq : 0 < q) (hqn : q ∣ n) (r : ℕ) :
    (((Ioc 0 n).filter fun x => x ≡ r [MOD q]).card : ℚ) = (n : ℚ) / q := by
  obtain ⟨m, rfl⟩ := hqn
  have hq' : (q : ℚ) ≠ 0 := by positivity
  have hdiv : (((q * m : ℕ) : ℚ) - r) / q = -(r : ℚ) / q + m := by
    push_cast
    field_simp
    ring
  have H := Nat.Ioc_filter_modEq_card 0 (q * m) hq r
  rw [hdiv, Int.floor_add_natCast] at H
  simp only [Nat.cast_zero, zero_sub, add_sub_cancel_left, max_eq_left (Int.natCast_nonneg m)] at H
  have H' : ((Ioc 0 (q * m)).filter fun x => x ≡ r [MOD q]).card = m := by exact_mod_cast H
  rw [H', Nat.cast_mul, mul_div_cancel_left₀ _ hq']

private theorem card_double_residue {n q : ℕ} (hq : 0 < q) (hqn : q ∣ n) (r : ℕ) :
    (((Ioc 0 n).filter fun x => 2 * x ≡ r [MOD q]).card : ℚ) =
      if Odd q then (n : ℚ) / q else if Odd r then 0 else 2 * (n : ℚ) / q := by
  by_cases hqo : Odd q
  · rw [ite_eq_left hqo]
    let u := (q + 1) / 2
    have hu : u * 2 ≡ 1 [MOD q] := by
      have h : u * 2 = 1 + q := by obtain ⟨t, ht⟩ := hqo; dsimp [u]; omega
      rw [h, Nat.add_modulus_modEq_iff]
    have h (x : ℕ) : 2 * x ≡ r [MOD q] ↔ x ≡ u * r [MOD q] := by
      constructor
      · intro H
        exact (by simpa [mul_assoc] using hu.symm.mul_right x :
          x ≡ u * (2 * x) [MOD q]).trans (H.mul_left u)
      · intro H
        have hu' : 2 * u ≡ 1 [MOD q] := by rwa [mul_comm 2 u]
        exact (H.mul_left 2).trans (by simpa only [mul_assoc, one_mul] using hu'.mul_right r)
    simp_rw [h]
    exact card_residue hq hqn _
  rw [ite_eq_right hqo]
  obtain ⟨d, hd⟩ := Nat.not_odd_iff_even.mp hqo
  have hqd : q = 2 * d := by omega
  by_cases hro : Odd r
  · rw [ite_eq_left hro, filter_false_of_mem]
    · simp
    intro x _ H
    have H' := H.of_dvd (show 2 ∣ q from ⟨d, hqd⟩)
    simp [Nat.ModEq, Nat.odd_iff.mp hro] at H'
  · rw [ite_eq_right hro]
    obtain ⟨s, hs⟩ := Nat.not_odd_iff_even.mp hro
    have hrs : r = 2 * s := by omega
    have hd' : 0 < d := by omega
    have hdn : d ∣ n := (show d ∣ q from ⟨2, by omega⟩).trans hqn
    simp only [hqd, hrs, Nat.ModEq.mul_left_cancel_iff' (by decide : 2 ≠ 0), card_residue hd' hdn]
    have : (d : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp

private theorem basePow_of_modEq_one {b k q : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k)
    (hq : 1 ≤ q) (hbq : b ≡ 1 [MOD q]) (r : ℕ) :
    (palindromeAPCount b (b ^ k) q r : ℚ) =
      if Odd q then ((b : ℚ) ^ ((k + 1) / 2) + (b : ℚ) ^ (k / 2) - 2) / q
      else if Odd r then ((b : ℚ) - 1) * (b : ℚ) ^ ((k - 1) / 2) / q
      else (((b : ℚ) + 1) * (b : ℚ) ^ ((k - 1) / 2) + 2 * (b : ℚ) ^ (k / 2) - 4) / q := by
  have hpos (j : ℕ) : 1 ≤ b ^ j := Nat.one_le_pow _ _ (by omega)
  have hd (j : ℕ) : q ∣ b ^ j - 1 :=
    (Nat.modEq_iff_dvd' (hpos j)).mp (by simpa using (hbq.pow j).symm)
  have he (j : ℕ) : 2 ≤ (b + 1) * b ^ j := by
    calc
      2 ≤ b + 1 := by omega
      _ ≤ (b + 1) * b ^ j := Nat.le_mul_of_pos_right _ (by positivity)
  have htotal (j : ℕ) : q ∣ (b + 1) * b ^ j - 2 :=
    (Nat.modEq_iff_dvd' (he j)).mp (by simpa using ((hbq.add_right 1).mul (hbq.pow j)).symm)
  have H := congrArg (fun n : ℕ => (n : ℚ)) (palindromeAPCount_base_pow_add_skipped_eq hb hk hbq r)
  push_cast only [Nat.cast_add] at H
  rw [card_double_residue (by omega) (hd _), card_double_residue (by omega) (hd _),
    card_residue (by omega) (htotal _)] at H
  push_cast only [Nat.cast_sub (he _), Nat.cast_sub (hpos _), Nat.cast_add, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat] at H
  have hpow : (b : ℚ) ^ ((k + 1) / 2) = (b : ℚ) ^ ((k - 1) / 2) * b := by
    rw [show (k + 1) / 2 = (k - 1) / 2 + 1 by omega, pow_succ]
  rw [hpow, eq_sub_of_add_eq H]
  by_cases hqo : Odd q
  · simp only [hqo, ite_true]
    ring
  · have hrParity : Odd (r + 1) ↔ ¬ Odd r := by simp [Nat.odd_iff]; omega
    by_cases hro : Odd r <;> simp [hqo, hro, hrParity] <;> ring

/-- **Palindromes up to a power of the base in residue classes.** Let $b \ge 2$, $k \ge 1$ and
$q \ge 1$ be natural numbers and let $r$ be a natural number with $r < q$. Write $A_b(m, q, r)$
for the number of base-$b$ palindromes $n$ with $1 \le n \le m$ and $n \equiv r \pmod q$, and
$[r = 0]$ for $1$ if $r = 0$ and $0$ otherwise. If $q \mid b$, then

$$A_b(b^k, q, r) = \left(\frac{b}{q} - [r = 0]\right)
\frac{b^{\lceil k/2 \rceil} + b^{\lfloor k/2 \rfloor} - 2}{b - 1}.$$

If $b \equiv 1 \pmod q$, then $A_b(b^k, q, r)$ equals
$(b^{\lceil k/2 \rceil} + b^{\lfloor k/2 \rfloor} - 2)/q$ if $q$ is odd,
$(b - 1) b^{\lfloor (k-1)/2 \rfloor}/q$ if $q$ is even and $r$ is odd, and
$((b + 1) b^{\lfloor (k-1)/2 \rfloor} + 2 b^{\lfloor k/2 \rfloor} - 4)/q$ if $q$ and $r$ are both
even. All these identities hold as identities of rational numbers.

Source: K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact
Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer
Sequences 27 (2024), Article 24.4.8, Corollary 11. -/
public theorem palindromeAPCount_base_pow {b k q r : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k)
    (hq : 1 ≤ q) (hr : r < q) :
    (q ∣ b →
      (palindromeAPCount b (b ^ k) q r : ℚ) =
        ((b : ℚ) / q - (if r = 0 then 1 else 0)) *
          (((b : ℚ) ^ ((k + 1) / 2) + (b : ℚ) ^ (k / 2) - 2) / ((b : ℚ) - 1))) ∧
    (b ≡ 1 [MOD q] →
      (palindromeAPCount b (b ^ k) q r : ℚ) =
        if Odd q then ((b : ℚ) ^ ((k + 1) / 2) + (b : ℚ) ^ (k / 2) - 2) / q
        else if Odd r then ((b : ℚ) - 1) * (b : ℚ) ^ ((k - 1) / 2) / q
        else (((b : ℚ) + 1) * (b : ℚ) ^ ((k - 1) / 2) + 2 * (b : ℚ) ^ (k / 2) - 4) / q) := by
  exact ⟨basePow_of_dvd hb hk hq hr, fun hbq => basePow_of_modEq_one hb hk hq hbq r⟩

end MetaMathlibExt
