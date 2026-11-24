/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# The gcd-term sequence

We bound the coefficients of the generating function by counting pairs on a natural-number
antidiagonal. A finite geometric sum gives a double-remainder formula for the gcd in base five.
-/

namespace MetaMathlibExt

open PowerSeries

@[expose] public section

/-- **The gcd-term sequence.** For natural numbers $a$, $b$ and $n$, $s_{a,b}(n)$ is the rational
number that is the coefficient of $z^n$ in the inverse of the formal power series
$(z^a - 1)(z^b - 1)$ over $\mathbb{Q}$. For $a, b \ge 1$ this series has constant coefficient $1$,
so $s_{a,b}$ is the coefficient sequence of $f_{a,b}(z) = 1 / ((z^a - 1)(z^b - 1))$. If $a = 0$
or $b = 0$ the series is $0$, whose inverse is taken to be $0$, so $s_{a,b}(n) = 0$.

Source: Mihai Prunescu and Joseph M. Shunia, *Arithmetic-Term Representations for the Greatest
Common Divisor*, INTEGERS 26 (2026), Article A96, Section 2 (definition of `s_{a,b}`). -/
public noncomputable def gcdTermSeq (a b n : ℕ) : ℚ :=
  coeff n (((X : ℚ⟦X⟧) ^ a - 1) * ((X : ℚ⟦X⟧) ^ b - 1))⁻¹

/-- **Initial value of the gcd-term sequence.** For natural numbers $a, b \ge 1$, the gcd-term
sequence satisfies $s_{a,b}(0) = 1$.

Source: Prunescu and Shunia, *Arithmetic-Term Representations for the Greatest Common Divisor*,
INTEGERS 26 (2026), Article A96, Section 2. -/
public theorem gcdTermSeq_zero (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) : gcdTermSeq a b 0 = 1 := by
  have ha' : a ≠ 0 := by omega
  have hb' : b ≠ 0 := by omega
  simp [gcdTermSeq, ha', hb']

/-- **Generating function of the gcd-term sequence.** For natural numbers $a, b \ge 1$, in the
ring $\mathbb{Q}[[z]]$ of formal power series, the gcd-term sequence $s_{a,b}$ satisfies
$$
(z^a - 1)(z^b - 1) \sum_{n \ge 0} s_{a,b}(n) z^n = 1.
$$

Source: Prunescu and Shunia, *Arithmetic-Term Representations for the Greatest Common Divisor*,
INTEGERS 26 (2026), Article A96, Section 2. -/
public theorem mul_mk_gcdTermSeq (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ((X : ℚ⟦X⟧) ^ a - 1) * ((X : ℚ⟦X⟧) ^ b - 1) * PowerSeries.mk (gcdTermSeq a b) = 1 := by
  have ha' : a ≠ 0 := by omega
  have hb' : b ≠ 0 := by omega
  have hmk : PowerSeries.mk (gcdTermSeq a b) =
      (((X : ℚ⟦X⟧) ^ a - 1) * ((X : ℚ⟦X⟧) ^ b - 1))⁻¹ := by
    ext n
    simp [gcdTermSeq]
  rw [hmk]
  apply PowerSeries.mul_inv_cancel
  simp [ha', hb']

namespace gcdTermSeq_le_gcdTermSeq_one_one

private theorem coeff_inv_one_sub_X_pow (d : ℕ) (hd : d ≠ 0) (k : ℕ) :
    coeff k ((1 - X ^ d : ℚ⟦X⟧)⁻¹) = if d ∣ k then 1 else 0 := by
  have hinv : (1 - X ^ d : ℚ⟦X⟧)⁻¹ = expand d hd (mk 1) := by
    apply (inv_eq_iff_mul_eq_one (by simp [hd])).2
    simpa using congrArg (expand d hd) (mk_one_mul_one_sub_eq_one ℚ)
  simp [hinv, coeff_expand]

private theorem eq_card (a b n : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    gcdTermSeq a b n =
      ((Finset.antidiagonal n).filter fun p => a ∣ p.1 ∧ b ∣ p.2).card := by
  have hden : (X ^ a - 1 : ℚ⟦X⟧) * (X ^ b - 1) = (1 - X ^ b) * (1 - X ^ a) := by
    ring
  rw [gcdTermSeq, hden, PowerSeries.mul_inv_rev, coeff_mul, Finset.natCast_card_filter]
  apply Finset.sum_congr rfl
  intro p _
  rw [coeff_inv_one_sub_X_pow a (by omega), coeff_inv_one_sub_X_pow b (by omega)]
  by_cases h : a ∣ p.1 <;> simp [h]

end gcdTermSeq_le_gcdTermSeq_one_one

open gcdTermSeq_le_gcdTermSeq_one_one in
/-- **The gcd-term sequence is bounded by $n + 1$.** Let $a, b \ge 1$ be natural numbers, at least
one of them greater than $1$, and let $s_{a,b}$ be the gcd-term sequence. For every natural
number $n$, $s_{a,b}(n) \le s_{1,1}(n) = n + 1$, and $s_{a,b}(n) = s_{1,1}(n)$ only if $n = 0$.

Source: Mihai Prunescu and Joseph M. Shunia, *Arithmetic-Term Representations for the Greatest
Common Divisor*, INTEGERS 26 (2026), Article A96, Lemma 5. -/
public theorem gcdTermSeq_le_gcdTermSeq_one_one (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hab : 1 < a ∨ 1 < b) (n : ℕ) :
    gcdTermSeq a b n ≤ gcdTermSeq 1 1 n ∧ gcdTermSeq 1 1 n = n + 1 ∧
      (gcdTermSeq a b n = gcdTermSeq 1 1 n → n = 0) := by
  have h₁₁ : gcdTermSeq 1 1 n = ((Finset.antidiagonal n).card : ℚ) := by
    simp [eq_card 1 1 n le_rfl le_rfl]
  rw [h₁₁, eq_card a b n ha hb]
  refine ⟨by exact_mod_cast Finset.card_filter_le _ _, by simp, ?_⟩
  intro heq
  have hall := Finset.card_filter_eq_iff.mp (Nat.cast_injective heq)
  cases n with
  | zero => rfl
  | succ k =>
    have ha₁ := (hall (1, k) (by simp [Nat.add_comm])).1
    have hb₁ := (hall (k, 1) (by simp)).2
    simp only [Nat.dvd_one] at ha₁ hb₁
    omega

open gcdTermSeq_le_gcdTermSeq_one_one in
/-- **The gcd-term sequence is integral and recovers the gcd.** Let $a, b \ge 1$ be natural
numbers and let $s_{a,b}$ be the gcd-term sequence. Every value $s_{a,b}(n)$ is a natural number,
and $s_{a,b}(ab) = \gcd(a, b) + 1$.

Source: Mihai Prunescu and Joseph M. Shunia, *Arithmetic-Term Representations for the Greatest
Common Divisor*, INTEGERS 26 (2026), Article A96, Lemma 4. -/
public theorem gcdTermSeq_natural_and_eq_gcd_add_one (a b : ℕ) (ha : 1 ≤ a)
    (hb : 1 ≤ b) :
    (∀ n, ∃ m : ℕ, gcdTermSeq a b n = m) ∧ gcdTermSeq a b (a * b) = Nat.gcd a b + 1 := by
  constructor
  · intro n
    exact ⟨_, eq_card a b n ha hb⟩
  rw [eq_card a b (a * b) ha hb]
  norm_cast
  -- Since b divides ab, it divides ab - i exactly when it divides i.
  calc
    _ = ((Finset.range (a * b + 1)).filter (Nat.lcm a b ∣ ·)).card := by
      rw [Finset.Nat.antidiagonal_eq_map, Finset.filter_map, Finset.card_map]
      apply congrArg Finset.card
      apply Finset.filter_congr
      intro i hi
      change (a ∣ i ∧ b ∣ a * b - i) ↔ Nat.lcm a b ∣ i
      rw [Nat.dvd_sub_iff_right (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) (dvd_mul_left b a),
        Nat.lcm_dvd_iff]
    _ = a * b / Nat.lcm a b + 1 := by
      rw [Nat.range_succ_eq_Icc_zero, ← Finset.insert_left_Ioc (Nat.zero_le (a * b)),
        Finset.filter_insert, ite_eq_left (dvd_zero _), Finset.card_insert_of_notMem (by simp),
        Nat.Ioc_filter_dvd_card_eq_div]
    _ = Nat.gcd a b + 1 := by
      rw [← Nat.gcd_mul_lcm a b, Nat.mul_div_cancel _ (Nat.lcm_pos ha hb)]

namespace gcd_eq_neg_emod_emod_five_sub_two

open Finset

-- Reducing the exponents modulo b uses q ^ b ≡ 1 modulo q ^ b - 1.
private def reducedSum (q : ℤ) (a b : ℕ) : ℤ :=
  ∑ i ∈ range (b + 1), q ^ (a * i % b)

private theorem numerator_modEq (q : ℤ) (a b : ℕ) :
    q ^ (a * b + a + b) ≡ q ^ b + (q ^ a - 1) * reducedSum q a b
      [ZMOD (q ^ a - 1) * (q ^ b - 1)] := by
  have hB := Int.modEq_sub (q ^ b) 1
  have hsum : (∑ i ∈ range (b + 1), (q ^ a) ^ i) ≡ reducedSum q a b [ZMOD q ^ b - 1] := by
    apply Int.ModEq.sum
    intro i _
    rw [← pow_mul]
    calc
      q ^ (a * i) = q ^ (a * i % b) * (q ^ b) ^ (a * i / b) := by
        rw [← pow_mul, ← pow_add, Nat.mod_add_div]
      _ ≡ q ^ (a * i % b) [ZMOD q ^ b - 1] := by
        simpa using (hB.pow (a * i / b)).mul_left (q ^ (a * i % b))
  have h := (hB.mul hsum).mul_left' (c := q ^ a - 1)
  simp only [one_mul] at h
  calc
    q ^ (a * b + a + b) =
        q ^ b + (q ^ a - 1) * (q ^ b * ∑ i ∈ range (b + 1), (q ^ a) ^ i) := by
      rw [show a * b + a + b = b + a * (b + 1) by ring, pow_add, pow_mul]
      linear_combination q ^ b * (mul_geom_sum (q ^ a) (b + 1)).symm
    _ ≡ _ [ZMOD _] := h.add_left _

-- The bound on each exponent makes this representative strictly smaller than the modulus.
private theorem remainder_bounds {q : ℤ} {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hq : 2 * (b + 1 : ℤ) < q) :
    0 < q ^ b + (q ^ a - 1) * reducedSum q a b ∧
      q ^ b + (q ^ a - 1) * reducedSum q a b < (q ^ a - 1) * (q ^ b - 1) := by
  have hq₅ : 5 ≤ q := by omega
  have hA : 5 ≤ q ^ a := hq₅.trans (by simpa using pow_le_pow_right₀ (by omega : 1 ≤ q) ha)
  have hB : 5 ≤ q ^ b := hq₅.trans (by simpa using pow_le_pow_right₀ (by omega : 1 ≤ q) hb)
  have hs : 0 ≤ reducedSum q a b := sum_nonneg fun i _ => pow_nonneg (by omega) _
  have hbound : reducedSum q a b ≤ (b + 1 : ℤ) * q ^ (b - 1) := by
    calc
      _ ≤ ∑ _i ∈ range (b + 1), q ^ (b - 1) := by
        apply sum_le_sum
        intro i _
        apply pow_le_pow_right₀ (by omega)
        have := Nat.mod_lt (a * i) hb
        omega
      _ = _ := by simp
  have hhalf : 2 * reducedSum q a b ≤ q ^ b := calc
    _ ≤ (2 * (b + 1 : ℤ)) * q ^ (b - 1) := by linarith
    _ ≤ q * q ^ (b - 1) := by gcongr
    _ = _ := by rw [← pow_succ', Nat.sub_add_cancel hb]
  constructor
  · exact add_pos_of_pos_of_nonneg (by omega) (mul_nonneg (by omega) hs)
  · nlinarith [mul_nonneg (show 0 ≤ q ^ a - 5 by omega) (show 0 ≤ q ^ b - 2 by omega),
      mul_nonneg (show 0 ≤ q ^ a - 1 by omega) (show 0 ≤ q ^ b - 2 * reducedSum q a b by omega)]

-- The constant terms occur at the multiples of b / gcd(b,a), including both endpoints.
private theorem reducedSum_modEq (q : ℤ) (a b : ℕ) (hb : 1 ≤ b) :
    reducedSum q a b ≡ (Nat.gcd a b : ℤ) + 1 [ZMOD q] := by
  let d := b.gcd a
  have hd : d ∣ b := Nat.gcd_dvd_left ..
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left a hb
  have hiff (i : ℕ) : b ∣ a * i ↔ b / d ∣ i :=
    Nat.dvd_gcd_mul_iff_dvd_mul.symm.trans (Nat.div_dvd_iff_dvd_mul hd hdpos).symm
  calc
    reducedSum q a b ≡ ∑ i ∈ range (b + 1), (if b / d ∣ i then 1 else 0 : ℤ) [ZMOD q] := by
      apply Int.ModEq.sum
      intro i _
      by_cases hi : b ∣ a * i
      · simp [Nat.mod_eq_zero_of_dvd hi, (hiff i).mp hi]
      · rw [ite_eq_right (hi ∘ (hiff i).mpr)]
        exact Int.modEq_zero_iff_dvd.mpr (dvd_pow_self q (fun h => hi (Nat.dvd_of_mod_eq_zero h)))
    _ = _ := by
      rw [← natCast_card_filter, Nat.range_succ_eq_Icc_zero,
        ← insert_left_Ioc (Nat.zero_le b), filter_insert, ite_eq_left (dvd_zero _),
        card_insert_of_notMem (by simp), Nat.Ioc_filter_dvd_card_eq_div,
        Nat.div_div_self hd (by omega)]
      simp [d, Nat.gcd_comm]

end gcd_eq_neg_emod_emod_five_sub_two

open gcd_eq_neg_emod_emod_five_sub_two in
/-- **Second arithmetic term for the gcd in base $5$.** For all natural numbers $a, b \ge 1$,
$$
\gcd(a, b) = \Big( \big( (-5^{ab(ab+a+b)}) \bmod \big( (5^{a^2 b} - 1)(5^{a b^2} - 1) \big) \big)
\bmod 5^{ab} \Big) - 2
$$
in the integers, where $x \bmod m$ is the remainder of $x$ in $\{0, \dots, m - 1\}$ for $m > 0$,
also when $x < 0$.

Source: Mihai Prunescu and Joseph M. Shunia, *Arithmetic-Term Representations for the Greatest
Common Divisor*, INTEGERS 26 (2026), Article A96, Corollary 1. -/
public theorem gcd_eq_neg_emod_emod_five_sub_two (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (Nat.gcd a b : ℤ) =
      (-(5 : ℤ) ^ (a * b * (a * b + a + b))) %
          (((5 : ℤ) ^ (a ^ 2 * b) - 1) * ((5 : ℤ) ^ (a * b ^ 2) - 1)) %
        (5 : ℤ) ^ (a * b) - 2 := by
  let q := (5 : ℤ) ^ (a * b)
  have hq : 2 * (b + 1 : ℤ) < q := by
    have h := one_add_mul_le_pow (by norm_num : (-2 : ℤ) ≤ 4) (a * b)
    have hab := Nat.le_mul_of_pos_left b ha
    change _ < (1 + 4 : ℤ) ^ (a * b)
    omega
  let D := (q ^ a - 1) * (q ^ b - 1)
  let R := q ^ b + (q ^ a - 1) * reducedSum q a b
  have hnum := numerator_modEq q a b
  have ⟨hpos, hlt⟩ := remainder_bounds ha hb hq
  have hfirst : (-q ^ (a * b + a + b)) % D = D - R := by
    have hneg : -q ^ (a * b + a + b) ≡ D - R [ZMOD D] := by
      rw [sub_eq_add_neg, Int.modEq_modulus_add_iff]
      exact hnum.neg
    rw [hneg.eq, Int.emod_eq_of_lt (by dsimp [D, R]; omega) (by dsimp [D, R]; omega)]
  have hA : q ^ a ≡ 0 [ZMOD q] := Int.modEq_zero_iff_dvd.mpr (dvd_pow_self _ (by omega))
  have hB : q ^ b ≡ 0 [ZMOD q] := Int.modEq_zero_iff_dvd.mpr (dvd_pow_self _ (by omega))
  have hS := reducedSum_modEq q a b hb
  have hres : D - R ≡ (a.gcd b : ℤ) + 2 [ZMOD q] := by
    have h := ((hA.sub_right 1).mul (hB.sub_right 1)).sub
      (hB.add ((hA.sub_right 1).mul hS))
    convert h using 1
    ring
  have hg := Nat.gcd_le_right a hb
  have hsmall : (a.gcd b : ℤ) + 2 < q := by omega
  have hpowA : a ^ 2 * b = (a * b) * a := by ring
  have hpowB : a * b ^ 2 = (a * b) * b := by ring
  rw [hpowA, hpowB, pow_mul (5 : ℤ) (a * b) a, pow_mul (5 : ℤ) (a * b) b,
    pow_mul (5 : ℤ) (a * b) (a * b + a + b)]
  change _ = (-q ^ (a * b + a + b)) % D % q - 2
  rw [hfirst, hres.eq, Int.emod_eq_of_lt (by positivity) hsmall]
  omega

end

end MetaMathlibExt
