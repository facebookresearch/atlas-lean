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
The same argument gives the floor-division and double-remainder gcd terms in bases two, three and
four.
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


namespace gcd_arithmetic_terms_small_bases

open gcd_eq_neg_emod_emod_five_sub_two

-- This adapts the proof of `gcd_eq_neg_emod_emod_five_sub_two` from base five to any base `c`
-- with `2 * (b + 1) < c ^ (a * b)`.
private theorem emod_of_bound (c : ℤ) (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hbound : 2 * ((b : ℤ) + 1) < c ^ (a * b)) :
    (Nat.gcd a b : ℤ) =
      (-c ^ (a * b * (a * b + a + b))) %
          ((c ^ (a ^ 2 * b) - 1) * (c ^ (a * b ^ 2) - 1)) %
        c ^ (a * b) - 2 := by
  let q := c ^ (a * b)
  have hq : 2 * (b + 1 : ℤ) < q := hbound
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
  have hpowE : a * b * (a * b + a + b) = (a * b) * (a * b + a + b) := by ring
  rw [hpowA, hpowB, hpowE, pow_mul c (a * b) a, pow_mul c (a * b) b,
    pow_mul c (a * b) (a * b + a + b)]
  change _ = (-q ^ (a * b + a + b)) % D % q - 2
  rw [hfirst, hres.eq, Int.emod_eq_of_lt (by positivity) hsmall]
  omega

-- The same argument, with the quotient in place of the negated remainder.
private theorem floor_of_bound (c : ℤ) (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hbound : 2 * ((b : ℤ) + 1) < c ^ (a * b)) :
    (Nat.gcd a b : ℤ) =
      c ^ (a * b * (a * b + a + b)) / ((c ^ (a ^ 2 * b) - 1) * (c ^ (a * b ^ 2) - 1)) %
        c ^ (a * b) - 1 := by
  let q := c ^ (a * b)
  have hq : 2 * (b + 1 : ℤ) < q := hbound
  let N := q ^ (a * b + a + b)
  let D := (q ^ a - 1) * (q ^ b - 1)
  let S := reducedSum q a b
  let R := q ^ b + (q ^ a - 1) * S
  let Q := N / D
  have hnum := numerator_modEq q a b
  have ⟨hpos, hlt⟩ := remainder_bounds ha hb hq
  have hNmod : N % D = R := by
    have heq : N % D = R % D := by
      have h : N ≡ R [ZMOD D] := hnum
      exact h.eq
    rw [heq, Int.emod_eq_of_lt (by dsimp [R, D, S]; omega) (by dsimp [R, D, S]; omega)]
  have hEq : N = D * Q + R := by
    rw [← hNmod]
    exact (Int.mul_ediv_add_emod _ _).symm
  have hA : q ^ a ≡ 0 [ZMOD q] := Int.modEq_zero_iff_dvd.mpr (dvd_pow_self _ (by omega))
  have hB : q ^ b ≡ 0 [ZMOD q] := Int.modEq_zero_iff_dvd.mpr (dvd_pow_self _ (by omega))
  have hS : S ≡ (a.gcd b : ℤ) + 1 [ZMOD q] := reducedSum_modEq q a b hb
  have hN0 : N ≡ 0 [ZMOD q] :=
    Int.modEq_zero_iff_dvd.mpr (dvd_pow_self _ (by dsimp [N]; omega))
  have hD1 : D ≡ 1 [ZMOD q] := by
    have h := (hA.sub_right 1).mul (hB.sub_right 1)
    convert h using 1
    ring
  have hR : R ≡ -(S) [ZMOD q] := by
    have h := hB.add ((hA.sub_right 1).mul (Int.ModEq.refl S))
    convert h using 1
    ring
  have hMod : D * Q + R ≡ (1 : ℤ) * Q + (-(S)) [ZMOD q] := (hD1.mul_right Q).add hR
  have hEqMod : N ≡ D * Q + R [ZMOD q] := by rw [hEq]
  have h0 : D * Q + R ≡ 0 [ZMOD q] := hEqMod.symm.trans hN0
  have h1 : (1 : ℤ) * Q + (-(S)) ≡ 0 [ZMOD q] := hMod.symm.trans h0
  have h2 : Q - S ≡ 0 [ZMOD q] := by
    convert h1 using 1
    ring
  have hQS : Q ≡ S [ZMOD q] := by
    have h := h2.add_right S
    simpa using h
  have hQ : Q ≡ (a.gcd b : ℤ) + 1 [ZMOD q] := hQS.trans hS
  have hg := Nat.gcd_le_right a hb
  have hsmall : (a.gcd b : ℤ) + 1 < q := by omega
  have hQmod : Q % q = (a.gcd b : ℤ) + 1 := by
    rw [hQ.eq, Int.emod_eq_of_lt (by positivity) hsmall]
  have hpowA : a ^ 2 * b = (a * b) * a := by ring
  have hpowB : a * b ^ 2 = (a * b) * b := by ring
  have hpowE : a * b * (a * b + a + b) = (a * b) * (a * b + a + b) := by ring
  rw [hpowA, hpowB, hpowE, pow_mul c (a * b) a, pow_mul c (a * b) b,
    pow_mul c (a * b) (a * b + a + b)]
  change _ = Q % q - 1
  omega

private theorem pow_bound_two_mul (k : ℕ) (hk : 2 ≤ k) :
    2 * ((k : ℤ) + 1) < (2 : ℤ) ^ (2 * k) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hpow : (2 : ℤ) ^ (2 * (n + 1)) = 4 * (2 : ℤ) ^ (2 * n) := by
      rw [show 2 * (n + 1) = 2 * n + 2 by ring, pow_add]
      norm_num
      ring
    rw [hpow]
    push_cast
    have hn' : (2 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
    linarith

private theorem pow_bound_four_lt (b : ℕ) (hb : 3 ≤ b) : (4 : ℤ) < (2 : ℤ) ^ b := by
  induction b, hb using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hpow : (2 : ℤ) ^ (n + 1) = 2 * (2 : ℤ) ^ n := by
      rw [pow_add]
      norm_num
      ring
    rw [hpow]
    have hpos : (0 : ℤ) < (2 : ℤ) ^ n := by positivity
    linarith

private theorem bound_or_base2 (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h11 : (a, b) ≠ (1, 1)) (h12 : (a, b) ≠ (1, 2)) (h21 : (a, b) ≠ (2, 1)) :
    2 * ((a : ℤ) + 1) < (2 : ℤ) ^ (a * b) ∨
      2 * ((b : ℤ) + 1) < (2 : ℤ) ^ (a * b) := by
  by_cases hle : a ≤ b
  · left
    by_cases ha1 : a = 1
    · subst ha1
      have hb_ne1 : b ≠ 1 := by simpa using h11
      have hb_ne2 : b ≠ 2 := by simpa using h12
      have hb3 : 3 ≤ b := by omega
      have h4 := pow_bound_four_lt b hb3
      simpa using h4
    · have ha2 : 2 ≤ a := by omega
      have hb2 : 2 ≤ b := le_trans ha2 hle
      have hab_ge : 2 * a ≤ a * b := by
        rw [mul_comm 2 a]
        gcongr
      have hpow_ge : (2 : ℤ) ^ (2 * a) ≤ (2 : ℤ) ^ (a * b) :=
        pow_le_pow_right₀ (by norm_num) hab_ge
      exact lt_of_lt_of_le (pow_bound_two_mul a ha2) hpow_ge
  · right
    by_cases hb1 : b = 1
    · subst hb1
      have ha_ne1 : a ≠ 1 := by simpa using h11
      have ha_ne2 : a ≠ 2 := by simpa using h21
      have ha3 : 3 ≤ a := by omega
      have h4 := pow_bound_four_lt a ha3
      simpa using h4
    · have hb2 : 2 ≤ b := by omega
      have ha2 : 2 ≤ a := by omega
      have hab_ge : 2 * b ≤ a * b := by gcongr
      have hpow_ge : (2 : ℤ) ^ (2 * b) ≤ (2 : ℤ) ^ (a * b) :=
        pow_le_pow_right₀ (by norm_num) hab_ge
      exact lt_of_lt_of_le (pow_bound_two_mul b hb2) hpow_ge

private theorem bound_or_base_ge3 (c : ℤ) (hc : 3 ≤ c) (a b : ℕ) (ha : 1 ≤ a)
    (hb : 1 ≤ b) (h11 : (a, b) ≠ (1, 1)) :
    2 * ((a : ℤ) + 1) < c ^ (a * b) ∨ 2 * ((b : ℤ) + 1) < c ^ (a * b) := by
  by_cases hle : a ≤ b
  · left
    by_cases ha1 : a = 1
    · subst ha1
      have hb_ne : b ≠ 1 := by simpa using h11
      have hb2 : 2 ≤ b := by omega
      have h9 : (9 : ℤ) ≤ (3 : ℤ) ^ b := by
        have h : (3 : ℤ) ^ 2 ≤ (3 : ℤ) ^ b := pow_le_pow_right₀ (by norm_num) hb2
        norm_num at h
        exact h
      have hcb : (3 : ℤ) ^ b ≤ c ^ b := pow_le_pow_left₀ (by norm_num) hc b
      have hab : 1 * b = b := one_mul b
      rw [hab]
      norm_num
      linarith
    · have ha2 : 2 ≤ a := by omega
      have hb2 : 2 ≤ b := le_trans ha2 hle
      have hab_ge : 2 * a ≤ a * b := by
        rw [mul_comm 2 a]
        gcongr
      have h2ge : (2 : ℤ) ^ (2 * a) ≤ (2 : ℤ) ^ (a * b) :=
        pow_le_pow_right₀ (by norm_num) hab_ge
      have h2c : (2 : ℤ) ≤ c := by omega
      have hcb : (2 : ℤ) ^ (a * b) ≤ c ^ (a * b) :=
        pow_le_pow_left₀ (by norm_num) h2c _
      exact lt_of_lt_of_le (pow_bound_two_mul a ha2) (le_trans h2ge hcb)
  · right
    by_cases hb1 : b = 1
    · subst hb1
      have ha_ne : a ≠ 1 := by simpa using h11
      have ha2 : 2 ≤ a := by omega
      have h9 : (9 : ℤ) ≤ (3 : ℤ) ^ a := by
        have h : (3 : ℤ) ^ 2 ≤ (3 : ℤ) ^ a := pow_le_pow_right₀ (by norm_num) ha2
        norm_num at h
        exact h
      have hca : (3 : ℤ) ^ a ≤ c ^ a := pow_le_pow_left₀ (by norm_num) hc a
      have hab : a * 1 = a := mul_one a
      rw [hab]
      norm_num
      linarith
    · have hb2 : 2 ≤ b := by omega
      have ha2 : 2 ≤ a := by omega
      have hab_ge : 2 * b ≤ a * b := by gcongr
      have h2ge : (2 : ℤ) ^ (2 * b) ≤ (2 : ℤ) ^ (a * b) :=
        pow_le_pow_right₀ (by norm_num) hab_ge
      have h2c : (2 : ℤ) ≤ c := by omega
      have hcb : (2 : ℤ) ^ (a * b) ≤ c ^ (a * b) :=
        pow_le_pow_left₀ (by norm_num) h2c _
      exact lt_of_lt_of_le (pow_bound_two_mul b hb2) (le_trans h2ge hcb)

private theorem floor_symm (c : ℤ) (a b : ℕ) :
    ((Nat.gcd a b : ℤ) =
        c ^ (a * b * (a * b + a + b)) / ((c ^ (a ^ 2 * b) - 1) * (c ^ (a * b ^ 2) - 1)) %
            c ^ (a * b) - 1) ↔
      ((Nat.gcd b a : ℤ) =
        c ^ (b * a * (b * a + b + a)) / ((c ^ (b ^ 2 * a) - 1) * (c ^ (b * a ^ 2) - 1)) %
            c ^ (b * a) - 1) := by
  have hgcd : (Nat.gcd a b : ℤ) = (Nat.gcd b a : ℤ) := by rw [Nat.gcd_comm]
  have hE : a * b * (a * b + a + b) = b * a * (b * a + b + a) := by ring
  have hA : a ^ 2 * b = b * a ^ 2 := by ring
  have hB : a * b ^ 2 = b ^ 2 * a := by ring
  have hab : a * b = b * a := mul_comm _ _
  rw [hgcd, hE, hA, hB, hab, mul_comm ((c ^ (b * a ^ 2) : ℤ) - 1) ((c ^ (b ^ 2 * a) : ℤ) - 1)]

private theorem emod_symm (c : ℤ) (a b : ℕ) :
    ((Nat.gcd a b : ℤ) =
        (-c ^ (a * b * (a * b + a + b))) % ((c ^ (a ^ 2 * b) - 1) * (c ^ (a * b ^ 2) - 1)) %
            c ^ (a * b) - 2) ↔
      ((Nat.gcd b a : ℤ) =
        (-c ^ (b * a * (b * a + b + a))) % ((c ^ (b ^ 2 * a) - 1) * (c ^ (b * a ^ 2) - 1)) %
            c ^ (b * a) - 2) := by
  have hgcd : (Nat.gcd a b : ℤ) = (Nat.gcd b a : ℤ) := by rw [Nat.gcd_comm]
  have hE : a * b * (a * b + a + b) = b * a * (b * a + b + a) := by ring
  have hA : a ^ 2 * b = b * a ^ 2 := by ring
  have hB : a * b ^ 2 = b ^ 2 * a := by ring
  have hab : a * b = b * a := mul_comm _ _
  rw [hgcd, hE, hA, hB, hab, mul_comm ((c ^ (b * a ^ 2) : ℤ) - 1) ((c ^ (b ^ 2 * a) : ℤ) - 1)]

end gcd_arithmetic_terms_small_bases

open gcd_arithmetic_terms_small_bases in
/-- **The gcd terms in bases $2$, $3$ and $4$.** Let $c \in \{2, 3, 4\}$, let $a, b \ge 1$ be
natural numbers, and put $E = ab(ab + a + b)$ and $D = (c^{a^2 b} - 1)(c^{a b^2} - 1)$. Then the
identity
$$
\gcd(a, b) = \left( \lfloor c^E / D \rfloor \bmod c^{ab} \right) - 1
$$
holds if and only if $(a, b) \ne (1, 1)$, and the identity
$$
\gcd(a, b) = \big( ((-c^E) \bmod D) \bmod c^{ab} \big) - 2
$$
holds if and only if $(a, b) \ne (1, 1)$. Both identities are read in the integers, where
$x \bmod m$ is the remainder of $x$ in $\{0, \dots, m - 1\}$ for $m > 0$, also when $x < 0$.

Source: Mihai Prunescu and Joseph M. Shunia, *Arithmetic-Term Representations for the Greatest
Common Divisor*, INTEGERS 26 (2026), Article A96, Corollary 2. -/
public theorem gcd_arithmetic_terms_small_bases (c : ℤ) (hc : c = 2 ∨ c = 3 ∨ c = 4)
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ((Nat.gcd a b : ℤ) =
        c ^ (a * b * (a * b + a + b)) / ((c ^ (a ^ 2 * b) - 1) * (c ^ (a * b ^ 2) - 1)) %
            c ^ (a * b) - 1 ↔ (a, b) ≠ (1, 1)) ∧
      ((Nat.gcd a b : ℤ) =
        (-c ^ (a * b * (a * b + a + b))) % ((c ^ (a ^ 2 * b) - 1) * (c ^ (a * b ^ 2) - 1)) %
            c ^ (a * b) - 2 ↔ (a, b) ≠ (1, 1)) := by
  rcases hc with rfl | hc
  · constructor
    · constructor
      · intro hEq hContra
        have hpair : a = 1 ∧ b = 1 := by simpa using hContra
        obtain ⟨rfl, rfl⟩ := hpair
        norm_num at hEq
      · intro hNe
        by_cases h12 : (a, b) = (1, 2)
        · have hpair : a = 1 ∧ b = 2 := by simpa using h12
          obtain ⟨rfl, rfl⟩ := hpair
          norm_num
        · by_cases h21 : (a, b) = (2, 1)
          · have hpair : a = 2 ∧ b = 1 := by simpa using h21
            obtain ⟨rfl, rfl⟩ := hpair
            norm_num
          · have hbound := bound_or_base2 a b ha hb hNe h12 h21
            rcases hbound with h | h
            · have hbound' : 2 * ((a : ℤ) + 1) < (2 : ℤ) ^ (b * a) := by
                rw [mul_comm b a]
                exact h
              have hEq' := floor_of_bound 2 b a hb ha hbound'
              exact (floor_symm 2 a b).mpr hEq'
            · exact floor_of_bound 2 a b ha hb h
    · constructor
      · intro hEq hContra
        have hpair : a = 1 ∧ b = 1 := by simpa using hContra
        obtain ⟨rfl, rfl⟩ := hpair
        norm_num at hEq
      · intro hNe
        by_cases h12 : (a, b) = (1, 2)
        · have hpair : a = 1 ∧ b = 2 := by simpa using h12
          obtain ⟨rfl, rfl⟩ := hpair
          norm_num
        · by_cases h21 : (a, b) = (2, 1)
          · have hpair : a = 2 ∧ b = 1 := by simpa using h21
            obtain ⟨rfl, rfl⟩ := hpair
            norm_num
          · have hbound := bound_or_base2 a b ha hb hNe h12 h21
            rcases hbound with h | h
            · have hbound' : 2 * ((a : ℤ) + 1) < (2 : ℤ) ^ (b * a) := by
                rw [mul_comm b a]
                exact h
              have hEq' := emod_of_bound 2 b a hb ha hbound'
              exact (emod_symm 2 a b).mpr hEq'
            · exact emod_of_bound 2 a b ha hb h
  · have hc3 : 3 ≤ c := by omega
    constructor
    · constructor
      · intro hEq hContra
        have hpair : a = 1 ∧ b = 1 := by simpa using hContra
        obtain ⟨rfl, rfl⟩ := hpair
        rcases hc with rfl | rfl <;> norm_num at hEq
      · intro hNe
        have hbound := bound_or_base_ge3 c hc3 a b ha hb hNe
        rcases hbound with h | h
        · have hbound' : 2 * ((a : ℤ) + 1) < c ^ (b * a) := by
            rw [mul_comm b a]
            exact h
          have hEq' := floor_of_bound c b a hb ha hbound'
          exact (floor_symm c a b).mpr hEq'
        · exact floor_of_bound c a b ha hb h
    · constructor
      · intro hEq hContra
        have hpair : a = 1 ∧ b = 1 := by simpa using hContra
        obtain ⟨rfl, rfl⟩ := hpair
        rcases hc with rfl | rfl <;> norm_num at hEq
      · intro hNe
        have hbound := bound_or_base_ge3 c hc3 a b ha hb hNe
        rcases hbound with h | h
        · have hbound' : 2 * ((a : ℤ) + 1) < c ^ (b * a) := by
            rw [mul_comm b a]
            exact h
          have hEq' := emod_of_bound c b a hb ha hbound'
          exact (emod_symm c a b).mpr hEq'
        · exact emod_of_bound c a b ha hb h

end

end MetaMathlibExt
