/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import MathlibExt.Combinatorics.Enumerative.FussCatalanDivisibility

@[expose] public section

namespace MetaMathlibExt

/-! # Prime divisibility of generalized Catalan numbers -/

/-- The sum of the base-`p` digits of a nonzero number is positive. -/
private lemma one_le_digit_sum {p m : ℕ} (hm : m ≠ 0) : 1 ≤ (p.digits m).sum := by
  have hne : p.digits m ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hm
  have hlast : (p.digits m).getLast hne ≠ 0 := Nat.getLast_digit_ne_zero p hm
  exact le_trans (Nat.one_le_iff_ne_zero.mpr hlast) (List.le_sum_of_mem (List.getLast_mem hne))

/-- Auxiliary strong-induction step: digit sum `1` forces a prime power. -/
private lemma exists_pow_of_digit_sum_eq_one {p : ℕ} (hp : 1 < p) (m : ℕ) :
    0 < m → (p.digits m).sum = 1 → ∃ k, m = p ^ k := by
  refine Nat.strong_induction_on
    (p := fun m => 0 < m → (p.digits m).sum = 1 → ∃ k, m = p ^ k) m ?_
  intro m ih hm hs
  rw [Nat.digits_def' hp hm, List.sum_cons] at hs
  by_cases h0 : m / p = 0
  · have hmod : m % p = 1 := by
      rw [Nat.digits_eq_nil_iff_eq_zero.mpr h0, List.sum_nil, Nat.add_zero] at hs
      exact hs
    have hmeq : p * (m / p) + m % p = m := Nat.div_add_mod m p
    rw [h0, mul_zero, zero_add] at hmeq
    have hm1 : m = 1 := by omega
    exact ⟨0, by rw [hm1, pow_zero]⟩
  · have hpos : 0 < m / p := Nat.pos_of_ne_zero h0
    have hsum1 : 1 ≤ (p.digits (m / p)).sum := one_le_digit_sum h0
    have hmod : m % p = 0 := by omega
    have hrest : (p.digits (m / p)).sum = 1 := by omega
    obtain ⟨k, hk⟩ := ih (m / p) (Nat.div_lt_self hm hp) hpos hrest
    refine ⟨k + 1, ?_⟩
    rw [pow_succ, ← hk]
    exact (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)).symm

/-- Digit sum `1` characterizes prime powers. -/
private lemma digit_sum_eq_one_iff_pow {p m : ℕ} (hp : 1 < p) (hm : 0 < m) :
    (p.digits m).sum = 1 ↔ ∃ k, m = p ^ k := by
  constructor
  · exact fun hs => exists_pow_of_digit_sum_eq_one hp m hm hs
  · rintro ⟨k, rfl⟩
    have h1 : p.digits (p ^ k * 1) = List.replicate k 0 ++ p.digits 1 :=
      Nat.digits_base_pow_mul hp one_pos
    rw [← mul_one (p ^ k), h1, Nat.digits_of_lt p 1 one_ne_zero hp]
    simp

/-- Split off one copy of `n` from `p * n`. -/
private lemma mul_eq_add_sub_mul {p n : ℕ} (hp1 : 1 ≤ p) : p * n = n + (p - 1) * n := by
  have h := Nat.sub_add_cancel hp1
  conv_lhs => rw [← h]
  rw [Nat.add_mul, one_mul, add_comm]

/--
**Prime divisibility of generalized Catalan numbers.** Let $p$ be a prime and $n$ a natural
number. Then $p$ divides the generalized Catalan number $\frac{1}{(p-1)n+1}\binom{pn}{n}$ (an
integer) if and only if $n$ is not of the form $\frac{p^k-1}{p-1}$ for any natural number $k$.

The source theorem's "in particular" Mersenne-index clause is already recorded
as `catalan_odd_iff`; this declaration keeps only the new general-`p` result.

Proves `Wanted` entry `generalizedCatalan_prime_dvd_iff_not_geometric_sum`.

Source: B. Sury, "Generalized Catalan Numbers: Linear Recursion and
Divisibility," Journal of Integer Sequences 12 (2009), Article 09.7.5,
Theorem (label divis), lines 154–158,
https://cs.uwaterloo.ca/journals/JIS/VOL12/Sury/sury31.tex
-/
theorem generalizedCatalan_prime_dvd_iff_not_geometric_sum
    (p n : ℕ) (hp : p.Prime) :
    p ∣ Nat.choose (p * n) n / ((p - 1) * n + 1) ↔
      ∀ k : ℕ, n ≠ (p ^ k - 1) / (p - 1) := by
  have : Fact (Nat.Prime p) := Fact.mk hp
  have hp1lt : 1 < p := hp.one_lt
  have hp1 : 1 ≤ p := by omega
  have hpos : 0 < p := by omega
  have hp1' : 1 ≤ p - 1 := by omega
  have hm_pos : 0 < (p - 1) * n + 1 := by omega
  have hle1 : n ≤ p * n := Nat.le_mul_of_pos_left n hpos
  have hdiv : (p - 1) * n + 1 ∣ (p * n).choose n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact fuss_catalan_dvd_choose p n hp.two_le hn
  have hpn := mul_eq_add_sub_mul (p := p) (n := n) hp1
  have hsub1 : p * n - n = (p - 1) * n := by omega
  -- Kummer's digit-sum formula for `C (p * n) n`.
  have hkummer :=
    sub_one_mul_padicValNat_choose_eq_sub_sum_digits (p := p) (k := n) (n := p * n) hle1
  have hdig_mul : (p.digits (p * n)).sum = (p.digits n).sum := by
    rcases eq_zero_or_pos n with rfl | hn
    · simp
    · have h := Nat.digits_add p hp1lt 0 n hpos (Or.inr (by omega : n ≠ 0))
      rw [show (0 : ℕ) + p * n = p * n from by ring] at h
      rw [h, List.sum_cons, Nat.zero_add]
  rw [hsub1, hdig_mul] at hkummer
  have hval_choose : (p - 1) * padicValNat p ((p * n).choose n)
      = (p.digits ((p - 1) * n)).sum := by
    omega
  -- The exact factorial valuations give the digit sum of `(p - 1) * n`.
  have hm_sub : (p - 1) * n + 1 - 1 = (p - 1) * n := by omega
  have hleg1 := sub_one_mul_padicValNat_factorial (p := p) ((p - 1) * n + 1)
  have hleg2 := sub_one_mul_padicValNat_factorial (p := p) (((p - 1) * n + 1) - 1)
  rw [hm_sub] at hleg2
  have hfact : ((p - 1) * n + 1) * Nat.factorial ((p - 1) * n)
      = Nat.factorial ((p - 1) * n + 1) :=
    Nat.mul_factorial_pred (by omega)
  have hm_ne : (p - 1) * n + 1 ≠ 0 := by omega
  have hvmul : padicValNat p (Nat.factorial ((p - 1) * n + 1))
      = padicValNat p ((p - 1) * n + 1)
        + padicValNat p (Nat.factorial ((p - 1) * n)) := by
    conv_lhs => rw [← hfact]
    exact padicValNat.mul (p := p) hm_ne (Nat.factorial_ne_zero _)
  have hdist2 : (p - 1) * padicValNat p (Nat.factorial ((p - 1) * n + 1))
      = (p - 1) * padicValNat p (Nat.factorial ((p - 1) * n))
        + (p - 1) * padicValNat p ((p - 1) * n + 1) := by
    rw [← mul_add, hvmul, add_comm]
  have hS2_le : (p.digits ((p - 1) * n + 1)).sum ≤ (p - 1) * n + 1 :=
    Nat.digit_sum_le _ _
  have hS1_le : (p.digits ((p - 1) * n)).sum ≤ (p - 1) * n := Nat.digit_sum_le _ _
  have hs1 : 1 ≤ (p.digits ((p - 1) * n + 1)).sum := one_le_digit_sum (by omega)
  have hval_m : (p.digits ((p - 1) * n)).sum
      = (p.digits ((p - 1) * n + 1)).sum - 1
        + (p - 1) * padicValNat p ((p - 1) * n + 1) := by
    omega
  -- The valuation of the generalized Catalan number itself.
  have hchoose_ne : (p * n).choose n ≠ 0 := ne_of_gt (Nat.choose_pos hle1)
  have hC_ne : (p * n).choose n / ((p - 1) * n + 1) ≠ 0 :=
    ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Nat.choose_pos hle1) hdiv) hm_pos)
  have hmul_eq : (p * n).choose n / ((p - 1) * n + 1) * ((p - 1) * n + 1)
      = (p * n).choose n := Nat.div_mul_cancel hdiv
  have hval_div : padicValNat p ((p * n).choose n)
      = padicValNat p ((p * n).choose n / ((p - 1) * n + 1))
        + padicValNat p ((p - 1) * n + 1) := by
    conv_lhs => rw [← hmul_eq]
    exact padicValNat.mul hC_ne hm_ne
  have hvalC : (p - 1) * padicValNat p ((p * n).choose n / ((p - 1) * n + 1))
      = (p.digits ((p - 1) * n + 1)).sum - 1 := by
    have hdist : (p - 1) * padicValNat p ((p * n).choose n / ((p - 1) * n + 1))
        + (p - 1) * padicValNat p ((p - 1) * n + 1)
        = (p - 1) * padicValNat p ((p * n).choose n) := by
      rw [← mul_add, hval_div]
    omega
  -- `p` divides the quotient iff the digit sum is not `1`.
  have hiff1 : p ∣ (p * n).choose n / ((p - 1) * n + 1)
      ↔ (p.digits ((p - 1) * n + 1)).sum ≠ 1 := by
    constructor
    · intro hdvd heq
      have h1V : 1 ≤ padicValNat p ((p * n).choose n / ((p - 1) * n + 1)) := by
        have hpow : p ^ 1 ∣ (p * n).choose n / ((p - 1) * n + 1) := by rwa [pow_one]
        rcases (padicValNat_dvd_iff 1 _).mp hpow with h0 | hle
        · omega
        · exact hle
      have hX : 0 < (p - 1)
          * padicValNat p ((p * n).choose n / ((p - 1) * n + 1)) :=
        mul_pos (by omega) h1V
      omega
    · intro hne
      have hs2 : 2 ≤ (p.digits ((p - 1) * n + 1)).sum := by omega
      have hX : 1 ≤ (p - 1)
          * padicValNat p ((p * n).choose n / ((p - 1) * n + 1)) := by
        omega
      have hV : 1 ≤ padicValNat p ((p * n).choose n / ((p - 1) * n + 1)) := by
        rcases eq_zero_or_pos (padicValNat p ((p * n).choose n / ((p - 1) * n + 1))) with h0 | hpos'
        · exfalso
          rw [h0, mul_zero] at hX
          omega
        · exact hpos'
      have h := (padicValNat_dvd_iff 1 _).mpr (Or.inr hV)
      rwa [pow_one] at h
  -- Geometric-sum indices are exactly the prime powers of `(p - 1) * n + 1`.
  have hgeom : ∀ k, ((p - 1) * n + 1 = p ^ k) ↔ (n = (p ^ k - 1) / (p - 1)) := by
    intro k
    constructor
    · intro hk
      have hmul : p ^ k - 1 = n * (p - 1) := by
        have hcomm : n * (p - 1) = (p - 1) * n := mul_comm _ _
        omega
      exact (Nat.div_eq_of_eq_mul_left (by omega) hmul).symm
    · intro hk
      have hpeq : p = (p - 1) + 1 := (Nat.sub_add_cancel hp1).symm
      have hmod : p ≡ 1 [MOD p - 1] := by
        rw [hpeq]
        exact Nat.add_mod_left _ _
      have hpow := Nat.ModEq.pow k hmod
      rw [one_pow] at hpow
      have h1 : 1 ≤ p ^ k := Nat.one_le_pow k p hpos
      have hdvd : (p - 1) ∣ p ^ k - 1 := (Nat.modEq_iff_dvd' h1).mp hpow.symm
      have hmul := Nat.mul_div_cancel' hdvd
      rw [hk]
      omega
  rw [hiff1, ne_eq, digit_sum_eq_one_iff_pow hp1lt hm_pos, not_exists]
  exact forall_congr' fun k => (hgeom k).not

end MetaMathlibExt
