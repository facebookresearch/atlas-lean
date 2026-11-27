/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Ring.CharZero
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MathlibExt.Combinatorics.Enumerative.Catalan.Recurrence

/-!
# Catalan polynomial identity in Bernstein form

The quadratics used in `CentralBinomialBernstein.lean` still agree after taking their
`n`th powers and multiplying by `1 - X²`. This factor changes the middle binomial
coefficients into ballot differences, giving the Catalan weights.
-/

namespace MetaMathlibExt

open Finset Polynomial

private theorem coeff_mul_pow_add_C_mul_X (n : ℕ) (a b : ℂ) (p q : ℂ[X]) :
    (q * (C a * p + C b * X) ^ n).coeff n =
      ∑ k ∈ range (n + 1), (n.choose k : ℂ) * a ^ k * b ^ (n - k) * (q * p ^ k).coeff k := by
  rw [add_pow, mul_sum, finsetSum_coeff]
  apply sum_congr rfl
  intro k hk
  have hkn := Nat.le_of_lt_succ (mem_range.mp hk)
  have hterm : q * ((C a * p) ^ k * (C b * X) ^ (n - k)) =
      C (a ^ k * b ^ (n - k)) * ((q * p ^ k) * X ^ (n - k)) := by
    simp only [mul_pow, map_mul, map_pow]
    ac_rfl
  rw [← mul_assoc, coeff_mul_natCast, hterm, coeff_C_mul, coeff_mul_X_pow',
    ite_eq_left (Nat.sub_le _ _), Nat.sub_sub_self hkn]
  ring

private theorem coeff_catalan (k : ℕ) :
    ((1 - X) * (1 + X) ^ (2 * k) : ℂ[X]).coeff k = (catalan k : ℂ) := by
  rw [sub_mul, one_mul, coeff_sub,
    show X * (1 + X) ^ (2 * k) = (X : ℂ[X]) ^ 1 * (1 + X) ^ (2 * k) by rw [pow_one],
    coeff_X_pow_mul', coeff_one_add_X_pow]
  have hshift :
      (if 1 ≤ k then ((1 + X : ℂ[X]) ^ (2 * k)).coeff (k - 1) else 0) =
        ((2 * k).choose (k + 1) : ℂ) := by
    cases k with
    | zero => simp
    | succ k =>
      rw [ite_eq_left (show 1 ≤ k + 1 by omega), coeff_one_add_X_pow,
        Nat.choose_symm_of_eq_add (n := 2 * k.succ) (a := k.succ - 1) (b := k.succ + 1)
          (by omega)]
  rw [hshift]
  have hchoose := Nat.choose_succ_right_eq (2 * k) k
  rw [show 2 * k - k = k by omega] at hchoose
  have hchoose' : ((2 * k).choose (k + 1) : ℂ) * ((k : ℂ) + 1) =
      ((2 * k).choose k : ℂ) * k := by
    exact_mod_cast hchoose
  have hcat : (catalan k : ℂ) * ((k : ℂ) + 1) = ((2 * k).choose k : ℂ) := by
    exact_mod_cast (mul_comm (catalan k) (k + 1)).trans (succ_mul_catalan_eq_centralBinom k)
  have hk : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  apply mul_right_cancel₀ hk
  rw [sub_mul, hchoose', hcat]
  ring

private theorem coeff_catalan_succ (k : ℕ) :
    ((1 - X ^ 2) * (1 + X) ^ (2 * k) : ℂ[X]).coeff k = (catalan (k + 1) : ℂ) := by
  let p : ℂ[X] := (1 - X ^ 2) * (1 + X) ^ (2 * k)
  -- The coefficient just above `k` vanishes by binomial symmetry.
  have hzero : p.coeff (k + 1) = 0 := by
    simp only [p, sub_mul, one_mul, mul_comm (X ^ 2), coeff_sub, coeff_mul_X_pow',
      coeff_one_add_X_pow]
    cases k with
    | zero => simp
    | succ k =>
      rw [ite_eq_left (by omega), Nat.choose_symm_of_eq_add (n := 2 * k.succ)
        (a := k.succ + 1) (b := k.succ + 1 - 2) (by omega), sub_self]
  have hmul : p * (1 + X) = (1 - X) * (1 + X) ^ (2 * (k + 1)) := by
    dsimp [p]
    rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]
    ring
  calc
    p.coeff k = (p * (1 + X)).coeff (k + 1) := by
      rw [mul_add, mul_one, coeff_add, hzero, zero_add, coeff_mul_X]
    _ = (catalan (k + 1) : ℂ) := by rw [hmul, coeff_catalan]

/-- **Catalan polynomial identity, Bernstein form.** Let $C_m = \binom{2m}{m}/(m+1)$ denote the
$m$-th Catalan number. For every natural number $n$ and every complex $x$,
$$\sum_{k=0}^{n} \binom{n}{k} 2^{-k} C_{k+1} (1-x)^k x^{n-k} =
\sum_{k=0}^{\lfloor n/2 \rfloor} \binom{n}{2k} 2^{-2k} C_k (1-x)^{2k}.$$

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Corollary 6 (`integers-2026-A19-cor-6`). -/
public theorem sum_choose_catalan_succ_one_sub_pow_mul_pow (n : ℕ) (x : ℂ) :
    ∑ k ∈ range (n + 1),
        (n.choose k : ℂ) / 2 ^ k * (catalan (k + 1) : ℂ) * (1 - x) ^ k * x ^ (n - k) =
      ∑ k ∈ range (n / 2 + 1),
        (n.choose (2 * k) : ℂ) / 2 ^ (2 * k) * (catalan k : ℂ) * (1 - x) ^ (2 * k) := by
  let a := (1 - x) / 2
  have ha : 2 * a + x = 1 := by
    dsimp [a]
    ring
  have hquad : C a * (1 + X) ^ 2 + C x * X = C a * (1 + X ^ 2) + C (1 : ℂ) * X := by
    rw [← ha, map_add, map_mul, map_ofNat]
    ring
  calc
    _ = ((1 - X ^ 2) * (C a * (1 + X) ^ 2 + C x * X) ^ n).coeff n := by
      rw [coeff_mul_pow_add_C_mul_X]
      apply sum_congr rfl
      intro k _
      rw [← pow_mul, coeff_catalan_succ]
      simp only [a, div_pow]
      ring
    _ = ((1 - X ^ 2) * (C a * (1 + X ^ 2) + C (1 : ℂ) * X) ^ n).coeff n := by rw [hquad]
    _ = _ := by
      rw [coeff_mul_pow_add_C_mul_X]
      have hexpand (k : ℕ) : (1 - X ^ 2 : ℂ[X]) * (1 + X ^ 2) ^ k =
          expand ℂ 2 ((1 - X) * (1 + X) ^ k) := by simp
      simp only [hexpand, coeff_expand (by decide : 0 < 2), one_pow, mul_one]
      symm
      apply sum_of_injOn (fun j ↦ 2 * j)
      · exact (mul_right_injective₀ (two_ne_zero (α := ℕ))).injOn
      · intro j hj
        simp only [coe_range, Set.mem_Iio] at hj ⊢
        omega
      · intro k hk hmiss
        have hklt := mem_range.mp hk
        have hodd : ¬ 2 ∣ k := by
          rintro ⟨j, rfl⟩
          exact hmiss ⟨j, mem_range.mpr (by omega), rfl⟩
        simp [hodd]
      · intro j _
        simp only [dvd_mul_right, ite_true, Nat.mul_div_cancel_left _ (by decide : 0 < 2),
          coeff_catalan, a, div_pow]
        ring

/-- **Alternating binomial sum of Catalan numbers.** For every natural number $n$, in the
rational numbers

$$
\sum_{k=0}^{n} (-1)^k \binom{n}{k} \frac{2k+1}{k+2} \cdot \frac{2^{n+1}}{2^{2k}} C_k
= \sum_{k=0}^{\lfloor n/2 \rfloor} \binom{n}{2k} \frac{C_k}{2^{2k}},
$$

where $C_k = \binom{2k}{k}/(k+1)$ is the $k$-th Catalan number.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Proposition 3 (`integers-2026-A19-prop-3`). -/
public theorem sum_neg_one_pow_choose_two_pow_catalan (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1 : ℚ) ^ k * (n.choose k : ℚ) * (2 * k + 1) / (k + 2) *
        2 ^ (n + 1) / 2 ^ (2 * k) * catalan k =
      ∑ k ∈ range (n / 2 + 1), (n.choose (2 * k) : ℚ) / 2 ^ (2 * k) * catalan k := by
  apply (Rat.cast_injective (α := ℂ))
  change (Rat.castHom ℂ) _ = (Rat.castHom ℂ) _
  simp only [map_sum, map_add, map_mul, map_div₀, map_pow, map_natCast, map_ofNat, map_neg, map_one]
  have heven (k : ℕ) : (-1 : ℂ) ^ (2 * k) = 1 := by
    rw [pow_mul, neg_one_sq, one_pow]
  have h := sum_choose_catalan_succ_one_sub_pow_mul_pow n 2
  simp only [show 1 - (2 : ℂ) = -1 by norm_num, heven, mul_one] at h
  refine Eq.trans ?_ h
  apply sum_congr rfl
  intro k hk
  have hkn := Nat.le_of_lt_succ (mem_range.mp hk)
  have hn : (2 : ℂ) ^ n = 2 ^ (n - k) * 2 ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hkn]
  have hpow : (2 : ℂ) ^ n / 2 ^ (2 * k) = 2 ^ (n - k) / 2 ^ k := by
    rw [hn, two_mul, pow_add, mul_div_mul_right _ _ (pow_ne_zero k (two_ne_zero : (2 : ℂ) ≠ 0))]
  calc
    _ = (-1 : ℂ) ^ k * (n.choose k : ℂ) * (2 ^ n / 2 ^ (2 * k)) *
          ((2 * (k : ℂ) + 1) / (k + 2) * 2 * catalan k) := by rw [pow_succ]; ring
    _ = _ := by rw [hpow, ← cast_catalan_succ_eq (K := ℂ)]; ring

end MetaMathlibExt
