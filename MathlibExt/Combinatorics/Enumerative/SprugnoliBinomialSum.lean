/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Substitution
import MathlibExt.Combinatorics.Enumerative.RiordanArraySum

/-!
# Sprugnoli's binomial sum theorem

Two specializations of the fundamental theorem of Riordan arrays. In each case the
monomial in the substitution controls which columns can contribute to a given row.
-/

open PowerSeries

namespace MetaMathlibExt

-- The negative binomial expansion of `(1 - X) ^ (-(d + 1))`.
private theorem coeff_inv_one_sub_pow_succ (d j : ℕ) :
    coeff j (((1 - X : PowerSeries ℂ) ^ (d + 1))⁻¹) = ((d + j).choose d : ℂ) := by
  have hinv : ((1 - X : PowerSeries ℂ) ^ (d + 1))⁻¹ =
      (mk fun i => ((d + i).choose d : ℂ)) :=
    (inv_eq_iff_mul_eq_one (by simp)).2 (mk_add_choose_mul_one_sub_pow_eq_one ℂ d)
  rw [hinv, coeff_mk]

private theorem coeff_sprugnoli_column (n x a b k : ℕ) (hab : a < b) :
    coeff n (X ^ x * ((1 - X) ^ (x + 1))⁻¹ *
      (X ^ (b - a) * ((1 - X) ^ b)⁻¹) ^ k) = ((n + a * k).choose (x + b * k) : ℂ) := by
  have hseries : X ^ x * ((1 - X) ^ (x + 1))⁻¹ *
      (X ^ (b - a) * ((1 - X) ^ b)⁻¹) ^ k =
        (X : PowerSeries ℂ) ^ (x + (b - a) * k) * ((1 - X) ^ (x + b * k + 1))⁻¹ := by
    rw [mul_pow, mul_mul_mul_comm, ← pow_mul, ← pow_add,
      ← PowerSeries.inv_pow (1 - X) b, ← pow_mul, PowerSeries.inv_pow,
      ← PowerSeries.mul_inv_rev, ← pow_add, show b * k + (x + 1) = x + b * k + 1 by omega]
  have hmul : (b - a) * k + a * k = b * k := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hab.le]
  rw [hseries, coeff_X_pow_mul']
  by_cases hshift : x + (b - a) * k ≤ n
  · rw [ite_eq_left hshift, coeff_inv_one_sub_pow_succ,
      show x + b * k + (n - (x + (b - a) * k)) = n + a * k by omega]
  · rw [ite_eq_right hshift, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]

private theorem binomialSeries_mul_nat (z : ℂ) (k : ℕ) :
    binomialSeries ℂ (z * k) = binomialSeries ℂ z ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.cast_succ, mul_add, mul_one, binomialSeries_add, ih, pow_succ]

/-- **Sprugnoli's binomial sum theorem.** Write $[t^j]F$ for the coefficient of $t^j$ in a power
series $F$ over $\mathbb{C}$, $\binom{u}{j}$ for the generalized binomial coefficient, and
$(1 + t)^u = \sum_{j \ge 0} \binom{u}{j} t^j$ for the binomial series of a complex number $u$.
Let $f$ be a power series over $\mathbb{C}$. For natural numbers $n$, $x$, $a$, $b$ with
$a < b$,

$$\sum_{k=0}^{n} \binom{n + ak}{x + bk} [t^k]\,f =
[t^n]\,\frac{t^x}{(1 - t)^{x+1}}\, f\!\left(\frac{t^{b-a}}{(1 - t)^b}\right),$$

and for natural numbers $m$, $c$ with $c > 0$, every complex $y$ and every integer $a'$,

$$\sum_{k=0}^{\lfloor m/c \rfloor} \binom{y + a'k}{m - ck} [t^k]\,f =
[t^m]\,(1 + t)^y f\!\left(t^c (1 + t)^{a'}\right).$$

In the first sum the terms with $k > n$ would vanish, and the second stops where the lower
index $m - ck$ would become negative. The paper allows integer $x$ and $a$ in the first
identity and writes the second with $b = -c < 0$.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 2 (`jis-2025-25.3.5-thm-2`). -/
public theorem sum_choose_mul_coeff_eq_coeff_subst (n x a b m c : ℕ) (hab : a < b)
    (hc : 0 < c) (y : ℂ) (a' : ℤ) (f : PowerSeries ℂ) :
    ∑ k ∈ Finset.range (n + 1), ((n + a * k).choose (x + b * k) : ℂ) * coeff k f =
        coeff n (X ^ x * ((1 - X) ^ (x + 1))⁻¹ * f.subst (X ^ (b - a) * ((1 - X) ^ b)⁻¹)) ∧
      ∑ k ∈ Finset.range (m / c + 1), Ring.choose (y + a' * k) (m - c * k) * coeff k f =
        coeff m (PowerSeries.binomialSeries ℂ y *
          f.subst (X ^ c * PowerSeries.binomialSeries ℂ (a' : ℂ))) := by
  constructor
  · have hh : constantCoeff (X ^ (b - a) * ((1 - X : PowerSeries ℂ) ^ b)⁻¹) = 0 := by
      simp [zero_pow (Nat.sub_ne_zero_of_lt hab)]
    rw [← riordan_array_sum_eq_coeff_subst _ _ _ hh]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [coeff_sprugnoli_column n x a b k hab]
  · let h : PowerSeries ℂ := X ^ c * binomialSeries ℂ (a' : ℂ)
    have hh : constantCoeff h = 0 := by simp [h, zero_pow hc.ne']
    rw [← riordan_array_sum_eq_coeff_subst _ _ _ hh]
    have hterm (k : ℕ) : coeff m (binomialSeries ℂ y * h ^ k) =
        if c * k ≤ m then Ring.choose (y + a' * k) (m - c * k) else 0 := by
      dsimp only [h]
      rw [mul_pow, ← pow_mul, ← binomialSeries_mul_nat, mul_left_comm, ← binomialSeries_add,
        coeff_X_pow_mul']
      simp only [binomialSeries_coeff, smul_eq_mul, mul_one]
    have hle (k : ℕ) : c * k ≤ m ↔ k < m / c + 1 := by
      rw [mul_comm, ← Nat.le_div_iff_mul_le hc, Nat.lt_succ_iff]
    refine Finset.sum_subset_zero_on_sdiff
      (Finset.range_subset_range.mpr (Nat.succ_le_succ (Nat.div_le_self m c))) ?_ ?_
    · intro k hk
      simp only [Finset.mem_sdiff, Finset.mem_range] at hk
      rw [hterm, ite_eq_right (mt (hle k).mp hk.2), zero_mul]
    · intro k hk
      rw [hterm, ite_eq_left ((hle k).mpr (Finset.mem_range.mp hk))]

end MetaMathlibExt
