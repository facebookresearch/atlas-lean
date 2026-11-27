/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith

/-!
# Cohen's lcm–gcd inequality

For nonnegative exponents, compare prime multiplicities one layer at a time. At a given layer,
each index contributes once to the product, and each pair of distinct indices contributes once
to the product of gcds, provided both indices reach that layer.
-/

namespace MetaMathlibExt

open Finset

private theorem consecutive_mul_nonneg (z : ℤ) : 0 ≤ z * (z + 1) := by
  by_cases h : 0 ≤ z
  · exact mul_nonneg h (by omega)
  · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)

/-- Twice the number of strictly ordered pairs, plus the diagonal, counts all pairs in `s`. -/
private theorem twice_sum_Ioi_add_card {k : ℕ} (s : Finset (Fin k)) :
    2 * (∑ i, ∑ j ∈ Ioi i, (if i ∈ s ∧ j ∈ s then 1 else 0 : ℕ)) + s.card =
      s.card * s.card := by
  let f (i j : Fin k) : ℕ := if i < j then (if i ∈ s ∧ j ∈ s then 1 else 0) else 0
  let g (i j : Fin k) : ℕ := if j = i then (if i ∈ s then 1 else 0) else 0
  have hlt (i : Fin k) : (∑ j ∈ Ioi i, (if i ∈ s ∧ j ∈ s then 1 else 0 : ℕ)) =
      ∑ j, f i j := by
    rw [show Ioi i = univ.filter (fun j => i < j) by ext j; simp, sum_filter]
  have hcard : (∑ i : Fin k, (if i ∈ s then 1 else 0 : ℕ)) = s.card := by
    rw [← sum_filter]
    simp
  have hdiag : (∑ i, ∑ j, g i j) = s.card := by
    simp [g]
  calc
    _ = (∑ i, ∑ j, f i j) + (∑ i, ∑ j, f j i) + (∑ i, ∑ j, g i j) := by
      rw [sum_congr rfl (fun i _ => hlt i), sum_comm (f := fun i j => f j i), hdiag, two_mul]
    _ = ∑ i, ∑ j, ((if i ∈ s then 1 else 0 : ℕ) * (if j ∈ s then 1 else 0)) := by
      simp only [← sum_add_distrib]
      refine sum_congr rfl (fun i _ => sum_congr rfl (fun j _ => ?_))
      rcases lt_trichotomy i j with h | rfl | h
      · by_cases hi : i ∈ s <;> by_cases hj : j ∈ s <;> simp [f, g, h, h.not_gt, h.ne', hi, hj]
      · by_cases hi : i ∈ s <;> simp [f, g, hi]
      · by_cases hi : i ∈ s <;> by_cases hj : j ∈ s <;> simp [f, g, h, h.not_gt, h.ne, hi, hj]
    _ = _ := by rw [← sum_mul_sum, hcard]

private theorem sum_lt_indicator {a M : ℕ} (ha : a ≤ M) :
    (∑ m ∈ range M, (if m < a then 1 else 0 : ℕ)) = a := by
  rw [← sum_filter, show (range M).filter (· < a) = range a by ext m; simp; omega]
  simp

/-- Sum the per-layer bound over all levels below the common valuation bound `M`. -/
private theorem valuation_bound {k M : ℕ} (a : Fin k → ℕ) (ha : ∀ i, a i ≤ M) (n : ℕ) :
    n * (∑ i, a i) ≤ M * (n * (n + 1) / 2) + ∑ i, ∑ j ∈ Ioi i, min (a i) (a j) := by
  let s (m : ℕ) := univ.filter (fun i => m < a i)
  have hcard (m : ℕ) : (s m).card = ∑ i, (if m < a i then 1 else 0 : ℕ) :=
    (sum_boole (R := ℕ) (fun i => m < a i) univ).symm
  calc
    _ = ∑ m ∈ range M, n * (s m).card := by
      simp only [hcard, mul_sum]
      rw [sum_comm (s := range M)]
      exact sum_congr rfl (fun i _ => by rw [← mul_sum, sum_lt_indicator (ha i)])
    _ ≤ ∑ m ∈ range M, (n * (n + 1) / 2 +
        ∑ i, ∑ j ∈ Ioi i, (if i ∈ s m ∧ j ∈ s m then 1 else 0 : ℕ)) := by
      refine sum_le_sum (fun m _ => ?_)
      have hpair := twice_sum_Ioi_add_card (s m)
      have htri := Nat.div_mul_cancel (Nat.two_dvd_mul_add_one n)
      -- For `c` indices at this layer, the doubled surplus is `(n - c) * (n - c + 1)`.
      zify at hpair htri ⊢
      nlinarith only [hpair, htri, consecutive_mul_nonneg ((n : ℤ) - ((s m).card : ℤ))]
    _ = _ := by
      rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, sum_comm]
      refine congrArg (_ + ·) (sum_congr rfl (fun i _ => ?_))
      rw [sum_comm]
      refine sum_congr rfl (fun j _ => ?_)
      simpa only [s, mem_filter, mem_univ, true_and, lt_min_iff] using
        sum_lt_indicator ((min_le_left (a i) (a j)).trans (ha i))

private theorem prod_pow_dvd_lcm_pow_mul_prod_gcd {k : ℕ} (d : Fin k → ℕ)
    (hd : ∀ i, d i ≠ 0) (n : ℕ) :
    (∏ i, d i ^ n) ∣
      univ.lcm d ^ (n * (n + 1) / 2) * ∏ i, ∏ j ∈ Ioi i, (d i).gcd (d j) := by
  have hL : univ.lcm d ≠ 0 := fun h => by
    obtain ⟨i, _, hi⟩ := lcm_eq_zero_iff.mp h
    exact hd i hi
  have hgcd (i j : Fin k) : (d i).gcd (d j) ≠ 0 :=
    (Nat.gcd_pos_of_pos_left (d j) (Nat.pos_of_ne_zero (hd i))).ne'
  have hrow (i : Fin k) : (∏ j ∈ Ioi i, (d i).gcd (d j)) ≠ 0 :=
    prod_ne_zero_iff.mpr (fun j _ => hgcd i j)
  have hprod : (∏ i, ∏ j ∈ Ioi i, (d i).gcd (d j)) ≠ 0 :=
    prod_ne_zero_iff.mpr (fun i _ => hrow i)
  have hpow : ∀ i ∈ univ, d i ^ n ≠ 0 := fun i _ => pow_ne_zero n (hd i)
  apply (Nat.factorization_le_iff_dvd (prod_ne_zero_iff.mpr hpow)
    (mul_ne_zero (pow_ne_zero _ hL) hprod)).mp
  intro p
  have hmin (i j : Fin k) : ((d i).gcd (d j)).factorization p =
      min ((d i).factorization p) ((d j).factorization p) := by
    rw [Nat.factorization_gcd (hd i) (hd j), Finsupp.inf_apply]
  simp only [Nat.factorization_prod_apply hpow,
    Nat.factorization_mul (pow_ne_zero _ hL) hprod, Finsupp.add_apply,
    Nat.factorization_prod_apply (fun i _ => hrow i),
    Nat.factorization_prod_apply (fun j _ => hgcd _ j), hmin,
    Nat.factorization_pow, Finsupp.smul_apply, nsmul_eq_mul, Nat.cast_id, ← mul_sum]
  rw [mul_comm (n * (n + 1) / 2)]
  exact valuation_bound (fun i => (d i).factorization p)
    (fun i => (Nat.factorization_le_iff_dvd (hd i) hL).mpr (dvd_lcm (mem_univ i)) p) n

/-- **Cohen's lcm–gcd inequality.** Let $k$ be a natural number, let $d_1, \dots, d_k$ be
positive integers and let $t$ be an integer. Then, as an inequality of rational numbers,
$$\prod_{i=1}^{k} d_i^{\,t} \le \operatorname{lcm}(d_1, \dots, d_k)^{t(t+1)/2}
\prod_{1 \le i < j \le k} \gcd(d_i, d_j),$$
where the exponent $t(t+1)/2$ is an integer.

Source: Patrick Letendre, *Divisors of an Integer in a Short Interval*, INTEGERS 26 (2026),
Article A115, Lemma 1 (`integers-2026-A115-lem-1`). -/
public theorem prod_zpow_le_lcm_zpow_mul_prod_gcd {k : ℕ} (d : Fin k → ℕ)
    (hd : ∀ i, 0 < d i) (t : ℤ) :
    ∏ i, (d i : ℚ) ^ t ≤
      ((Finset.univ.lcm d : ℕ) : ℚ) ^ (t * (t + 1) / 2) *
        ∏ i, ∏ j ∈ Finset.Ioi i, ((Nat.gcd (d i) (d j) : ℕ) : ℚ) := by
  have hL : 0 < univ.lcm d := Nat.pos_of_ne_zero (fun h => by
    obtain ⟨i, _, hi⟩ := lcm_eq_zero_iff.mp h
    exact (hd i).ne' hi)
  have hgcd (i j : Fin k) : 0 < (d i).gcd (d j) := Nat.gcd_pos_of_pos_left (d j) (hd i)
  by_cases ht : 0 ≤ t
  · let n := t.toNat
    have hn : (n : ℤ) = t := Int.toNat_of_nonneg ht
    have htri : ((n * (n + 1) / 2 : ℕ) : ℤ) = t * (t + 1) / 2 := by
      simp only [Int.natCast_ediv, Nat.cast_mul, Nat.cast_add, Nat.cast_one, hn, Nat.cast_ofNat]
    rw [← htri]
    simp only [← hn, zpow_natCast]
    have hpos : 0 < univ.lcm d ^ (n * (n + 1) / 2) * ∏ i, ∏ j ∈ Ioi i, (d i).gcd (d j) :=
      mul_pos (pow_pos hL _) (prod_pos (fun i _ => prod_pos (fun j _ => hgcd i j)))
    exact_mod_cast Nat.le_of_dvd hpos (prod_pow_dvd_lcm_pow_mul_prod_gcd d (fun i => (hd i).ne') n)
  · refine (prod_le_one₀ (fun i _ => zpow_nonneg (Nat.cast_nonneg (d i)) t)
      (fun i _ => zpow_le_one_of_nonpos₀ (Nat.one_le_cast.mpr (hd i)) (le_of_not_ge ht))).trans ?_
    apply one_le_mul_of_one_le_of_one_le
    · exact one_le_zpow₀ (Nat.one_le_cast.mpr hL)
        (Int.ediv_nonneg (consecutive_mul_nonneg t) (by decide))
    · exact one_le_prod₀ (fun i _ => one_le_prod₀ (fun j _ => Nat.one_le_cast.mpr (hgcd i j)))

end MetaMathlibExt
