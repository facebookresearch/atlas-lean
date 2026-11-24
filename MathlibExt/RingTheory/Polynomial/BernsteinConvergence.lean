/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Polynomial.BernsteinConversion
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Quantitative Bernstein coefficient convergence

An elementary binomial-ratio estimate used to bound the distance between
Bernstein coefficients and polynomial values at the associated grid points.
Reference: Garloff and Hamadneh (2016), *Convergence and Inclusion Isotonicity
of the Tensorial Rational Bernstein Form*, Theorem 1 and Remark 1,
https://d-nb.info/1163536172/34. The estimate here uses a simpler, weaker
constant and a larger degree threshold than that reference.
-/

@[expose] public section

open Finset

/-- For two finite families of real numbers in `[0,1]`, the absolute difference
of their products is at most the sum of their pointwise absolute differences.
Zero factors and an empty index set are allowed. -/
theorem Finset.abs_prod_sub_prod_le_sum_of_mem_Icc {ι : Type*} (s : Finset ι)
    {f g : ι → ℝ} (hf : ∀ i ∈ s, f i ∈ Set.Icc 0 1)
    (hg : ∀ i ∈ s, g i ∈ Set.Icc 0 1) :
    |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤ ∑ i ∈ s, |f i - g i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hfa := hf a (mem_insert_self a s)
    have hgs : ∀ i ∈ s, g i ∈ Set.Icc 0 1 := fun i hi => hg i (mem_insert_of_mem hi)
    have hi := ih (fun i hi => hf i (mem_insert_of_mem hi)) hgs
    have hgp0 : 0 ≤ ∏ i ∈ s, g i := prod_nonneg fun i hi => (hgs i hi).1
    have hgp1 : ∏ i ∈ s, g i ≤ 1 := prod_le_one₀ (fun i hi => (hgs i hi).1)
      (fun i hi => (hgs i hi).2)
    rw [prod_insert ha, prod_insert ha, sum_insert ha]
    calc
      _ = |f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) +
          (f a - g a) * ∏ i ∈ s, g i| := by congr 1; ring
      _ ≤ |f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)| +
          |(f a - g a) * ∏ i ∈ s, g i| := abs_add_le _ _
      _ = f a * |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| +
          |f a - g a| * ∏ i ∈ s, g i := by
        rw [abs_mul, abs_mul, abs_of_nonneg hfa.1, abs_of_nonneg hgp0]
      _ ≤ f a * (∑ i ∈ s, |f i - g i|) + |f a - g a| * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hi hfa.1)
          (mul_le_mul_of_nonneg_left hgp1 (abs_nonneg _))
      _ ≤ _ := by
        have := mul_le_of_le_one_left
          (show 0 ≤ ∑ i ∈ s, |f i - g i| from sum_nonneg fun i _ => abs_nonneg _) hfa.2
        linarith

namespace bernsteinPolynomial

private theorem choose_ratio_eq_prod (n k d : ℕ) :
    (k.choose d : ℝ) / n.choose d =
      ∏ j ∈ range d, ((k - j : ℕ) : ℝ) / ((n - j : ℕ) : ℝ) := by
  have hf : (d.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  rw [prod_div_distrib, ← Nat.cast_prod, ← Nat.cast_prod,
    ← Nat.descFactorial_eq_prod_range, ← Nat.descFactorial_eq_prod_range,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose]
  simp only [Nat.cast_mul]
  exact (mul_div_mul_left _ _ hf).symm

private theorem falling_ratio_mem_Icc {n k j : ℕ} (hk : k ≤ n) (hj : j < n) :
    ((k - j : ℕ) : ℝ) / ((n - j : ℕ) : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  have hd : (0 : ℝ) < (n - j : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hj
  exact ⟨div_nonneg (Nat.cast_nonneg _) hd.le,
    (div_le_one hd).mpr (by exact_mod_cast Nat.sub_le_sub_right hk j)⟩

private theorem falling_ratio_error {n k d j : ℕ} (hn : 0 < n) (hk : k ≤ n)
    (hd : 2 * d ≤ n) (hj : j < d) :
    |((k - j : ℕ) : ℝ) / ((n - j : ℕ) : ℝ) - (k : ℝ) / n| ≤
      2 * (j : ℝ) / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hknR : (k : ℝ) ≤ n := by exact_mod_cast hk
  have hjn : j < n := by omega
  have hjnR : (0 : ℝ) < (n : ℝ) - j := sub_pos.mpr (by exact_mod_cast hjn)
  have h2j : 2 * (j : ℝ) ≤ n := by exact_mod_cast (show 2 * j ≤ n by omega)
  rw [Nat.cast_sub hjn.le]
  by_cases hjk : j ≤ k
  · rw [Nat.cast_sub hjk]
    have heq : ((k : ℝ) - j) / ((n : ℝ) - j) - (k : ℝ) / n =
        -((j : ℝ) / n) * (((n : ℝ) - k) / ((n : ℝ) - j)) := by
      field_simp [hnR.ne', hjnR.ne']
      ring
    rw [heq, abs_mul, abs_neg, abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hnR.le),
      abs_of_nonneg (div_nonneg (sub_nonneg.mpr hknR) hjnR.le)]
    have hr : ((n : ℝ) - k) / ((n : ℝ) - j) ≤ 2 :=
      (div_le_iff₀ hjnR).mpr (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
    calc
      _ ≤ ((j : ℝ) / n) * 2 :=
        mul_le_mul_of_nonneg_left hr (div_nonneg (Nat.cast_nonneg _) hnR.le)
      _ = _ := by ring
  · rw [Nat.sub_eq_zero_of_le (by omega)]
    simp only [Nat.cast_zero, zero_div, zero_sub, abs_neg,
      abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hnR.le)]
    exact div_le_div_of_nonneg_right (by exact_mod_cast (show k ≤ 2 * j by omega)) hnR.le

/-- For natural indices `k ≤ n`, positive `n` and `2*d ≤ n`, the real
binomial ratio `choose k d / choose n d` differs from `(k/n)^d` by at most
`d²/n`. The bound is uniform in `k`, including `k < d` and both endpoints;
it also includes exponent zero. -/
theorem abs_choose_ratio_sub_pow_le {n k d : ℕ} (hn : 0 < n) (hk : k ≤ n)
    (hd : 2 * d ≤ n) :
    |(k.choose d : ℝ) / n.choose d - ((k : ℝ) / n)^d| ≤ (d : ℝ)^2 / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hx : (k : ℝ) / n ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (Nat.cast_nonneg _) hnR.le,
      (div_le_one hnR).mpr (by exact_mod_cast hk)⟩
  rw [choose_ratio_eq_prod]
  have h := Finset.abs_prod_sub_prod_le_sum_of_mem_Icc (range d)
    (f := fun j => ((k - j : ℕ) : ℝ) / ((n - j : ℕ) : ℝ))
    (g := fun _ => (k : ℝ) / n)
    (fun j hj => falling_ratio_mem_Icc hk (by have := mem_range.mp hj; omega))
    (fun _ _ => hx)
  simp only [prod_const, card_range] at h
  apply h.trans
  calc
    _ ≤ ∑ j ∈ range d, 2 * (j : ℝ) / n :=
      sum_le_sum fun j hj => falling_ratio_error hn hk hd (mem_range.mp hj)
    _ = (d : ℝ) * ((d : ℝ) - 1) / n := by
      rw [← sum_div, ← mul_sum]
      have hs (m : ℕ) : (∑ j ∈ range m, (j : ℝ)) = (m : ℝ) * ((m : ℝ) - 1) / 2 := by
        induction m with
        | zero => simp
        | succ m ih => rw [sum_range_succ, ih]; push_cast; ring
      rw [hs]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith [Nat.cast_nonneg (α := ℝ) d]) hnR.le

end bernsteinPolynomial
