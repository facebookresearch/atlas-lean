/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.RingTheory.PowerSeries.Inverse
public import MathlibExt.Combinatorics.Enumerative.GaussianBinomial
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# Limit of the fixed-hook generating functions

The normalized generating functions for hooks in a fixed column stabilize coefficientwise.
The proof uses the Pascal recursion for Gaussian binomials after clearing the denominators.
-/

namespace MetaMathlibExt

open Finset PowerSeries MathlibExt

namespace columnHook_size_genFun_limit

variable {R : Type*} [CommRing R]

/-- Pascal recursion summed against an arbitrary function of the lower index. -/
private theorem sum_gauss_succ (q : R) (f : ℕ → R) (d : ℕ) :
    ∑ j ∈ range (d + 2), gaussBinom q (d + 1) j * f j =
      ∑ j ∈ range (d + 1), gaussBinom q d j * (f (j + 1) + q ^ j * f j) := by
  have hshift : (∑ j ∈ range (d + 1), q ^ (j + 1) * gaussBinom q d (j + 1) * f (j + 1)) +
      f 0 = ∑ j ∈ range (d + 1), q ^ j * gaussBinom q d j * f j := by
    let g (j : ℕ) := q ^ j * gaussBinom q d j * f j
    have h := (sum_range_succ' g (d + 1)).symm.trans (sum_range_succ g (d + 1))
    simpa [g, gaussBinom_eq_zero_of_lt q d (d + 1) (by omega)] using h
  rw [sum_range_succ']
  simp only [gaussBinom_succ_succ, gaussBinom_zero_right, one_mul, add_mul,
    mul_add, sum_add_distrib, add_assoc, hshift]
  congr 1
  apply sum_congr rfl
  intro j _
  ring

private def poch (q z : R) (j : ℕ) : R := ∏ i ∈ range j, (1 - z * q ^ i)

/-- The two terms from the Pascal recursion cancel the last factor of the product. -/
private theorem sum_gauss_poch (q z : R) (d : ℕ) :
    ∑ j ∈ range (d + 1), gaussBinom q d j * (z ^ (d - j) * poch q z j) = 1 := by
  induction d with
  | zero => simp [poch]
  | succ d ih =>
    rw [sum_gauss_succ, ← ih]
    apply sum_congr rfl
    intro j hj
    have hj' := mem_range.mp hj
    rw [show d + 1 - j = d - j + 1 by omega, Nat.add_sub_add_right, pow_succ]
    simp only [poch, prod_range_succ]
    ring

private theorem poch_shift (a j : ℕ) (q : R) :
    (1 - q ^ a) * (∏ i ∈ range j, (1 - q ^ (a + 1 + i))) =
      poch q (q ^ a) j * (1 - q ^ (a + j)) := by
  have h := (prod_range_succ' (fun i => 1 - q ^ (a + i)) j).symm.trans
    (prod_range_succ (fun i => 1 - q ^ (a + i)) j)
  simpa only [poch, ← pow_add, Nat.add_zero, Nat.add_right_comm a 1, Nat.add_assoc,
    Nat.add_comm 1, mul_comm (1 - q ^ a)] using h

private theorem constantCoeff_qPoch (j : ℕ) :
    constantCoeff (qPochFin (X : ℚ⟦X⟧) j) = 1 := by
  simp [qPochFin, map_prod]

/-- Multiply the sum by its limiting denominator. In degree at most `d`, each summand
then agrees with the corresponding term of `sum_gauss_poch`. -/
private theorem cleared_sum (F : ℚ⟦X⟧ →+* R) (a d : ℕ) (ha : 1 ≤ a)
    (hd : F X ^ (d + 1) = 0) :
    F (((1 - X ^ a) * qPochFin X d) *
      ∑ j ∈ range (d + 1), X ^ (a * (d - j)) *
        (∏ i ∈ range j, (1 - X ^ (a + 1 + i))) *
        (qPochFin X j * qPochFin X (d - j))⁻¹) = 1 := by
  conv_rhs => rw [← map_one F, ← sum_gauss_poch X (X ^ a) d]
  simp only [mul_sum, map_sum]
  apply sum_congr rfl
  intro j hj
  have hj' : j ≤ d := by simpa using hj
  have hgauss : gaussBinom (X : ℚ⟦X⟧) d j =
      qPochFin X d * (qPochFin X j * qPochFin X (d - j))⁻¹ := by
    apply (PowerSeries.eq_mul_inv_iff_mul_eq (by simp [constantCoeff_qPoch])).2
    simpa only [← mul_assoc] using gaussBinom_mul_qPochFin_mul_qPochFin (X : ℚ⟦X⟧) d j hj'
  have hkill : F (X ^ (a * (d - j))) * F (X ^ (a + j)) = 0 := by
    rw [← map_mul, ← pow_add, map_pow]
    have hle := Nat.mul_le_mul_right (d - j) ha
    exact pow_eq_zero_of_le (by omega) hd
  rw [← pow_mul]
  calc
    _ = F ((qPochFin X d * (qPochFin X j * qPochFin X (d - j))⁻¹) *
        (X ^ (a * (d - j)) * ((1 - X ^ a) * ∏ i ∈ range j, (1 - X ^ (a + 1 + i))))) := by
      congr 1
      ring
    _ = _ := by
      rw [← hgauss, poch_shift]
      simp only [map_mul, map_sub, map_one]
      linear_combination -F (gaussBinom X d j) * F (poch X (X ^ a) j) * hkill

private theorem sum_Icc_one (f : ℕ → ℚ⟦X⟧) (d : ℕ) :
    ∑ l ∈ Icc 1 (d + 1), f l = ∑ j ∈ range (d + 1), f (j + 1) := by
  rw [← Ico_succ_right_eq_Icc, sum_Ico_eq_sum_range]
  simp [Nat.add_comm]

end columnHook_size_genFun_limit

open columnHook_size_genFun_limit

/-- **Limit of the fixed-hook generating functions.** Let $m \ge 2$ be a natural number and work
in $\mathbb{Q}[[q]]$. For $j \in \mathbb{N}$ write $(q;q)_j = \prod_{i=1}^{j} (1 - q^i)$ and
$(q^m;q)_j = \prod_{i=0}^{j-1} (1 - q^{m+i})$. Then for every natural number $n$ there is a $K$
such that for every $k \ge K$ the coefficient of $q^n$ in
$$
\frac{q^{m-1}}{\prod_{i=0}^{n} (1 - q^{k+i})}
\sum_{l=1}^{k} \frac{q^{(m-1)(k-l)} (q^m;q)_{l-1}}{(q;q)_{l-1} (q;q)_{k-l}}
$$
equals the coefficient of $q^n$ in
$$
\frac{q^{m-1}}{(1 - q^{m-1}) (q;q)_{n+1}}.
$$

This is the coefficientwise ($q$-adic) form of the limit
$$
\lim_{k \to \infty} \frac{q^{m-1}}{(q^k;q)_\infty}
\sum_{l=1}^{k} \frac{q^{(m-1)(k-l)} (q^m;q)_{l-1}}{(q;q)_{l-1} (q;q)_{k-l}}
= \frac{q^{m-1}}{(1 - q^{m-1}) (q;q)_\infty},
$$
where $(a;q)_\infty = \prod_{i \ge 0} (1 - a q^i)$: for the coefficient of $q^n$, the products
$(q^k;q)_\infty$ and $(q;q)_\infty$ are replaced by their first $n + 1$ factors, which changes no
coefficient below $q^{n+1}$.

Source: Philip Cuthbertson, *Fixed Hooks in Arbitrary Columns of Partitions*, INTEGERS 25
(2025), Article A28, Theorem 5 (`integers-2025-A28-thm-5`). -/
public theorem columnHook_size_genFun_limit (m : ℕ) (hm : 2 ≤ m) (n : ℕ) :
    ∀ᶠ k in Filter.atTop,
      coeff n (X ^ (m - 1) * (∏ i ∈ Finset.range (n + 1), (1 - X ^ (k + i)))⁻¹ *
        ∑ l ∈ Finset.Icc 1 k, X ^ ((m - 1) * (k - l)) *
          (∏ i ∈ Finset.range (l - 1), (1 - X ^ (m + i))) *
          (qPochFin (X : ℚ⟦X⟧) (l - 1) * qPochFin X (k - l))⁻¹) =
      coeff n (X ^ (m - 1) * ((1 - X ^ (m - 1)) * qPochFin (X : ℚ⟦X⟧) (n + 1))⁻¹) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
  have ha : 1 ≤ a := by omega
  apply Filter.eventually_atTop.2
  refine ⟨n + 2, ?_⟩
  rintro (_ | d) hk
  · omega
  let I : Ideal ℚ⟦X⟧ := Ideal.span {(X : ℚ⟦X⟧) ^ (n + 1)}
  let F := Ideal.Quotient.mk I
  have hX : F X ^ (n + 1) = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_singleton _)
  have low_coeff (x y : ℚ⟦X⟧) (h : F x = F y) : coeff n x = coeff n y := by
    have hdvd : X ^ (n + 1) ∣ x - y := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h)
    simpa only [map_sub, sub_eq_zero] using X_pow_dvd_iff.mp hdvd n (by omega)
  apply low_coeff
  rw [sum_Icc_one]
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.add_sub_add_right]
  -- Beyond degree n the prefactor is one, and all longer Pochhammer products agree.
  have hpref : F ((∏ i ∈ range (n + 1), (1 - X ^ (d + 1 + i)))⁻¹) = 1 := by
    have hp : F (∏ i ∈ range (n + 1), (1 - X ^ (d + 1 + i))) = 1 := by
      rw [map_prod]
      apply prod_eq_one
      intro i _
      simp [pow_eq_zero_of_le (show n + 1 ≤ d + 1 + i by omega) hX]
    have hunit := PowerSeries.mul_inv_cancel
      (∏ i ∈ range (n + 1), (1 - (X : ℚ⟦X⟧) ^ (d + 1 + i)))
      (by simp [map_prod])
    simpa only [hp, one_mul] using map_mul_eq_one F hunit
  have hpoch : F (qPochFin X d) = F (qPochFin X (n + 1)) := by
    simp only [qPochFin, map_prod, map_sub, map_one, map_pow]
    apply eventually_constant_prod _ (by omega)
    intro i hi
    simp [pow_eq_zero_of_le (show n + 1 ≤ i + 1 by omega) hX]
  have hsum := cleared_sum F a d ha (pow_eq_zero_of_le (by omega) hX)
  rw [map_mul, map_mul, hpoch, ← map_mul, mul_comm] at hsum
  rw [map_mul, map_mul, hpref, mul_one, map_mul]
  congr 1
  apply left_inv_eq_right_inv hsum
  apply map_mul_eq_one
  apply PowerSeries.mul_inv_cancel
  simp [constantCoeff_qPoch, Nat.ne_of_gt ha]

end MetaMathlibExt
