/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.AlternatingBinomialPowerSumRecurrences
public import MathlibExt.Combinatorics.Enumerative.HypersequenceMatrixB
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Tactic.Ring

/-!
# The product of Parisse's hypersequence matrices

Vieta's formula identifies each row of `hyperseqB` with the coefficients of a shifted
rising factorial. Evaluation at the arguments in `alternatingBinomialPowerSum` turns
this into a signed falling factorial, leaving an alternating binomial sum.

## References

* Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums II*,
  INTEGERS 26 (2026), Article A36, pp. 1–15, Section 2, Corollary 2 (p. 7).
-/

namespace MetaMathlibExt

open Finset Polynomial

private theorem eval_hyperseqB_row (n j k : ℕ) :
    ∑ i ∈ range (j + 1), hyperseqB n j i * ((k : ℤ) + (n + 1)) ^ i =
      (-1 : ℤ) ^ j * (j.factorial : ℤ) * (k.choose j : ℤ) := by
  let s := (Icc 1 j).val.map (fun t : ℕ => (n : ℤ) + t)
  have hcard : s.card = j := by simp [s]
  have hvieta := congrArg (eval (-((k : ℤ) + (n + 1))))
    (Multiset.prod_X_add_C_eq_sum_esymm s)
  simp only [eval_multiset_prod, Multiset.map_map, Function.comp_def, eval_add, eval_X,
    eval_C, eval_finsetSum, eval_mul, eval_pow, hcard] at hvieta
  have hprod (r : ℕ) : (∏ t ∈ Icc 1 r, ((t : ℤ) - 1 - k)) =
      (ascPochhammer ℤ r).eval (-(k : ℤ)) := by
    induction r with
    | zero => simp
    | succ r ih =>
      rw [prod_Icc_succ_top (by omega), ih, ascPochhammer_succ_eval]
      push_cast
      ring
  calc
    _ = ∑ i ∈ range (j + 1), s.esymm i * (-((k : ℤ) + (n + 1))) ^ (j - i) := by
      rw [← sum_range_reflect (fun i => hyperseqB n j i * ((k : ℤ) + (n + 1)) ^ i) (j + 1)]
      refine sum_congr rfl fun i hi => ?_
      have hi' := Nat.le_of_lt_succ (mem_range.mp hi)
      rw [Nat.add_sub_cancel, hyperseqB, ite_eq_left (Nat.sub_le _ _), Nat.sub_sub_self hi',
        neg_pow ((k : ℤ) + (n + 1))]
      change (-1 : ℤ) ^ (j - i) * s.esymm i * _ = _
      ring
    _ = ∏ t ∈ Icc 1 j, ((t : ℤ) - 1 - k) := by
      rw [← hvieta]
      simp only [s, Multiset.map_map, Function.comp_def, prod_map_val]
      exact prod_congr rfl fun t _ => by ring
    _ = _ := by
      rw [hprod, ascPochhammer_eval_neg_eq_descPochhammer, descPochhammer_eval_eq_descFactorial,
        Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, mul_assoc]

private theorem sum_signed_choose_mul_choose (j m : ℕ) :
    ∑ k ∈ range (m + 1),
      (-1 : ℂ) ^ k * (m.choose k : ℂ) * ((-1) ^ j * (j.factorial : ℂ) * (k.choose j : ℂ)) =
        if j = m then (j.factorial : ℂ) else 0 := by
  by_cases hjm : j ≤ m
  · have halt : ∑ q ∈ range (m - j + 1), (-1 : ℂ) ^ q * ((m - j).choose q : ℂ) =
        (0 : ℂ) ^ (m - j) := by
      simpa only [one_pow, mul_one, neg_add_cancel] using (add_pow (-1 : ℂ) 1 (m - j)).symm
    calc
      _ = ∑ k ∈ Ico j (m + 1),
          (-1 : ℂ) ^ k * (m.choose k : ℂ) * ((-1) ^ j * (j.factorial : ℂ) * (k.choose j : ℂ)) := by
        symm
        refine sum_subset (fun k hk => mem_range.mpr (mem_Ico.mp hk).2) fun k hk hki => ?_
        have hkj : k < j := by
          simp only [mem_range, mem_Ico] at hk hki
          omega
        rw [Nat.choose_eq_zero_of_lt hkj, Nat.cast_zero, mul_zero, mul_zero]
      _ = ((j.factorial : ℂ) * (m.choose j : ℂ)) *
          ∑ q ∈ range (m - j + 1), (-1 : ℂ) ^ q * ((m - j).choose q : ℂ) := by
        rw [sum_Ico_eq_sum_range, show m + 1 - j = m - j + 1 by omega, mul_sum]
        refine sum_congr rfl fun q _ => ?_
        have hc : (m.choose (j + q) : ℂ) * ((j + q).choose j : ℂ) =
            (m.choose j : ℂ) * ((m - j).choose q : ℂ) := by
          rw [← Nat.cast_mul, ← Nat.cast_mul, Nat.choose_mul (Nat.le_add_right j q),
            Nat.add_sub_cancel_left]
        have hs : (-1 : ℂ) ^ (j + q) * (-1) ^ j = (-1) ^ q := by
          rw [Nat.add_comm j q, pow_add, mul_assoc, ← mul_pow]
          simp
        calc
          _ = ((-1 : ℂ) ^ (j + q) * (-1) ^ j) *
              ((j.factorial : ℂ) * ((m.choose (j + q) : ℂ) * ((j + q).choose j : ℂ))) := by ring
          _ = _ := by rw [hs, hc]; ring
      _ = _ := by
        rw [halt]
        by_cases h : j = m
        · subst m
          simp
        · simp [h, zero_pow (show m - j ≠ 0 by omega)]
  · rw [ite_eq_right (Ne.symm (ne_of_lt (Nat.lt_of_not_ge hjm)))]
    refine sum_eq_zero fun k hk => ?_
    have hkj : k < j := by
      have := mem_range.mp hk
      omega
    rw [Nat.choose_eq_zero_of_lt hkj, Nat.cast_zero, mul_zero, mul_zero]

/-- **The product of Parisse's matrices B(n) and C(n).** For $n, j, m \in \mathbb{N}$ let
$b_{j,i}(n) = (-1)^i e_{j-i}(n + 1, \dots, n + j)$ for $i \le j$ be the entries of Parisse's
matrix $B(n)$, where $e_d$ is the elementary symmetric polynomial of degree $d$, and let
$c_{i,m}(n) = \sum_{k=0}^{m} (-1)^k \binom{m}{k} (k + n + 1)^i$ be the entries
of $C(n)$. Then $\sum_{i=0}^{j} b_{j,i}(n)\, c_{i,m}(n)$ equals $j!$ if $j = m$ and $0$ otherwise.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36,
Corollary 2 (`integers-2026-A36-cor-2`). -/
public theorem sum_hyperseqB_mul_hyperseqC (n j m : ℕ) :
    ∑ i ∈ Finset.range (j + 1), (hyperseqB n j i : ℂ) * alternatingBinomialPowerSum i m 1 (n + 1) =
      if j = m then (j.factorial : ℂ) else 0 := by
  simp only [alternatingBinomialPowerSum, mul_one, mul_sum]
  rw [sum_comm]
  calc
    _ = ∑ k ∈ range (m + 1), (-1 : ℂ) ^ k * (m.choose k : ℂ) *
        ∑ i ∈ range (j + 1), (hyperseqB n j i : ℂ) * ((k : ℂ) + (n + 1)) ^ i := by
      refine sum_congr rfl fun k _ => ?_
      rw [mul_sum]
      exact sum_congr rfl fun i _ => by ac_rfl
    _ = _ := by
      have hrow (k : ℕ) :
          ∑ i ∈ range (j + 1), (hyperseqB n j i : ℂ) * ((k : ℂ) + (n + 1)) ^ i =
            (-1 : ℂ) ^ j * (j.factorial : ℂ) * (k.choose j : ℂ) := by
        exact_mod_cast eval_hyperseqB_row n j k
      simp_rw [hrow]
      exact sum_signed_choose_mul_choose j m

end MetaMathlibExt
