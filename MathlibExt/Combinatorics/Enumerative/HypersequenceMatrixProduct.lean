/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.AlternatingBinomialPowerSumRecurrences
public import MathlibExt.Combinatorics.Enumerative.HypersequenceMatrixB
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Matrix.SemiringInverse
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Tactic.Ring
import MathlibExt.Combinatorics.Enumerative.AlternatingBinomialPowerSumStirling

/-!
# The product of Parisse's hypersequence matrices

Vieta's formula identifies each row of `hyperseqB` with the coefficients of a shifted
rising factorial. Evaluation at the arguments in `alternatingBinomialPowerSum` turns
this into a signed falling factorial, leaving an alternating binomial sum.

For each $n \in \mathbb{N}$, dividing column $m$ of $C(n)$ by $m!$ gives a two-sided
inverse of $B(n)$. The first product follows from `sum_hyperseqB_mul_hyperseqC`. Both
factors are lower triangular, so the $(j,m)$ entry, for any $j,m \in \mathbb{N}$, can be
computed on a finite square truncation containing both indices. There a right inverse
is also a left inverse.

## References

* Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums II*,
  INTEGERS 26 (2026), Article A36, pp. 1–15, Section 2, Corollary 1, Equation (2.9) (p. 6)
  and Corollary 2 (p. 7).
* Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
  INTEGERS 24 (2024), Article A70, pp. 1–31, Proposition 1(ii), Equation (3.11).
* H. Katsuura, *Summations Involving Binomial Coefficients*, The College Mathematics Journal
  40 (2009), pp. 275–278, pp. 275–276 for the vanishing above the diagonal.
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

/-- **The inverse of Parisse's matrix $B(n)$.** Let $n \in \mathbb{N}$. Let $e_{j,i}(n)$ be the
elementary symmetric polynomial of degree $i$ in $n + 1, \dots, n + j$, let
$b_{j,k}(n) = (-1)^k e_{j,j-k}(n)$ for $k \le j$ and $b_{j,k}(n) = 0$ for $k > j$, let
$p_{\ell,m}(x, y) = \sum_{k=0}^{m} (-1)^k \binom{m}{k} (k x + y)^\ell$ for complex $x, y$, and let
$c_{\ell,m}(n) = p_{\ell,m}(1, n + 1) = \sum_{k=0}^{m} (-1)^k \binom{m}{k} (k + n + 1)^\ell$.
Then for all $j, m \in \mathbb{N}$, with $\delta_{j,m}$ the Kronecker delta,
$\sum_{k=0}^{j} b_{j,k}(n) \, \frac{c_{k,m}(n)}{m!} = \delta_{j,m}$ and
$\sum_{k=0}^{j} \frac{c_{j,k}(n)}{k!} \, b_{k,m}(n) = \delta_{j,m}$.

In matrix form, with $B(n) = (b_{j,k}(n))$, $C(n) = (c_{\ell,m}(n))$ and $D$ the diagonal matrix
of the factorials $j!$, this says $B(n)^{-1} = C(n) D^{-1}$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36,
Corollary 1, Equation (2.9) (`integers-2026-A36-cor-1`). -/
public theorem hyperseqB_inv_eq_hyperseqC_div_factorial (n j m : ℕ) :
    ∑ k ∈ Finset.range (j + 1), (hyperseqB n j k : ℂ) *
        (alternatingBinomialPowerSum k m 1 (n + 1) / m.factorial) = (if j = m then 1 else 0) ∧
      ∑ k ∈ Finset.range (j + 1), alternatingBinomialPowerSum j k 1 (n + 1) / k.factorial *
        (hyperseqB n k m : ℂ) = if j = m then 1 else 0 := by
  let b (r s : ℕ) : ℂ := hyperseqB n r s
  let c (r s : ℕ) : ℂ := alternatingBinomialPowerSum r s 1 (n + 1) / s.factorial
  have hright (r s : ℕ) : ∑ k ∈ range (r + 1), b r k * c k s = if r = s then 1 else 0 := by
    dsimp only [b, c]
    simp_rw [← mul_div_assoc, ← sum_div]
    rw [sum_hyperseqB_mul_hyperseqC]
    by_cases h : r = s
    · subst s
      simp [Nat.factorial_ne_zero]
    · simp [h]
  refine ⟨hright j m, ?_⟩
  -- Work in a square truncation containing both indices of the desired entry.
  let N := max j m + 1
  let B : Matrix (Fin N) (Fin N) ℂ := fun r s => b r s
  let C : Matrix (Fin N) (Fin N) ℂ := fun r s => c r s
  have truncate (r : Fin N) (f : ℕ → ℂ) (hf : ∀ k, r.val < k → f k = 0) :
      ∑ k : Fin N, f k = ∑ k ∈ range (r.val + 1), f k := by
    rw [← Finset.sum_range]
    symm
    refine sum_subset (range_mono (Nat.succ_le_of_lt r.isLt)) fun k _ hk => ?_
    exact hf k (by simpa only [mem_range, Nat.lt_succ_iff, not_le] using hk)
  have hBC : B * C = 1 := by
    apply Matrix.ext
    intro r s
    rw [Matrix.mul_apply, Matrix.one_apply]
    change (∑ k : Fin N, b r k * c k s) = _
    rw [truncate r (fun k => b r k * c k s), hright]
    · simp only [Fin.val_inj]
    · intro k hk
      dsimp only [b]
      rw [(hyperseqB_recurrence_closed_form_row_sums n).2.2.2.1 r k, Icc_eq_empty_of_lt hk,
        sum_empty, mul_zero, Int.cast_zero, zero_mul]
  have hCB : C * B = 1 := mul_eq_one_comm.mp hBC
  let r : Fin N := ⟨j, Nat.lt_succ_of_le (le_max_left j m)⟩
  let s : Fin N := ⟨m, Nat.lt_succ_of_le (le_max_right j m)⟩
  have hentry := congrArg (fun M : Matrix (Fin N) (Fin N) ℂ => M r s) hCB
  rw [Matrix.mul_apply, Matrix.one_apply] at hentry
  change (∑ k : Fin N, c j k * b k m) = _ at hentry
  rw [truncate r (fun k => c j k * b k m)] at hentry
  · simpa only [r, s, Fin.mk.injEq] using hentry
  · intro k hk
    dsimp only [c]
    rw [(alternatingBinomialPowerSum_eq_sum_stirlingSecond 1 (n + 1) j k).2.1 hk,
      zero_div, zero_mul]

end MetaMathlibExt
