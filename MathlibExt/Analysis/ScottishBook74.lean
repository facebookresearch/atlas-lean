/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Basic

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The homogeneous polynomial coefficient bound of Scottish Book Problem 74 -/

@[expose] public section

open scoped BigOperators

namespace MathlibExt.Analysis.ScottishBook74Wanted

/-- **Evaluation of a homogeneous polynomial.** Given a natural number $n$, real coefficients
$a_k$ indexed by multi-indices $k = (k_1, \dots, k_n) \in \mathbb{N}^n$, and a point
$t = (t_1, \dots, t_n) \in \mathbb{R}^n$, the value is

$$\sum_{k_1 + \cdots + k_n = n} a_k \, t_1^{k_1} \cdots t_n^{k_n},$$

the value at $t$ of the homogeneous polynomial of degree $n$ in $n$ variables with these
coefficients. The sum runs over all $k \in \mathbb{N}^n$ with $k_1 + \cdots + k_n = n$;
coefficients of other multi-indices do not enter.

Source: Scottish Book Problem 74. -/
def EvalPoly (n : ℕ) (a : (Fin n → ℕ) → ℝ) (t : Fin n → ℝ) : ℝ :=
  ∑ k ∈ (Fintype.piFinset fun _ : Fin n => Finset.range (n + 1)).filter
      (fun k => ∑ i, k i = n),
    a k * ∏ i, t i ^ k i

/-- **The coefficient bound of Scottish Book Problem 74.** This is the statement that for every
$n \ge 1$ and all real coefficients $a_k$ indexed by multi-indices
$k = (k_1, \dots, k_n) \in \mathbb{N}^n$ the following holds. Let
$P(t) = \sum_{k_1 + \cdots + k_n = n} a_k \, t_1^{k_1} \cdots t_n^{k_n}$ be the corresponding
homogeneous polynomial of degree $n$ on $\mathbb{R}^n$. If $|P(t)| \le 1$ for every
$t \in \mathbb{R}^n$ with $|t_1| + \cdots + |t_n| \le 1$, then
$|a_k| \le n^n / (k_1! \cdots k_n!)$ for every $k \in \mathbb{N}^n$ with
$k_1 + \cdots + k_n = n$.

This is only the coefficient upper bound asked for in Problem 74; the best constant is not
formalized here. -/
def ScottishBookProblem74Claim : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    ∀ a : (Fin n → ℕ) → ℝ,
      (∀ t : Fin n → ℝ, (∑ i, |t i|) ≤ 1 → |EvalPoly n a t| ≤ 1) →
      ∀ k : Fin n → ℕ, (∑ i, k i) = n →
        |a k| ≤ (n : ℝ) ^ n / ∏ i, (Nat.factorial (k i) : ℝ)

private lemma evalPoly_scale {n : ℕ} (a : (Fin n → ℕ) → ℝ) (c : ℝ) (t : Fin n → ℝ) :
    EvalPoly n a (fun i ↦ c * t i) = c ^ n * EvalPoly n a t := by
  simp only [EvalPoly, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [Finset.mem_filter] at hk
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hk.2]
  ring

private def weight (d j : ℕ) : ℝ := (-1 : ℝ) ^ (d - j) * (d.choose j : ℝ)

private noncomputable def point (d j : ℕ) : ℝ := (j : ℝ) - (d : ℝ) / 2

private lemma abs_point_le (d : ℕ) (j : Fin (d + 1)) : |point d j| ≤ (d : ℝ) / 2 := by
  have hlo : (0 : ℝ) ≤ (j.val : ℝ) := Nat.cast_nonneg _
  have hhi : (j.val : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.le_of_lt_succ j.isLt
  exact abs_le.mpr ⟨by unfold point; linarith, by unfold point; linarith⟩

private lemma sum_abs_weight (d : ℕ) : (∑ j : Fin (d + 1), |weight d j|) = (2 : ℝ) ^ d := by
  simp only [weight, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ (d.choose j : ℝ))]
  exact_mod_cast Nat.sum_range_choose d

private noncomputable def moment (d m : ℕ) : ℝ :=
  ∑ j : Fin (d + 1), weight d j * point d j ^ m

private lemma moment_eq_fwdDiff (d m : ℕ) :
    moment d m = (fwdDiff (1 : ℝ))^[d] (fun x : ℝ ↦ x ^ m) (-(d : ℝ) / 2) := by
  rw [moment, fwdDiff_iter_eq_sum_shift]
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ weight d j * point d j ^ m)]
  simp only [weight, point, zsmul_eq_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one, Int.cast_natCast, nsmul_eq_mul, mul_one, sub_eq_neg_add, neg_div]

private noncomputable def mixedDifference {n : ℕ} (k : Fin n → ℕ) (P : (Fin n → ℝ) → ℝ) : ℝ :=
  ∑ j : (∀ i, Fin (k i + 1)), (∏ i, weight (k i) (j i)) * P (fun i ↦ point (k i) (j i))

private lemma mixedDifference_evalPoly {n : ℕ} (a : (Fin n → ℕ) → ℝ)
    (k : Fin n → ℕ) (hk : (∑ i, k i) = n) :
    mixedDifference k (EvalPoly n a) = a k * ∏ i, (Nat.factorial (k i) : ℝ) := by
  classical
  let s := (Fintype.piFinset fun _ : Fin n => Finset.range (n + 1)).filter
      (fun l => ∑ i, l i = n)
  have hks : k ∈ s := by
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i ↦ ?_, hk⟩
    have hki : k i ≤ n := hk ▸ Finset.single_le_sum
      (f := k) (fun j _ ↦ Nat.zero_le (k j)) (Finset.mem_univ i)
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hki)
  -- Apply the mixed difference termwise, then factor the grid sum by coordinate.
  calc
    mixedDifference k (EvalPoly n a) = ∑ l ∈ s, a l * ∏ i, moment (k i) (l i) := by
      simp only [mixedDifference, EvalPoly, Finset.mul_sum, s]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      simp only [moment, Fintype.prod_sum, Finset.prod_mul_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      ring
    _ = a k * ∏ i, (Nat.factorial (k i) : ℝ) := by
      rw [Finset.sum_eq_single_of_mem k hks]
      · simp [moment_eq_fwdDiff, fwdDiff_iter_eq_factorial]
      · intro l hl hne
        have hls := (Finset.mem_filter.mp hl).2
        -- Distinct multi-indices of equal total degree must drop in some coordinate.
        have hex : ∃ i, l i < k i := by
          by_contra! h
          have heq : k = l := by
            funext i
            by_contra hi
            have hlt := Finset.sum_lt_sum (fun j _ ↦ h j)
              ⟨i, Finset.mem_univ i, lt_of_le_of_ne (h i) hi⟩
            exact (not_lt_of_ge (hk.trans hls.symm).ge) hlt
          exact hne heq.symm
        obtain ⟨i, hi⟩ := hex
        rw [Finset.prod_eq_zero (Finset.mem_univ i) (by
          simp [moment_eq_fwdDiff, fwdDiff_iter_pow_eq_zero_of_lt hi]), mul_zero]

/-- **Scottish Book Problem 74: the coefficient bound holds.** A real homogeneous polynomial
of degree $n \ge 1$ in $n$ variables with $|P(t)| \le 1$ on the unit $\ell^1$ ball has
$|a_k| \le n^n / \prod_i k_i!$ for every multi-index $k$ of total degree $n$.

Source: S. Mazur and W. Orlicz, Problem 74 of the Scottish Book; typescript PDF p. 36
(printed p. 33); see also R. D. Mauldin (ed.), *The Scottish Book*, 2nd ed. (2015).

The proof takes a mixed forward difference with order $k_i$ in coordinate $i$, centered
at zero. It isolates $a_k \prod_i k_i!$. The sample points have $\ell^1$ norm at most
$n/2$, and the absolute weights sum to $2^n$. Homogeneity gives the bound.
No claim about the best constant or its attainment is made. -/
theorem scottishBook74_holds : ScottishBookProblem74Claim := by
  intro n hn a hnorm k hk
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn : 0 < n)
  let r : ℝ := (n : ℝ) / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hbound (t : Fin n → ℝ) (ht : (∑ i, |t i|) ≤ r) : |EvalPoly n a t| ≤ r ^ n := by
    have hunit : (∑ i, |t i / r|) ≤ 1 := by
      simpa only [abs_div, abs_of_pos hr, ← Finset.sum_div] using (div_le_one hr).mpr ht
    calc
      |EvalPoly n a t| = r ^ n * |EvalPoly n a (fun i ↦ t i / r)| := by
        rw [← abs_of_nonneg (pow_nonneg hr.le n), ← abs_mul, ← evalPoly_scale]
        congr 2
        funext i
        exact (mul_div_cancel₀ _ hr.ne').symm
      _ ≤ r ^ n := mul_le_of_le_one_right (pow_nonneg hr.le n) (hnorm _ hunit)
  have hweights : (∑ j : (∀ i, Fin (k i + 1)), |∏ i, weight (k i) (j i)|) = (2 : ℝ) ^ n := by
    simp only [Finset.abs_prod]
    rw [← Fintype.prod_sum (fun i (j : Fin (k i + 1)) ↦ |weight (k i) j|)]
    simp only [sum_abs_weight, Finset.prod_pow_eq_pow_sum, hk]
  have hdiff : |mixedDifference k (EvalPoly n a)| ≤ (n : ℝ) ^ n := by
    calc
      |mixedDifference k (EvalPoly n a)| ≤ ∑ j : (∀ i, Fin (k i + 1)),
          |(∏ i, weight (k i) (j i)) * EvalPoly n a (fun i ↦ point (k i) (j i))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : (∀ i, Fin (k i + 1)), |∏ i, weight (k i) (j i)| * r ^ n := by
        refine Finset.sum_le_sum fun j _ ↦ ?_
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_left (hbound _ ?_) (abs_nonneg _)
        calc
          (∑ i, |point (k i) (j i)|) ≤ ∑ i, (k i : ℝ) / 2 :=
            Finset.sum_le_sum fun i _ ↦ abs_point_le _ _
          _ = r := by rw [← Finset.sum_div, ← Nat.cast_sum, hk]
      _ = (n : ℝ) ^ n := by rw [← Finset.sum_mul, hweights, ← mul_pow]; congr 1; dsimp [r]; ring
  have hfac : 0 < ∏ i, (Nat.factorial (k i) : ℝ) :=
    Finset.prod_pos fun i _ ↦ Nat.cast_pos.mpr (Nat.factorial_pos (k i))
  rw [mixedDifference_evalPoly a k hk, abs_mul, abs_of_pos hfac] at hdiff
  exact (le_div_iff₀ hfac).mpr hdiff

end MathlibExt.Analysis.ScottishBook74Wanted
