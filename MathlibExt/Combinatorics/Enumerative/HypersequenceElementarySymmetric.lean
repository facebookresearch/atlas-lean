/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import MathlibExt.Combinatorics.Enumerative.Hypersequence
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Tactic.Ring

/-! # Hypersequences through elementary symmetric polynomials

Iterating partial sums `j + 1` times weights `a_i` by the binomial coefficient
`binom(n - i + j, j)`, and `j!` times this coefficient is the product
`(n - i + 1) ⋯ (n - i + j)`. Vieta's formula expands that product in the elementary symmetric
polynomials of `n + 1, …, n + j`. The main result, `factorial_mul_hypersequence_eq_sum_esymm`,
expresses `j! a^{(j+1)}_n` through the weighted sums `t_k(n) = ∑_{i=0}^{n} i^k a_i`, in two
forms that differ by reversing the summation index.
-/

namespace MetaMathlibExt

open Finset

namespace factorial_mul_hypersequence_eq_sum_esymm

/-- Iterated partial sums are binomially weighted sums of the sequence. -/
private theorem hypersequence_succ_eq_sum (a : ℕ → ℂ) (r n : ℕ) :
    hypersequence a (r + 1) n = ∑ i ∈ range (n + 1), ((n - i + r).choose r : ℂ) * a i := by
  induction r generalizing n with
  | zero => simp [hypersequence]
  | succ r ih =>
    rw [hypersequence_succ]
    simp_rw [ih]
    rw [sum_comm' (t' := range (n + 1)) (s' := fun i => Ico i (n + 1))
      (fun k i => by simp only [mem_range, mem_Ico]; omega)]
    refine sum_congr rfl fun i hi => ?_
    have hi : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
    rw [← sum_mul, ← Nat.cast_sum, sum_Ico_eq_sum_range, show n + 1 - i = n - i + 1 by omega]
    simp only [Nat.add_sub_cancel_left]
    rw [Nat.sum_range_add_choose, Nat.add_assoc]

/-- `j!` times a binomial coefficient is a rising factorial. -/
private theorem factorial_mul_choose_eq_prod (j m : ℕ) :
    (j.factorial : ℂ) * ((m + j).choose j : ℂ) = ∏ x ∈ Icc 1 j, ((m : ℂ) + x) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [prod_Icc_succ_top (by omega), ← ih, ← Nat.cast_mul, ← Nat.cast_mul,
      ← Nat.ascFactorial_eq_factorial_mul_choose, ← Nat.ascFactorial_eq_factorial_mul_choose,
      Nat.ascFactorial_succ]
    push_cast
    ring

/-- Vieta's formula evaluated at a point. -/
private theorem prod_add_eq_sum_esymm (s : Multiset ℂ) (x : ℂ) :
    (s.map fun r => x + r).prod =
      ∑ k ∈ range (Multiset.card s + 1), s.esymm k * x ^ (Multiset.card s - k) := by
  have h := congrArg (Polynomial.eval x) (Multiset.prod_X_add_C_eq_sum_esymm s)
  simpa only [Polynomial.eval_multiset_prod, Multiset.map_map, Function.comp_def,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_pow] using h

/-- Elementary symmetric polynomials commute with the cast from `ℕ` to `ℂ`. -/
private theorem cast_esymm (s : Multiset ℕ) (k : ℕ) :
    ((s.esymm k : ℕ) : ℂ) = (s.map (Nat.cast : ℕ → ℂ)).esymm k := by
  simp only [Multiset.esymm, Multiset.powersetCard_map, Multiset.map_map, Function.comp_def,
    Nat.cast_multiset_sum, Nat.cast_multiset_prod]

/-- The weight `j! binom(n - i + j, j)` expanded in the elementary symmetric polynomials of
`n + 1, …, n + j`. -/
private theorem factorial_mul_choose_eq_sum_esymm (j n i : ℕ) (hi : i ≤ n) :
    (j.factorial : ℂ) * ((n - i + j).choose j : ℂ) =
      ∑ k ∈ range (j + 1),
        (((Icc 1 j).val.map (n + ·)).esymm k : ℕ) * (-(i : ℂ)) ^ (j - k) := by
  have hcard : Multiset.card (((Icc 1 j).val.map (n + ·)).map (Nat.cast : ℕ → ℂ)) = j := by
    simp
  have h := prod_add_eq_sum_esymm (((Icc 1 j).val.map (n + ·)).map (Nat.cast : ℕ → ℂ))
    (-(i : ℂ))
  rw [hcard] at h
  simp_rw [cast_esymm]
  rw [← h, factorial_mul_choose_eq_prod, Multiset.map_map, Multiset.map_map, prod_map_val]
  refine prod_congr rfl fun x _ => ?_
  simp only [Function.comp_apply]
  push_cast [hi]
  ring

end factorial_mul_hypersequence_eq_sum_esymm

open factorial_mul_hypersequence_eq_sum_esymm in
/-- **Hypersequences through elementary symmetric polynomials.** Let $a$ be a sequence of complex
numbers and let $j, n \in \mathbb{N}$. Write $a^{(r)}_n$ for the hypersequence of generation $r$
of $a$, write $e_{j,k}(n)$ for the elementary symmetric polynomial of degree $k$ in
$n + 1, \dots, n + j$, and put $t_i(n) = \sum_{k=0}^{n} k^i a_k$, with $0^0 = 1$. Then
$j! \, a^{(j+1)}_n = (-1)^j \sum_{k=0}^{j} (-1)^k e_{j,k}(n) \, t_{j-k}(n)$ and
$j! \, a^{(j+1)}_n = \sum_{k=0}^{j} (-1)^k e_{j,j-k}(n) \, t_k(n)$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36,
Theorem 1, Equation (2.1) (`integers-2026-A36-thm-1`). -/
public theorem factorial_mul_hypersequence_eq_sum_esymm (a : ℕ → ℂ) (j n : ℕ) :
    (j.factorial : ℂ) * hypersequence a (j + 1) n =
        (-1) ^ j * ∑ k ∈ Finset.range (j + 1), (-1) ^ k *
          (((Finset.Icc 1 j).val.map (n + ·)).esymm k : ℕ) *
            ∑ i ∈ Finset.range (n + 1), (i : ℂ) ^ (j - k) * a i ∧
      (j.factorial : ℂ) * hypersequence a (j + 1) n =
        ∑ k ∈ Finset.range (j + 1), (-1) ^ k *
          (((Finset.Icc 1 j).val.map (n + ·)).esymm (j - k) : ℕ) *
            ∑ i ∈ Finset.range (n + 1), (i : ℂ) ^ k * a i := by
  -- Both forms are reindexings of the expansion with signs `(-1) ^ (j - k)`.
  have key : (j.factorial : ℂ) * hypersequence a (j + 1) n =
      ∑ k ∈ range (j + 1), (-1) ^ (j - k) * (((Icc 1 j).val.map (n + ·)).esymm k : ℕ) *
        ∑ i ∈ range (n + 1), (i : ℂ) ^ (j - k) * a i := by
    rw [hypersequence_succ_eq_sum, mul_sum]
    trans ∑ i ∈ range (n + 1), ∑ k ∈ range (j + 1),
      (-1) ^ (j - k) * (((Icc 1 j).val.map (n + ·)).esymm k : ℕ) * ((i : ℂ) ^ (j - k) * a i)
    · refine sum_congr rfl fun i hi => ?_
      rw [← mul_assoc, factorial_mul_choose_eq_sum_esymm j n i
        (Nat.lt_succ_iff.mp (mem_range.mp hi)), sum_mul]
      refine sum_congr rfl fun k _ => ?_
      rw [neg_pow]
      ring
    · rw [sum_comm]
      exact sum_congr rfl fun k _ => (mul_sum _ _ _).symm
  refine ⟨?_, ?_⟩
  · rw [key, mul_sum]
    refine sum_congr rfl fun k hk => ?_
    have hk : k ≤ j := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have hsign : (-1 : ℂ) ^ (j - k) = (-1) ^ j * (-1) ^ k := by
      rw [← pow_add, show j + k = j - k + 2 * k by omega, pow_add, pow_mul, neg_one_sq,
        one_pow, mul_one]
    rw [hsign]
    ring
  · have hrefl := sum_range_reflect (fun k => (-1 : ℂ) ^ k *
      (((Icc 1 j).val.map (n + ·)).esymm (j - k) : ℕ) *
        ∑ i ∈ range (n + 1), (i : ℂ) ^ k * a i) (j + 1)
    rw [key, ← hrefl]
    refine sum_congr rfl fun k hk => ?_
    have hk : k ≤ j := Nat.lt_succ_iff.mp (mem_range.mp hk)
    rw [show j + 1 - 1 - k = j - k by omega, show j - (j - k) = k by omega]

end MetaMathlibExt
