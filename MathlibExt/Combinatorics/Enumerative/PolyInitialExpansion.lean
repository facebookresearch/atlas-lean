/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module


public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Basic.Real.Basic
public import MathlibExt.Combinatorics.Enumerative.GeneralizedStirlingNumbers

import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Ring

/-! # Weighted Stirling expansion of the associated polynomial at index zero

This file proves Chen's Stirling expansion for a variant of the Akiyama-Tanigawa algorithm and
its weighted generalization.
-/

@[expose] public section

namespace MetaMathlibExt

private theorem polyInitialExpansion_stirlingSecond_sum_succ (t : ℕ) (b : ℕ → ℝ) :
    ∑ m ∈ Finset.range (t + 1),
        (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) * (Nat.stirlingSecond t m : ℝ) *
          ((m : ℝ) * b m - ((m : ℝ) + 1) * b (m + 1)) =
      ∑ m ∈ Finset.range (t + 2),
        (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) *
          (Nat.stirlingSecond (t + 1) m : ℝ) * b m := by
  have hshift :
      (∑ m ∈ Finset.range (t + 1),
          (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) * (Nat.stirlingSecond t m : ℝ) *
            ((m : ℝ) * b m)) =
        ∑ m ∈ Finset.range (t + 1),
          (-1 : ℝ) ^ (m + 1) * (Nat.factorial (m + 1) : ℝ) *
            (Nat.stirlingSecond t (m + 1) : ℝ) * ((m + 1 : ℕ) : ℝ) * b (m + 1) := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ]
    simp only [Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self t), Nat.cast_zero,
      mul_zero, zero_mul, add_zero]
    ring_nf
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  rw [hshift, ← Finset.sum_sub_distrib]
  conv_rhs => rw [Finset.sum_range_succ']
  simp only [Nat.stirlingSecond_succ_zero, Nat.cast_zero, mul_zero, zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Nat.factorial_succ, Nat.stirlingSecond_succ_succ, pow_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  ring

/-- Chen's expansion of the zeroth entry of an array satisfying
`a m (s + 1) = m * a m s - (m + 1) * a (m + 1) s`, a variant of the Akiyama-Tanigawa
algorithm, by signed Stirling numbers of the second kind.

Source: K.-W. Chen, "Algorithms for Bernoulli numbers and Euler numbers," Journal of Integer
Sequences 4 (2001), Article 01.1.6, as stated in Dil, Kurt, and Cenkci (2007), Proposition 4.
It is the `x = 0` case of `poly_initial_expansion`. -/
public theorem chen_stirlingSecond_expansion (t : ℕ) :
    ∀ (a : ℕ → ℕ → ℝ),
      (∀ (m s : ℕ),
        a m (s + 1) = (m : ℝ) * a m s - ((m : ℝ) + 1) * a (m + 1) s) →
      a 0 t = ∑ m ∈ Finset.range (t + 1),
        (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) *
          (Nat.stirlingSecond t m : ℝ) * a m 0 := by
  induction t with
  | zero =>
      intro a hrec
      simp
  | succ t ih =>
      intro a hrec
      have hshift : ∀ (m s : ℕ),
          a m (s + 1 + 1) =
            (m : ℝ) * a m (s + 1) - ((m : ℝ) + 1) * a (m + 1) (s + 1) := by
        intro m s
        exact hrec m (s + 1)
      calc
        a 0 (t + 1) =
            ∑ m ∈ Finset.range (t + 1),
              (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) *
                (Nat.stirlingSecond t m : ℝ) * a m 1 := by
          simpa using ih (fun m s ↦ a m (s + 1)) hshift
        _ = ∑ m ∈ Finset.range (t + 1),
              (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) *
                (Nat.stirlingSecond t m : ℝ) *
                  ((m : ℝ) * a m 0 - ((m : ℝ) + 1) * a (m + 1) 0) := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [hrec m 0]
        _ = ∑ m ∈ Finset.range (t + 2),
              (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) *
                (Nat.stirlingSecond (t + 1) m : ℝ) * a m 0 :=
          polyInitialExpansion_stirlingSecond_sum_succ t (fun m ↦ a m 0)

private theorem polyInitialExpansion_generalizedStirlingSecond_full_range
    (n m : ℕ) (x : ℝ) :
    generalizedStirlingSecond n m x =
      ∑ i ∈ Finset.range (n + 1),
        (Nat.choose n i : ℝ) * (Nat.stirlingSecond (n - i) m : ℝ) * x ^ i := by
  unfold generalizedStirlingSecond
  apply Finset.sum_subset
  · intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  · intro i hi hnot
    simp only [Finset.mem_range] at hi
    simp only [Finset.mem_range, not_lt] at hnot
    rw [Nat.stirlingSecond_eq_zero_of_lt (by omega : n - i < m)]
    simp

private theorem polyInitialExpansion_zero_full_range (n t : ℕ) (ht : t ≤ n)
    (a : ℕ → ℕ → ℝ)
    (hrec : ∀ (m s : ℕ),
      a m (s + 1) = (m : ℝ) * a m s - ((m : ℝ) + 1) * a (m + 1) s) :
    ∑ m ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) *
          (Nat.stirlingSecond t m : ℝ) * a m 0 = a 0 t := by
  symm
  calc
    a 0 t = ∑ m ∈ Finset.range (t + 1),
        (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) *
          (Nat.stirlingSecond t m : ℝ) * a m 0 :=
      chen_stirlingSecond_expansion t a hrec
    _ = ∑ m ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) *
          (Nat.stirlingSecond t m : ℝ) * a m 0 := by
      apply Finset.sum_subset
      · intro m hm
        simp only [Finset.mem_range] at hm ⊢
        omega
      · intro m hm hnot
        simp only [Finset.mem_range] at hm
        simp only [Finset.mem_range, not_lt] at hnot
        rw [Nat.stirlingSecond_eq_zero_of_lt (by omega : t < m)]
        simp

set_option linter.unusedVariables false in
/-- Proposition 5 expansion of the associated polynomial at index zero by
weighted Stirling numbers of the second kind: the binomial-weighted sum of
`a 0 (n - k)` against `x ^ k` equals the signed factorial-weighted sum of the
canonical generalized Stirling numbers against `a m 0`, for arrays satisfying the
stated recurrence in the second argument.

Source: Ayhan Dil, Veli Kurt, and Mehmet Cenkci, "Algorithms for Bernoulli
and Related Polynomials," Journal of Integer Sequences 10 (2007),
Article 07.5.4, Proposition 5 (label prop5), lines 661–671,
https://cs.uwaterloo.ca/journals/JIS/VOL10/Dil/dil11.tex

Proves `Wanted` entry `poly_initial_expansion`.

Proof: Following Dil, Kurt, and Cenkci, Proposition 5, the proof is induction on
`t` for Chen's expansion `chen_stirlingSecond_expansion`, followed by a binomial convolution.
-/
public theorem poly_initial_expansion : ∀ (n : ℕ) (x : ℝ) (a : ℕ → ℕ → ℝ)
    (hrec : ∀ (m t : ℕ),
      a m (t + 1) = (m : ℝ) * a m t - ((m : ℝ) + 1) * a (m + 1) t),
    ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℝ) * x ^ k * a 0 (n - k) =
      ∑ m ∈ Finset.range (n + 1), (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) *
        (generalizedStirlingSecond n m x) * a m 0 := by
  intro n x a hrec
  symm
  calc
    (∑ m ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) *
          (generalizedStirlingSecond n m x) * a m 0) =
      ∑ m ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) *
          (∑ i ∈ Finset.range (n + 1),
            (Nat.choose n i : ℝ) * (Nat.stirlingSecond (n - i) m : ℝ) * x ^ i) *
          a m 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [polyInitialExpansion_generalizedStirlingSecond_full_range]
    _ = ∑ m ∈ Finset.range (n + 1),
        ∑ i ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) *
            ((Nat.choose n i : ℝ) * (Nat.stirlingSecond (n - i) m : ℝ) * x ^ i) *
            a m 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ i ∈ Finset.range (n + 1),
        ∑ m ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) *
            ((Nat.choose n i : ℝ) * (Nat.stirlingSecond (n - i) m : ℝ) * x ^ i) *
            a m 0 := by
      rw [Finset.sum_comm]
    _ = ∑ i ∈ Finset.range (n + 1),
        (Nat.choose n i : ℝ) * x ^ i *
          (∑ m ∈ Finset.range (n + 1),
            (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) *
              (Nat.stirlingSecond (n - i) m : ℝ) * a m 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      ring
    _ = ∑ i ∈ Finset.range (n + 1),
        (Nat.choose n i : ℝ) * x ^ i * a 0 (n - i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [polyInitialExpansion_zero_full_range n (n - i) (Nat.sub_le n i) a hrec]

end MetaMathlibExt
