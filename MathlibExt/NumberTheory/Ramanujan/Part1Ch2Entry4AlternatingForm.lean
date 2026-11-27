/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 2, Entry 4

Alternating-harmonic identity for the sum of reciprocals of 64k³-4k.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2

namespace Entry4AlternatingForm

/-- **Alternating form of Ramanujan's identity for $1/((4k)^3 - 4k)$, including $n = 0$.** For
every natural number $n$,
$$
1 + 2 \sum_{k=1}^{n} \frac{1}{(4k)^3 - 4k} =
\sum_{k=1}^{4n+1} \frac{(-1)^{k+1}}{k} + \frac{1}{2} \sum_{k=1}^{2n} \frac{(-1)^{k+1}}{k}.
$$
-/
theorem ramanujan_part1_ch2_entry4_alternating_form_general (n : ℕ) :
    (1 : ℝ) + 2 * ∑ k ∈ Finset.Icc 1 n, (1 / ((4 * (k : ℝ)) ^ 3 - 4 * (k : ℝ))) =
    (∑ k ∈ Finset.Icc 1 (4 * n + 1), ((-1 : ℝ) ^ (k + 1) / (k : ℝ))) +
    (1 / 2 : ℝ) * ∑ k ∈ Finset.Icc 1 (2 * n), ((-1 : ℝ) ^ (k + 1) / (k : ℝ)) := by
  have gen : ∀ m : ℕ,
      (1 : ℝ) + 2 * ∑ k ∈ Finset.Icc 1 m, (1 / ((4 * (k : ℝ)) ^ 3 - 4 * (k : ℝ))) =
      (∑ k ∈ Finset.Icc 1 (4 * m + 1), ((-1 : ℝ) ^ (k + 1) / (k : ℝ))) +
      (1 / 2 : ℝ) * ∑ k ∈ Finset.Icc 1 (2 * m), ((-1 : ℝ) ^ (k + 1) / (k : ℝ)) := by
    intro m
    induction m with
    | zero => simp
    | succ n ih =>
      have eA : 4 * (n + 1) + 1 = 4 * n + 5 := by ring
      have eB : 2 * (n + 1) = 2 * n + 2 := by ring
      rw [eA, eB]
      have peelL : (∑ k ∈ Finset.Icc 1 (n + 1), (1 / ((4 * (k : ℝ)) ^ 3 - 4 * (k : ℝ)))) =
          (∑ k ∈ Finset.Icc 1 n, (1 / ((4 * (k : ℝ)) ^ 3 - 4 * (k : ℝ)))) +
          (1 / ((4 * (((n + 1 : ℕ)) : ℝ)) ^ 3 - 4 * (((n + 1 : ℕ)) : ℝ))) :=
        Finset.sum_Icc_succ_top (by omega) _
      have peelA1 : (∑ k ∈ Finset.Icc 1 (4 * n + 5), ((-1 : ℝ) ^ (k + 1) / (k : ℝ))) =
          (∑ k ∈ Finset.Icc 1 (4 * n + 4), ((-1 : ℝ) ^ (k + 1) / (k : ℝ))) +
          ((-1 : ℝ) ^ ((4 * n + 5) + 1) / (((4 * n + 5 : ℕ)) : ℝ)) := by
        have h := Finset.sum_Icc_succ_top (show 1 ≤ (4 * n + 4) + 1 by omega)
          (fun k => ((-1 : ℝ) ^ (k + 1) / (k : ℝ)))
        rwa [show (4 * n + 4) + 1 = 4 * n + 5 from by ring] at h
      have peelA2 : (∑ k ∈ Finset.Icc 1 (4 * n + 4), ((-1 : ℝ) ^ (k + 1) / (k : ℝ))) =
          (∑ k ∈ Finset.Icc 1 (4 * n + 3), ((-1 : ℝ) ^ (k + 1) / (k : ℝ))) +
          ((-1 : ℝ) ^ ((4 * n + 4) + 1) / (((4 * n + 4 : ℕ)) : ℝ)) := by
        have h := Finset.sum_Icc_succ_top (show 1 ≤ (4 * n + 3) + 1 by omega)
          (fun k => ((-1 : ℝ) ^ (k + 1) / (k : ℝ)))
        rwa [show (4 * n + 3) + 1 = 4 * n + 4 from by ring] at h
      have peelA3 : (∑ k ∈ Finset.Icc 1 (4 * n + 3), ((-1 : ℝ) ^ (k + 1) / (k : ℝ))) =
          (∑ k ∈ Finset.Icc 1 (4 * n + 2), ((-1 : ℝ) ^ (k + 1) / (k : ℝ))) +
          ((-1 : ℝ) ^ ((4 * n + 3) + 1) / (((4 * n + 3 : ℕ)) : ℝ)) := by
        have h := Finset.sum_Icc_succ_top (show 1 ≤ (4 * n + 2) + 1 by omega)
          (fun k => ((-1 : ℝ) ^ (k + 1) / (k : ℝ)))
        rwa [show (4 * n + 2) + 1 = 4 * n + 3 from by ring] at h
      have peelA4 : (∑ k ∈ Finset.Icc 1 (4 * n + 2), ((-1 : ℝ) ^ (k + 1) / (k : ℝ))) =
          (∑ k ∈ Finset.Icc 1 (4 * n + 1), ((-1 : ℝ) ^ (k + 1) / (k : ℝ))) +
          ((-1 : ℝ) ^ ((4 * n + 2) + 1) / (((4 * n + 2 : ℕ)) : ℝ)) := by
        have h := Finset.sum_Icc_succ_top (show 1 ≤ (4 * n + 1) + 1 by omega)
          (fun k => ((-1 : ℝ) ^ (k + 1) / (k : ℝ)))
        rwa [show (4 * n + 1) + 1 = 4 * n + 2 from by ring] at h
      have peelB1 : (∑ k ∈ Finset.Icc 1 (2 * n + 2), ((-1 : ℝ) ^ (k + 1) / (k : ℝ))) =
          (∑ k ∈ Finset.Icc 1 (2 * n + 1), ((-1 : ℝ) ^ (k + 1) / (k : ℝ))) +
          ((-1 : ℝ) ^ ((2 * n + 2) + 1) / (((2 * n + 2 : ℕ)) : ℝ)) := by
        have h := Finset.sum_Icc_succ_top (show 1 ≤ (2 * n + 1) + 1 by omega)
          (fun k => ((-1 : ℝ) ^ (k + 1) / (k : ℝ)))
        rwa [show (2 * n + 1) + 1 = 2 * n + 2 from by ring] at h
      have peelB2 : (∑ k ∈ Finset.Icc 1 (2 * n + 1), ((-1 : ℝ) ^ (k + 1) / (k : ℝ))) =
          (∑ k ∈ Finset.Icc 1 (2 * n + 0), ((-1 : ℝ) ^ (k + 1) / (k : ℝ))) +
          ((-1 : ℝ) ^ ((2 * n + 1) + 1) / (((2 * n + 1 : ℕ)) : ℝ)) := by
        have h := Finset.sum_Icc_succ_top (show 1 ≤ (2 * n + 0) + 1 by omega)
          (fun k => ((-1 : ℝ) ^ (k + 1) / (k : ℝ)))
        rwa [show (2 * n + 0) + 1 = 2 * n + 1 from by ring] at h
      have hB0 : Finset.Icc 1 (2 * n + 0) = Finset.Icc 1 (2 * n) := by ring_nf
      rw [peelL, peelA1, peelA2, peelA3, peelA4, peelB1, peelB2, hB0]
      have s2 : ((-1 : ℝ) ^ ((4 * n + 2) + 1)) = -1 :=
        ((by rw [Nat.odd_iff]; omega : Odd ((4 * n + 2) + 1))).neg_one_pow
      have s3 : ((-1 : ℝ) ^ ((4 * n + 3) + 1)) = 1 :=
        ((by rw [Nat.even_iff]; omega : Even ((4 * n + 3) + 1))).neg_one_pow
      have s4 : ((-1 : ℝ) ^ ((4 * n + 4) + 1)) = -1 :=
        ((by rw [Nat.odd_iff]; omega : Odd ((4 * n + 4) + 1))).neg_one_pow
      have s5 : ((-1 : ℝ) ^ ((4 * n + 5) + 1)) = 1 :=
        ((by rw [Nat.even_iff]; omega : Even ((4 * n + 5) + 1))).neg_one_pow
      have t1 : ((-1 : ℝ) ^ ((2 * n + 1) + 1)) = 1 :=
        ((by rw [Nat.even_iff]; omega : Even ((2 * n + 1) + 1))).neg_one_pow
      have t2 : ((-1 : ℝ) ^ ((2 * n + 2) + 1)) = -1 :=
        ((by rw [Nat.odd_iff]; omega : Odd ((2 * n + 2) + 1))).neg_one_pow
      rw [s2, s3, s4, s5, t1, t2]
      push_cast
      have key : 2 * (1 / ((4 * ((n : ℝ) + 1)) ^ 3 - 4 * ((n : ℝ) + 1))) =
          (-1 / (4 * (n : ℝ) + 2) + 1 / (4 * (n : ℝ) + 3) - 1 / (4 * (n : ℝ) + 4) +
          1 / (4 * (n : ℝ) + 5)) +
          (1 / 2 : ℝ) * (1 / (2 * (n : ℝ) + 1) - 1 / (2 * (n : ℝ) + 2)) := by
        have hpos : (0 : ℝ) < (4 * ((n : ℝ) + 1)) ^ 3 - 4 * ((n : ℝ) + 1) := by
          have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          nlinarith [sq_nonneg (n : ℝ), sq_nonneg ((n : ℝ) + 1),
            mul_nonneg hn hn,
            mul_pos (show (0 : ℝ) < (n : ℝ) + 1 by linarith)
              (show (0 : ℝ) < (n : ℝ) + 1 by linarith)]
        have h1 : (4 * (n : ℝ) + 2) ≠ 0 := by positivity
        have h2 : (4 * (n : ℝ) + 3) ≠ 0 := by positivity
        have h3 : (4 * (n : ℝ) + 4) ≠ 0 := by positivity
        have h4 : (4 * (n : ℝ) + 5) ≠ 0 := by positivity
        have h5 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
        have h6 : (2 * (n : ℝ) + 2) ≠ 0 := by positivity
        have h7 : ((4 * ((n : ℝ) + 1)) ^ 3 - 4 * ((n : ℝ) + 1)) ≠ 0 := ne_of_gt hpos
        have e : 2 * (1 / ((4 * ((n : ℝ) + 1)) ^ 3 - 4 * ((n : ℝ) + 1)))
          = 2 / ((4 * ((n : ℝ) + 1)) ^ 3 - 4 * ((n : ℝ) + 1)) := by ring
        rw [e, div_eq_iff h7]
        field_simp
        ring
      linear_combination ih + key
  exact gen n

set_option linter.unusedVariables false in
/-- **Alternating form of Ramanujan's sum identity for $1/((4k)^3 - 4k)$.** For every positive
integer $n$,
$$
1 + 2 \sum_{k=1}^{n} \frac{1}{(4k)^3 - 4k} =
\sum_{k=1}^{4n+1} \frac{(-1)^{k+1}}{k} + \frac{1}{2} \sum_{k=1}^{2n} \frac{(-1)^{k+1}}{k}.
$$

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I (Springer, 1985), Chapter 2, Entry
    4, formula (4.1), printed p. 28 / PDF p. 38.
Proves `Wanted` entry `ramanujan_part1_ch2_entry4_alternating_form`.
-/
theorem ramanujan_part1_ch2_entry4_alternating_form (n : ℕ) (hn : 0 < n) :
    (1 : ℝ) + 2 * ∑ k ∈ Finset.Icc 1 n, (1 / ((4 * (k : ℝ)) ^ 3 - 4 * (k : ℝ))) =
    (∑ k ∈ Finset.Icc 1 (4 * n + 1), ((-1 : ℝ) ^ (k + 1) / (k : ℝ))) +
    (1 / 2 : ℝ) * ∑ k ∈ Finset.Icc 1 (2 * n), ((-1 : ℝ) ^ (k + 1) / (k : ℝ)) :=
  by apply ramanujan_part1_ch2_entry4_alternating_form_general <;> assumption

end Entry4AlternatingForm

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2
