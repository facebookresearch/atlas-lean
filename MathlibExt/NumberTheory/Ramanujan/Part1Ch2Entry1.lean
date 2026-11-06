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
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 2, Entry 1

Sum of 1/(n+k) over k ≤ n via reciprocals of 8k³-2k.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2

namespace Entry1

private lemma icc_one_eq_range (n : ℕ) (h : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 n, h k = ∑ k ∈ Finset.range n, h (k + 1) := by
  have h1 : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [h1, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  omega

/-- **Ramanujan's identity for $\sum_{k=1}^{n} 1/(n+k)$, including $n = 0$.** For every natural
number $n$,
$$\sum_{k=1}^{n} \frac{1}{n+k} = \frac{n}{2n+1} + \sum_{k=1}^{n} \frac{1}{(2k)^3 - 2k}.$$

This is Ramanujan's Entry 1 of Chapter 2 without the hypothesis $n \ge 1$; at $n = 0$ both sides
are $0$. -/
theorem ramanujan_part1_ch2_entry1_general (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((n : ℝ) + (k : ℝ)) =
      (n : ℝ) / (2 * (n : ℝ) + 1) + ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) /
          ((2 * (k : ℝ)) ^ 3 - 2 * (k : ℝ)) := by
  have aux : ∀ m : ℕ,
      ∑ k ∈ Finset.Icc 1 m, (1 : ℝ) / ((m : ℝ) + (k : ℝ)) =
        (m : ℝ) / (2 * (m : ℝ) + 1) + ∑ k ∈ Finset.Icc 1 m, (1 : ℝ) /
            ((2 * (k : ℝ)) ^ 3 - 2 * (k : ℝ)) := by
    intro m
    induction m with
    | zero => simp
    | succ n ih =>
      have hR : ∑ k ∈ Finset.Icc 1 (n + 1), (1 : ℝ) / ((2 * (k : ℝ)) ^ 3 - 2 * (k : ℝ)) =
          (∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((2 * (k : ℝ)) ^ 3 - 2 * (k : ℝ))) +
          (1 : ℝ) / ((2 * ((((n + 1 : ℕ)) : ℝ))) ^ 3 - 2 * ((((n + 1 : ℕ)) : ℝ))) :=
        Finset.sum_Icc_succ_top (by omega) _
      have hA1 : ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((n : ℝ) + (k : ℝ)) =
          ∑ k ∈ Finset.range n, (1 : ℝ) / ((n : ℝ) + 1 + ((k : ℕ) : ℝ)) := by
        rw [icc_one_eq_range]
        apply Finset.sum_congr rfl
        intro k _
        congr 1
        push_cast
        ring
      have hA2 : ∑ k ∈ Finset.Icc 1 (n + 1), (1 : ℝ) / ((((n + 1 : ℕ)) : ℝ) + (k : ℝ)) =
          ∑ k ∈ Finset.range (n + 1), (1 : ℝ) / ((n : ℝ) + 2 + ((k : ℕ) : ℝ)) := by
        rw [icc_one_eq_range]
        apply Finset.sum_congr rfl
        intro k _
        congr 1
        push_cast
        ring
      have hD_top : ∑ k ∈ Finset.range (n + 1), (1 : ℝ) / ((n : ℝ) + 1 + ((k : ℕ) : ℝ)) =
          (∑ k ∈ Finset.range n, (1 : ℝ) / ((n : ℝ) + 1 + ((k : ℕ) : ℝ))) +
          (1 : ℝ) / ((n : ℝ) + 1 + ((n : ℕ) : ℝ)) :=
        Finset.sum_range_succ _ _
      have hD_bot : ∑ k ∈ Finset.range (n + 1), (1 : ℝ) / ((n : ℝ) + 1 + ((k : ℕ) : ℝ)) =
          (∑ k ∈ Finset.range n, (1 : ℝ) / ((n : ℝ) + 2 + ((k : ℕ) : ℝ))) +
          (1 : ℝ) / ((n : ℝ) + 1) := by
        rw [Finset.sum_range_succ']
        congr 1
        · apply Finset.sum_congr rfl
          intro k _
          congr 1
          push_cast
          ring
        · simp
      have hA2_top : ∑ k ∈ Finset.range (n + 1), (1 : ℝ) / ((n : ℝ) + 2 + ((k : ℕ) : ℝ)) =
          (∑ k ∈ Finset.range n, (1 : ℝ) / ((n : ℝ) + 2 + ((k : ℕ) : ℝ))) +
          (1 : ℝ) / ((n : ℝ) + 2 + ((n : ℕ) : ℝ)) :=
        Finset.sum_range_succ _ _
      rw [hR, hA2]
      rw [hA1] at ih
      have hDeq : (∑ k ∈ Finset.range n, (1 : ℝ) / ((n : ℝ) + 1 + ((k : ℕ) : ℝ))) +
          (1 : ℝ) / ((n : ℝ) + 1 + ((n : ℕ) : ℝ)) =
          (∑ k ∈ Finset.range n, (1 : ℝ) / ((n : ℝ) + 2 + ((k : ℕ) : ℝ))) +
          (1 : ℝ) / ((n : ℝ) + 1) := by
        rw [← hD_top, hD_bot]
      have hLHS : ∑ k ∈ Finset.range (n + 1), (1 : ℝ) / ((n : ℝ) + 2 + ((k : ℕ) : ℝ)) =
          (∑ k ∈ Finset.range n, (1 : ℝ) / ((n : ℝ) + 1 + ((k : ℕ) : ℝ))) +
          (1 : ℝ) / ((n : ℝ) + 1 + ((n : ℕ) : ℝ)) -
          (1 : ℝ) / ((n : ℝ) + 1) +
          (1 : ℝ) / ((n : ℝ) + 2 + ((n : ℕ) : ℝ)) := by
        rw [hA2_top]
        linarith [hDeq]
      rw [hLHS, ih]
      have hn1n : (1 : ℝ) / ((n : ℝ) + 1 + ((n : ℕ) : ℝ)) = (1 : ℝ) / (2 * (n : ℝ) + 1) := by
        congr 1
        ring
      have hn2n : (1 : ℝ) / ((n : ℝ) + 2 + ((n : ℕ) : ℝ)) = (1 : ℝ) / (2 * (n : ℝ) + 2) := by
        congr 1
        ring
      rw [hn1n, hn2n]
      have hcast : ((((n + 1 : ℕ)) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      have hterm : (1 : ℝ) / ((2 * (((n : ℝ) + 1))) ^ 3 - 2 * (((n : ℝ) + 1))) =
          (1 : ℝ) / ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 2) * (2 * (n : ℝ) + 3)) := by
        congr 1
        ring
      rw [hterm]
      have h2n3 : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
      have h2n2' : (2 * (n : ℝ) + 2) ≠ 0 := by positivity
      have h2n1 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
      have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
  exact aux n

set_option linter.unusedVariables false in
/-- **Ramanujan's identity for $\sum_{k=1}^{n} 1/(n+k)$.** For every positive integer $n$,
$$\sum_{k=1}^{n} \frac{1}{n+k} = \frac{n}{2n+1} + \sum_{k=1}^{n} \frac{1}{(2k)^3 - 2k}.$$

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I (Springer, 1985), Chapter 2, Entry
    1, formula (1.1), printed p. 25 / PDF p. 35.
Proves `Wanted` entry `ramanujan_part1_ch2_entry1`.
-/
theorem ramanujan_part1_ch2_entry1 (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((n : ℝ) + (k : ℝ)) =
      (n : ℝ) / (2 * (n : ℝ) + 1) + ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) /
          ((2 * (k : ℝ)) ^ 3 - 2 * (k : ℝ)) :=
  ramanujan_part1_ch2_entry1_general ..

end Entry1

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2
