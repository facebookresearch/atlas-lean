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
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 2, Entry 5

Reciprocals of 216k³-6k relate two harmonic-type sums of 1/(n+k).
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2

namespace Entry5

private lemma S2_step (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 (n + 1), (1 : ℝ) / ((((n + 1 : ℕ)) : ℝ) + (k : ℝ)) =
    (∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((n : ℝ) + (k : ℝ))) -
      1 / ((n : ℝ) + 1) + 1 / (2 * (n : ℝ) + 1) + 1 / (2 * (n : ℝ) + 2) := by
  have e1 : Finset.Icc 1 (n + 1) = Finset.Ico 1 (n + 2) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have e2 : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [e1, e2, Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
  have r1 : n + 2 - 1 = n + 1 := by omega
  have r2 : n + 1 - 1 = n := by omega
  rw [r1, r2]
  set h : ℕ → ℝ := fun i => 1 / ((n : ℝ) + 1 + (i : ℝ)) with hh
  have cL : (∑ k ∈ Finset.range (n + 1), (1 : ℝ) / ((((n + 1 : ℕ)) : ℝ) + (((1 + k : ℕ)) : ℝ))) =
      ∑ i ∈ Finset.range (n + 1), h (i + 1) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [hh]
    congr 1
    push_cast
    ring
  have cR : (∑ k ∈ Finset.range n, (1 : ℝ) / ((n : ℝ) + (((1 + k : ℕ)) : ℝ))) =
      ∑ i ∈ Finset.range n, h i := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [hh]
    congr 1
    push_cast
    ring
  rw [cL, cR]
  have t1 : ∑ i ∈ Finset.range (n + 1), h i = ∑ i ∈ Finset.range n, h i + h n :=
    Finset.sum_range_succ h n
  have t2 : ∑ i ∈ Finset.range (n + 2), h i = ∑ i ∈ Finset.range (n + 1), h (i + 1) + h 0 :=
    Finset.sum_range_succ' h (n + 1)
  have t3 : ∑ i ∈ Finset.range (n + 2), h i = ∑ i ∈ Finset.range (n + 1), h i + h (n + 1) :=
    Finset.sum_range_succ h (n + 1)
  have h0 : h 0 = 1 / ((n : ℝ) + 1) := by simp [hh]
  have hn : h n = 1 / (2 * (n : ℝ) + 1) := by
    simp only [hh]
    congr 1
    ring
  have hn1 : h (n + 1) = 1 / (2 * (n : ℝ) + 2) := by
    simp only [hh]
    congr 1
    push_cast
    ring
  rw [hn] at t1
  rw [h0] at t2
  rw [hn1] at t3
  linear_combination -t2 + t3 + t1

private lemma S3_step (n : ℕ) :
    ∑ k ∈ Finset.Icc 0 (2 * (n + 1)), (1 : ℝ) / (2 * ((((n + 1 : ℕ)) : ℝ)) + 2 * (k : ℝ) + 1) =
    (∑ k ∈ Finset.Icc 0 (2 * n), (1 : ℝ) / (2 * (n : ℝ) + 2 * (k : ℝ) + 1)) -
      1 / (2 * (n : ℝ) + 1) + 1 / (6 * (n : ℝ) + 3) + 1 / (6 * (n : ℝ) + 5) +
      1 / (6 * (n : ℝ) + 7) := by
  have e1 : Finset.Icc 0 (2 * (n + 1)) = Finset.Ico 0 (2 * (n + 1) + 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have e2 : Finset.Icc 0 (2 * n) = Finset.Ico 0 (2 * n + 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [e1, e2, Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
  have r1 : 2 * (n + 1) + 1 - 0 = 2 * n + 3 := by omega
  have r2 : 2 * n + 1 - 0 = 2 * n + 1 := by omega
  rw [r1, r2]
  set g : ℕ → ℝ := fun i => 1 / (2 * (n : ℝ) + 3 + 2 * (i : ℝ)) with hg
  set Rf : ℕ → ℝ := fun k => 1 / (2 * (n : ℝ) + 2 * (k : ℝ) + 1) with hRf
  have cL : (∑ k ∈ Finset.range (2 * n + 3),
      (1 : ℝ) / (2 * ((((n + 1 : ℕ)) : ℝ)) + 2 * ((((0 + k : ℕ))) : ℝ) + 1)) =
      ∑ i ∈ Finset.range (2 * n + 3), g i := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [hg]
    congr 1
    push_cast
    ring
  have cR : (∑ k ∈ Finset.range (2 * n + 1),
      (1 : ℝ) / (2 * (n : ℝ) + 2 * ((((0 + k : ℕ))) : ℝ) + 1)) =
      ∑ k ∈ Finset.range (2 * n + 1), Rf k := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [hRf]
    congr 1
    push_cast
    ring
  rw [cL, cR]
  have s1a : ∑ k ∈ Finset.range (2 * n + 1), Rf k =
      (∑ k ∈ Finset.range (2 * n), Rf (k + 1)) + Rf 0 :=
    Finset.sum_range_succ' Rf (2 * n)
  have s1b : (∑ k ∈ Finset.range (2 * n), Rf (k + 1)) = ∑ i ∈ Finset.range (2 * n), g i := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [hRf, hg]
    congr 1
    push_cast
    ring
  have s1c : Rf 0 = 1 / (2 * (n : ℝ) + 1) := by simp [hRf]
  have s1 : ∑ k ∈ Finset.range (2 * n + 1), Rf k =
      1 / (2 * (n : ℝ) + 1) + ∑ i ∈ Finset.range (2 * n), g i := by
    rw [s1a, s1b, s1c]
    ring
  rw [s1]
  have w1 : 2 * n + 3 = (2 * n + 2) + 1 := by omega
  have w2 : 2 * n + 2 = (2 * n + 1) + 1 := by omega
  have w3 : 2 * n + 1 = (2 * n) + 1 := by omega
  rw [w1, Finset.sum_range_succ, w2, Finset.sum_range_succ, w3, Finset.sum_range_succ]
  have gv0 : g (2 * n) = 1 / (6 * (n : ℝ) + 3) := by
    simp only [hg]
    congr 1
    push_cast
    ring
  have gv1 : g (2 * n + 1) = 1 / (6 * (n : ℝ) + 5) := by
    simp only [hg]
    congr 1
    push_cast
    ring
  have gv2 : g (2 * n + 2) = 1 / (6 * (n : ℝ) + 7) := by
    simp only [hg]
    congr 1
    push_cast
    ring
  rw [gv0, gv1, gv2]
  ring

private lemma step_identity (n : ℕ) :
    2 * ((1 : ℝ) / ((6 * ((((n + 1 : ℕ))) : ℝ)) ^ 3 - 6 * ((((n + 1 : ℕ))) : ℝ))) =
    (2 : ℝ) / 3 * (-1 / ((n : ℝ) + 1) + 1 / (2 * (n : ℝ) + 1) + 1 / (2 * (n : ℝ) + 2)) +
    (-1 / (2 * (n : ℝ) + 1) + 1 / (6 * (n : ℝ) + 3) + 1 / (6 * (n : ℝ) + 5) +
      1 / (6 * (n : ℝ) + 7)) := by
  have hx : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have p1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have p2 : (0 : ℝ) < 2 * (n : ℝ) + 1 := by linarith
  have p3 : (0 : ℝ) < 2 * (n : ℝ) + 2 := by linarith
  have p4 : (0 : ℝ) < 6 * (n : ℝ) + 3 := by linarith
  have p5 : (0 : ℝ) < 6 * (n : ℝ) + 5 := by linarith
  have p6 : (0 : ℝ) < 6 * (n : ℝ) + 7 := by linarith
  have e1 : ((n : ℝ) + 1) ≠ 0 := ne_of_gt p1
  have e2 : (2 * (n : ℝ) + 1) ≠ 0 := ne_of_gt p2
  have e3 : (2 * (n : ℝ) + 2) ≠ 0 := ne_of_gt p3
  have e4 : (6 * (n : ℝ) + 3) ≠ 0 := ne_of_gt p4
  have e5 : (6 * (n : ℝ) + 5) ≠ 0 := ne_of_gt p5
  have e6 : (6 * (n : ℝ) + 7) ≠ 0 := ne_of_gt p6
  have hm1 : (1 : ℝ) ≤ ((((n + 1 : ℕ))) : ℝ) := by exact_mod_cast Nat.le_add_left 1 n
  have hm0 : ((((n + 1 : ℕ))) : ℝ) ≠ 0 := by
    have hne : n + 1 ≠ 0 := by omega
    exact_mod_cast hne
  have h1' : 6 * ((((n + 1 : ℕ))) : ℝ) - 1 ≠ 0 := by
    have p : (0 : ℝ) < 6 * ((((n + 1 : ℕ))) : ℝ) - 1 := by linarith
    exact ne_of_gt p
  have h2' : 6 * ((((n + 1 : ℕ))) : ℝ) + 1 ≠ 0 := by
    have p : (0 : ℝ) < 6 * ((((n + 1 : ℕ))) : ℝ) + 1 := by linarith
    exact ne_of_gt p
  have decomp : 2 * (1 / (6 * ((((n + 1 : ℕ))) : ℝ) * (6 * ((((n + 1 : ℕ))) : ℝ) - 1) *
      (6 * ((((n + 1 : ℕ))) : ℝ) + 1))) =
      -1 / (3 * ((((n + 1 : ℕ))) : ℝ)) + 1 / (6 * ((((n + 1 : ℕ))) : ℝ) - 1) +
      1 / (6 * ((((n + 1 : ℕ))) : ℝ) + 1) := by
    field_simp
    ring
  have hDfac : (6 * ((((n + 1 : ℕ))) : ℝ)) ^ 3 - 6 * ((((n + 1 : ℕ))) : ℝ) =
      6 * ((((n + 1 : ℕ))) : ℝ) * (6 * ((((n + 1 : ℕ))) : ℝ) - 1) *
      (6 * ((((n + 1 : ℕ))) : ℝ) + 1) := by ring
  have m_eq : ((((n + 1 : ℕ))) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hDfac, decomp, m_eq]
  have e33 : (3 * (n : ℝ) + 3) ≠ 0 := by
    have p : (0 : ℝ) < 3 * ((n : ℝ) + 1) := by linarith
    have h : (0 : ℝ) < 3 * (n : ℝ) + 3 := by linarith [p]
    exact ne_of_gt h
  have g1 : 3 * ((n : ℝ) + 1) = 3 * (n : ℝ) + 3 := by ring
  have g2 : 6 * ((n : ℝ) + 1) - 1 = 6 * (n : ℝ) + 5 := by ring
  have g3 : 6 * ((n : ℝ) + 1) + 1 = 6 * (n : ℝ) + 7 := by ring
  rw [g1, g2, g3]
  field_simp
  ring

/-- **Ramanujan's sum identity for $1/((6k)^3 - 6k)$, including $n = 0$.** For every natural
number $n$,
$$
1 + 2 \sum_{k=1}^{n} \frac{1}{(6k)^3 - 6k} =
\frac{2}{3} \sum_{k=1}^{n} \frac{1}{n+k} + \sum_{k=0}^{2n} \frac{1}{2n+2k+1}.
$$
-/
theorem ramanujan_part1_ch2_entry5_general (n : ℕ) :
    (1 : ℝ) + 2 * ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((6 * (k : ℝ)) ^ 3 - 6 * (k : ℝ)) =
      (2 : ℝ) / 3 * ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((n : ℝ) + (k : ℝ)) +
        ∑ k ∈ Finset.Icc 0 (2 * n), (1 : ℝ) / (2 * (n : ℝ) + 2 * (k : ℝ) + 1) := by
  have hall : ∀ m : ℕ,
      (1 : ℝ) + 2 * ∑ k ∈ Finset.Icc 1 m, (1 : ℝ) / ((6 * (k : ℝ)) ^ 3 - 6 * (k : ℝ)) =
        (2 : ℝ) / 3 * ∑ k ∈ Finset.Icc 1 m, (1 : ℝ) / ((m : ℝ) + (k : ℝ)) +
          ∑ k ∈ Finset.Icc 0 (2 * m), (1 : ℝ) / (2 * (m : ℝ) + 2 * (k : ℝ) + 1) := by
    intro m
    induction m with
    | zero =>
      have z1 : Finset.Icc 1 (0 : ℕ) = ∅ := by decide
      have z2 : 2 * (0 : ℕ) = 0 := by ring
      rw [z1, z2]
      simp
    | succ m ih =>
      have hL : ∑ k ∈ Finset.Icc 1 (m + 1),
          ((1 : ℝ) / ((6 * (k : ℝ)) ^ 3 - 6 * (k : ℝ))) =
          (∑ k ∈ Finset.Icc 1 m, (1 : ℝ) / ((6 * (k : ℝ)) ^ 3 - 6 * (k : ℝ))) +
          (1 : ℝ) / ((6 * ((((m + 1 : ℕ))) : ℝ)) ^ 3 - 6 * ((((m + 1 : ℕ))) : ℝ)) :=
        Finset.sum_Icc_succ_top (by omega) _
      rw [hL, S2_step m, S3_step m]
      have key := step_identity m
      linear_combination ih + key
  exact hall n


set_option linter.unusedVariables false in
/-- **Ramanujan's sum identity for $1/((6k)^3 - 6k)$.** For every positive integer $n$,
$$
1 + 2 \sum_{k=1}^{n} \frac{1}{(6k)^3 - 6k} =
\frac{2}{3} \sum_{k=1}^{n} \frac{1}{n+k} + \sum_{k=0}^{2n} \frac{1}{2n+2k+1}.
$$

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I (Springer, 1985), Chapter 2, Entry
    5, formula (5.1), printed p. 29 / PDF p. 39.
Proves `Wanted` entry `ramanujan_part1_ch2_entry5`.
-/
theorem ramanujan_part1_ch2_entry5 (n : ℕ) (hn : 0 < n) :
    (1 : ℝ) + 2 * ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((6 * (k : ℝ)) ^ 3 - 6 * (k : ℝ)) =
      (2 : ℝ) / 3 * ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((n : ℝ) + (k : ℝ)) +
        ∑ k ∈ Finset.Icc 0 (2 * n), (1 : ℝ) / (2 * (n : ℝ) + 2 * (k : ℝ) + 1) :=
  ramanujan_part1_ch2_entry5_general ..

end Entry5

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2
