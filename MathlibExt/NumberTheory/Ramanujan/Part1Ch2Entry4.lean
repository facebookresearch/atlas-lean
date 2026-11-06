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
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 2, Entry 4

Sum of 1/(n+k) plus 1/(2n+2k+1) equals 1 plus reciprocals of 64k³-4k.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2

namespace Entry4

private lemma S1_reindex (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((n : ℝ) + (k : ℝ))) =
    ∑ j ∈ Finset.Icc (n + 1) (2 * n), (1 : ℝ) / (j : ℝ) := by
  have himg : Finset.image (fun x => n + x) (Finset.Icc 1 n) = Finset.Icc (n + 1) (2 * n) := by
    have h : n + n = 2 * n := by ring
    rw [Finset.image_add_left_Icc, h]
  have hinj : Function.Injective (fun x => n + x) := by
    intro a b h
    dsimp at h
    omega
  rw [← himg, Finset.sum_image hinj.injOn]
  apply Finset.sum_congr rfl
  intro k hk
  push_cast
  ring_nf

private lemma S2_reindex (n : ℕ) :
    (∑ k ∈ Finset.Icc 0 n, (1 : ℝ) / (2 * (n : ℝ) + 2 * (k : ℝ) + 1)) =
    ∑ j ∈ Finset.Icc n (2 * n), (1 : ℝ) / (2 * (j : ℝ) + 1) := by
  have himg : Finset.image (fun x => n + x) (Finset.Icc 0 n) = Finset.Icc n (2 * n) := by
    have h1 : n + 0 = n := by ring
    have h2 : n + n = 2 * n := by ring
    rw [Finset.image_add_left_Icc, h1, h2]
  have hinj : Function.Injective (fun x => n + x) := by
    intro a b h
    dsimp at h
    omega
  rw [← himg, Finset.sum_image hinj.injOn]
  apply Finset.sum_congr rfl
  intro k hk
  push_cast
  ring_nf

private lemma S1_step (n : ℕ) :
    (∑ j ∈ Finset.Icc (n + 2) (2 * (n + 1)), (1 : ℝ) / (j : ℝ)) -
    (∑ j ∈ Finset.Icc (n + 1) (2 * n), (1 : ℝ) / (j : ℝ)) =
    1 / (2 * (n : ℝ) + 1) + 1 / (2 * (n : ℝ) + 2) - 1 / ((n : ℝ) + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp
  · have h1 : n + 2 ≤ 2 * n + 1 + 1 := by omega
    have h2 : n + 2 ≤ 2 * n + 1 := by omega
    have h3 : n + 1 ≤ 2 * n := by omega
    have htop1 : ∑ j ∈ Finset.Icc (n + 2) (2 * (n + 1)), (1 : ℝ) / (j : ℝ)
        = (∑ j ∈ Finset.Icc (n + 2) (2 * n + 1), (1 : ℝ) / (j : ℝ))
          + 1 / ((2 * (n + 1) : ℕ) : ℝ) := by
      have h : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
      rw [h]
      exact Finset.sum_Icc_succ_top h1 _
    have htop2 : ∑ j ∈ Finset.Icc (n + 2) (2 * n + 1), (1 : ℝ) / (j : ℝ)
        = (∑ j ∈ Finset.Icc (n + 2) (2 * n), (1 : ℝ) / (j : ℝ)) + 1 / ((2 * n + 1 : ℕ) : ℝ) := by
      have h : 2 * n + 1 = (2 * n) + 1 := by omega
      rw [h]
      exact Finset.sum_Icc_succ_top h2 _
    have hbot : ∑ j ∈ Finset.Icc (n + 1) (2 * n), (1 : ℝ) / (j : ℝ)
        = 1 / (((n + 1 : ℕ)) : ℝ) + ∑ j ∈ Finset.Icc (n + 2) (2 * n), (1 : ℝ) / (j : ℝ) := by
      have hIcc : Finset.Icc (n + 1) (2 * n) = insert (n + 1) (Finset.Icc (n + 2) (2 * n)) := by
        have h : n + 1 + 1 = n + 2 := by omega
        rw [← h]
        exact (Finset.insert_Icc_add_one_left_eq_Icc h3).symm
      rw [hIcc, Finset.sum_insert (by simp)]
    rw [htop1, htop2, hbot]
    push_cast
    ring

private lemma S2_step (n : ℕ) :
    (∑ j ∈ Finset.Icc (n + 1) (2 * (n + 1)), (1 : ℝ) / (2 * (j : ℝ) + 1)) -
    (∑ j ∈ Finset.Icc n (2 * n), (1 : ℝ) / (2 * (j : ℝ) + 1)) =
    1 / (4 * (n : ℝ) + 3) + 1 / (4 * (n : ℝ) + 5) - 1 / (2 * (n : ℝ) + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · have e1 : Finset.Icc (0 + 1) (2 * (0 + 1)) = ({1, 2} : Finset ℕ) := by decide
    have e2 : Finset.Icc (0 : ℕ) (2 * 0) = ({0} : Finset ℕ) := by decide
    rw [e1, e2]
    norm_num
  · have h1 : n + 1 ≤ 2 * n + 1 + 1 := by omega
    have h2 : n + 1 ≤ 2 * n + 1 := by omega
    have h3 : n ≤ 2 * n := by omega
    have htop1 : ∑ j ∈ Finset.Icc (n + 1) (2 * (n + 1)), (1 : ℝ) / (2 * (j : ℝ) + 1)
        = (∑ j ∈ Finset.Icc (n + 1) (2 * n + 1), (1 : ℝ) / (2 * (j : ℝ) + 1))
          + 1 / (2 * ((2 * (n + 1) : ℕ) : ℝ) + 1) := by
      have h : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
      rw [h]
      exact Finset.sum_Icc_succ_top h1 _
    have htop2 : ∑ j ∈ Finset.Icc (n + 1) (2 * n + 1), (1 : ℝ) / (2 * (j : ℝ) + 1)
        = (∑ j ∈ Finset.Icc (n + 1) (2 * n), (1 : ℝ) / (2 * (j : ℝ) + 1))
          + 1 / (2 * ((2 * n + 1 : ℕ) : ℝ) + 1) := by
      have h : 2 * n + 1 = (2 * n) + 1 := by omega
      rw [h]
      exact Finset.sum_Icc_succ_top h2 _
    have hbot : ∑ j ∈ Finset.Icc n (2 * n), (1 : ℝ) / (2 * (j : ℝ) + 1)
        = 1 / (2 * ((n : ℕ) : ℝ) + 1)
          + ∑ j ∈ Finset.Icc (n + 1) (2 * n), (1 : ℝ) / (2 * (j : ℝ) + 1) := by
      have hIcc : Finset.Icc n (2 * n) = insert n (Finset.Icc (n + 1) (2 * n)) := by
        exact (Finset.insert_Icc_add_one_left_eq_Icc h3).symm
      rw [hIcc, Finset.sum_insert (by simp)]
    rw [htop1, htop2, hbot]
    push_cast
    ring

private lemma key_id (n : ℕ) :
    (1 / (2 * (n : ℝ) + 1) + 1 / (2 * (n : ℝ) + 2) - 1 / ((n : ℝ) + 1) +
    (1 / (4 * (n : ℝ) + 3) + 1 / (4 * (n : ℝ) + 5) - 1 / (2 * (n : ℝ) + 1))) =
    2 / ((4 * ((n : ℝ) + 1)) ^ 3 - 4 * ((n : ℝ) + 1)) := by
  have h2 : (2 : ℝ) * (n : ℝ) + 2 ≠ 0 := by positivity
  have h3 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h4 : (4 : ℝ) * (n : ℝ) + 3 ≠ 0 := by positivity
  have h5 : (4 : ℝ) * (n : ℝ) + 5 ≠ 0 := by positivity
  have h41 : (4 : ℝ) * ((n : ℝ) + 1) ≠ 0 := by positivity
  have h_factor : (4 * ((n : ℝ) + 1)) ^ 3 - 4 * ((n : ℝ) + 1)
      = 4 * ((n : ℝ) + 1) * (4 * (n : ℝ) + 3) * (4 * (n : ℝ) + 5) := by ring
  rw [h_factor]
  field_simp
  ring

/-- **Ramanujan's sum identity for $1/((4k)^3 - 4k)$, including $n = 0$.** For every natural
number $n$,
$$
\sum_{k=1}^{n} \frac{1}{n+k} + \sum_{k=0}^{n} \frac{1}{2n+2k+1} =
1 + 2 \sum_{k=1}^{n} \frac{1}{(4k)^3 - 4k}.
$$
At $n = 0$ both sides equal $1$. -/
theorem ramanujan_part1_ch2_entry4_general (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((n : ℝ) + (k : ℝ))) + (∑ k ∈ Finset.Icc 0 n, (1 : ℝ) /
        (2 * (n : ℝ) + 2 * (k : ℝ) + 1)) =
        1 + 2 * (∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((4 * (k : ℝ)) ^ 3 - 4 * (k : ℝ))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hL1n := S1_reindex n
    have hL1s := S1_reindex (n + 1)
    have hL2n := S2_reindex n
    have hL2s := S2_reindex (n + 1)
    have st1 := S1_step n
    have st2 := S2_step n
    have kk := key_id n
    have hrhs : (∑ k ∈ Finset.Icc 1 (n + 1), (1 : ℝ) / ((4 * (k : ℝ)) ^ 3 - 4 * (k : ℝ)))
        = (∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((4 * (k : ℝ)) ^ 3 - 4 * (k : ℝ)))
          + 1 / ((4 * ((n : ℝ) + 1)) ^ 3 - 4 * ((n : ℝ) + 1)) := by
      have h := Finset.sum_Icc_succ_top (show (1 : ℕ) ≤ n + 1 by omega)
        (fun k => (1 : ℝ) / ((4 * (k : ℝ)) ^ 3 - 4 * (k : ℝ)))
      rw [h]
      congr 1
      push_cast
      ring_nf
    have e1 : n + 1 + 1 = n + 2 := by omega
    rw [e1] at hL1s
    linear_combination ih + hL1s - hL1n + hL2s - hL2n + st1 + st2 + kk - 2 * hrhs

set_option linter.unusedVariables false in
/-- **Ramanujan's sum identity for $1/((4k)^3 - 4k)$.** For every positive integer $n$,
$$
\sum_{k=1}^{n} \frac{1}{n+k} + \sum_{k=0}^{n} \frac{1}{2n+2k+1} =
1 + 2 \sum_{k=1}^{n} \frac{1}{(4k)^3 - 4k}.
$$

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I (Springer, 1985), Chapter 2, Entry
    4, formula (4.1), printed p. 28 / PDF p. 38.
It follows from `ramanujan_part1_ch2_entry4_general`, which extends it to `n = 0`; the
hypothesis `hn` is unused and keeps the source's shape.
Proves `Wanted` entry `ramanujan_part1_ch2_entry4`.
-/
theorem ramanujan_part1_ch2_entry4 (n : ℕ) (hn : 0 < n) :
    (∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((n : ℝ) + (k : ℝ))) + (∑ k ∈ Finset.Icc 0 n, (1 : ℝ) /
        (2 * (n : ℝ) + 2 * (k : ℝ) + 1)) =
        1 + 2 * (∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((4 * (k : ℝ)) ^ 3 - 4 * (k : ℝ))) := by
  exact ramanujan_part1_ch2_entry4_general n

end Entry4

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2
