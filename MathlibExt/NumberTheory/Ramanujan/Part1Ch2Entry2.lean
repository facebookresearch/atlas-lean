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
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 2, Entry 2

Sum of 1/(n+k) over k ≤ 2n+1 via reciprocals of 27k³-3k.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2

namespace Entry2

private lemma entry2_shift_sum (M : ℕ) (f : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 M, f (k + 1) = ∑ j ∈ Finset.Icc 2 (M + 1), f j := by
  by_cases hM : M = 0
  · subst hM; simp
  · have h1 : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr hM
    apply Finset.sum_bij (fun k _ => k + 1)
    · intro k hk
      simp only [Finset.mem_Icc] at hk ⊢
      omega
    · intro a ha1 b ha2 hab
      exact Nat.add_right_cancel hab
    · intro b hb
      simp only [Finset.mem_Icc] at hb
      refine ⟨b - 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro k hk
      rfl

private lemma entry2_peel_head (M : ℕ) (g : ℕ → ℝ) :
    ∑ j ∈ Finset.Icc 1 (M + 1), g j = g 1 + ∑ j ∈ Finset.Icc 2 (M + 1), g j := by
  have hmem : (1 : ℕ) ∈ Finset.Icc 1 (M + 1) := by
    simp only [Finset.mem_Icc]
    omega
  have herase : (Finset.Icc 1 (M + 1)).erase 1 = Finset.Icc 2 (M + 1) := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_Icc]
    omega
  have h := Finset.add_sum_erase (Finset.Icc 1 (M + 1)) g hmem
  rw [herase] at h
  linarith

private lemma entry2_partial_frac (x : ℝ) (hx0 : x ≠ 0) (hx1 : 3 * x - 1 ≠ 0)
    (hx2 : 3 * x + 1 ≠ 0) :
    2 / ((3 * x) ^ 3 - 3 * x)
      = 1 / (3 * x - 1) + 1 / (3 * x) + 1 / (3 * x + 1) - 1 / x := by
  have h3x : (3 : ℝ) * x ≠ 0 := mul_ne_zero (by norm_num) hx0
  have hfac : (3 * x) ^ 3 - 3 * x = 3 * x * (3 * x - 1) * (3 * x + 1) := by ring
  rw [hfac]
  field_simp
  ring

private lemma entry2_aux_all : ∀ n : ℕ,
    (∑ k ∈ Finset.Icc 1 (2 * n + 1), (1 : ℝ) / ((n : ℝ) + (k : ℝ))) =
    1 + 2 * ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((3 * (k : ℝ)) ^ 3 - 3 * (k : ℝ)) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hRHS : (∑ k ∈ Finset.Icc 1 (n + 1), (1 : ℝ) / ((3 * (k : ℝ)) ^ 3 - 3 * (k : ℝ)))
        = (∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((3 * (k : ℝ)) ^ 3 - 3 * (k : ℝ)))
          + (1 : ℝ) / ((3 * ((n : ℝ) + 1)) ^ 3 - 3 * ((n : ℝ) + 1)) := by
      have h := Finset.sum_Icc_succ_top (show 1 ≤ n + 1 from by omega)
        (fun k => (1 : ℝ) / ((3 * (k : ℝ)) ^ 3 - 3 * (k : ℝ)))
      simpa using h
    have hcast_n : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    have hLHS2 : (∑ k ∈ Finset.Icc 1 (2 * (n + 1) + 1), (1 : ℝ) / ((((n + 1 : ℕ)) : ℝ) + (k : ℝ)))
        = (∑ k ∈ Finset.Icc 1 (2 * n + 1), (1 : ℝ) / ((((n + 1 : ℕ)) : ℝ) + (k : ℝ)))
          + (1 : ℝ) / ((((n + 1 : ℕ)) : ℝ) + (((2 * n + 2 : ℕ)) : ℝ))
          + (1 : ℝ) / ((((n + 1 : ℕ)) : ℝ) + (((2 * n + 3 : ℕ)) : ℝ)) := by
      set g : ℕ → ℝ := fun k => (1 : ℝ) / ((((n + 1 : ℕ)) : ℝ) + (k : ℝ)) with hg
      have h1 : ∑ k ∈ Finset.Icc 1 (2 * n + 3), g k
          = ∑ k ∈ Finset.Icc 1 (2 * n + 2), g k + g (2 * n + 3) := by
        have h := Finset.sum_Icc_succ_top (show 1 ≤ (2 * n + 2) + 1 from by omega) g
        rwa [show (2 * n + 2) + 1 = 2 * n + 3 from by omega] at h
      have h2 : ∑ k ∈ Finset.Icc 1 (2 * n + 2), g k
          = ∑ k ∈ Finset.Icc 1 (2 * n + 1), g k + g (2 * n + 2) := by
        have h := Finset.sum_Icc_succ_top (show 1 ≤ (2 * n + 1) + 1 from by omega) g
        rwa [show (2 * n + 1) + 1 = 2 * n + 2 from by omega] at h
      have e0 : 2 * (n + 1) + 1 = 2 * n + 3 := by omega
      rw [e0, h1, h2]
    rw [hLHS2]
    have hshift : (∑ k ∈ Finset.Icc 1 (2 * n + 1), (1 : ℝ) / ((((n + 1 : ℕ)) : ℝ) + (k : ℝ)))
        = ∑ j ∈ Finset.Icc 2 ((2 * n + 1) + 1), (1 : ℝ) / ((n : ℝ) + (j : ℝ)) := by
      have heq : (∑ k ∈ Finset.Icc 1 (2 * n + 1), (1 : ℝ) / ((((n + 1 : ℕ)) : ℝ) + (k : ℝ)))
          = ∑ k ∈ Finset.Icc 1 (2 * n + 1), (fun j : ℕ => (1 : ℝ) / ((n : ℝ) + ((j : ℕ) : ℝ))) (k + 1) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk1 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
        rw [hcast_n]
        congr 1
        push_cast
        ring
      rw [heq]
      exact entry2_shift_sum (2 * n + 1) (fun j : ℕ => (1 : ℝ) / ((n : ℝ) + ((j : ℕ) : ℝ)))
    rw [hshift]
    have hcomb : (∑ j ∈ Finset.Icc 2 ((2 * n + 1) + 1), (1 : ℝ) / ((n : ℝ) + (j : ℝ)))
        = (∑ k ∈ Finset.Icc 1 (2 * n + 1), (1 : ℝ) / ((n : ℝ) + (k : ℝ)))
          - (1 : ℝ) / ((n : ℝ) + 1) + (1 : ℝ) / ((n : ℝ) + (((2 * n + 2 : ℕ)) : ℝ)) := by
      have htop := Finset.sum_Icc_succ_top (show 1 ≤ ((2 * n + 1)) + 1 from by omega)
        (fun j => (1 : ℝ) / ((n : ℝ) + (j : ℝ)))
      have hhead := entry2_peel_head (2 * n + 1) (fun j => (1 : ℝ) / ((n : ℝ) + (j : ℝ)))
      have e : (2 * n + 1) + 1 = 2 * n + 2 := by omega
      rw [e] at htop hhead ⊢
      have g1 : (1 : ℝ) / ((n : ℝ) + ((1 : ℕ) : ℝ)) = (1 : ℝ) / ((n : ℝ) + 1) := by norm_num
      rw [g1] at hhead
      linarith [htop, hhead]
    rw [hcomb]
    rw [hRHS]
    have hnR : ((n : ℝ) + 1) ≠ 0 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hpf := entry2_partial_frac ((n : ℝ) + 1) hnR
      (by have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)
      (by have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)
    have b1 : (n : ℝ) + (((2 * n + 2 : ℕ)) : ℝ) = 3 * ((n : ℝ) + 1) - 1 := by push_cast; ring
    have b2 : (((n + 1 : ℕ)) : ℝ) + (((2 * n + 2 : ℕ)) : ℝ) = 3 * ((n : ℝ) + 1) := by push_cast; ring
    have b3 : (((n + 1 : ℕ)) : ℝ) + (((2 * n + 3 : ℕ)) : ℝ) = 3 * ((n : ℝ) + 1) + 1 := by push_cast; ring
    rw [b1, b2, b3]
    linear_combination ih - hpf

/-- **Ramanujan's identity for $\sum_{k=1}^{2n+1} 1/(n+k)$, including $n = 0$.** For every
natural number $n$,
$$\sum_{k=1}^{2n+1} \frac{1}{n+k} = 1 + 2 \sum_{k=1}^{n} \frac{1}{(3k)^3 - 3k}.$$

This is Ramanujan's Entry 2 of Chapter 2 without the hypothesis $n \ge 1$; at $n = 0$ both sides
are $1$. -/
theorem ramanujan_part1_ch2_entry2_general (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 (2 * n + 1), (1 : ℝ) / ((n : ℝ) + (k : ℝ))) =
    1 + 2 * ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((3 * (k : ℝ)) ^ 3 - 3 * (k : ℝ)) := by
  exact entry2_aux_all n

set_option linter.unusedVariables false in
/-- **Ramanujan's identity for $\sum_{k=1}^{2n+1} 1/(n+k)$.** For every positive integer $n$,
$$\sum_{k=1}^{2n+1} \frac{1}{n+k} = 1 + 2 \sum_{k=1}^{n} \frac{1}{(3k)^3 - 3k}.$$

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I (Springer, 1985), Chapter 2, Entry
    2, formula (2.1), printed p. 27 / PDF p. 37.
Proves `Wanted` entry `ramanujan_part1_ch2_entry2`.
-/
theorem ramanujan_part1_ch2_entry2 (n : ℕ) (hn : 0 < n) :
    (∑ k ∈ Finset.Icc 1 (2 * n + 1), (1 : ℝ) / ((n : ℝ) + (k : ℝ))) =
    1 + 2 * ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / ((3 * (k : ℝ)) ^ 3 - 3 * (k : ℝ)) :=
  ramanujan_part1_ch2_entry2_general ..

end Entry2

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2
