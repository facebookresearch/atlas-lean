/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open scoped Real
open MeasureTheory

namespace StatMech.Onsager






theorem ons_riemann_periodic (f : ℝ → ℝ) (hf : Continuous f)
    (hper : Function.Periodic f (2 * Real.pi)) :
    Filter.Tendsto (fun n : ℕ => (2 * Real.pi / n) * ∑ k ∈ Finset.range n, f (2 * Real.pi * k / n))
      Filter.atTop (nhds (∫ x in (0)..(2 * Real.pi), f x)) := by
  set T : ℝ := 2 * Real.pi with hT
  have hTpos : (0 : ℝ) < T := by rw [hT]; linarith [Real.pi_pos]
  
  have hucon : UniformContinuousOn f (Set.Icc (0 : ℝ) T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf.continuousOn
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h2T : (0 : ℝ) < 2 * T := by linarith
  set ε' : ℝ := ε / (2 * T) with hε'
  have hε'pos : 0 < ε' := div_pos hε h2T
  obtain ⟨δ, hδpos, hδ⟩ := (Metric.uniformContinuousOn_iff.mp hucon) ε' hε'pos
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (T / δ)
  refine ⟨max N₀ 1, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnN0 : N₀ ≤ n := le_trans (le_max_left _ _) hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hn0R : (n : ℝ) ≠ 0 := ne_of_gt hnR
  
  set a : ℕ → ℝ := fun k => T * (k : ℝ) / (n : ℝ) with ha
  have hpos : (0 : ℝ) < T / n := div_pos hTpos hnR
  have hTn : T / n < δ := by
    rw [div_lt_iff₀ hnR]
    have hlt : T / δ < (n : ℝ) := lt_of_lt_of_le hN₀ (by exact_mod_cast hnN0)
    rw [div_lt_iff₀ hδpos] at hlt
    linarith
  have hdiff : ∀ k, a (k + 1) - a k = T / n := by
    intro k
    simp only [ha]
    push_cast
    field_simp
    ring
  have ha0 : a 0 = 0 := by simp [ha]
  have han : a n = T := by
    simp only [ha]
    rw [mul_div_assoc, div_self hn0R, mul_one]
  
  have hsplit : (∫ x in (0 : ℝ)..T, f x) = ∑ k ∈ Finset.range n, ∫ x in a k..a (k + 1), f x := by
    have h := intervalIntegral.sum_integral_adjacent_intervals (f := f) (n := n) (a := a)
      (μ := volume) (fun k _ => hf.intervalIntegrable (a k) (a (k + 1)))
    rw [ha0, han] at h
    exact h.symm
  
  have hdiffeq : (∫ x in (0 : ℝ)..T, f x) - (T / n) * ∑ k ∈ Finset.range n, f (a k)
      = ∑ k ∈ Finset.range n, ∫ x in a k..a (k + 1), (f x - f (a k)) := by
    rw [hsplit, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _) intervalIntegrable_const,
        intervalIntegral.integral_const, hdiff k, smul_eq_mul]
  
  have hbound : ∀ k ∈ Finset.range n,
      |∫ x in a k..a (k + 1), (f x - f (a k))| ≤ ε' * (T / n) := by
    intro k hk
    have hkn : k < n := Finset.mem_range.mp hk
    have hlek : a k ≤ a (k + 1) := by have h1 := hdiff k; linarith
    have hak0 : 0 ≤ a k := by
      simp only [ha]
      exact div_nonneg (mul_nonneg hTpos.le (Nat.cast_nonneg k)) (Nat.cast_nonneg n)
    have hakT : a k ≤ T := by
      simp only [ha]
      rw [div_le_iff₀ hnR]
      have hkc : (k : ℝ) ≤ n := by exact_mod_cast hkn.le
      nlinarith [hTpos, hkc]
    have hak1T : a (k + 1) ≤ T := by
      have hk1 : k + 1 ≤ n := hkn
      simp only [ha]
      rw [div_le_iff₀ hnR]
      push_cast
      have hkc : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk1
      nlinarith [hTpos, hkc]
    have hmemk : a k ∈ Set.Icc (0 : ℝ) T := ⟨hak0, hakT⟩
    have hmain : ‖∫ x in a k..a (k + 1), (f x - f (a k))‖ ≤ ε' * |a (k + 1) - a k| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [Set.uIoc_of_le hlek] at hx
      have hxk : a k < x := hx.1
      have hxk1 : x ≤ a (k + 1) := hx.2
      have hxmem : x ∈ Set.Icc (0 : ℝ) T :=
        ⟨le_of_lt (lt_of_le_of_lt hak0 hxk), le_trans hxk1 hak1T⟩
      have hdistlt : dist x (a k) < δ := by
        rw [Real.dist_eq, abs_of_pos (by linarith)]
        have h1 := hdiff k
        linarith [hTn]
      have hcl := hδ x hxmem (a k) hmemk hdistlt
      rw [Real.norm_eq_abs, ← Real.dist_eq]
      exact le_of_lt hcl
    rw [Real.norm_eq_abs, hdiff k, abs_of_pos hpos] at hmain
    exact hmain
  
  have key : |(∫ x in (0 : ℝ)..T, f x) - (T / n) * ∑ k ∈ Finset.range n, f (a k)| ≤ ε' * T := by
    calc |(∫ x in (0 : ℝ)..T, f x) - (T / n) * ∑ k ∈ Finset.range n, f (a k)|
        = |∑ k ∈ Finset.range n, ∫ x in a k..a (k + 1), (f x - f (a k))| := by rw [hdiffeq]
      _ ≤ ∑ k ∈ Finset.range n, |∫ x in a k..a (k + 1), (f x - f (a k))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range n, ε' * (T / n) := Finset.sum_le_sum hbound
      _ = ε' * T := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm (n : ℝ),
            mul_assoc, div_mul_cancel₀ T hn0R]
  have hεT : ε' * T = ε / 2 := by
    rw [hε']
    field_simp
  change dist ((T / (n : ℝ)) * ∑ k ∈ Finset.range n, f (a k)) (∫ x in (0 : ℝ)..T, f x) < ε
  rw [Real.dist_eq, abs_sub_comm]
  linarith [key, hεT]

end StatMech.Onsager
