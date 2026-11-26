/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Data.Int.ModEq
public import MathlibExt.NumberTheory.DoublyExponentialReciprocalSum
public import MathlibExt.NumberTheory.GeneralizedSylvester
public import MathlibExt.NumberTheory.MillinSeries
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Tactic.Linarith
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.OrderClosed

/-!
# Recovering a doubly exponential sequence from its reciprocal sum

This module proves that a doubly exponential sequence of positive integers can be
recovered from its reciprocal sum by rounding. The main theorem is
`MetaMathlibExt.eq_round_inv_remainder_add`.

Statements from Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly
Exponential Sequences*, INTEGERS 26 (2026), Article A28 (arXiv:2504.05933). Sequences are
indexed from `0` (the paper's `a₁` is `a 0`), the nearest-integer function
`⌊x⌉ = ⌊x + 1/2⌋` is written out, and "for `n ≫ 0`" is `∀ᶠ n in atTop`.
-/

open Filter Topology

namespace MetaMathlibExt

@[expose] public section

private theorem pos_real {a : ℕ → ℕ} (hpos : ∀ n, 0 < a n) (n : ℕ) : 0 < (a n : ℝ) := by
  exact_mod_cast hpos n

private theorem b_pos {β : ℝ} (hβ : 0 ≤ β) : 0 < β + 1 / 3 := by
  linarith

private theorem ratio_le {β : ℝ} {a : ℕ → ℕ}
    (hratio : ∀ n, |(a n : ℝ) ^ 2 / a (n + 1) - β| ≤ 1 / 3) (n : ℕ) :
    (a n : ℝ) ^ 2 / a (n + 1) ≤ β + 1 / 3 := by
  have h := (abs_le.mp (hratio n)).2
  linarith

private theorem growth_sq {β : ℝ} {a : ℕ → ℕ} (hpos : ∀ n, 0 < a n)
    (hratio : ∀ n, |(a n : ℝ) ^ 2 / a (n + 1) - β| ≤ 1 / 3) (n : ℕ) :
    (a n : ℝ) ^ 2 ≤ (β + 1 / 3) * a (n + 1) := by
  have hnext : 0 < (a (n + 1) : ℝ) := pos_real hpos (n + 1)
  have hle := ratio_le hratio n
  rwa [div_le_iff₀ hnext] at hle

private theorem geom_step {β : ℝ} {a : ℕ → ℕ} (hβ : 0 ≤ β) (hpos : ∀ n, 0 < a n)
    (hratio : ∀ n, |(a n : ℝ) ^ 2 / a (n + 1) - β| ≤ 1 / 3)
    {n m : ℕ} (hlarge : 8 * (β + 1 / 3) ^ 2 ≤ (a n : ℝ))
    (hle : (a n : ℝ) ≤ (a m : ℝ)) : (8 / 3 : ℝ) * (a m : ℝ) ≤ (a (m + 1) : ℝ) := by
  have hB := b_pos hβ
  have hBm : (1 / 3 : ℝ) ≤ β + 1 / 3 := by linarith
  have ham : 0 < (a m : ℝ) := pos_real hpos m
  have hsq := growth_sq hpos hratio m
  have hBB : (8 / 3 : ℝ) * (β + 1 / 3) ≤ 8 * (β + 1 / 3) ^ 2 := by
    nlinarith [hB, hBm, sq_nonneg (β + 1 / 3)]
  have hAm : (8 / 3 : ℝ) * (β + 1 / 3) ≤ (a m : ℝ) := le_trans hBB (le_trans hlarge hle)
  have h5 : ((8 / 3 : ℝ) * (β + 1 / 3)) * (a m : ℝ) ≤ (a m : ℝ) * (a m : ℝ) :=
    mul_le_mul_of_nonneg_right hAm ham.le
  have h4 : (8 / 3 : ℝ) * (a m : ℝ) * (β + 1 / 3) ≤ (a m : ℝ) ^ 2 := by
    calc (8 / 3 : ℝ) * (a m : ℝ) * (β + 1 / 3)
        = ((8 / 3 : ℝ) * (β + 1 / 3)) * (a m : ℝ) := by ring
      _ ≤ (a m : ℝ) * (a m : ℝ) := h5
      _ = (a m : ℝ) ^ 2 := by ring
  have h6 : (8 / 3 : ℝ) * (a m : ℝ) * (β + 1 / 3) ≤ (β + 1 / 3) * (a (m + 1) : ℝ) :=
    le_trans h4 hsq
  have h6' : (8 / 3 : ℝ) * (a m : ℝ) * (β + 1 / 3) ≤ (a (m + 1) : ℝ) * (β + 1 / 3) := by
    simpa [mul_comm] using h6
  exact le_of_mul_le_mul_right h6' hB

private theorem mono_le {β : ℝ} {a : ℕ → ℕ} (hβ : 0 ≤ β) (hpos : ∀ n, 0 < a n)
    (hratio : ∀ n, |(a n : ℝ) ^ 2 / a (n + 1) - β| ≤ 1 / 3)
    {n : ℕ} (hlarge : 8 * (β + 1 / 3) ^ 2 ≤ (a n : ℝ)) {m : ℕ} (hm : n ≤ m) :
    (a n : ℝ) ≤ (a m : ℝ) := by
  induction m, hm using Nat.le_induction with
  | base => exact le_rfl
  | succ m hm ih =>
    have hstep := geom_step hβ hpos hratio hlarge ih
    have ham : 0 < (a m : ℝ) := pos_real hpos m
    have hle2 : (a m : ℝ) ≤ (8 / 3 : ℝ) * (a m : ℝ) := by linarith
    exact le_trans ih (le_trans hle2 hstep)

private theorem geom_bound {β : ℝ} {a : ℕ → ℕ} (hβ : 0 ≤ β) (hpos : ∀ n, 0 < a n)
    (hratio : ∀ n, |(a n : ℝ) ^ 2 / a (n + 1) - β| ≤ 1 / 3)
    {n m : ℕ} (hlarge : 8 * (β + 1 / 3) ^ 2 ≤ (a n : ℝ)) (hm : n ≤ m) (j : ℕ) :
    1 / (a (m + j) : ℝ) ≤ (1 / (a m : ℝ)) * (3 / 8 : ℝ) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hmj : n ≤ m + j := le_trans hm (Nat.le_add_right m j)
    have hle : (a n : ℝ) ≤ (a (m + j) : ℝ) := mono_le hβ hpos hratio hlarge hmj
    have hstep := geom_step hβ hpos hratio hlarge hle
    have ham : 0 < (a (m + j) : ℝ) := pos_real hpos (m + j)
    have h83 : 0 < (8 / 3 : ℝ) * (a (m + j) : ℝ) := by positivity
    have hdiv : 1 / (a (m + j + 1) : ℝ) ≤ 1 / ((8 / 3 : ℝ) * (a (m + j) : ℝ)) :=
      one_div_le_one_div_of_le h83 hstep
    have heq : (1 : ℝ) / ((8 / 3 : ℝ) * (a (m + j) : ℝ)) = (3 / 8 : ℝ) * (1 / (a (m + j) : ℝ)) := by
      field_simp
    rw [Nat.add_succ]
    calc 1 / (a (m + j + 1) : ℝ)
        ≤ 1 / ((8 / 3 : ℝ) * (a (m + j) : ℝ)) := hdiv
      _ = (3 / 8 : ℝ) * (1 / (a (m + j) : ℝ)) := heq
      _ ≤ (3 / 8 : ℝ) * ((1 / (a m : ℝ)) * (3 / 8 : ℝ) ^ j) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (1 / (a m : ℝ)) * (3 / 8 : ℝ) ^ (j + 1) := by ring

private theorem tail_hasSum {r : ℝ} {a : ℕ → ℕ}
    (hsum : HasSum (fun n => 1 / (a n : ℝ)) r) (m : ℕ) :
    HasSum (fun j => 1 / (a (j + m) : ℝ)) (r - ∑ k ∈ Finset.range m, 1 / (a k : ℝ)) := by
  have h := (hasSum_nat_add_iff' m).mpr hsum
  simpa only using h

private theorem tail_bound {β r : ℝ} {a : ℕ → ℕ} (hβ : 0 ≤ β) (hpos : ∀ n, 0 < a n)
    (hratio : ∀ n, |(a n : ℝ) ^ 2 / a (n + 1) - β| ≤ 1 / 3)
    (hsum : HasSum (fun n => 1 / (a n : ℝ)) r)
    {n m : ℕ} (hlarge : 8 * (β + 1 / 3) ^ 2 ≤ (a n : ℝ)) (hm : n ≤ m) :
    (r - ∑ k ∈ Finset.range m, 1 / (a k : ℝ)) ≤ (1 / (a m : ℝ)) * (8 / 5 : ℝ) := by
  have htail := tail_hasSum hsum m
  have hgb : ∀ j : ℕ, 1 / (a (j + m) : ℝ) ≤ (1 / (a m : ℝ)) * (3 / 8 : ℝ) ^ j := by
    intro j
    rw [Nat.add_comm j m]
    exact geom_bound hβ hpos hratio hlarge hm j
  have hgeom : ∀ k : ℕ, ∑ j ∈ Finset.range k, (3 / 8 : ℝ) ^ j ≤ 8 / 5 := by
    intro k
    have hx : (0 : ℝ) ≤ 3 / 8 := by norm_num
    have hx1 : (3 / 8 : ℝ) < 1 := by norm_num
    have h := geom_sum_Ico_le_of_lt_one (x := (3 / 8 : ℝ)) (m := 0) (n := k) hx hx1
    rw [Finset.range_eq_Ico]
    calc ∑ i ∈ Finset.Ico 0 k, (3 / 8 : ℝ) ^ i ≤ (3 / 8 : ℝ) ^ (0 : ℕ) / (1 - 3 / 8) := h
      _ = 8 / 5 := by norm_num
  have hpart : ∀ k : ℕ, ∑ j ∈ Finset.range k, 1 / (a (j + m) : ℝ) ≤
      (1 / (a m : ℝ)) * (8 / 5 : ℝ) := by
    intro k
    calc ∑ j ∈ Finset.range k, 1 / (a (j + m) : ℝ)
        ≤ ∑ j ∈ Finset.range k, (1 / (a m : ℝ)) * (3 / 8 : ℝ) ^ j :=
          Finset.sum_le_sum (fun j _ => hgb j)
      _ = (1 / (a m : ℝ)) * ∑ j ∈ Finset.range k, (3 / 8 : ℝ) ^ j := by
          rw [← Finset.mul_sum]
      _ ≤ (1 / (a m : ℝ)) * (8 / 5 : ℝ) :=
          mul_le_mul_of_nonneg_left (hgeom k) (one_div_nonneg.mpr (pos_real hpos m).le)
  exact le_of_tendsto htail.tendsto_sum_nat (Filter.Eventually.of_forall hpart)

private theorem ratio_nonneg {a : ℕ → ℕ} (hpos : ∀ n, 0 < a n) (n : ℕ) :
    0 ≤ (a n : ℝ) ^ 2 / a (n + 1) := by
  exact div_nonneg (sq_nonneg _) (pos_real hpos (n + 1)).le

private theorem rem_succ {r : ℝ} {a : ℕ → ℕ} (m : ℕ) :
    (r - ∑ k ∈ Finset.range (m + 1), 1 / (a k : ℝ)) =
      (r - ∑ k ∈ Finset.range m, 1 / (a k : ℝ)) - 1 / (a m : ℝ) := by
  rw [Finset.sum_range_succ]
  ring

private theorem rem_add {r : ℝ} {a : ℕ → ℕ} (m : ℕ) :
    (r - ∑ k ∈ Finset.range m, 1 / (a k : ℝ)) =
      1 / (a m : ℝ) + (r - ∑ k ∈ Finset.range (m + 1), 1 / (a k : ℝ)) := by
  have h := rem_succ (r := r) (a := a) m
  linarith

private theorem rem_ge {r : ℝ} {a : ℕ → ℕ} (hpos : ∀ n, 0 < a n)
    (hsum : HasSum (fun n => 1 / (a n : ℝ)) r) (m : ℕ) :
    1 / (a m : ℝ) ≤ r - ∑ k ∈ Finset.range m, 1 / (a k : ℝ) := by
  have htail := tail_hasSum hsum m
  have h := le_hasSum htail 0 (fun j _ => one_div_nonneg.mpr (pos_real hpos (j + m)).le)
  simpa only [Nat.zero_add] using h

private theorem rem_pos {r : ℝ} {a : ℕ → ℕ} (hpos : ∀ n, 0 < a n)
    (hsum : HasSum (fun n => 1 / (a n : ℝ)) r) (m : ℕ) :
    0 < r - ∑ k ∈ Finset.range m, 1 / (a k : ℝ) := by
  exact (one_div_pos.mpr (pos_real hpos m)).trans_le (rem_ge hpos hsum m)

private theorem quartic {β : ℝ} {a : ℕ → ℕ} (hpos : ∀ n, 0 < a n)
    (hratio : ∀ n, |(a n : ℝ) ^ 2 / a (n + 1) - β| ≤ 1 / 3) (n : ℕ) :
    (a n : ℝ) ^ 4 ≤ (β + 1 / 3) ^ 3 * (a (n + 2) : ℝ) := by
  have h1 := growth_sq hpos hratio n
  have h2 : (a (n + 1) : ℝ) ^ 2 ≤ (β + 1 / 3) * (a (n + 2) : ℝ) :=
    growth_sq hpos hratio (n + 1)
  have h1nn : 0 ≤ (a n : ℝ) ^ 2 := sq_nonneg _
  have hsq1 : (a n : ℝ) ^ 4 ≤ ((β + 1 / 3) * (a (n + 1) : ℝ)) ^ 2 := by
    have h := pow_le_pow_left₀ h1nn h1 2
    have heq : (((a n : ℝ) ^ 2) ^ 2) = (a n : ℝ) ^ 4 := by ring
    rwa [heq] at h
  calc (a n : ℝ) ^ 4 ≤ ((β + 1 / 3) * (a (n + 1) : ℝ)) ^ 2 := hsq1
    _ = (β + 1 / 3) ^ 2 * (a (n + 1) : ℝ) ^ 2 := by ring
    _ ≤ (β + 1 / 3) ^ 2 * ((β + 1 / 3) * (a (n + 2) : ℝ)) :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = (β + 1 / 3) ^ 3 * (a (n + 2) : ℝ) := by ring

private theorem v_bound {β : ℝ} {a : ℕ → ℕ} (hpos : ∀ n, 0 < a n)
    (hratio : ∀ n, |(a n : ℝ) ^ 2 / a (n + 1) - β| ≤ 1 / 3)
    {n : ℕ} (hlarge : 8 * (β + 1 / 3) ^ 2 ≤ (a n : ℝ)) :
    ((a n : ℝ) ^ 2 / a (n + 1)) ^ 2 / (a n : ℝ) ≤ 1 / 8 := by
  have han : 0 < (a n : ℝ) := pos_real hpos n
  have hnn := ratio_nonneg hpos n
  have hle := ratio_le hratio n
  have hsq : ((a n : ℝ) ^ 2 / a (n + 1)) ^ 2 ≤ (β + 1 / 3) ^ 2 :=
    pow_le_pow_left₀ hnn hle 2
  have hdiv : ((a n : ℝ) ^ 2 / a (n + 1)) ^ 2 / (a n : ℝ) ≤ (β + 1 / 3) ^ 2 / (a n : ℝ) := by
    apply div_le_div_of_nonneg_right _ han.le
    exact hsq
  have hB2 : (β + 1 / 3) ^ 2 / (a n : ℝ) ≤ 1 / 8 := by
    rw [div_le_iff₀ han]
    linarith [hlarge]
  exact le_trans hdiv hB2

private theorem w2_bound {β r : ℝ} {a : ℕ → ℕ} (hβ : 0 ≤ β) (hpos : ∀ n, 0 < a n)
    (hratio : ∀ n, |(a n : ℝ) ^ 2 / a (n + 1) - β| ≤ 1 / 3)
    (hsum : HasSum (fun n => 1 / (a n : ℝ)) r)
    {n : ℕ} (hlarge : 8 * (β + 1 / 3) ^ 2 ≤ (a n : ℝ)) :
    (a n : ℝ) ^ 2 * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ)) ≤ 1 / 8 := by
  have hB := b_pos hβ
  have hBm : (1 / 3 : ℝ) ≤ β + 1 / 3 := by linarith
  have han : 0 < (a n : ℝ) := pos_real hpos n
  have ha2 : 0 < (a (n + 2) : ℝ) := pos_real hpos (n + 2)
  have htail : (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ)) ≤
      (1 / (a (n + 2) : ℝ)) * (8 / 5 : ℝ) :=
    tail_bound hβ hpos hratio hsum hlarge (Nat.le_add_right n 2)
  have hmul : (a n : ℝ) ^ 2 * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ)) ≤
      (a n : ℝ) ^ 2 * ((1 / (a (n + 2) : ℝ)) * (8 / 5 : ℝ)) :=
    mul_le_mul_of_nonneg_left htail (sq_nonneg _)
  have heq : (a n : ℝ) ^ 2 * ((1 / (a (n + 2) : ℝ)) * (8 / 5 : ℝ)) =
      (((a n : ℝ) ^ 2) / (a (n + 2) : ℝ)) * (8 / 5 : ℝ) := by ring
  rw [heq] at hmul
  have hdiv : ((a n : ℝ) ^ 2) / (a (n + 2) : ℝ) ≤ 5 / 64 := by
    rw [div_le_iff₀ ha2]
    have hgoal : 64 * (a n : ℝ) ^ 2 ≤ 5 * (a (n + 2) : ℝ) := by
      have hq := quartic hpos hratio n
      have hB3pos : 0 < (β + 1 / 3) ^ 3 := pow_pos hB 3
      have hB3nn : 0 ≤ (β + 1 / 3) ^ 3 := hB3pos.le
      have hcube : 64 * (β + 1 / 3) ^ 3 ≤ 5 * (a n : ℝ) ^ 2 := by
        have h83nn : 0 ≤ 8 * (β + 1 / 3) ^ 2 := by positivity
        have hpow := pow_le_pow_left₀ h83nn hlarge 2
        have heq4 : (8 * (β + 1 / 3) ^ 2) ^ 2 = 64 * (β + 1 / 3) ^ 4 := by ring
        rw [heq4] at hpow
        have h320 : (64 : ℝ) ≤ 320 * (β + 1 / 3) := by linarith [hBm]
        have h64B : 64 * (β + 1 / 3) ^ 3 ≤ (320 * (β + 1 / 3)) * (β + 1 / 3) ^ 3 :=
          mul_le_mul_of_nonneg_right h320 hB3nn
        have hB4eq : (320 * (β + 1 / 3)) * (β + 1 / 3) ^ 3 = 320 * (β + 1 / 3) ^ 4 := by ring
        rw [hB4eq] at h64B
        have h5 : 5 * (64 * (β + 1 / 3) ^ 4) ≤ 5 * (a n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hpow (by norm_num)
        calc 64 * (β + 1 / 3) ^ 3 ≤ 320 * (β + 1 / 3) ^ 4 := h64B
          _ = 5 * (64 * (β + 1 / 3) ^ 4) := by ring
          _ ≤ 5 * (a n : ℝ) ^ 2 := h5
      have h4 : 64 * (β + 1 / 3) ^ 3 * (a n : ℝ) ^ 2 ≤ 5 * (a n : ℝ) ^ 4 := by
        have h := mul_le_mul_of_nonneg_right hcube (sq_nonneg ((a n : ℝ)))
        calc 64 * (β + 1 / 3) ^ 3 * (a n : ℝ) ^ 2
            = (64 * (β + 1 / 3) ^ 3) * (a n : ℝ) ^ 2 := by ring
          _ ≤ (5 * (a n : ℝ) ^ 2) * (a n : ℝ) ^ 2 := h
          _ = 5 * (a n : ℝ) ^ 4 := by ring
      have h5 : 5 * (a n : ℝ) ^ 4 ≤ 5 * ((β + 1 / 3) ^ 3 * (a (n + 2) : ℝ)) :=
        mul_le_mul_of_nonneg_left hq (by norm_num)
      have h6 : (64 * (a n : ℝ) ^ 2) * ((β + 1 / 3) ^ 3) ≤
          (5 * (a (n + 2) : ℝ)) * ((β + 1 / 3) ^ 3) := by
        calc (64 * (a n : ℝ) ^ 2) * ((β + 1 / 3) ^ 3)
            = 64 * (β + 1 / 3) ^ 3 * (a n : ℝ) ^ 2 := by ring
          _ ≤ 5 * (a n : ℝ) ^ 4 := h4
          _ ≤ 5 * ((β + 1 / 3) ^ 3 * (a (n + 2) : ℝ)) := h5
          _ = (5 * (a (n + 2) : ℝ)) * ((β + 1 / 3) ^ 3) := by ring
      exact le_of_mul_le_mul_right h6 hB3pos
    linarith [hgoal]
  calc (a n : ℝ) ^ 2 * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ))
      ≤ (((a n : ℝ) ^ 2) / (a (n + 2) : ℝ)) * (8 / 5 : ℝ) := hmul
    _ ≤ (5 / 64) * (8 / 5) := mul_le_mul_of_nonneg_right hdiv (by norm_num)
    _ = 1 / 8 := by norm_num

private theorem approx_abs {β r : ℝ} {a : ℕ → ℕ} (hβ : 0 ≤ β) (hpos : ∀ n, 0 < a n)
    (hratio : ∀ n, |(a n : ℝ) ^ 2 / a (n + 1) - β| ≤ 1 / 3)
    (hsum : HasSum (fun n => 1 / (a n : ℝ)) r)
    {n : ℕ} (hlarge : 8 * (β + 1 / 3) ^ 2 ≤ (a n : ℝ)) :
    |(r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ + β - (a n : ℝ)| ≤ 11 / 24 := by
  have han : 0 < (a n : ℝ) := pos_real hpos n
  have ha1 : 0 < (a (n + 1) : ℝ) := pos_real hpos (n + 1)
  have hane : (a n : ℝ) ≠ 0 := ne_of_gt han
  have ha1ne : (a (n + 1) : ℝ) ≠ 0 := ne_of_gt ha1
  have hx : 0 < (r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ)) := rem_pos hpos hsum n
  have hx1 : 0 < (r - ∑ k ∈ Finset.range (n + 1), 1 / (a k : ℝ)) := rem_pos hpos hsum (n + 1)
  have hx2 : 0 < (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ)) := rem_pos hpos hsum (n + 2)
  have hadd : (r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ)) =
      1 / (a n : ℝ) + (r - ∑ k ∈ Finset.range (n + 1), 1 / (a k : ℝ)) := rem_add n
  have hadd1 : (r - ∑ k ∈ Finset.range (n + 1), 1 / (a k : ℝ)) =
      1 / (a (n + 1) : ℝ) + (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ)) :=
    rem_add (n + 1)
  have hc : (a n : ℝ) ^ 2 / (a (n + 1) : ℝ) =
      ((a n : ℝ) / (a (n + 1) : ℝ)) * (a n : ℝ) := by ring
  have hU : (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 1), 1 / (a k : ℝ)) =
      (a n : ℝ) / (a (n + 1) : ℝ) +
        (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ)) := by
    rw [hadd1]
    ring
  have hU1pos : 0 < 1 + (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 1), 1 / (a k : ℝ)) := by
    have hnn : 0 ≤ (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 1), 1 / (a k : ℝ)) :=
      mul_nonneg han.le hx1.le
    linarith
  have hU1ne : 1 + (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 1), 1 / (a k : ℝ)) ≠ 0 :=
    ne_of_gt hU1pos
  have hxn : (r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ)) =
      (1 + (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 1), 1 / (a k : ℝ))) / (a n : ℝ) := by
    rw [hadd]
    field_simp
  have hinv : (r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ =
      (a n : ℝ) / (1 + (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 1), 1 / (a k : ℝ))) := by
    rw [hxn, inv_div]
  have hstep := geom_step hβ hpos hratio hlarge (le_rfl : (a n : ℝ) ≤ (a n : ℝ))
  have hlt : (a n : ℝ) < (a (n + 1) : ℝ) := by linarith [hstep, han]
  have hv1 : (a n : ℝ) / (a (n + 1) : ℝ) < 1 := (div_lt_one ha1).mpr hlt
  have hvnn : 0 ≤ (a n : ℝ) / (a (n + 1) : ℝ) := div_nonneg han.le ha1.le
  have hwpos : 0 ≤ (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ)) :=
    mul_nonneg han.le hx2.le
  have hD : ((r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ - (a n : ℝ) +
        (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)) *
        (1 + (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 1), 1 / (a k : ℝ))) =
      (a n : ℝ) * ((a n : ℝ) / (a (n + 1) : ℝ)) ^ 2 -
        (a n : ℝ) * (1 - (a n : ℝ) / (a (n + 1) : ℝ)) *
          ((a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ))) := by
    have hD1 : ((r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ - (a n : ℝ) +
          (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)) *
          (1 + (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 1), 1 / (a k : ℝ))) =
        (a n : ℝ) - ((a n : ℝ) - (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)) *
          (1 + (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 1), 1 / (a k : ℝ))) := by
      rw [hinv]
      field_simp
      ring
    have hD2 : (a n : ℝ) - ((a n : ℝ) - (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)) *
          (1 + (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 1), 1 / (a k : ℝ))) =
        (a n : ℝ) * ((a n : ℝ) / (a (n + 1) : ℝ)) ^ 2 -
          (a n : ℝ) * (1 - (a n : ℝ) / (a (n + 1) : ℝ)) *
            ((a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ))) := by
      rw [hc, hU]
      ring
    rw [hD1]
    exact hD2
  have hanv2 : (a n : ℝ) * ((a n : ℝ) / (a (n + 1) : ℝ)) ^ 2 =
      ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ)) ^ 2 / (a n : ℝ) := by
    field_simp
  have hanv2le : (a n : ℝ) * ((a n : ℝ) / (a (n + 1) : ℝ)) ^ 2 ≤ 1 / 8 := by
    rw [hanv2]
    exact v_bound hpos hratio hlarge
  have hanw : (a n : ℝ) * ((a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ))) =
      (a n : ℝ) ^ 2 * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ)) := by ring
  have hanwle : (a n : ℝ) * ((a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ))) ≤
      1 / 8 := by
    rw [hanw]
    exact w2_bound hβ hpos hratio hsum hlarge
  have h1U : (1 : ℝ) ≤ 1 + (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 1), 1 / (a k : ℝ)) := by
    have hnn : 0 ≤ (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 1), 1 / (a k : ℝ)) :=
      mul_nonneg han.le hx1.le
    linarith
  have hupper : (r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ - (a n : ℝ) +
      (a n : ℝ) ^ 2 / (a (n + 1) : ℝ) ≤ 1 / 8 := by
    have hnn : 0 ≤ (a n : ℝ) * (1 - (a n : ℝ) / (a (n + 1) : ℝ)) *
        ((a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ))) := by
      have h1 : 0 ≤ 1 - (a n : ℝ) / (a (n + 1) : ℝ) := by linarith [hv1]
      have h2 : 0 ≤ (a n : ℝ) * (1 - (a n : ℝ) / (a (n + 1) : ℝ)) :=
        mul_nonneg han.le h1
      exact mul_nonneg h2 hwpos
    have hDle : ((r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ - (a n : ℝ) +
          (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)) *
          (1 + (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 1), 1 / (a k : ℝ))) ≤
        (a n : ℝ) * ((a n : ℝ) / (a (n + 1) : ℝ)) ^ 2 := by
      linarith [hD, hnn]
    have hD18 : ((r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ - (a n : ℝ) +
          (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)) *
          (1 + (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 1), 1 / (a k : ℝ))) ≤ 1 / 8 :=
      le_trans hDle hanv2le
    by_cases hD0 : (r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ - (a n : ℝ) +
        (a n : ℝ) ^ 2 / (a (n + 1) : ℝ) ≤ 0
    · linarith
    · push Not at hD0
      calc (r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ - (a n : ℝ) +
              (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)
            = ((r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ - (a n : ℝ) +
              (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)) * 1 := by ring
        _ ≤ ((r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ - (a n : ℝ) +
              (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)) *
              (1 + (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 1), 1 / (a k : ℝ))) :=
            mul_le_mul_of_nonneg_left h1U hD0.le
        _ ≤ 1 / 8 := hD18
  have hlower : -(1 / 8 : ℝ) ≤ (r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ - (a n : ℝ) +
      (a n : ℝ) ^ 2 / (a (n + 1) : ℝ) := by
    have hanv2nn : 0 ≤ (a n : ℝ) * ((a n : ℝ) / (a (n + 1) : ℝ)) ^ 2 :=
      mul_nonneg han.le (sq_nonneg _)
    have h1v : 1 - (a n : ℝ) / (a (n + 1) : ℝ) ≤ 1 := by linarith [hvnn]
    have hanwnn : 0 ≤ (a n : ℝ) * ((a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ))) :=
      mul_nonneg han.le hwpos
    have hle : (a n : ℝ) * (1 - (a n : ℝ) / (a (n + 1) : ℝ)) *
          ((a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ))) ≤
        (a n : ℝ) * ((a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ))) := by
      have h : ((a n : ℝ) * ((a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ)))) *
          (1 - (a n : ℝ) / (a (n + 1) : ℝ)) ≤
          ((a n : ℝ) * ((a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ)))) * 1 :=
        mul_le_mul_of_nonneg_left h1v hanwnn
      calc (a n : ℝ) * (1 - (a n : ℝ) / (a (n + 1) : ℝ)) *
              ((a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ)))
            = ((a n : ℝ) * ((a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ)))) *
              (1 - (a n : ℝ) / (a (n + 1) : ℝ)) := by ring
        _ ≤ ((a n : ℝ) * ((a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ)))) * 1 := h
        _ = (a n : ℝ) * ((a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ))) := by ring
    have hDge : -((a n : ℝ) * ((a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ)))) ≤
        ((r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ - (a n : ℝ) +
          (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)) *
          (1 + (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 1), 1 / (a k : ℝ))) := by
      linarith [hD, hanv2nn, hle]
    have hD18 : -(1 / 8 : ℝ) ≤ ((r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ - (a n : ℝ) +
          (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)) *
          (1 + (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 1), 1 / (a k : ℝ))) := by
      linarith [hDge, hanwle]
    by_cases hD0 : 0 ≤ (r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ - (a n : ℝ) +
        (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)
    · linarith
    · push Not at hD0
      have hmul : ((r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ - (a n : ℝ) +
            (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)) *
            (1 + (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 1), 1 / (a k : ℝ))) ≤
          ((r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ - (a n : ℝ) +
            (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)) * 1 :=
        mul_le_mul_of_nonpos_left h1U hD0.le
      calc -(1 / 8 : ℝ) ≤ ((r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ - (a n : ℝ) +
              (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)) *
              (1 + (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 1), 1 / (a k : ℝ))) := hD18
        _ ≤ ((r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ - (a n : ℝ) +
              (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)) * 1 := hmul
        _ = (r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ - (a n : ℝ) +
            (a n : ℝ) ^ 2 / (a (n + 1) : ℝ) := by ring
  have hD0abs : |(r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ - (a n : ℝ) +
      (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)| ≤ 1 / 8 := abs_le.mpr ⟨hlower, hupper⟩
  have hβc : |β - (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)| ≤ 1 / 3 := by
    rw [abs_sub_comm]
    exact hratio n
  have hDeq : (r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ + β - (a n : ℝ) =
      ((r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ - (a n : ℝ) +
        (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)) + (β - (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)) := by
    ring
  rw [hDeq]
  calc |((r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ - (a n : ℝ) +
          (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)) + (β - (a n : ℝ) ^ 2 / (a (n + 1) : ℝ))|
        ≤ |(r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ - (a n : ℝ) +
          (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)| + |β - (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)| :=
          abs_add_le _ _
    _ ≤ 1 / 8 + 1 / 3 := by linarith [hD0abs, hβc]
    _ = 11 / 24 := by norm_num

private theorem round_eq {β r : ℝ} {a : ℕ → ℕ} (hβ : 0 ≤ β) (hpos : ∀ n, 0 < a n)
    (hratio : ∀ n, |(a n : ℝ) ^ 2 / a (n + 1) - β| ≤ 1 / 3)
    (hsum : HasSum (fun n => 1 / (a n : ℝ)) r)
    {n : ℕ} (hlarge : 8 * (β + 1 / 3) ^ 2 ≤ (a n : ℝ)) :
    (a n : ℤ) = ⌊(r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ + β + 1 / 2⌋ := by
  have habs := approx_abs hβ hpos hratio hsum hlarge
  symm
  rw [Int.floor_eq_iff]
  have hcast : (((a n : ℤ) : ℝ)) = (a n : ℝ) := by norm_cast
  rw [hcast]
  have hle := (abs_le.mp habs).1
  have hle2 := (abs_le.mp habs).2
  constructor
  · linarith
  · linarith

private theorem tendsto_a_top {r : ℝ} {a : ℕ → ℕ} (hpos : ∀ n, 0 < a n)
    (hsum : HasSum (fun n => 1 / (a n : ℝ)) r) :
    Tendsto (fun n => (a n : ℝ)) atTop atTop := by
  have h0 : Tendsto (fun n => 1 / (a n : ℝ)) atTop (𝓝 0) := hsum.summable.tendsto_atTop_zero
  rw [Filter.tendsto_atTop]
  intro b
  set K : ℝ := max b 0 + 1 with hKdef
  have hK : 0 < K := by
    have hmax : 0 ≤ max b 0 := le_max_right b 0
    linarith
  have heps : 0 < 1 / K := one_div_pos.mpr hK
  have hev := (Metric.tendsto_nhds.mp h0) (1 / K) heps
  filter_upwards [hev] with n hn
  rw [Real.dist_eq] at hn
  have han : 0 < (a n : ℝ) := pos_real hpos n
  have h1a : 0 < 1 / (a n : ℝ) := one_div_pos.mpr han
  have habs : |1 / (a n : ℝ) - 0| = 1 / (a n : ℝ) := by
    rw [sub_zero]
    exact abs_of_pos h1a
  rw [habs] at hn
  have hKa : K < (a n : ℝ) := (one_div_lt_one_div han hK).mp hn
  have hmax : b ≤ max b 0 := le_max_left b 0
  linarith

private theorem eventually_hlarge {β r : ℝ} {a : ℕ → ℕ} (hpos : ∀ n, 0 < a n)
    (hsum : HasSum (fun n => 1 / (a n : ℝ)) r) :
    ∀ᶠ n in atTop, 8 * (β + 1 / 3) ^ 2 ≤ (a n : ℝ) := by
  have htop := tendsto_a_top hpos hsum
  have hev := Filter.eventually_ge_atTop (8 * (β + 1 / 3) ^ 2)
  exact htop.eventually hev

private theorem tendsto_c_div_a {β r : ℝ} {a : ℕ → ℕ} (hpos : ∀ n, 0 < a n)
    (hratio : ∀ n, |(a n : ℝ) ^ 2 / a (n + 1) - β| ≤ 1 / 3)
    (hsum : HasSum (fun n => 1 / (a n : ℝ)) r) :
    Tendsto (fun n => (a n : ℝ) / (a (n + 1) : ℝ)) atTop (𝓝 0) := by
  have h0 : Tendsto (fun n => 1 / (a n : ℝ)) atTop (𝓝 0) := hsum.summable.tendsto_atTop_zero
  have hB : Tendsto (fun n => (β + 1 / 3) * (1 / (a n : ℝ))) atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => (β + 1 / 3)) atTop (𝓝 (β + 1 / 3)) := tendsto_const_nhds
    have h := hc.mul h0
    simpa using h
  apply squeeze_zero (fun n => div_nonneg (pos_real hpos n).le (pos_real hpos (n + 1)).le) _ hB
  intro n
  have han : 0 < (a n : ℝ) := pos_real hpos n
  have ha1 : 0 < (a (n + 1) : ℝ) := pos_real hpos (n + 1)
  have hane : (a n : ℝ) ≠ 0 := ne_of_gt han
  have ha1ne : (a (n + 1) : ℝ) ≠ 0 := ne_of_gt ha1
  have hle := ratio_le hratio n
  have heq : (a n : ℝ) / (a (n + 1) : ℝ) = ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ)) / (a n : ℝ) := by
    field_simp
  have heq2 : (β + 1 / 3) * (1 / (a n : ℝ)) = (β + 1 / 3) / (a n : ℝ) := by ring
  rw [heq, heq2]
  exact div_le_div_of_nonneg_right hle han.le

private theorem tendsto_c_sq_div_a {β r : ℝ} {a : ℕ → ℕ} (hpos : ∀ n, 0 < a n)
    (hratio : ∀ n, |(a n : ℝ) ^ 2 / a (n + 1) - β| ≤ 1 / 3)
    (hsum : HasSum (fun n => 1 / (a n : ℝ)) r) :
    Tendsto (fun n => ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ)) ^ 2 / (a n : ℝ)) atTop (𝓝 0) := by
  have h0 : Tendsto (fun n => 1 / (a n : ℝ)) atTop (𝓝 0) := hsum.summable.tendsto_atTop_zero
  have hB2 : Tendsto (fun n => (β + 1 / 3) ^ 2 * (1 / (a n : ℝ))) atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => (β + 1 / 3) ^ 2) atTop (𝓝 ((β + 1 / 3) ^ 2)) :=
      tendsto_const_nhds
    have h := hc.mul h0
    simpa using h
  apply squeeze_zero _ _ hB2
  · intro n
    exact div_nonneg (sq_nonneg _) (pos_real hpos n).le
  · intro n
    have han : 0 < (a n : ℝ) := pos_real hpos n
    have hnn := ratio_nonneg hpos n
    have hle := ratio_le hratio n
    have hsq : ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ)) ^ 2 ≤ (β + 1 / 3) ^ 2 :=
      pow_le_pow_left₀ hnn hle 2
    have heq : (β + 1 / 3) ^ 2 * (1 / (a n : ℝ)) = (β + 1 / 3) ^ 2 / (a n : ℝ) := by ring
    rw [heq]
    exact div_le_div_of_nonneg_right hsq han.le

private theorem tendsto_a_sq_mul_rem {β r : ℝ} {a : ℕ → ℕ} (hβ : 0 ≤ β) (hpos : ∀ n, 0 < a n)
    (hratio : ∀ n, |(a n : ℝ) ^ 2 / a (n + 1) - β| ≤ 1 / 3)
    (hsum : HasSum (fun n => 1 / (a n : ℝ)) r) :
    Tendsto (fun n => (a n : ℝ) ^ 2 * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ)))
      atTop (𝓝 0) := by
  have h0 : Tendsto (fun n => 1 / (a n : ℝ)) atTop (𝓝 0) := hsum.summable.tendsto_atTop_zero
  have h00 : Tendsto (fun n => (1 / (a n : ℝ)) * (1 / (a n : ℝ))) atTop (𝓝 0) := by
    have h := h0.mul h0
    simpa using h
  have hg : Tendsto (fun n => (8 * (β + 1 / 3) ^ 3 / 5) * ((1 / (a n : ℝ)) * (1 / (a n : ℝ))))
      atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => (8 * (β + 1 / 3) ^ 3 / 5)) atTop
        (𝓝 (8 * (β + 1 / 3) ^ 3 / 5)) :=
      tendsto_const_nhds
    have h := hc.mul h00
    simpa using h
  apply squeeze_zero' _ _ hg
  · apply Filter.Eventually.of_forall
    intro n
    exact mul_nonneg (sq_nonneg _) (rem_pos hpos hsum (n + 2)).le
  · have hev := eventually_hlarge (β := β) hpos hsum
    filter_upwards [hev] with n hn
    have han : 0 < (a n : ℝ) := pos_real hpos n
    have ha2 : 0 < (a (n + 2) : ℝ) := pos_real hpos (n + 2)
    have hane : (a n : ℝ) ≠ 0 := ne_of_gt han
    have htail := tail_bound hβ hpos hratio hsum hn (Nat.le_add_right n 2)
    have hq := quartic hpos hratio n
    have hsqpos : 0 < (a n : ℝ) ^ 2 := pow_pos han 2
    have hdiv : (a n : ℝ) ^ 2 / (a (n + 2) : ℝ) ≤ (β + 1 / 3) ^ 3 / (a n : ℝ) ^ 2 := by
      rw [div_le_div_iff₀ ha2 hsqpos]
      have heq : (a n : ℝ) ^ 2 * (a n : ℝ) ^ 2 = (a n : ℝ) ^ 4 := by ring
      rw [heq]
      exact hq
    have hmul : (a n : ℝ) ^ 2 * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ)) ≤
        (a n : ℝ) ^ 2 * ((1 / (a (n + 2) : ℝ)) * (8 / 5 : ℝ)) :=
      mul_le_mul_of_nonneg_left htail (sq_nonneg _)
    have heq1 : (a n : ℝ) ^ 2 * ((1 / (a (n + 2) : ℝ)) * (8 / 5 : ℝ)) =
        ((a n : ℝ) ^ 2 / (a (n + 2) : ℝ)) * (8 / 5 : ℝ) := by ring
    rw [heq1] at hmul
    have hle2 : ((a n : ℝ) ^ 2 / (a (n + 2) : ℝ)) * (8 / 5 : ℝ) ≤
        ((β + 1 / 3) ^ 3 / (a n : ℝ) ^ 2) * (8 / 5 : ℝ) :=
      mul_le_mul_of_nonneg_right hdiv (by norm_num)
    have heq2 : ((β + 1 / 3) ^ 3 / (a n : ℝ) ^ 2) * (8 / 5 : ℝ) =
        (8 * (β + 1 / 3) ^ 3 / 5) * ((1 / (a n : ℝ)) * (1 / (a n : ℝ))) := by
      field_simp
    calc (a n : ℝ) ^ 2 * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ))
          ≤ ((a n : ℝ) ^ 2 / (a (n + 2) : ℝ)) * (8 / 5 : ℝ) := hmul
      _ ≤ ((β + 1 / 3) ^ 3 / (a n : ℝ) ^ 2) * (8 / 5 : ℝ) := hle2
      _ = (8 * (β + 1 / 3) ^ 3 / 5) * ((1 / (a n : ℝ)) * (1 / (a n : ℝ))) := heq2

private theorem tendsto_U {β r : ℝ} {a : ℕ → ℕ} (hβ : 0 ≤ β) (hpos : ∀ n, 0 < a n)
    (hratio : ∀ n, |(a n : ℝ) ^ 2 / a (n + 1) - β| ≤ 1 / 3)
    (hsum : HasSum (fun n => 1 / (a n : ℝ)) r) :
    Tendsto (fun n => (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 1), 1 / (a k : ℝ))) atTop (𝓝 0) := by
  have hv := tendsto_c_div_a hpos hratio hsum
  have hw2 := tendsto_a_sq_mul_rem hβ hpos hratio hsum
  have h0 : Tendsto (fun n => 1 / (a n : ℝ)) atTop (𝓝 0) := hsum.summable.tendsto_atTop_zero
  have hw : Tendsto (fun n => (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ)))
      atTop (𝓝 0) := by
    have heq : ∀ n : ℕ, (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ)) =
        ((a n : ℝ) ^ 2 * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ))) * (1 / (a n : ℝ)) := by
      intro n
      have hane : (a n : ℝ) ≠ 0 := ne_of_gt (pos_real hpos n)
      field_simp
    have hmul := hw2.mul h0
    have hlim : Tendsto
        (fun n => ((a n : ℝ) ^ 2 * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ))) *
          (1 / (a n : ℝ))) atTop (𝓝 0) := by
      simpa using hmul
    have hev : (fun n => (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ))) =ᶠ[atTop]
        (fun n => ((a n : ℝ) ^ 2 * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ))) *
          (1 / (a n : ℝ))) :=
      Filter.Eventually.of_forall heq
    exact Tendsto.congr' hev.symm hlim
  have hadd_eq : ∀ n : ℕ, (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 1), 1 / (a k : ℝ)) =
      (a n : ℝ) / (a (n + 1) : ℝ) +
        (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ)) := by
    intro n
    have hadd1 : (r - ∑ k ∈ Finset.range (n + 1), 1 / (a k : ℝ)) =
        1 / (a (n + 1) : ℝ) + (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ)) :=
      rem_add (n + 1)
    rw [hadd1]
    ring
  have hadd_lim : Tendsto
      (fun n => (a n : ℝ) / (a (n + 1) : ℝ) +
        (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ))) atTop (𝓝 0) := by
    have h := hv.add hw
    simpa using h
  have hev2 : (fun n => (a n : ℝ) / (a (n + 1) : ℝ) +
      (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ))) =ᶠ[atTop]
      (fun n => (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 1), 1 / (a k : ℝ))) :=
    Filter.Eventually.of_forall (fun n => (hadd_eq n).symm)
  exact Tendsto.congr' hev2 hadd_lim

private theorem D_eq {r : ℝ} {a : ℕ → ℕ} (hpos : ∀ n, 0 < a n)
    (hsum : HasSum (fun n => 1 / (a n : ℝ)) r) (n : ℕ) :
    (r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ - (a n : ℝ) +
        (a n : ℝ) ^ 2 / (a (n + 1) : ℝ) =
      ((a n : ℝ) * ((a n : ℝ) / (a (n + 1) : ℝ)) ^ 2 -
        (a n : ℝ) * (1 - (a n : ℝ) / (a (n + 1) : ℝ)) *
          ((a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ)))) /
        (1 + (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 1), 1 / (a k : ℝ))) := by
  have han : 0 < (a n : ℝ) := pos_real hpos n
  have hx1 : 0 < (r - ∑ k ∈ Finset.range (n + 1), 1 / (a k : ℝ)) := rem_pos hpos hsum (n + 1)
  have hadd : (r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ)) =
      1 / (a n : ℝ) + (r - ∑ k ∈ Finset.range (n + 1), 1 / (a k : ℝ)) := rem_add n
  have hadd1 : (r - ∑ k ∈ Finset.range (n + 1), 1 / (a k : ℝ)) =
      1 / (a (n + 1) : ℝ) + (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ)) :=
    rem_add (n + 1)
  have hc : (a n : ℝ) ^ 2 / (a (n + 1) : ℝ) =
      ((a n : ℝ) / (a (n + 1) : ℝ)) * (a n : ℝ) := by ring
  have hU : (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 1), 1 / (a k : ℝ)) =
      (a n : ℝ) / (a (n + 1) : ℝ) +
        (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ)) := by
    rw [hadd1]
    ring
  have hU1pos : 0 < 1 + (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 1), 1 / (a k : ℝ)) := by
    have hnn : 0 ≤ (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 1), 1 / (a k : ℝ)) :=
      mul_nonneg han.le hx1.le
    linarith
  have hU1ne : 1 + (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 1), 1 / (a k : ℝ)) ≠ 0 :=
    ne_of_gt hU1pos
  have hxn : (r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ)) =
      (1 + (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 1), 1 / (a k : ℝ))) / (a n : ℝ) := by
    rw [hadd]
    field_simp
  have hinv : (r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ =
      (a n : ℝ) / (1 + (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 1), 1 / (a k : ℝ))) := by
    rw [hxn, inv_div]
  rw [eq_div_iff hU1ne]
  have hD1 : ((r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ - (a n : ℝ) +
        (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)) *
        (1 + (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 1), 1 / (a k : ℝ))) =
      (a n : ℝ) - ((a n : ℝ) - (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)) *
        (1 + (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 1), 1 / (a k : ℝ))) := by
    rw [hinv]
    field_simp
    ring
  have hD2 : (a n : ℝ) - ((a n : ℝ) - (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)) *
        (1 + (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 1), 1 / (a k : ℝ))) =
      (a n : ℝ) * ((a n : ℝ) / (a (n + 1) : ℝ)) ^ 2 -
        (a n : ℝ) * (1 - (a n : ℝ) / (a (n + 1) : ℝ)) *
          ((a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ))) := by
    rw [hc, hU]
    ring
  rw [hD1]
  exact hD2

private theorem tendsto_D0 {β r : ℝ} {a : ℕ → ℕ} (hβ : 0 ≤ β) (hpos : ∀ n, 0 < a n)
    (hratio : ∀ n, |(a n : ℝ) ^ 2 / a (n + 1) - β| ≤ 1 / 3)
    (hsum : HasSum (fun n => 1 / (a n : ℝ)) r) :
    Tendsto (fun n => (r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ - (a n : ℝ) +
      (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)) atTop (𝓝 0) := by
  have hT1 : Tendsto (fun n => (a n : ℝ) * ((a n : ℝ) / (a (n + 1) : ℝ)) ^ 2) atTop (𝓝 0) := by
    have hlim := tendsto_c_sq_div_a hpos hratio hsum
    have heq : ∀ n : ℕ, (a n : ℝ) * ((a n : ℝ) / (a (n + 1) : ℝ)) ^ 2 =
        ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ)) ^ 2 / (a n : ℝ) := by
      intro n
      have hane : (a n : ℝ) ≠ 0 := ne_of_gt (pos_real hpos n)
      have ha1ne : (a (n + 1) : ℝ) ≠ 0 := ne_of_gt (pos_real hpos (n + 1))
      field_simp
    have hev : (fun n => (a n : ℝ) * ((a n : ℝ) / (a (n + 1) : ℝ)) ^ 2) =ᶠ[atTop]
        (fun n => ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ)) ^ 2 / (a n : ℝ)) :=
      Filter.Eventually.of_forall heq
    exact Tendsto.congr' hev.symm hlim
  have hv := tendsto_c_div_a hpos hratio hsum
  have hw2 := tendsto_a_sq_mul_rem hβ hpos hratio hsum
  have h1v : Tendsto (fun n => 1 - (a n : ℝ) / (a (n + 1) : ℝ)) atTop (𝓝 1) := by
    have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have h := hc.sub hv
    simpa using h
  have hT2 : Tendsto (fun n => (1 - (a n : ℝ) / (a (n + 1) : ℝ)) *
      ((a n : ℝ) ^ 2 * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ)))) atTop (𝓝 0) := by
    have h := h1v.mul hw2
    simpa using h
  have hT2' : Tendsto (fun n => (a n : ℝ) * (1 - (a n : ℝ) / (a (n + 1) : ℝ)) *
      ((a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ)))) atTop (𝓝 0) := by
    have heq : ∀ n : ℕ, (a n : ℝ) * (1 - (a n : ℝ) / (a (n + 1) : ℝ)) *
          ((a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ))) =
        (1 - (a n : ℝ) / (a (n + 1) : ℝ)) *
          ((a n : ℝ) ^ 2 * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ))) := by
      intro n
      ring
    have hev : (fun n => (a n : ℝ) * (1 - (a n : ℝ) / (a (n + 1) : ℝ)) *
        ((a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ)))) =ᶠ[atTop]
        (fun n => (1 - (a n : ℝ) / (a (n + 1) : ℝ)) *
          ((a n : ℝ) ^ 2 * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ)))) :=
      Filter.Eventually.of_forall heq
    exact Tendsto.congr' hev.symm hT2
  have hN : Tendsto (fun n => (a n : ℝ) * ((a n : ℝ) / (a (n + 1) : ℝ)) ^ 2 -
      (a n : ℝ) * (1 - (a n : ℝ) / (a (n + 1) : ℝ)) *
        ((a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ)))) atTop (𝓝 0) := by
    have h := hT1.sub hT2'
    simpa using h
  have hU := tendsto_U hβ hpos hratio hsum
  have hDn : Tendsto (fun n => 1 + (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 1), 1 / (a k : ℝ)))
      atTop (𝓝 1) := by
    have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have h := hc.add hU
    simpa using h
  have hdiv : Tendsto ((fun n => (a n : ℝ) * ((a n : ℝ) / (a (n + 1) : ℝ)) ^ 2 -
      (a n : ℝ) * (1 - (a n : ℝ) / (a (n + 1) : ℝ)) *
        ((a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ)))) /
      (fun n => 1 + (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 1), 1 / (a k : ℝ)))) atTop (𝓝 0) := by
    have h := hN.div hDn one_ne_zero
    simpa using h
  have heq : ∀ n : ℕ, (r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ - (a n : ℝ) +
        (a n : ℝ) ^ 2 / (a (n + 1) : ℝ) =
      ((a n : ℝ) * ((a n : ℝ) / (a (n + 1) : ℝ)) ^ 2 -
        (a n : ℝ) * (1 - (a n : ℝ) / (a (n + 1) : ℝ)) *
          ((a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ)))) /
        (1 + (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 1), 1 / (a k : ℝ))) :=
    fun n => D_eq hpos hsum n
  have hev : (fun n => (r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ - (a n : ℝ) +
      (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)) =ᶠ[atTop]
      ((fun n => (a n : ℝ) * ((a n : ℝ) / (a (n + 1) : ℝ)) ^ 2 -
        (a n : ℝ) * (1 - (a n : ℝ) / (a (n + 1) : ℝ)) *
          ((a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 2), 1 / (a k : ℝ)))) /
        (fun n => 1 + (a n : ℝ) * (r - ∑ k ∈ Finset.range (n + 1), 1 / (a k : ℝ)))) :=
    Filter.Eventually.of_forall heq
  exact Tendsto.congr' hev.symm hdiv

/-- **Recovering a doubly exponential sequence from its reciprocal sum.** Let $\beta \ge 0$ and
$r$ be real numbers, and let $(a_n)_{n \ge 0}$ be a sequence of positive integers with
$|a_n^2 / a_{n+1} - \beta| \le 1/3$ for all $n$ and $\sum_n 1 / a_n = r$. Write
$x_n = r - \sum_{k<n} 1 / a_k$. Then for every $n$ with $a_n \ge 8 (\beta + 1/3)^2$ we have
$a_n = \lfloor x_n^{-1} + \beta + 1/2 \rfloor$, that is, $a_n$ is the integer nearest to
$x_n^{-1} + \beta$, with halves rounded up. Moreover, if $a_n^2 / a_{n+1} \to \beta$, then
$|x_n^{-1} + \beta - a_n| \to 0$.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Theorem 1 (`integers-2026-A28-thm-1`). -/
public theorem eq_round_inv_remainder_add {β r : ℝ} (hβ : 0 ≤ β) {a : ℕ → ℕ}
    (hpos : ∀ n, 0 < a n) (hratio : ∀ n, |(a n : ℝ) ^ 2 / a (n + 1) - β| ≤ 1 / 3)
    (hsum : HasSum (fun n => 1 / (a n : ℝ)) r) :
    (∀ n, 8 * (β + 1 / 3) ^ 2 ≤ (a n : ℝ) →
      (a n : ℤ) = ⌊(r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ + β + 1 / 2⌋) ∧
    (Tendsto (fun n => (a n : ℝ) ^ 2 / a (n + 1)) atTop (𝓝 β) →
      Tendsto (fun n => |(r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ + β - a n|) atTop (𝓝 0)) := by
  constructor
  · intro n hlarge
    exact round_eq hβ hpos hratio hsum hlarge
  · intro hlim
    have hD0 := tendsto_D0 hβ hpos hratio hsum
    have hβc : Tendsto (fun n => β - (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)) atTop (𝓝 0) := by
      have hc : Tendsto (fun _ : ℕ => β) atTop (𝓝 β) := tendsto_const_nhds
      have h := hc.sub hlim
      simpa using h
    have hsum0 : Tendsto (fun n => ((r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ - (a n : ℝ) +
        (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)) + (β - (a n : ℝ) ^ 2 / (a (n + 1) : ℝ))) atTop (𝓝 0) := by
      have h := hD0.add hβc
      simpa using h
    have heq : ∀ n : ℕ, (r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ + β - (a n : ℝ) =
        ((r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ - (a n : ℝ) +
          (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)) + (β - (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)) := by
      intro n
      ring
    have htar : Tendsto (fun n => (r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ + β - (a n : ℝ))
        atTop (𝓝 0) := by
      have hev : (fun n => (r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ + β - (a n : ℝ)) =ᶠ[atTop]
          (fun n => ((r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ - (a n : ℝ) +
            (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)) + (β - (a n : ℝ) ^ 2 / (a (n + 1) : ℝ))) :=
        Filter.Eventually.of_forall heq
      exact Tendsto.congr' hev.symm hsum0
    have habs := htar.abs
    simpa using habs

end

end MetaMathlibExt
