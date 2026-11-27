/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.DoublyExponentialReciprocalSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Tails that are pseudo-greedy expansions

A sequence of positive integers with `aₙ² / aₙ₊₁ → 1` and convergent reciprocal sum
has a tail that is the pseudo-greedy expansion of its own reciprocal sum, with gap
sequence tending to zero.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28 (arXiv:2504.05933), Corollary 3.
-/

open Filter Topology

namespace MetaMathlibExt

@[expose] public section

/-- Doubling bound used to compare `2 ^ k` with linear exponents. -/
private theorem two_mul_add_two_le_two_pow_succ (j : ℕ) : 2 * j + 2 ≤ 2 ^ (j + 1) := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    rw [pow_succ]
    omega

/-- One-step growth: the ratio bound gives `aₖ² ≤ (4/3) * aₖ₊₁`. -/
private theorem sq_le_mul_next {b : ℕ → ℕ} (hpos : ∀ n, 0 < b n)
    (hratio : ∀ n, |(b n : ℝ) ^ 2 / b (n + 1) - 1| ≤ 1 / 3) (k : ℕ) :
    (b k : ℝ) ^ 2 ≤ (4 / 3) * (b (k + 1) : ℝ) := by
  have h1 : (b k : ℝ) ^ 2 / b (k + 1) ≤ 4 / 3 := by
    have h := (abs_le.mp (hratio k)).2
    linarith
  have hpos' : (0 : ℝ) < b (k + 1) := by exact_mod_cast hpos (k + 1)
  rw [div_le_iff₀ hpos'] at h1
  exact h1

/-- Iterated growth: `aₙ ^ 2 ^ k ≤ (4 / 3) ^ (2 ^ k - 1) * aₙ₊ₖ`. -/
private theorem pow_le_pow_mul_shift {b : ℕ → ℕ} (hpos : ∀ n, 0 < b n)
    (hratio : ∀ n, |(b n : ℝ) ^ 2 / b (n + 1) - 1| ≤ 1 / 3) (n k : ℕ) :
    (b n : ℝ) ^ 2 ^ k ≤ (4 / 3 : ℝ) ^ (2 ^ k - 1) * (b (n + k) : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h2k : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
    have e2 : 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
    have hexp : (2 ^ k - 1) * 2 + 1 = 2 ^ (k + 1) - 1 := by omega
    have hn : n + (k + 1) = (n + k) + 1 := by omega
    have hstep := sq_le_mul_next hpos hratio (n + k)
    rw [hn]
    have hsq : ((b n : ℝ) ^ 2 ^ k) ^ 2 ≤ ((4 / 3 : ℝ) ^ (2 ^ k - 1) * b (n + k)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) ih 2
    calc (b n : ℝ) ^ 2 ^ (k + 1)
        = ((b n : ℝ) ^ 2 ^ k) ^ 2 := by rw [e2, pow_mul]
      _ ≤ ((4 / 3 : ℝ) ^ (2 ^ k - 1) * b (n + k)) ^ 2 := hsq
      _ = (4 / 3 : ℝ) ^ ((2 ^ k - 1) * 2) * ((b (n + k) : ℝ) ^ 2) := by
          rw [mul_pow, ← pow_mul]
      _ ≤ (4 / 3 : ℝ) ^ ((2 ^ k - 1) * 2) * ((4 / 3) * b ((n + k) + 1)) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = (4 / 3 : ℝ) ^ ((2 ^ k - 1) * 2 + 1) * b ((n + k) + 1) := by
          rw [pow_succ']
          ring
      _ = (4 / 3 : ℝ) ^ (2 ^ (k + 1) - 1) * b ((n + k) + 1) := by rw [hexp]

/-- Term bound for the `A` series: `aₙ / aₙ₊₁₊ⱼ ≤ q ^ (2 * j + 1)`. -/
private theorem termA_le {b : ℕ → ℕ} (hpos : ∀ n, 0 < b n)
    (hratio : ∀ n, |(b n : ℝ) ^ 2 / b (n + 1) - 1| ≤ 1 / 3) (n : ℕ)
    (hn : (15 : ℝ) ≤ b n) (j : ℕ) :
    (b n : ℝ) / b (n + 1 + j) ≤ ((4 / 3 : ℝ) / b n) ^ (2 * j + 1) := by
  have hb : (0 : ℝ) < b n := by exact_mod_cast hpos n
  have hq0 : (0 : ℝ) ≤ (4 / 3) / b n := by positivity
  have hq1 : (4 / 3 : ℝ) / b n ≤ 1 := by
    rw [div_le_one hb]
    linarith
  have h2 : 1 ≤ 2 ^ (j + 1) := Nat.one_le_pow (j + 1) 2 (by norm_num)
  have hG2 := pow_le_pow_mul_shift hpos hratio n (j + 1)
  have hshift : n + (j + 1) = n + 1 + j := by omega
  rw [hshift] at hG2
  have hpow : (b n : ℝ) ^ 2 ^ (j + 1) = (b n : ℝ) * (b n : ℝ) ^ (2 ^ (j + 1) - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel h2]
    rw [pow_succ']
  have hD : (0 : ℝ) < b (n + 1 + j) := by exact_mod_cast hpos (n + 1 + j)
  have step_a : (b n : ℝ) / b (n + 1 + j) ≤ ((4 / 3 : ℝ) / b n) ^ (2 ^ (j + 1) - 1) := by
    rw [div_pow, div_le_div_iff₀ hD (pow_pos hb _), ← hpow]
    exact hG2
  have e2 : 2 * j + 1 ≤ 2 ^ (j + 1) - 1 := by
    have e1 := two_mul_add_two_le_two_pow_succ j
    omega
  have step_b : ((4 / 3 : ℝ) / b n) ^ (2 ^ (j + 1) - 1)
      ≤ ((4 / 3 : ℝ) / b n) ^ (2 * j + 1) :=
    pow_le_pow_of_le_one hq0 hq1 e2
  exact le_trans step_a step_b

/-- Term bound for the `B` series: `aₙ² / aₙ₊₂₊ⱼ ≤ (4 / 3) * q ^ (2 * j + 2)`. -/
private theorem termB_le {b : ℕ → ℕ} (hpos : ∀ n, 0 < b n)
    (hratio : ∀ n, |(b n : ℝ) ^ 2 / b (n + 1) - 1| ≤ 1 / 3) (n : ℕ)
    (hn : (15 : ℝ) ≤ b n) (j : ℕ) :
    (b n : ℝ) ^ 2 / b (n + 2 + j)
      ≤ (4 / 3) * (((4 / 3 : ℝ) / b n) ^ (2 * j + 2)) := by
  have hb : (0 : ℝ) < b n := by exact_mod_cast hpos n
  have hq0 : (0 : ℝ) ≤ (4 / 3) / b n := by positivity
  have hq1 : (4 / 3 : ℝ) / b n ≤ 1 := by
    rw [div_le_one hb]
    linarith
  have e1 := two_mul_add_two_le_two_pow_succ (j + 1)
  have h2 : 2 ≤ 2 ^ (j + 1 + 1) := by omega
  have hG2 := pow_le_pow_mul_shift hpos hratio n (j + 1 + 1)
  have hshift : n + (j + 1 + 1) = n + 2 + j := by omega
  rw [hshift] at hG2
  have hexpE : 2 + (2 ^ (j + 1 + 1) - 2) = 2 ^ (j + 1 + 1) := by omega
  have hexpE' : 2 ^ (j + 1 + 1) - 2 + 1 = 2 ^ (j + 1 + 1) - 1 := by omega
  have hD : (0 : ℝ) < b (n + 2 + j) := by exact_mod_cast hpos (n + 2 + j)
  have step_a : (b n : ℝ) ^ 2 / b (n + 2 + j)
      ≤ (4 / 3 : ℝ) * (((4 / 3 : ℝ) / b n) ^ (2 ^ (j + 1 + 1) - 2)) := by
    rw [div_pow, ← mul_div_assoc, div_le_div_iff₀ hD (pow_pos hb _)]
    conv_lhs => rw [← pow_add, hexpE]
    conv_rhs => rw [← pow_succ', hexpE']
    exact hG2
  have e2 : 2 * j + 2 ≤ 2 ^ (j + 1 + 1) - 2 := by omega
  have step_b : (4 / 3 : ℝ) * (((4 / 3 : ℝ) / b n) ^ (2 ^ (j + 1 + 1) - 2))
      ≤ (4 / 3) * (((4 / 3 : ℝ) / b n) ^ (2 * j + 2)) :=
    mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hq0 hq1 e2) (by norm_num)
  exact le_trans step_a step_b

/-- Facts about `q = (4 / 3) / aₙ` when `15 ≤ aₙ`. -/
private theorem qfacts {b : ℕ → ℕ} (hpos : ∀ n, 0 < b n) (n : ℕ)
    (hn : (15 : ℝ) ≤ b n) :
    (((4 / 3 : ℝ) / b n) ^ 2 < 1) ∧
    (((4 / 3 : ℝ) / b n) ^ 2 ≤ 1 / 8) ∧
    ((1 - (((4 / 3 : ℝ) / b n) ^ 2))⁻¹ ≤ 8 / 7) := by
  have hb : (0 : ℝ) < b n := by exact_mod_cast hpos n
  have hqlt : (4 / 3 : ℝ) / b n < 1 := by
    rw [div_lt_one hb]
    linarith
  have hq0 : (0 : ℝ) ≤ (4 / 3) / b n := by positivity
  have hq2lt : (((4 / 3 : ℝ) / b n) ^ 2 < 1) := pow_lt_one₀ hq0 hqlt two_ne_zero
  have hsq : (225 : ℝ) ≤ (b n) ^ 2 := by
    have hb0 : (0 : ℝ) ≤ b n := hb.le
    nlinarith [hn, hb0, sq_nonneg ((b n : ℝ) - 15)]
  have hq2le : (((4 / 3 : ℝ) / b n) ^ 2 ≤ 1 / 8) := by
    rw [div_pow, div_le_iff₀ (pow_pos hb 2)]
    norm_num
    linarith
  have h1q : (7 / 8 : ℝ) ≤ 1 - (((4 / 3 : ℝ) / b n) ^ 2) := by linarith
  have hinv : (1 - (((4 / 3 : ℝ) / b n) ^ 2))⁻¹ ≤ 8 / 7 := by
    have h := (inv_le_inv₀ (by linarith : (0 : ℝ) < 1 - (((4 / 3 : ℝ) / b n) ^ 2))
      (by norm_num : (0 : ℝ) < 7 / 8)).mpr h1q
    norm_num at h
    exact h
  exact ⟨hq2lt, hq2le, hinv⟩

/-- The `A` series is summable. -/
private theorem summable_A {b : ℕ → ℕ} (hpos : ∀ n, 0 < b n)
    (hratio : ∀ n, |(b n : ℝ) ^ 2 / b (n + 1) - 1| ≤ 1 / 3) (n : ℕ)
    (hn : (15 : ℝ) ≤ b n) :
    Summable (fun j => (b n : ℝ) / b (n + 1 + j)) := by
  obtain ⟨hq2lt, -, -⟩ := qfacts hpos n hn
  have hsG := (summable_geometric_of_lt_one
    (sq_nonneg ((4 / 3 : ℝ) / b n)) hq2lt).mul_left ((4 / 3 : ℝ) / b n)
  refine Summable.of_nonneg_of_le (fun j => by positivity) ?_ hsG
  intro j
  have hpowA : (((4 / 3 : ℝ) / b n) ^ (2 * j + 1))
      = ((4 / 3 : ℝ) / b n) * ((((4 / 3 : ℝ) / b n) ^ 2) ^ j) := by
    rw [pow_succ', pow_mul]
  change (b n : ℝ) / b (n + 1 + j)
    ≤ ((4 / 3 : ℝ) / b n) * ((((4 / 3 : ℝ) / b n) ^ 2) ^ j)
  rw [← hpowA]
  exact termA_le hpos hratio n hn j

/-- Bound on the `A` series: `aₙ * A ^ 2 ≤ (1024 / 441) / aₙ`. -/
private theorem tsum_A_le {b : ℕ → ℕ} (hpos : ∀ n, 0 < b n)
    (hratio : ∀ n, |(b n : ℝ) ^ 2 / b (n + 1) - 1| ≤ 1 / 3) (n : ℕ)
    (hn : (15 : ℝ) ≤ b n) :
    (b n : ℝ) * (∑' j, (b n : ℝ) / b (n + 1 + j)) ^ 2 ≤ (1024 / 441) / b n := by
  obtain ⟨hq2lt, -, hinv⟩ := qfacts hpos n hn
  have hb : (0 : ℝ) < b n := by exact_mod_cast hpos n
  have hbne : (b n : ℝ) ≠ 0 := ne_of_gt hb
  have hq0 : (0 : ℝ) ≤ (4 / 3) / b n := by positivity
  have hsG := (summable_geometric_of_lt_one
    (sq_nonneg ((4 / 3 : ℝ) / b n)) hq2lt).mul_left ((4 / 3 : ℝ) / b n)
  have htsumG : (∑' j, ((4 / 3 : ℝ) / b n) * ((((4 / 3 : ℝ) / b n) ^ 2) ^ j))
      = ((4 / 3 : ℝ) / b n) * (1 - (((4 / 3 : ℝ) / b n) ^ 2))⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one (sq_nonneg _) hq2lt]
  have hsA := summable_A hpos hratio n hn
  have hAle : (∑' j, (b n : ℝ) / b (n + 1 + j))
      ≤ ((4 / 3 : ℝ) / b n) * (1 - (((4 / 3 : ℝ) / b n) ^ 2))⁻¹ := by
    rw [← htsumG]
    apply Summable.tsum_le_tsum _ hsA hsG
    intro j
    have hpowA : (((4 / 3 : ℝ) / b n) ^ (2 * j + 1))
        = ((4 / 3 : ℝ) / b n) * ((((4 / 3 : ℝ) / b n) ^ 2) ^ j) := by
      rw [pow_succ', pow_mul]
    change (b n : ℝ) / b (n + 1 + j)
      ≤ ((4 / 3 : ℝ) / b n) * ((((4 / 3 : ℝ) / b n) ^ 2) ^ j)
    rw [← hpowA]
    exact termA_le hpos hratio n hn j
  have hAge0 : 0 ≤ ∑' j, (b n : ℝ) / b (n + 1 + j) :=
    tsum_nonneg (fun j => by positivity)
  have hAub : (∑' j, (b n : ℝ) / b (n + 1 + j)) ≤ (8 / 7) * ((4 / 3 : ℝ) / b n) := by
    calc (∑' j, (b n : ℝ) / b (n + 1 + j))
        ≤ ((4 / 3 : ℝ) / b n) * (1 - (((4 / 3 : ℝ) / b n) ^ 2))⁻¹ := hAle
      _ ≤ ((4 / 3 : ℝ) / b n) * (8 / 7) := mul_le_mul_of_nonneg_left hinv hq0
      _ = (8 / 7) * ((4 / 3 : ℝ) / b n) := by ring
  have hAsq : (∑' j, (b n : ℝ) / b (n + 1 + j)) ^ 2 ≤ ((8 / 7) * ((4 / 3 : ℝ) / b n)) ^ 2 :=
    pow_le_pow_left₀ hAge0 hAub 2
  have h2 : (b n : ℝ) * (∑' j, (b n : ℝ) / b (n + 1 + j)) ^ 2
      ≤ (b n) * (((8 / 7) * ((4 / 3 : ℝ) / b n)) ^ 2) :=
    mul_le_mul_of_nonneg_left hAsq (by positivity)
  have heq : (b n : ℝ) * (((8 / 7) * ((4 / 3 : ℝ) / b n)) ^ 2) = 1024 / (441 * b n) := by
    field_simp
    ring
  rw [heq] at h2
  have h3 : (1024 : ℝ) / (441 * b n) = (1024 / 441) / b n := by rw [div_div]
  rw [h3] at h2
  exact h2

/-- The `B` series is summable. -/
private theorem summable_B {b : ℕ → ℕ} (hpos : ∀ n, 0 < b n)
    (hratio : ∀ n, |(b n : ℝ) ^ 2 / b (n + 1) - 1| ≤ 1 / 3) (n : ℕ)
    (hn : (15 : ℝ) ≤ b n) :
    Summable (fun j => (b n : ℝ) ^ 2 / b (n + 2 + j)) := by
  obtain ⟨hq2lt, -, -⟩ := qfacts hpos n hn
  have hsG := (summable_geometric_of_lt_one
    (sq_nonneg ((4 / 3 : ℝ) / b n)) hq2lt).mul_left
    ((4 / 3 : ℝ) * (((4 / 3 : ℝ) / b n) ^ 2))
  refine Summable.of_nonneg_of_le (fun j => by positivity) ?_ hsG
  intro j
  have hpowB : (4 / 3 : ℝ) * (((4 / 3 : ℝ) / b n) ^ (2 * j + 2))
      = ((4 / 3 : ℝ) * (((4 / 3 : ℝ) / b n) ^ 2)) * ((((4 / 3 : ℝ) / b n) ^ 2) ^ j) := by
    have h : (((4 / 3 : ℝ) / b n) ^ (2 * j + 2))
        = (((4 / 3 : ℝ) / b n) ^ 2) * ((((4 / 3 : ℝ) / b n) ^ 2) ^ j) := by
      conv_lhs => rw [show 2 * j + 2 = 2 + 2 * j by omega]
      rw [pow_add, pow_mul]
    rw [h]
    ring
  change (b n : ℝ) ^ 2 / b (n + 2 + j)
    ≤ ((4 / 3 : ℝ) * (((4 / 3 : ℝ) / b n) ^ 2)) * ((((4 / 3 : ℝ) / b n) ^ 2) ^ j)
  rw [← hpowB]
  exact termB_le hpos hratio n hn j

/-- Bound on the `B` series: `B ≤ (512 / 189) / aₙ ^ 2`. -/
private theorem tsum_B_le {b : ℕ → ℕ} (hpos : ∀ n, 0 < b n)
    (hratio : ∀ n, |(b n : ℝ) ^ 2 / b (n + 1) - 1| ≤ 1 / 3) (n : ℕ)
    (hn : (15 : ℝ) ≤ b n) :
    (∑' j, (b n : ℝ) ^ 2 / b (n + 2 + j)) ≤ (512 / 189) / (b n) ^ 2 := by
  obtain ⟨hq2lt, -, hinv⟩ := qfacts hpos n hn
  have hsG := (summable_geometric_of_lt_one
    (sq_nonneg ((4 / 3 : ℝ) / b n)) hq2lt).mul_left
    ((4 / 3 : ℝ) * (((4 / 3 : ℝ) / b n) ^ 2))
  have htsumG : (∑' j, ((4 / 3 : ℝ) * (((4 / 3 : ℝ) / b n) ^ 2))
        * ((((4 / 3 : ℝ) / b n) ^ 2) ^ j))
      = ((4 / 3 : ℝ) * (((4 / 3 : ℝ) / b n) ^ 2)) * (1 - (((4 / 3 : ℝ) / b n) ^ 2))⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one (sq_nonneg _) hq2lt]
  have hsB := summable_B hpos hratio n hn
  have hBle : (∑' j, (b n : ℝ) ^ 2 / b (n + 2 + j))
      ≤ ((4 / 3 : ℝ) * (((4 / 3 : ℝ) / b n) ^ 2)) * (1 - (((4 / 3 : ℝ) / b n) ^ 2))⁻¹ := by
    rw [← htsumG]
    apply Summable.tsum_le_tsum _ hsB hsG
    intro j
    have hpowB : (4 / 3 : ℝ) * (((4 / 3 : ℝ) / b n) ^ (2 * j + 2))
        = ((4 / 3 : ℝ) * (((4 / 3 : ℝ) / b n) ^ 2)) * ((((4 / 3 : ℝ) / b n) ^ 2) ^ j) := by
      have h : (((4 / 3 : ℝ) / b n) ^ (2 * j + 2))
          = (((4 / 3 : ℝ) / b n) ^ 2) * ((((4 / 3 : ℝ) / b n) ^ 2) ^ j) := by
        conv_lhs => rw [show 2 * j + 2 = 2 + 2 * j by omega]
        rw [pow_add, pow_mul]
      rw [h]
      ring
    change (b n : ℝ) ^ 2 / b (n + 2 + j)
      ≤ ((4 / 3 : ℝ) * (((4 / 3 : ℝ) / b n) ^ 2)) * ((((4 / 3 : ℝ) / b n) ^ 2) ^ j)
    rw [← hpowB]
    exact termB_le hpos hratio n hn j
  have hBub : (∑' j, (b n : ℝ) ^ 2 / b (n + 2 + j))
      ≤ (32 / 21) * (((4 / 3 : ℝ) / b n) ^ 2) := by
    calc (∑' j, (b n : ℝ) ^ 2 / b (n + 2 + j))
        ≤ ((4 / 3 : ℝ) * (((4 / 3 : ℝ) / b n) ^ 2))
          * (1 - (((4 / 3 : ℝ) / b n) ^ 2))⁻¹ := hBle
      _ ≤ ((4 / 3 : ℝ) * (((4 / 3 : ℝ) / b n) ^ 2)) * (8 / 7) :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = (32 / 21) * (((4 / 3 : ℝ) / b n) ^ 2) := by ring
  have heq : (32 / 21 : ℝ) * (((4 / 3 : ℝ) / b n) ^ 2) = (512 / 189) / (b n) ^ 2 := by
    have hbne : (b n : ℝ) ≠ 0 := by exact_mod_cast (hpos n).ne'
    field_simp
    ring
  rw [heq] at hBub
  exact hBub

/-- The remainder is the tail sum. -/
private theorem tail_tsum {b : ℕ → ℕ} {r : ℝ}
    (hsum : HasSum (fun n => 1 / (b n : ℝ)) r) (m : ℕ) :
    r - ∑ k ∈ Finset.range m, 1 / (b k : ℝ) = ∑' j, 1 / (b (m + j) : ℝ) := by
  have h0 := ((hasSum_nat_add_iff' m).mpr hsum).tsum_eq
  rw [← h0]
  apply tsum_congr
  intro j
  rw [add_comm j m]

/-- The `A` series is `aₙ` times the tail of reciprocals. -/
private theorem A_eq_mul_tail (b : ℕ → ℕ) (n : ℕ) :
    (∑' j, (b n : ℝ) / b (n + 1 + j))
      = (b n : ℝ) * (∑' j, 1 / (b (n + 1 + j) : ℝ)) := by
  have h : (fun j => (b n : ℝ) / b (n + 1 + j))
      = (fun j => (b n : ℝ) * (1 / (b (n + 1 + j) : ℝ))) := by
    funext j
    rw [mul_one_div]
  rw [h, tsum_mul_left]

/-- The remainder splits off its first term. -/
private theorem remainder_split {b : ℕ → ℕ} {r : ℝ}
    (hsum : HasSum (fun n => 1 / (b n : ℝ)) r) (n : ℕ) :
    r - ∑ k ∈ Finset.range n, 1 / (b k : ℝ)
      = 1 / (b n : ℝ) + (∑' j, 1 / (b (n + 1 + j) : ℝ)) := by
  have htail := tail_tsum hsum (n + 1)
  have hsum_succ : ∑ k ∈ Finset.range (n + 1), 1 / (b k : ℝ)
      = (∑ k ∈ Finset.range n, 1 / (b k : ℝ)) + 1 / (b n : ℝ) :=
    Finset.sum_range_succ _ n
  have htail2 : r - ∑ k ∈ Finset.range (n + 1), 1 / (b k : ℝ)
      = ∑' j, 1 / (b (n + 1 + j) : ℝ) := by
    rw [htail]
  have hsplit : r - ∑ k ∈ Finset.range n, 1 / (b k : ℝ) = 1 / (b n : ℝ)
      + (r - ∑ k ∈ Finset.range (n + 1), 1 / (b k : ℝ)) := by
    rw [hsum_succ]
    ring
  rw [hsplit, htail2]

/-- The `A` series splits off its first term. -/
private theorem A_split {b : ℕ → ℕ} (hpos : ∀ n, 0 < b n)
    (hratio : ∀ n, |(b n : ℝ) ^ 2 / b (n + 1) - 1| ≤ 1 / 3) (n : ℕ)
    (hn : (15 : ℝ) ≤ b n) :
    (∑' j, (b n : ℝ) / b (n + 1 + j))
      = (b n : ℝ) / b (n + 1) + (∑' j, (b n : ℝ) / b (n + 2 + j)) := by
  have hsA := summable_A hpos hratio n hn
  have h := Summable.tsum_eq_zero_add hsA
  have e0 : (b n : ℝ) / b (n + 1 + 0) = (b n : ℝ) / b (n + 1) := by rw [add_zero]
  have e1 : (fun j => (b n : ℝ) / b (n + 1 + (j + 1)))
      = (fun j => (b n : ℝ) / b (n + 2 + j)) := by
    funext j
    rw [show n + 1 + (j + 1) = n + 2 + j by omega]
  rw [e0, e1] at h
  exact h

/-- The tail of the `A` series is `B / aₙ`. -/
private theorem Atail_eq {b : ℕ → ℕ} (hpos : ∀ n, 0 < b n) (n : ℕ) :
    (∑' j, (b n : ℝ) / b (n + 2 + j))
      = (∑' j, (b n : ℝ) ^ 2 / b (n + 2 + j)) / (b n : ℝ) := by
  have hbne : (b n : ℝ) ≠ 0 := by exact_mod_cast (hpos n).ne'
  have h : (fun j => (b n : ℝ) / b (n + 2 + j))
      = (fun j => (1 / (b n : ℝ)) * ((b n : ℝ) ^ 2 / b (n + 2 + j))) := by
    funext j
    have hD : ((b (n + 2 + j) : ℝ)) ≠ 0 := by exact_mod_cast (hpos _).ne'
    field_simp
  rw [h, tsum_mul_left]
  conv_rhs => rw [div_eq_mul_one_div]
  ring

/-- The reciprocal expansion identity: `y⁻¹ + ratio - aₙ = C - B`. -/
private theorem reciprocal_id {b : ℕ → ℕ} (hpos : ∀ n, 0 < b n)
    (hratio : ∀ n, |(b n : ℝ) ^ 2 / b (n + 1) - 1| ≤ 1 / 3) {r : ℝ}
    (hsum : HasSum (fun n => 1 / (b n : ℝ)) r) (n : ℕ) (hn : (15 : ℝ) ≤ b n) :
    (r - ∑ k ∈ Finset.range n, 1 / (b k : ℝ))⁻¹ + (b n : ℝ) ^ 2 / b (n + 1) - b n
      = (b n : ℝ) * (∑' j, (b n : ℝ) / b (n + 1 + j)) ^ 2
          / (1 + (∑' j, (b n : ℝ) / b (n + 1 + j)))
        - (∑' j, (b n : ℝ) ^ 2 / b (n + 2 + j)) := by
  have hb : (0 : ℝ) < b n := by exact_mod_cast hpos n
  have hbne : (b n : ℝ) ≠ 0 := ne_of_gt hb
  have hb1ne : ((b (n + 1) : ℝ)) ≠ 0 := by exact_mod_cast (hpos _).ne'
  have hsplit := remainder_split hsum n
  have hAeq := A_eq_mul_tail b n
  have hRge : 0 ≤ ∑' j, 1 / (b (n + 1 + j) : ℝ) := tsum_nonneg (fun j => by positivity)
  have hAge0 : 0 ≤ ∑' j, (b n : ℝ) / b (n + 1 + j) := tsum_nonneg (fun j => by positivity)
  have hA1 : (1 : ℝ) + (∑' j, (b n : ℝ) / b (n + 1 + j)) ≠ 0 := by
    have hpos1 : (0 : ℝ) < 1 + (∑' j, (b n : ℝ) / b (n + 1 + j)) := by linarith
    exact ne_of_gt hpos1
  have y_eq : (r - ∑ k ∈ Finset.range n, 1 / (b k : ℝ)) * (b n : ℝ)
      = 1 + (∑' j, (b n : ℝ) / b (n + 1 + j)) := by
    have h1 : (1 / (b n : ℝ)) * b n = 1 := one_div_mul_cancel hbne
    rw [hsplit, hAeq, add_mul, h1]
    ring
  have hypos : (0 : ℝ) < r - ∑ k ∈ Finset.range n, 1 / (b k : ℝ) := by
    rw [hsplit]
    have h1 : (0 : ℝ) < 1 / (b n : ℝ) := one_div_pos.mpr hb
    linarith
  have hy0 : (r - ∑ k ∈ Finset.range n, 1 / (b k : ℝ)) ≠ 0 := ne_of_gt hypos
  have y_inv : (r - ∑ k ∈ Finset.range n, 1 / (b k : ℝ))⁻¹
      = (b n : ℝ) / (1 + (∑' j, (b n : ℝ) / b (n + 1 + j))) := by
    rw [eq_div_iff hA1, ← y_eq, ← mul_assoc, inv_mul_cancel₀ hy0, one_mul]
  have alg : (b n : ℝ) / (1 + (∑' j, (b n : ℝ) / b (n + 1 + j)))
      = (b n : ℝ) - (b n : ℝ) * (∑' j, (b n : ℝ) / b (n + 1 + j))
        + (b n : ℝ) * (∑' j, (b n : ℝ) / b (n + 1 + j)) ^ 2
          / (1 + (∑' j, (b n : ℝ) / b (n + 1 + j))) := by
    field_simp
    ring
  have hAsplit := A_split hpos hratio n hn
  have hAtail := Atail_eq hpos n
  have bA_eq : (b n : ℝ) * (∑' j, (b n : ℝ) / b (n + 1 + j))
      = (b n : ℝ) ^ 2 / b (n + 1) + (∑' j, (b n : ℝ) ^ 2 / b (n + 2 + j)) := by
    rw [hAsplit, hAtail]
    field_simp
  rw [y_inv, alg]
  linarith [bA_eq]

/-- A constant divided by the sequence tends to zero. -/
private theorem tendsto_const_div {b : ℕ → ℕ} {r : ℝ}
    (hsum : HasSum (fun n => 1 / (b n : ℝ)) r) (K : ℝ) :
    Tendsto (fun n => K / (b n : ℝ)) atTop (𝓝 0) := by
  have h10 : Tendsto (fun n => 1 / (b n : ℝ)) atTop (𝓝 0) :=
    hsum.summable.tendsto_atTop_zero
  have h := Filter.Tendsto.const_mul K h10
  simpa only [mul_one_div, mul_zero] using h

/-- Recovery of each large term by rounding (Theorem 1 with `β = 1`, first part). -/
private theorem floor_eq {b : ℕ → ℕ} (hpos : ∀ n, 0 < b n)
    (hratio : ∀ n, |(b n : ℝ) ^ 2 / b (n + 1) - 1| ≤ 1 / 3) {r : ℝ}
    (hsum : HasSum (fun n => 1 / (b n : ℝ)) r) (n : ℕ) (hn : (15 : ℝ) ≤ b n) :
    (b n : ℤ) = ⌊(r - ∑ k ∈ Finset.range n, 1 / (b k : ℝ))⁻¹ + 1 + 1 / 2⌋ := by
  have hb : (0 : ℝ) < b n := by exact_mod_cast hpos n
  have hA2 := tsum_A_le hpos hratio n hn
  have hB := tsum_B_le hpos hratio n hn
  have hAge0 : 0 ≤ ∑' j, (b n : ℝ) / b (n + 1 + j) :=
    tsum_nonneg (fun j => by positivity)
  have hBge0 : 0 ≤ ∑' j, (b n : ℝ) ^ 2 / b (n + 2 + j) :=
    tsum_nonneg (fun j => by positivity)
  have hCge : 0 ≤ (b n : ℝ) * (∑' j, (b n : ℝ) / b (n + 1 + j)) ^ 2
      / (1 + (∑' j, (b n : ℝ) / b (n + 1 + j))) := by
    apply div_nonneg _ (by linarith)
    exact mul_nonneg (by positivity) (sq_nonneg _)
  have hCle : (b n : ℝ) * (∑' j, (b n : ℝ) / b (n + 1 + j)) ^ 2
        / (1 + (∑' j, (b n : ℝ) / b (n + 1 + j)))
      ≤ (b n : ℝ) * (∑' j, (b n : ℝ) / b (n + 1 + j)) ^ 2 := by
    have hnn : (0 : ℝ) ≤ (b n : ℝ) * (∑' j, (b n : ℝ) / b (n + 1 + j)) ^ 2 :=
      mul_nonneg (by positivity) (sq_nonneg _)
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 + (∑' j, (b n : ℝ) / b (n + 1 + j)))]
    exact le_mul_of_one_le_right hnn (by linarith)
  have hnumA : (b n : ℝ) * (∑' j, (b n : ℝ) / b (n + 1 + j)) ^ 2 < 1 / 6 := by
    have h1 : ((1024 / 441 : ℝ)) / b n ≤ 1024 / 6615 := by
      rw [div_le_div_iff₀ hb (by norm_num)]
      linarith [hn]
    have h2 : (1024 / 6615 : ℝ) < 1 / 6 := by norm_num
    exact lt_of_le_of_lt (le_trans hA2 h1) h2
  have hnumB : (∑' j, (b n : ℝ) ^ 2 / b (n + 2 + j)) < 1 / 6 := by
    have hsq : (225 : ℝ) ≤ (b n) ^ 2 := by
      have hb0 : (0 : ℝ) ≤ b n := hb.le
      nlinarith [hn, hb0, sq_nonneg ((b n : ℝ) - 15)]
    have h1 : ((512 / 189 : ℝ)) / (b n) ^ 2 ≤ 512 / 42525 := by
      rw [div_le_div_iff₀ (pow_pos hb 2) (by norm_num)]
      linarith [hsq]
    have h2 : (512 / 42525 : ℝ) < 1 / 6 := by norm_num
    exact lt_of_le_of_lt (le_trans hB h1) h2
  have hClt : (b n : ℝ) * (∑' j, (b n : ℝ) / b (n + 1 + j)) ^ 2
      / (1 + (∑' j, (b n : ℝ) / b (n + 1 + j))) < 1 / 6 :=
    lt_of_le_of_lt hCle hnumA
  have hCB : |(b n : ℝ) * (∑' j, (b n : ℝ) / b (n + 1 + j)) ^ 2
      / (1 + (∑' j, (b n : ℝ) / b (n + 1 + j)))
      - (∑' j, (b n : ℝ) ^ 2 / b (n + 2 + j))| < 1 / 6 := by
    rw [abs_lt]
    constructor <;> linarith
  have hmain : |(r - ∑ k ∈ Finset.range n, 1 / (b k : ℝ))⁻¹ + 1 - b n| < 1 / 2 := by
    have hrid := reciprocal_id hpos hratio hsum n hn
    have hr := hratio n
    have heq : (r - ∑ k ∈ Finset.range n, 1 / (b k : ℝ))⁻¹ + 1 - b n
        = ((b n : ℝ) * (∑' j, (b n : ℝ) / b (n + 1 + j)) ^ 2
          / (1 + (∑' j, (b n : ℝ) / b (n + 1 + j)))
          - (∑' j, (b n : ℝ) ^ 2 / b (n + 2 + j)))
          + (1 - (b n : ℝ) ^ 2 / b (n + 1)) := by
      linarith
    rw [heq]
    calc |(b n : ℝ) * (∑' j, (b n : ℝ) / b (n + 1 + j)) ^ 2
            / (1 + (∑' j, (b n : ℝ) / b (n + 1 + j)))
            - (∑' j, (b n : ℝ) ^ 2 / b (n + 2 + j))
            + (1 - (b n : ℝ) ^ 2 / b (n + 1))|
          ≤ |(b n : ℝ) * (∑' j, (b n : ℝ) / b (n + 1 + j)) ^ 2
            / (1 + (∑' j, (b n : ℝ) / b (n + 1 + j)))
            - (∑' j, (b n : ℝ) ^ 2 / b (n + 2 + j))|
            + |1 - (b n : ℝ) ^ 2 / b (n + 1)| := abs_add_le _ _
      _ < 1 / 6 + 1 / 3 := by
          have hrr : |1 - (b n : ℝ) ^ 2 / b (n + 1)| ≤ 1 / 3 := by
            rw [abs_sub_comm]
            exact hr
          linarith
      _ = 1 / 2 := by norm_num
  symm
  rw [Int.floor_eq_iff]
  simp only [Int.cast_natCast]
  have hlt := abs_lt.mp hmain
  constructor <;> linarith

/-- The gap tends to zero (Theorem 1 with `β = 1`, second part). -/
private theorem gap_tendsto {b : ℕ → ℕ} (hpos : ∀ n, 0 < b n)
    (hratio : ∀ n, |(b n : ℝ) ^ 2 / b (n + 1) - 1| ≤ 1 / 3)
    (hbig : ∀ n, (15 : ℝ) ≤ b n) {r : ℝ}
    (hsum : HasSum (fun n => 1 / (b n : ℝ)) r)
    (hlim : Tendsto (fun n => (b n : ℝ) ^ 2 / b (n + 1)) atTop (𝓝 1)) :
    Tendsto (fun n => (r - ∑ k ∈ Finset.range n, 1 / (b k : ℝ))⁻¹ + 1 - b n)
      atTop (𝓝 0) := by
  have hC0 : Tendsto (fun n => (b n : ℝ) * (∑' j, (b n : ℝ) / b (n + 1 + j)) ^ 2
      / (1 + (∑' j, (b n : ℝ) / b (n + 1 + j)))) atTop (𝓝 0) := by
    have hCf : ∀ n, 0 ≤ (b n : ℝ) * (∑' j, (b n : ℝ) / b (n + 1 + j)) ^ 2
        / (1 + (∑' j, (b n : ℝ) / b (n + 1 + j))) := by
      intro n
      apply div_nonneg _ _
      · exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
      · have hA : 0 ≤ (∑' j, (b n : ℝ) / b (n + 1 + j)) :=
          tsum_nonneg (fun j => by positivity)
        linarith
    have hft : ∀ n, (b n : ℝ) * (∑' j, (b n : ℝ) / b (n + 1 + j)) ^ 2
          / (1 + (∑' j, (b n : ℝ) / b (n + 1 + j)))
        ≤ (1024 / 441 : ℝ) / b n := by
      intro n
      have hAge0 : 0 ≤ ∑' j, (b n : ℝ) / b (n + 1 + j) :=
        tsum_nonneg (fun j => by positivity)
      have hnn : (0 : ℝ) ≤ (b n : ℝ) * (∑' j, (b n : ℝ) / b (n + 1 + j)) ^ 2 :=
        mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
      have hCle : (b n : ℝ) * (∑' j, (b n : ℝ) / b (n + 1 + j)) ^ 2
          / (1 + (∑' j, (b n : ℝ) / b (n + 1 + j)))
          ≤ (b n : ℝ) * (∑' j, (b n : ℝ) / b (n + 1 + j)) ^ 2 := by
        rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 + (∑' j, (b n : ℝ) / b (n + 1 + j)))]
        exact le_mul_of_one_le_right hnn (by linarith)
      exact le_trans hCle (tsum_A_le hpos hratio n (hbig n))
    exact squeeze_zero hCf hft (tendsto_const_div hsum (1024 / 441))
  have hBbound : ∀ n, (∑' j, (b n : ℝ) ^ 2 / b (n + 2 + j)) ≤ (512 / 189 : ℝ) / b n := by
    intro n
    have hb1 : (1 : ℝ) ≤ b n := by linarith [hbig n]
    have hsq : (b n : ℝ) ≤ (b n) ^ 2 := by
      have he : (b n : ℝ) ^ 2 - b n = (b n) * ((b n) - 1) := by ring
      have hnn : (0 : ℝ) ≤ (b n) * ((b n) - 1) :=
        mul_nonneg (by positivity) (by linarith)
      linarith
    have hle : ((512 / 189 : ℝ)) / (b n) ^ 2 ≤ (512 / 189 : ℝ) / b n := by
      have hpos2 : (0 : ℝ) < (b n) ^ 2 := pow_pos (by linarith [hbig n]) 2
      have hpos1 : (0 : ℝ) < b n := by linarith [hbig n]
      rw [div_le_div_iff₀ hpos2 hpos1]
      linarith [hsq]
    exact le_trans (tsum_B_le hpos hratio n (hbig n)) hle
  have hB0 : Tendsto (fun n => (∑' j, (b n : ℝ) ^ 2 / b (n + 2 + j))) atTop (𝓝 0) :=
    squeeze_zero (fun n => tsum_nonneg (fun j => by positivity)) hBbound
      (tendsto_const_div hsum (512 / 189))
  have hCB0 : Tendsto (fun n => (b n : ℝ) * (∑' j, (b n : ℝ) / b (n + 1 + j)) ^ 2
      / (1 + (∑' j, (b n : ℝ) / b (n + 1 + j)))
      - (∑' j, (b n : ℝ) ^ 2 / b (n + 2 + j))) atTop (𝓝 0) := by
    simpa using hC0.sub hB0
  have hratio0 : Tendsto (fun n => 1 - (b n : ℝ) ^ 2 / b (n + 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa using h1.sub hlim
  have hgap0 : Tendsto (fun n => ((b n : ℝ) * (∑' j, (b n : ℝ) / b (n + 1 + j)) ^ 2
      / (1 + (∑' j, (b n : ℝ) / b (n + 1 + j)))
      - (∑' j, (b n : ℝ) ^ 2 / b (n + 2 + j)))
      + (1 - (b n : ℝ) ^ 2 / b (n + 1))) atTop (𝓝 0) := by
    simpa using hCB0.add hratio0
  apply Tendsto.congr _ hgap0
  intro n
  have hrid := reciprocal_id hpos hratio hsum n (hbig n)
  linarith

/-- A tail satisfying the rounding rule is the pseudo-greedy expansion. -/
private theorem tail_eq_expansion {b : ℕ → ℕ} {r : ℝ}
    (hfloor : ∀ k, (b k : ℤ)
      = ⌊(r - ∑ i ∈ Finset.range k, 1 / (b i : ℝ))⁻¹ + 1 + 1 / 2⌋) :
    (∀ k, pseudoGreedyRemainder r k = r - ∑ i ∈ Finset.range k, 1 / (b i : ℝ)) ∧
    (∀ k, (b k : ℤ) = pseudoGreedyExpansion r k) := by
  have hrem : ∀ k, pseudoGreedyRemainder r k
      = r - ∑ i ∈ Finset.range k, 1 / (b i : ℝ) := by
    intro k
    induction k with
    | zero => simp [pseudoGreedyRemainder]
    | succ k ih =>
      have hexp : pseudoGreedyExpansion r k = (b k : ℤ) := by
        change ⌊(pseudoGreedyRemainder r k)⁻¹ + 1 + 1 / 2⌋ = _
        rw [ih]
        exact (hfloor k).symm
      have hcast : ((pseudoGreedyExpansion r k : ℤ) : ℝ) = (b k : ℝ) := by
        rw [hexp]
        simp
      rw [pseudoGreedyRemainder_succ, ih, hcast, Finset.sum_range_succ]
      ring
  refine ⟨hrem, fun k => ?_⟩
  change (b k : ℤ) = ⌊(pseudoGreedyRemainder r k)⁻¹ + 1 + 1 / 2⌋
  rw [hrem k]
  exact hfloor k

/-- **Tails that are pseudo-greedy expansions.** Let $(a_n)_{n \ge 0}$ be a sequence of positive
integers with $a_n^2 / a_{n+1} \to 1$ such that $\sum_n 1 / a_n$ converges. Then there is a
natural number $N$ such that, with $r = \sum_{k \ge 0} 1 / a_{N+k}$, the tail
$(a_{N+n})_{n \ge 0}$ is the pseudo-greedy expansion of $r$, and the gap sequence of this
expansion tends to $0$.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Corollary 3 (`integers-2026-A28-cor-3`). -/
theorem exists_tail_eq_pseudoGreedyExpansion {a : ℕ → ℕ} (hpos : ∀ n, 0 < a n)
    (hratio : Tendsto (fun n => (a n : ℝ) ^ 2 / a (n + 1)) atTop (𝓝 1))
    (hsum : Summable fun n => 1 / (a n : ℝ)) :
    ∃ N : ℕ,
      (∀ n, (a (N + n) : ℤ) = pseudoGreedyExpansion (∑' k, 1 / (a (N + k) : ℝ)) n) ∧
      Tendsto (pseudoGreedyGap (∑' k, 1 / (a (N + k) : ℝ))) atTop (𝓝 0) := by
  have hev_ratio : ∀ᶠ n in atTop, |(a n : ℝ) ^ 2 / a (n + 1) - 1| ≤ 1 / 3 := by
    have hmem : ∀ᶠ x in 𝓝 (1 : ℝ), |x - 1| ≤ 1 / 3 := by
      have hball : Metric.ball (1 : ℝ) (1 / 3) ∈ 𝓝 (1 : ℝ) :=
        Metric.ball_mem_nhds _ (by norm_num)
      filter_upwards [hball] with x hx
      simp only [Metric.mem_ball, Real.dist_eq] at hx
      exact le_of_lt hx
    exact hratio.eventually hmem
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hev_ratio
  have h10 : Tendsto (fun n => 1 / (a n : ℝ)) atTop (𝓝 0) := hsum.tendsto_atTop_zero
  have hev_big : ∀ᶠ n in atTop, (15 : ℝ) ≤ a n := by
    have hmem : ∀ᶠ x in 𝓝 (0 : ℝ), x < 1 / 15 := eventually_lt_nhds (by norm_num)
    have h := h10.eventually hmem
    filter_upwards [h] with n hn
    have hapos : (0 : ℝ) < a n := by exact_mod_cast hpos n
    have hlt : (15 : ℝ) < a n :=
      (one_div_lt_one_div hapos (by norm_num : (0 : ℝ) < 15)).mp hn
    exact le_of_lt hlt
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp hev_big
  have hge1 : ∀ k, N₁ ≤ (N₁ + N₂) + k := fun k => by omega
  have hge2 : ∀ k, N₂ ≤ (N₁ + N₂) + k := fun k => by omega
  have hpos' : ∀ k, 0 < a ((N₁ + N₂) + k) := fun k => hpos _
  have hratio' : ∀ k, |(a ((N₁ + N₂) + k) : ℝ) ^ 2 / (a ((N₁ + N₂) + (k + 1)) : ℝ)
      - 1| ≤ 1 / 3 := by
    intro k
    have h := hN₁ ((N₁ + N₂) + k) (hge1 k)
    have e : (N₁ + N₂) + (k + 1) = ((N₁ + N₂) + k) + 1 := by omega
    rw [e]
    exact h
  have hbig' : ∀ k, (15 : ℝ) ≤ a ((N₁ + N₂) + k) := fun k => hN₂ _ (hge2 k)
  have htail_sum : Summable (fun k => 1 / (a ((N₁ + N₂) + k) : ℝ)) := by
    have h := (summable_nat_add_iff (N₁ + N₂)).mpr hsum
    simpa only [add_comm _ (N₁ + N₂)] using h
  have htail_has : HasSum (fun k => 1 / (a ((N₁ + N₂) + k) : ℝ))
      (∑' k, 1 / (a ((N₁ + N₂) + k) : ℝ)) :=
    htail_sum.hasSum
  have htail_lim : Tendsto
      (fun k => (a ((N₁ + N₂) + k) : ℝ) ^ 2 / a ((N₁ + N₂) + (k + 1)))
      atTop (𝓝 1) := by
    have h := (tendsto_add_atTop_iff_nat (N₁ + N₂)).mpr hratio
    apply Tendsto.congr _ h
    intro k
    show (a (k + (N₁ + N₂)) : ℝ) ^ 2 / a (k + (N₁ + N₂) + 1)
      = (a ((N₁ + N₂) + k) : ℝ) ^ 2 / a ((N₁ + N₂) + (k + 1))
    rw [add_comm k (N₁ + N₂)]
    rw [show (N₁ + N₂) + k + 1 = (N₁ + N₂) + (k + 1) by omega]
  have hfloor_all : ∀ k, (a ((N₁ + N₂) + k) : ℤ)
      = ⌊(∑' k, 1 / (a ((N₁ + N₂) + k) : ℝ)
        - ∑ i ∈ Finset.range k, 1 / (a ((N₁ + N₂) + i) : ℝ))⁻¹ + 1 + 1 / 2⌋ :=
    fun k => floor_eq (b := fun k => a ((N₁ + N₂) + k)) hpos' hratio' htail_has k
      (hbig' k)
  have htail := tail_eq_expansion (b := fun k => a ((N₁ + N₂) + k)) hfloor_all
  have hgap := gap_tendsto (b := fun k => a ((N₁ + N₂) + k)) hpos' hratio' hbig'
    htail_has htail_lim
  refine ⟨N₁ + N₂, fun n => htail.2 n, ?_⟩
  apply Tendsto.congr _ hgap
  intro n
  have hrem_n := htail.1 n
  have hexp_n := htail.2 n
  change (∑' k, 1 / (a ((N₁ + N₂) + k) : ℝ)
      - ∑ i ∈ Finset.range n, 1 / (a ((N₁ + N₂) + i) : ℝ))⁻¹
      + 1 - (a ((N₁ + N₂) + n) : ℝ)
      = pseudoGreedyGap (∑' k, 1 / (a ((N₁ + N₂) + k) : ℝ)) n
  have hgap_eq : pseudoGreedyGap (∑' k, 1 / (a ((N₁ + N₂) + k) : ℝ)) n
      = (∑' k, 1 / (a ((N₁ + N₂) + k) : ℝ)
        - ∑ i ∈ Finset.range n, 1 / (a ((N₁ + N₂) + i) : ℝ))⁻¹
        + 1 - (a ((N₁ + N₂) + n) : ℝ) := by
    change (pseudoGreedyRemainder (∑' k, 1 / (a ((N₁ + N₂) + k) : ℝ)) n)⁻¹ + 1
        - (pseudoGreedyExpansion (∑' k, 1 / (a ((N₁ + N₂) + k) : ℝ)) n : ℝ)
        = _
    rw [hrem_n, ← hexp_n, Int.cast_natCast]
  exact hgap_eq.symm

end

end MetaMathlibExt
