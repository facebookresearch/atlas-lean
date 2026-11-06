/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

section

namespace MetaMathlibExt

/-- The dominant root exceeds 1: from `α ^ k = ∑ i ∈ range k, α ^ i`, the sum
contains the terms `1` and `α`, so `α ^ k > 1`, forcing `α > 1`. -/
private theorem alpha_gt_one (k : ℕ) (hk : 2 ≤ k) (α : ℝ) (hαpos : 0 < α)
    (hαroot : α ^ k = ∑ i ∈ Finset.range k, α ^ i) : 1 < α := by
  by_contra h
  push Not at h
  have hpow : α ^ k ≤ 1 := by
    calc α ^ k ≤ 1 ^ k := by
          apply pow_le_pow_left₀ hαpos.le h k
      _ = 1 := one_pow k
  have hsum : (1 : ℝ) < ∑ i ∈ Finset.range k, α ^ i := by
    have h01 : ({0, 1} : Finset ℕ) ⊆ Finset.range k := by
      intro x hx
      simp at hx
      simp
      omega
    have hnn : ∀ i ∈ Finset.range k, i ∉ ({0, 1} : Finset ℕ) → (0 : ℝ) ≤ α ^ i := by
      intro i _ _
      exact pow_nonneg hαpos.le i
    have hle := Finset.sum_le_sum_of_subset_of_nonneg h01 hnn
    have hval : ∑ i ∈ ({0, 1} : Finset ℕ), α ^ i = 1 + α := by simp
    linarith
  linarith [hαroot]

/-- Key algebraic identity: the geometric-sum formula turns `hαroot` into
`α ^ k * (2 - α) = 1`. -/
private theorem alpha_key_identity (k : ℕ) (α : ℝ) (hα1 : 1 < α)
    (hαroot : α ^ k = ∑ i ∈ Finset.range k, α ^ i) :
    α ^ k * (2 - α) = 1 := by
  have hne : α - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hα1)
  have hgeom := geom_sum_mul (α : ℝ) k
  rw [← hαroot] at hgeom
  have h2 : α ^ k * (α - 2) = -1 := by linarith
  linarith

/-- The dominant root is below 2, since `α ^ k > 0` and `α ^ k * (2 - α) = 1`. -/
private theorem alpha_lt_two (k : ℕ) (α : ℝ) (hαpos : 0 < α)
    (hkey : α ^ k * (2 - α) = 1) : α < 2 := by
  by_contra h
  push Not at h
  have hpow : (0 : ℝ) < α ^ k := pow_pos hαpos k
  have hle : α ^ k * (2 - α) ≤ 0 := by
    apply mul_nonpos_of_nonneg_of_nonpos hpow.le
    linarith
  linarith

/-- Since `α > 1`, every term `α ^ i ≥ 1`, so the root equation gives `k ≤ α ^ k`. -/
private theorem alpha_pow_ge (k : ℕ) (α : ℝ) (hα1 : 1 < α)
    (hαroot : α ^ k = ∑ i ∈ Finset.range k, α ^ i) : (k : ℝ) ≤ α ^ k := by
  rw [hαroot]
  calc (k : ℝ) = ∑ _i ∈ Finset.range k, (1 : ℝ) := by simp
    _ ≤ ∑ i ∈ Finset.range k, α ^ i := by
        apply Finset.sum_le_sum
        intro i _
        exact one_le_pow₀ hα1.le

/-- The root sum is strictly larger than `k`, since its `i = 1` term is larger than 1. -/
private theorem ddb_alpha_pow_gt (k : ℕ) (hk : 2 ≤ k) (α : ℝ) (hα1 : 1 < α)
    (hαroot : α ^ k = ∑ i ∈ Finset.range k, α ^ i) : (k : ℝ) < α ^ k := by
  rw [hαroot]
  calc
    (k : ℝ) = ∑ _i ∈ Finset.range k, (1 : ℝ) := by simp
    _ < ∑ i ∈ Finset.range k, α ^ i := by
      apply Finset.sum_lt_sum
      · intro i _
        exact one_le_pow₀ hα1.le
      · refine ⟨1, by simp; omega, ?_⟩
        simpa using hα1

/-- A lower bound tailored to the initial error at index zero. -/
private theorem ddb_alpha_pow_pred_gt (k : ℕ) (hk : 2 ≤ k) (α : ℝ) (hα1 : 1 < α)
    (hαroot : α ^ k = ∑ i ∈ Finset.range k, α ^ i) :
    ((k : ℝ) + 1) / 2 < α ^ (k - 1) := by
  rcases eq_or_lt_of_le hk with rfl | hk3
  · simp only [Nat.cast_ofNat, Nat.reduceSubDiff, pow_one]
    have hroot : α ^ 2 = α + 1 := by simpa using hαroot
    by_contra h
    push Not at h
    have hmul := mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ α by linarith)
    nlinarith
  · have hsum : 1 + ((k : ℝ) - 1) * α ≤ α ^ k := by
      have hsplit : ∑ i ∈ Finset.range k, α ^ i =
          (∑ i ∈ Finset.range (k - 1), α ^ (i + 1)) + 1 := by
        rw [show k = (k - 1) + 1 by omega, Finset.sum_range_succ']
        simp
      rw [hαroot, hsplit]
      have hs : ∑ _i ∈ Finset.range (k - 1), α ≤
          ∑ i ∈ Finset.range (k - 1), α ^ (i + 1) := by
        apply Finset.sum_le_sum
        intro i _
        simpa using pow_le_pow_right₀ hα1.le (show 1 ≤ i + 1 by omega)
      calc
        1 + ((k : ℝ) - 1) * α = (∑ _i ∈ Finset.range (k - 1), α) + 1 := by
          simp [Nat.cast_sub (show 1 ≤ k by omega), add_comm]
        _ ≤ (∑ i ∈ Finset.range (k - 1), α ^ (i + 1)) + 1 :=
          by simpa [add_comm] using add_le_add_right hs 1
    have hpow : α ^ k = α ^ (k - 1) * α := by
      calc
        α ^ k = α ^ ((k - 1) + 1) := by
          congr 1
          omega
        _ = α ^ (k - 1) * α := by rw [pow_succ]
    have hk3r : (3 : ℝ) ≤ k := by exact_mod_cast (show 3 ≤ k by omega)
    have hnonneg : 0 ≤ ((k : ℝ) - 3) * α :=
      mul_nonneg (sub_nonneg.mpr hk3r) (by linarith)
    nlinarith

/-- The Binet coefficient denominator is positive: from `α ^ k * (2 - α) = 1`,
`2 - α = 1 / α ^ k`, and `(k + 1) / α ^ k ≤ (k + 1) / k ≤ 3 / 2 < 2`. -/
private theorem denom_pos (k : ℕ) (hk : 2 ≤ k) (α : ℝ) (hα1 : 1 < α)
    (hkey : α ^ k * (2 - α) = 1) (hge : (k : ℝ) ≤ α ^ k) :
    0 < 2 + ((k : ℝ) + 1) * (α - 2) := by
  have hαk : (0 : ℝ) < α ^ k := by positivity
  have h2α : 0 < 2 - α := by
    by_contra h
    push Not at h
    have hle : α ^ k * (2 - α) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hαk.le h
    linarith [hkey]
  have h21 : (2 : ℝ) - α = 1 / α ^ k := by
    field_simp
    linarith [hkey]
  have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h1 : ((k : ℝ) + 1) / α ^ k ≤ 3 / 2 := by
    rw [div_le_iff₀ hαk]
    nlinarith [hge, hk2]
  have hbound : ((k : ℝ) + 1) * (2 - α) < 2 := by
    rw [h21, mul_one_div]
    linarith
  linarith

/-- The Binet coefficient `c = (α - 1) / (2 + (k + 1) * (α - 2))` is positive. -/
private theorem c_pos (k : ℕ) (α : ℝ) (hα1 : 1 < α)
    (hden : 0 < 2 + ((k : ℝ) + 1) * (α - 2)) :
    0 < (α - 1) / (2 + ((k : ℝ) + 1) * (α - 2)) := by
  apply div_pos _ hden
  linarith

/-- The dominant coefficient is larger than one half. -/
private theorem ddb_c_gt_half (k : ℕ) (hk : 2 ≤ k) (α : ℝ) (hαlt : α < 2)
    (hden : 0 < 2 + ((k : ℝ) + 1) * (α - 2)) :
    (1 : ℝ) / 2 < (α - 1) / (2 + ((k : ℝ) + 1) * (α - 2)) := by
  rw [lt_div_iff₀ hden]
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hprod : 0 < ((k : ℝ) - 1) * (2 - α) :=
    mul_pos (sub_pos.mpr hk1) (sub_pos.mpr hαlt)
  nlinarith

/-- The dominant coefficient is smaller than one. -/
private theorem ddb_c_lt_one (k : ℕ) (α : ℝ) (hαlt : α < 2)
    (hkey : α ^ k * (2 - α) = 1) (hpow : (k : ℝ) < α ^ k)
    (hden : 0 < 2 + ((k : ℝ) + 1) * (α - 2)) :
    (α - 1) / (2 + ((k : ℝ) + 1) * (α - 2)) < 1 := by
  rw [div_lt_iff₀ hden]
  have hmul : (k : ℝ) * (2 - α) < α ^ k * (2 - α) :=
    mul_lt_mul_of_pos_right hpow (sub_pos.mpr hαlt)
  rw [hkey] at hmul
  nlinarith

/-- The initial Binet term at index zero is smaller than one half. -/
private theorem ddb_c_div_alpha_lt_half (k : ℕ) (hk : 2 ≤ k) (α : ℝ)
    (hαpos : 0 < α) (hαlt : α < 2) (hkey : α ^ k * (2 - α) = 1)
    (hpred : ((k : ℝ) + 1) / 2 < α ^ (k - 1))
    (hden : 0 < 2 + ((k : ℝ) + 1) * (α - 2)) :
    ((α - 1) / (2 + ((k : ℝ) + 1) * (α - 2))) / α < 1 / 2 := by
  rw [div_lt_iff₀ hαpos, div_lt_iff₀ hden]
  have hpred' : (k : ℝ) + 1 < 2 * α ^ (k - 1) := by linarith
  have hmul := mul_lt_mul_of_pos_right hpred' (mul_pos hαpos (sub_pos.mpr hαlt))
  have hpow : α ^ k = α ^ (k - 1) * α := by
    calc
      α ^ k = α ^ ((k - 1) + 1) := by
        congr 1
        omega
      _ = α ^ (k - 1) * α := by rw [pow_succ]
  nlinarith

/-- The root identity in reciprocal-power form. -/
private theorem ddb_zpow_neg_k (k : ℕ) (α : ℝ) (hαpos : 0 < α)
    (hkey : α ^ k * (2 - α) = 1) : α ^ (-(k : ℤ)) = 2 - α := by
  rw [zpow_neg, zpow_natCast]
  have hpowne : α ^ k ≠ 0 := pow_ne_zero k (ne_of_gt hαpos)
  field_simp
  nlinarith

/-- Positive left-eigenvector weights for the `k`-step recurrence. -/
private noncomputable def ddb_weight (k : ℕ) (α : ℝ) (i : ℕ) : ℝ :=
  1 - α ^ ((i : ℤ) - (k : ℤ))

/-- Every recurrence weight in the range `0, …, k-1` is positive. -/
private theorem ddb_weight_pos (k : ℕ) (α : ℝ) (hα1 : 1 < α) (i : ℕ) (hi : i < k) :
    0 < ddb_weight k α i := by
  have hpow : α ^ ((i : ℤ) - (k : ℤ)) < 1 :=
    (zpow_lt_one_iff_right₀ hα1).2 (by omega)
  unfold ddb_weight
  linarith

/-- The first recurrence weight is `α - 1`. -/
private theorem ddb_weight_zero (k : ℕ) (α : ℝ) (hneg : α ^ (-(k : ℤ)) = 2 - α) :
    ddb_weight k α 0 = α - 1 := by
  simp only [ddb_weight, Nat.cast_zero, zero_sub]
  rw [hneg]
  ring

/-- Consecutive recurrence weights satisfy the left-eigenvector relation. -/
private theorem ddb_weight_succ (k i : ℕ) (α : ℝ) (hαne : α ≠ 0) :
    ddb_weight k α (i + 1) + (α - 1) = α * ddb_weight k α i := by
  have hexp : ((i + 1 : ℕ) : ℤ) - (k : ℤ) = ((i : ℤ) - (k : ℤ)) + 1 := by
    push_cast
    ring
  unfold ddb_weight
  rw [hexp, zpow_add₀ hαne]
  norm_num
  ring

/-- The last recurrence weight closes the eigenvector relation. -/
private theorem ddb_weight_last (k : ℕ) (hk : 1 ≤ k) (α : ℝ) (hαne : α ≠ 0) :
    α * ddb_weight k α (k - 1) = α - 1 := by
  have h := ddb_weight_succ k (k - 1) α hαne
  rw [show k - 1 + 1 = k by omega] at h
  have hzero : ddb_weight k α k = 0 := by simp [ddb_weight]
  rw [hzero] at h
  linarith

/-- Multiplying a weight by its matching reciprocal power makes the sum telescope. -/
private theorem ddb_weight_mul_zpow (k i : ℕ) (α : ℝ) (hαne : α ≠ 0) :
    ddb_weight k α i * α ^ (-(i : ℤ)) =
      α ^ (-(i : ℤ)) - α ^ (-(k : ℤ)) := by
  have hexp : ((i : ℤ) - (k : ℤ)) + (-(i : ℤ)) = -(k : ℤ) := by ring
  have hpow : α ^ ((i : ℤ) - (k : ℤ)) * α ^ (-(i : ℤ)) = α ^ (-(k : ℤ)) := by
    rw [← zpow_add₀ hαne, hexp]
  unfold ddb_weight
  rw [sub_mul, one_mul, hpow]

/-- Dividing the root equation by `α^(k-1)` gives the reciprocal-power sum. -/
private theorem ddb_sum_reciprocal_powers (k : ℕ) (hk : 1 ≤ k) (α : ℝ)
    (hαne : α ≠ 0) (hαroot : α ^ k = ∑ i ∈ Finset.range k, α ^ i) :
    ∑ i ∈ Finset.range k, α ^ (-(i : ℤ)) = α := by
  have hpowne : α ^ (k - 1) ≠ 0 := pow_ne_zero (k - 1) hαne
  apply mul_left_cancel₀ hpowne (a := α ^ (k - 1))
  calc
    α ^ (k - 1) * ∑ i ∈ Finset.range k, α ^ (-(i : ℤ)) =
        ∑ i ∈ Finset.range k, α ^ (((k - 1 - i : ℕ) : ℤ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hik : i < k := Finset.mem_range.mp hi
      have hbase : (α ^ (k - 1) : ℝ) = α ^ (((k - 1 : ℕ) : ℤ)) := by simp
      rw [hbase, ← zpow_add₀ hαne]
      congr 1
      omega
    _ = ∑ j ∈ Finset.range k, α ^ (((j : ℕ) : ℤ)) := by
      simpa using Finset.sum_range_reflect (fun j => α ^ (((j : ℕ) : ℤ))) k
    _ = α ^ k := by simpa using hαroot.symm
    _ = α ^ (k - 1) * α := by
      calc
        α ^ k = α ^ ((k - 1) + 1) := by
          congr 1
          omega
        _ = α ^ (k - 1) * α := by rw [pow_succ]

/-- The weighted initial-window normalization is exactly the Binet denominator. -/
private theorem ddb_weight_normalization (k : ℕ) (hk : 1 ≤ k) (α : ℝ)
    (hαne : α ≠ 0) (hneg : α ^ (-(k : ℤ)) = 2 - α)
    (hαroot : α ^ k = ∑ i ∈ Finset.range k, α ^ i) :
    ∑ i ∈ Finset.range k, ddb_weight k α i * α ^ (-(i : ℤ)) =
      2 + ((k : ℝ) + 1) * (α - 2) := by
  rw [Finset.sum_congr rfl fun i _ => ddb_weight_mul_zpow k i α hαne]
  rw [Finset.sum_sub_distrib, ddb_sum_reciprocal_powers k hk α hαne hαroot]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hneg]
  ring

/-- Subtracting consecutive `k`-term recurrences gives a two-term update. -/
private theorem ddb_recurrence_step (k : ℕ) (hk : 1 ≤ k) (e : ℤ → ℝ)
    (hrec : ∀ n : ℤ, 1 < n → e n = ∑ i ∈ Finset.range k, e (n - 1 - (i : ℤ)))
    (n : ℤ) (hn : 2 ≤ n) : e (n + 1) = 2 * e n - e (n - (k : ℤ)) := by
  have hnext : e (n + 1) = ∑ i ∈ Finset.range k, e (n - (i : ℤ)) := by
    convert hrec (n + 1) (by omega) using 1
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    ring
  have hcur := hrec n (by omega)
  have hsplitNext : ∑ i ∈ Finset.range k, e (n - (i : ℤ)) =
      (∑ i ∈ Finset.range (k - 1), e (n - 1 - (i : ℤ))) + e n := by
    rw [show k = (k - 1) + 1 by omega, Finset.sum_range_succ']
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      congr 1
      push_cast
      ring
    · congr 1
      push_cast
      ring
  have hsplitCur : ∑ i ∈ Finset.range k, e (n - 1 - (i : ℤ)) =
      (∑ i ∈ Finset.range (k - 1), e (n - 1 - (i : ℤ))) + e (n - (k : ℤ)) := by
    rw [show k = (k - 1) + 1 by omega, Finset.sum_range_succ]
    congr 1
    push_cast
    rw [Nat.cast_sub hk]
    ring_nf
  rw [hsplitNext] at hnext
  rw [hsplitCur] at hcur
  linarith

/-- The weighted error functional is multiplied by `α` at each recurrence step. -/
private theorem ddb_weighted_sum_step (k : ℕ) (hk : 1 ≤ k) (α : ℝ) (hαne : α ≠ 0)
    (hneg : α ^ (-(k : ℤ)) = 2 - α) (e : ℤ → ℝ)
    (hrec : ∀ n : ℤ, 1 < n → e n = ∑ i ∈ Finset.range k, e (n - 1 - (i : ℤ)))
    (n : ℤ) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.range k, ddb_weight k α i * e (n + 1 - (i : ℤ)) =
      α * ∑ i ∈ Finset.range k, ddb_weight k α i * e (n - (i : ℤ)) := by
  have hnext : e (n + 1) = ∑ i ∈ Finset.range k, e (n - (i : ℤ)) := by
    convert hrec (n + 1) (by omega) using 1
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    ring
  have hsplitNext :
      ∑ i ∈ Finset.range k, ddb_weight k α i * e (n + 1 - (i : ℤ)) =
        (∑ i ∈ Finset.range (k - 1), ddb_weight k α (i + 1) * e (n - (i : ℤ))) +
          ddb_weight k α 0 * e (n + 1) := by
    rw [show k = (k - 1) + 1 by omega, Finset.sum_range_succ']
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      congr 2
      push_cast
      ring
    · simp
  have hsplitCur :
      ∑ i ∈ Finset.range k, ddb_weight k α i * e (n - (i : ℤ)) =
        (∑ i ∈ Finset.range (k - 1), ddb_weight k α i * e (n - (i : ℤ))) +
          ddb_weight k α (k - 1) * e (n - ((k - 1 : ℕ) : ℤ)) := by
    have h := Finset.sum_range_succ
      (fun i => ddb_weight k α i * e (n - (i : ℤ))) (k - 1)
    rw [show k - 1 + 1 = k by omega] at h
    exact h
  have hsplitE : ∑ i ∈ Finset.range k, e (n - (i : ℤ)) =
      (∑ i ∈ Finset.range (k - 1), e (n - (i : ℤ))) +
        e (n - ((k - 1 : ℕ) : ℤ)) := by
    have h := Finset.sum_range_succ (fun i => e (n - (i : ℤ))) (k - 1)
    rw [show k - 1 + 1 = k by omega] at h
    exact h
  have hprefix :
      (∑ i ∈ Finset.range (k - 1), ddb_weight k α (i + 1) * e (n - (i : ℤ))) +
          (α - 1) * ∑ i ∈ Finset.range (k - 1), e (n - (i : ℤ)) =
        α * ∑ i ∈ Finset.range (k - 1), ddb_weight k α i * e (n - (i : ℤ)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    calc
      ddb_weight k α (i + 1) * e (n - (i : ℤ)) + (α - 1) * e (n - (i : ℤ)) =
          (ddb_weight k α (i + 1) + (α - 1)) * e (n - (i : ℤ)) := by ring
      _ = (α * ddb_weight k α i) * e (n - (i : ℤ)) := by
        rw [ddb_weight_succ k i α hαne]
      _ = α * (ddb_weight k α i * e (n - (i : ℤ))) := by ring
  have hzero := ddb_weight_zero k α hneg
  have hlast := ddb_weight_last k hk α hαne
  rw [hsplitNext, hnext, hsplitE, hsplitCur, hzero]
  rw [mul_add, mul_add]
  calc
    (∑ i ∈ Finset.range (k - 1), ddb_weight k α (i + 1) * e (n - (i : ℤ))) +
          ((α - 1) * ∑ i ∈ Finset.range (k - 1), e (n - (i : ℤ)) +
            (α - 1) * e (n - ((k - 1 : ℕ) : ℤ))) =
        ((∑ i ∈ Finset.range (k - 1), ddb_weight k α (i + 1) * e (n - (i : ℤ))) +
          (α - 1) * ∑ i ∈ Finset.range (k - 1), e (n - (i : ℤ))) +
            (α - 1) * e (n - ((k - 1 : ℕ) : ℤ)) := by ring
    _ = α * (∑ i ∈ Finset.range (k - 1), ddb_weight k α i * e (n - (i : ℤ))) +
          (α - 1) * e (n - ((k - 1 : ℕ) : ℤ)) := by rw [hprefix]
    _ = α * (∑ i ∈ Finset.range (k - 1), ddb_weight k α i * e (n - (i : ℤ))) +
          (α * ddb_weight k α (k - 1)) * e (n - ((k - 1 : ℕ) : ℤ)) := by rw [hlast]
    _ = α * (∑ i ∈ Finset.range (k - 1), ddb_weight k α i * e (n - (i : ℤ))) +
          α * (ddb_weight k α (k - 1) * e (n - ((k - 1 : ℕ) : ℤ))) := by ring

/-- A zero weighted functional stays zero at every later index. -/
private theorem ddb_weighted_sum_zero (k : ℕ) (hk : 1 ≤ k) (α : ℝ) (hαne : α ≠ 0)
    (hneg : α ^ (-(k : ℤ)) = 2 - α) (e : ℤ → ℝ)
    (hrec : ∀ n : ℤ, 1 < n → e n = ∑ i ∈ Finset.range k, e (n - 1 - (i : ℤ)))
    (hbase : ∑ i ∈ Finset.range k, ddb_weight k α i * e (1 - (i : ℤ)) = 0) :
    ∀ n : ℤ, 1 ≤ n →
      ∑ i ∈ Finset.range k, ddb_weight k α i * e (n - (i : ℤ)) = 0 := by
  intro n hn
  refine Int.leInduction hbase ?_ n hn
  intro m hm ih
  rw [ddb_weighted_sum_step k hk α hαne hneg e hrec m hm, ih, mul_zero]

/-- A first positive error of size at least one half forces the next `k` errors positive. -/
private theorem ddb_positive_chain (k : ℕ) (e : ℤ → ℝ)
    (hstep : ∀ n : ℤ, 2 ≤ n → e (n + 1) = 2 * e n - e (n - (k : ℤ)))
    (m : ℤ) (hm : 2 ≤ m) (hbad : (1 : ℝ) / 2 ≤ e m)
    (hprev : ∀ q : ℤ, 2 - (k : ℤ) ≤ q → q < m → |e q| < 1 / 2) :
    ∀ j : ℕ, j < k → (1 : ℝ) / 2 ≤ e (m + (j : ℤ)) := by
  intro j hj
  induction j with
  | zero => simpa using hbad
  | succ j ih =>
      have hjk : j < k := by omega
      have hcur := ih hjk
      have hqlo : 2 - (k : ℤ) ≤ m + (j : ℤ) - (k : ℤ) := by
        omega
      have hqlt : m + (j : ℤ) - (k : ℤ) < m := by
        have hjz : ((j + 1 : ℕ) : ℤ) < (k : ℤ) := by exact_mod_cast hj
        omega
      have hq := hprev (m + (j : ℤ) - (k : ℤ)) hqlo hqlt
      rw [abs_lt] at hq
      have hs := hstep (m + (j : ℤ)) (by omega)
      have heq : e (m + ((j + 1 : ℕ) : ℤ)) =
          2 * e (m + (j : ℤ)) - e (m + (j : ℤ) - (k : ℤ)) := by
        convert hs using 1
        all_goals
          push_cast
          ring_nf
      rw [heq]
      linarith

/-- A first negative error of size at least one half forces the next `k` errors negative. -/
private theorem ddb_negative_chain (k : ℕ) (e : ℤ → ℝ)
    (hstep : ∀ n : ℤ, 2 ≤ n → e (n + 1) = 2 * e n - e (n - (k : ℤ)))
    (m : ℤ) (hm : 2 ≤ m) (hbad : e m ≤ -(1 : ℝ) / 2)
    (hprev : ∀ q : ℤ, 2 - (k : ℤ) ≤ q → q < m → |e q| < 1 / 2) :
    ∀ j : ℕ, j < k → e (m + (j : ℤ)) ≤ -(1 : ℝ) / 2 := by
  intro j hj
  induction j with
  | zero => simpa using hbad
  | succ j ih =>
      have hjk : j < k := by omega
      have hcur := ih hjk
      have hqlo : 2 - (k : ℤ) ≤ m + (j : ℤ) - (k : ℤ) := by
        omega
      have hqlt : m + (j : ℤ) - (k : ℤ) < m := by
        have hjz : ((j + 1 : ℕ) : ℤ) < (k : ℤ) := by exact_mod_cast hj
        omega
      have hq := hprev (m + (j : ℤ) - (k : ℤ)) hqlo hqlt
      rw [abs_lt] at hq
      have hs := hstep (m + (j : ℤ)) (by omega)
      have heq : e (m + ((j + 1 : ℕ) : ℤ)) =
          2 * e (m + (j : ℤ)) - e (m + (j : ℤ) - (k : ℤ)) := by
        convert hs using 1
        all_goals
          push_cast
          ring_nf
      rw [heq]
      linarith

/-- A zero positive weighted functional prevents any error from reaching one half. -/
private theorem ddb_error_bound (k : ℕ) (hk : 2 ≤ k) (α : ℝ) (hα1 : 1 < α)
    (e : ℤ → ℝ)
    (hstep : ∀ n : ℤ, 2 ≤ n → e (n + 1) = 2 * e n - e (n - (k : ℤ)))
    (hinv : ∀ n : ℤ, 1 ≤ n →
      ∑ i ∈ Finset.range k, ddb_weight k α i * e (n - (i : ℤ)) = 0)
    (hinit : ∀ n : ℤ, 2 - (k : ℤ) ≤ n → n ≤ 1 → |e n| < 1 / 2) :
    ∀ n : ℤ, 2 - (k : ℤ) ≤ n → |e n| < 1 / 2 := by
  have hall : ∀ r : ℕ, ∀ q : ℤ, 2 - (k : ℤ) ≤ q →
      q ≤ 2 - (k : ℤ) + (r : ℤ) → |e q| < 1 / 2 := by
    intro r
    induction r with
    | zero =>
        intro q hqlo hqhi
        apply hinit q hqlo
        omega
    | succ r ih =>
        intro q hqlo hqhi
        by_cases hqprev : q ≤ 2 - (k : ℤ) + (r : ℤ)
        · exact ih q hqlo hqprev
        · have hqeq : q = 2 - (k : ℤ) + ((r + 1 : ℕ) : ℤ) := by
            push_cast at hqhi
            omega
          subst q
          by_cases hsmall : 2 - (k : ℤ) + ((r + 1 : ℕ) : ℤ) ≤ 1
          · exact hinit _ (by omega) hsmall
          · have hm : 2 ≤ 2 - (k : ℤ) + ((r + 1 : ℕ) : ℤ) := by omega
            let m : ℤ := 2 - (k : ℤ) + ((r + 1 : ℕ) : ℤ)
            have hmdef : m = 2 - (k : ℤ) + ((r + 1 : ℕ) : ℤ) := rfl
            have hprev : ∀ p : ℤ, 2 - (k : ℤ) ≤ p → p < m → |e p| < 1 / 2 := by
              intro p hplo hplt
              apply ih p hplo
              rw [hmdef] at hplt
              push_cast at hplt
              omega
            by_contra hbound
            push Not at hbound
            rcases le_total 0 (e m) with hsign | hsign
            · have hbad : (1 : ℝ) / 2 ≤ e m := by
                rw [abs_of_nonneg hsign] at hbound
                exact hbound
              have hchain := ddb_positive_chain k e hstep m (by simpa [hmdef] using hm)
                hbad hprev
              have hsumpos : 0 < ∑ i ∈ Finset.range k,
                  ddb_weight k α i * e (m + (k : ℤ) - 1 - (i : ℤ)) := by
                apply Finset.sum_pos
                · intro i hi
                  have hik : i < k := Finset.mem_range.mp hi
                  have hjk : k - 1 - i < k := by omega
                  have he := hchain (k - 1 - i) hjk
                  have hindex : m + (k : ℤ) - 1 - (i : ℤ) =
                      m + ((k - 1 - i : ℕ) : ℤ) := by
                    rw [Nat.cast_sub (show i ≤ k - 1 by omega),
                      Nat.cast_sub (show 1 ≤ k by omega)]
                    ring
                  rw [hindex]
                  exact mul_pos (ddb_weight_pos k α hα1 i hik) (by linarith)
                · exact ⟨0, by simp; omega⟩
              have hzero := hinv (m + (k : ℤ) - 1) (by omega)
              linarith
            · have hbad : e m ≤ -(1 : ℝ) / 2 := by
                rw [abs_of_nonpos hsign] at hbound
                linarith
              have hchain := ddb_negative_chain k e hstep m (by simpa [hmdef] using hm)
                hbad hprev
              have hsumneg : ∑ i ∈ Finset.range k,
                  ddb_weight k α i * e (m + (k : ℤ) - 1 - (i : ℤ)) < 0 := by
                apply Finset.sum_neg
                · intro i hi
                  have hik : i < k := Finset.mem_range.mp hi
                  have hjk : k - 1 - i < k := by omega
                  have he := hchain (k - 1 - i) hjk
                  have hindex : m + (k : ℤ) - 1 - (i : ℤ) =
                      m + ((k - 1 - i : ℕ) : ℤ) := by
                    rw [Nat.cast_sub (show i ≤ k - 1 by omega),
                      Nat.cast_sub (show 1 ≤ k by omega)]
                    ring
                  rw [hindex]
                  exact mul_neg_of_pos_of_neg (ddb_weight_pos k α hα1 i hik) (by linarith)
                · exact ⟨0, by simp; omega⟩
              have hzero := hinv (m + (k : ℤ) - 1) (by omega)
              linarith
  intro n hn
  have hdiff : 0 ≤ n - (2 - (k : ℤ)) := by omega
  have hcast : (((n - (2 - (k : ℤ))).toNat : ℕ) : ℤ) = n - (2 - (k : ℤ)) :=
    Int.toNat_of_nonneg hdiff
  apply hall (n - (2 - (k : ℤ))).toNat n hn
  rw [hcast]
  ring_nf
  exact le_rfl

/-- The Binet term `c * α ^ (n - 1)` satisfies the same recurrence as `F`:
this is the exact-sequence step of Dresden–Du, following from `hαroot`
(`∑ i ∈ range k, α ^ (-(i + 1)) = 1` after clearing denominators). -/
private theorem binet_term_recurrence (k : ℕ) (α : ℝ) (hαpos : 0 < α)
    (hαroot : α ^ k = ∑ i ∈ Finset.range k, α ^ i) (c : ℝ) (n : ℤ) :
    c * α ^ (n - 1) = ∑ i ∈ Finset.range k, c * α ^ (n - 1 - (i : ℤ) - 1) := by
  have hαne : α ≠ 0 := ne_of_gt hαpos
  have hexp : ∀ i ∈ Finset.range k,
      c * α ^ (n - 1 - (i : ℤ) - 1) = (c * α ^ (n - 1)) * α ^ (-((i : ℤ) + 1)) := by
    intro i _
    have hsplit : (n - 1 - (i : ℤ) - 1) = (n - 1) + (-((i : ℤ) + 1)) := by ring
    rw [hsplit, zpow_add₀ hαne, mul_assoc]
  have hmul : ∀ i ∈ Finset.range k,
      (α ^ k : ℝ) * α ^ (-((i : ℤ) + 1)) = α ^ (((k - 1 - i : ℕ) : ℤ)) := by
    intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    have h1 : (α ^ k : ℝ) = α ^ ((k : ℤ)) := by simp
    rw [h1, ← zpow_add₀ hαne]
    congr 1
    omega
  have hS : ∑ i ∈ Finset.range k, α ^ (-((i : ℤ) + 1)) = 1 := by
    have hαk : α ^ k ≠ (0 : ℝ) := pow_ne_zero k hαne
    apply mul_left_cancel₀ hαk (a := (α ^ k : ℝ))
    rw [mul_one]
    have hmul_sum : (α ^ k : ℝ) * ∑ i ∈ Finset.range k, α ^ (-((i : ℤ) + 1))
        = ∑ i ∈ Finset.range k, α ^ (((k - 1 - i : ℕ) : ℤ)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl hmul
    rw [hmul_sum]
    have hrefl : ∑ i ∈ Finset.range k, α ^ (((k - 1 - i : ℕ) : ℤ))
        = ∑ j ∈ Finset.range k, α ^ (((j : ℕ) : ℤ)) := by
      have h := Finset.sum_range_reflect (fun j => α ^ (((j : ℕ) : ℤ))) k
      simpa using h
    rw [hrefl]
    have hcast : ∀ j ∈ Finset.range k, α ^ (((j : ℕ) : ℤ)) = α ^ j := by
      intro j _
      simp
    rw [Finset.sum_congr rfl hcast, ← hαroot]
  rw [Finset.sum_congr rfl hexp, ← Finset.mul_sum, hS, mul_one]

/-- Subtracting the Binet term from `F` preserves the `k`-term recurrence. -/
private theorem ddb_error_recurrence (k : ℕ) (F : ℤ → ℤ)
    (hFrec : ∀ n : ℤ, 1 < n → F n = ∑ i ∈ Finset.range k, F (n - 1 - (i : ℤ)))
    (α : ℝ) (hαpos : 0 < α) (hαroot : α ^ k = ∑ i ∈ Finset.range k, α ^ i)
    (c : ℝ) (n : ℤ) (hn : 1 < n) :
    (F n : ℝ) - c * α ^ (n - 1) =
      ∑ i ∈ Finset.range k,
        (((F (n - 1 - (i : ℤ)) : ℤ) : ℝ) - c * α ^ (n - 1 - (i : ℤ) - 1)) := by
  have hFreal : (F n : ℝ) =
      ∑ i ∈ Finset.range k, ((F (n - 1 - (i : ℤ)) : ℤ) : ℝ) := by
    exact_mod_cast hFrec n hn
  rw [hFreal, binet_term_recurrence k α hαpos hαroot c n]
  exact (Finset.sum_sub_distrib ..).symm

/-- The initial error window `2-k, …, 1` lies strictly inside the rounding interval. -/
private theorem ddb_initial_error_bound (k : ℕ) (F : ℤ → ℤ)
    (hFzero : ∀ n : ℤ, 2 - (k : ℤ) ≤ n → n < 1 → F n = 0) (hFone : F 1 = 1)
    (α c : ℝ) (hα1 : 1 < α) (hcpos : 0 < c) (hchalf : (1 : ℝ) / 2 < c)
    (hcone : c < 1) (hcdiv : c / α < 1 / 2) :
    ∀ n : ℤ, 2 - (k : ℤ) ≤ n → n ≤ 1 → |(F n : ℝ) - c * α ^ (n - 1)| < 1 / 2 := by
  intro n hnlo hn1
  rcases lt_or_eq_of_le hn1 with hn | rfl
  · have hpowpos : 0 < α ^ (n - 1) := zpow_pos (by linarith) _
    have hpowle : α ^ (n - 1) ≤ α ^ (-1 : ℤ) :=
      zpow_le_zpow_right₀ hα1.le (by omega)
    have hmul := mul_le_mul_of_nonneg_left hpowle hcpos.le
    have hmul' : c * α ^ (n - 1) ≤ c / α := by
      simpa [zpow_neg_one, div_eq_mul_inv] using hmul
    rw [hFzero n hnlo hn]
    norm_num
    rw [abs_of_pos hcpos, abs_of_pos hpowpos]
    linarith
  · rw [hFone]
    norm_num
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- The Binet coefficient makes the weighted initial error functional vanish. -/
private theorem ddb_initial_weighted_sum (k : ℕ) (hk : 1 ≤ k) (F : ℤ → ℤ)
    (hFzero : ∀ n : ℤ, 2 - (k : ℤ) ≤ n → n < 1 → F n = 0) (hFone : F 1 = 1)
    (α c : ℝ)
    (hzero : ddb_weight k α 0 = α - 1)
    (hnorm : ∑ i ∈ Finset.range k, ddb_weight k α i * α ^ (-(i : ℤ)) =
      2 + ((k : ℝ) + 1) * (α - 2))
    (hcden : c * (2 + ((k : ℝ) + 1) * (α - 2)) = α - 1) :
    ∑ i ∈ Finset.range k, ddb_weight k α i *
      ((F (1 - (i : ℤ)) : ℝ) - c * α ^ (1 - (i : ℤ) - 1)) = 0 := by
  have hFsum : ∑ i ∈ Finset.range k,
      ddb_weight k α i * (F (1 - (i : ℤ)) : ℝ) = ddb_weight k α 0 := by
    have hsplit := Finset.sum_range_succ'
      (fun i => ddb_weight k α i * (F (1 - (i : ℤ)) : ℝ)) (k - 1)
    rw [show k - 1 + 1 = k by omega] at hsplit
    rw [hsplit]
    have hprefix : ∑ i ∈ Finset.range (k - 1),
        ddb_weight k α (i + 1) * (F (1 - ((i + 1 : ℕ) : ℤ)) : ℝ) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hFzero]
      · simp
      · have hi' := Finset.mem_range.mp hi
        push_cast
        omega
      · push_cast
        omega
    rw [hprefix, zero_add]
    norm_num [hFone]
  calc
    ∑ i ∈ Finset.range k, ddb_weight k α i *
        ((F (1 - (i : ℤ)) : ℝ) - c * α ^ (1 - (i : ℤ) - 1)) =
        (∑ i ∈ Finset.range k, ddb_weight k α i * (F (1 - (i : ℤ)) : ℝ)) -
          c * ∑ i ∈ Finset.range k, ddb_weight k α i * α ^ (-(i : ℤ)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring_nf
    _ = 0 := by rw [hFsum, hzero, hnorm, hcden, sub_self]

/-- An integer within one half of a real number is its nearest-integer floor. -/
private theorem ddb_floor_of_abs_sub_lt (m : ℤ) (y : ℝ)
    (h : |(m : ℝ) - y| < 1 / 2) : m = ⌊y + 1 / 2⌋ := by
  symm
  rw [Int.floor_eq_iff]
  rw [abs_lt] at h
  constructor <;> linarith

/-! # Simplified Binet formula for k-generalized Fibonacci numbers -/

/-- **Simplified Binet formula for k-generalized Fibonacci numbers from an initial window.**
Let $k \ge 2$ and let $F : \mathbb{Z} \to \mathbb{Z}$ satisfy $F(n) = 0$ for all integers $n$ with
$2 - k \le n < 1$, $F(1) = 1$, and $F(n) = \sum_{i=0}^{k-1} F(n - 1 - i)$ for all integers
$n > 1$. Let $\alpha$ be a positive real number with $\alpha^k = \sum_{i=0}^{k-1} \alpha^i$, and
put $c = (\alpha - 1)/(2 + (k + 1)(\alpha - 2))$. Then for every integer $n \ge 2 - k$,
$F(n) = \lfloor c\,\alpha^{n-1} + 1/2 \rfloor$.

Proof: We follow Dresden–Du's recurrence and first-crossing route, replacing their appeal to
the non-dominant-root results of Miles (1960) and Miller (1971) with an exact positive weighted
invariant.

Source: G. P. B. Dresden and Z. Du, *A Simplified Binet Formula for k-Generalized
Fibonacci Numbers*, Journal of Integer Sequences 17 (2014), Article 14.4.7,
Theorem T2, lines 209-218,
<https://cs.uwaterloo.ca/journals/JIS/VOL17/Dresden/dresden6.tex>.
-/
public theorem dresden_du_simplified_binet_of_initial_window :
    ∀ (k : ℕ) (_hk : 2 ≤ k) (F : ℤ → ℤ)
      (_hFzero : ∀ n : ℤ, 2 - (k : ℤ) ≤ n → n < 1 → F n = 0)
      (_hFone : F 1 = 1)
      (_hFrec : ∀ n : ℤ, 1 < n → F n = ∑ i ∈ Finset.range k, F (n - 1 - (i : ℤ))) (α : ℝ)
      (_hαpos : 0 < α) (_hαroot : α ^ k = ∑ i ∈ Finset.range k, α ^ i),
      ∀ n : ℤ, 2 - (k : ℤ) ≤ n →
        F n = ⌊((α - 1) / (2 + ((k : ℝ) + 1) * (α - 2))) * α ^ (n - 1) + 1 / 2⌋ := by
  intro k hk F hFzero hFone hFrec α hαpos hαroot n hn
  have hα1 := alpha_gt_one k hk α hαpos hαroot
  have hkey := alpha_key_identity k α hα1 hαroot
  have hαlt := alpha_lt_two k α hαpos hkey
  have hpowge := alpha_pow_ge k α hα1 hαroot
  have hden := denom_pos k hk α hα1 hkey hpowge
  let c : ℝ := (α - 1) / (2 + ((k : ℝ) + 1) * (α - 2))
  let e : ℤ → ℝ := fun m => (F m : ℝ) - c * α ^ (m - 1)
  have hαne : α ≠ 0 := ne_of_gt hαpos
  have hcpos : 0 < c := c_pos k α hα1 hden
  have hpowgt := ddb_alpha_pow_gt k hk α hα1 hαroot
  have hpred := ddb_alpha_pow_pred_gt k hk α hα1 hαroot
  have hchalf : (1 : ℝ) / 2 < c := ddb_c_gt_half k hk α hαlt hden
  have hcone : c < 1 := ddb_c_lt_one k α hαlt hkey hpowgt hden
  have hcdiv : c / α < (1 : ℝ) / 2 :=
    ddb_c_div_alpha_lt_half k hk α hαpos hαlt hkey hpred hden
  have hneg := ddb_zpow_neg_k k α hαpos hkey
  have hweightzero := ddb_weight_zero k α hneg
  have hnorm := ddb_weight_normalization k (by omega) α hαne hneg hαroot
  have hcden : c * (2 + ((k : ℝ) + 1) * (α - 2)) = α - 1 := by
    exact div_mul_cancel₀ (α - 1) (ne_of_gt hden)
  have herec : ∀ m : ℤ, 1 < m →
      e m = ∑ i ∈ Finset.range k, e (m - 1 - (i : ℤ)) := by
    intro m hm
    simpa [e] using ddb_error_recurrence k F hFrec α hαpos hαroot c m hm
  have hstep : ∀ m : ℤ, 2 ≤ m → e (m + 1) = 2 * e m - e (m - (k : ℤ)) :=
    ddb_recurrence_step k (by omega) e herec
  have hbase : ∑ i ∈ Finset.range k, ddb_weight k α i * e (1 - (i : ℤ)) = 0 := by
    simpa [e] using ddb_initial_weighted_sum k (by omega) F hFzero hFone α c hweightzero hnorm
      hcden
  have hinv : ∀ m : ℤ, 1 ≤ m →
      ∑ i ∈ Finset.range k, ddb_weight k α i * e (m - (i : ℤ)) = 0 :=
    ddb_weighted_sum_zero k (by omega) α hαne hneg e herec hbase
  have hinit : ∀ m : ℤ, 2 - (k : ℤ) ≤ m → m ≤ 1 → |e m| < 1 / 2 := by
    intro m hmlo hmhi
    simpa [e] using ddb_initial_error_bound k F hFzero hFone α c hα1 hcpos hchalf hcone hcdiv
      m hmlo hmhi
  have herr : |e n| < (1 : ℝ) / 2 :=
    ddb_error_bound k hk α hα1 e hstep hinv hinit n hn
  apply ddb_floor_of_abs_sub_lt (F n) (c * α ^ (n - 1))
  simpa [e] using herr

/-- **Dresden–Du simplified Binet formula.** Let $k \ge 2$ and let $F : \mathbb{Z} \to \mathbb{Z}$
satisfy $F(n) = 0$ for all integers $n < 1$, $F(1) = 1$, and
$F(n) = \sum_{i=0}^{k-1} F(n - 1 - i)$ for all integers $n > 1$. Let $\alpha$ be a positive real
number with $\alpha^k = \sum_{i=0}^{k-1} \alpha^i$, and suppose that every positive real $\beta$
with $\beta^k = \sum_{i=0}^{k-1} \beta^i$ equals $\alpha$. Put
$c = (\alpha - 1)/(2 + (k + 1)(\alpha - 2))$. Then for every integer $n \ge 2 - k$,
$F(n) = \lfloor c\,\alpha^{n-1} + 1/2 \rfloor$.

Proves `Wanted` entry `dresden_du_simplified_binet`.

Source: G. P. B. Dresden and Z. Du, *A Simplified Binet Formula for k-Generalized
Fibonacci Numbers*, Journal of Integer Sequences 17 (2014), Article 14.4.7,
Theorem T2, lines 209-218,
<https://cs.uwaterloo.ca/journals/JIS/VOL17/Dresden/dresden6.tex>. -/
public theorem dresden_du_simplified_binet :
    ∀ (k : ℕ) (_hk : 2 ≤ k) (F : ℤ → ℤ) (_hFneg : ∀ n : ℤ, n < 1 → F n = 0)
      (_hFone : F 1 = 1)
      (_hFrec : ∀ n : ℤ, 1 < n → F n = ∑ i ∈ Finset.range k, F (n - 1 - (i : ℤ))) (α : ℝ)
      (_hαpos : 0 < α) (_hαroot : α ^ k = ∑ i ∈ Finset.range k, α ^ i)
      (_hαuniq : ∀ β : ℝ, 0 < β → β ^ k = ∑ i ∈ Finset.range k, β ^ i → β = α),
      ∀ n : ℤ, 2 - (k : ℤ) ≤ n →
        F n = ⌊((α - 1) / (2 + ((k : ℝ) + 1) * (α - 2))) * α ^ (n - 1) + 1 / 2⌋ := by
  intro k hk F hFneg hFone hFrec α hαpos hαroot _hαuniq
  exact dresden_du_simplified_binet_of_initial_window k hk F (fun n _ hn => hFneg n hn)
    hFone hFrec α hαpos hαroot

end MetaMathlibExt
end
