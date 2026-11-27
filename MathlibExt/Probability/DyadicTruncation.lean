/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Dyadic truncation of finite distributions

Dyadic truncation of a finite probability vector with the leftover mass routed to a reject outcome: total-variation and acceptance error bounds and the precision choice.

In Section IV of T. Morimae, D. Nagaj and N. Schuch, "Quantum proofs can be
verified using only single-qubit measurements", Physical Review A 93 (2016),
022326 (arXiv:1510.06789), the verifier samples a Pauli term exactly from a
probability distribution `π`. The dyadic truncation here is a finite-precision
version of that step, not a construction from the paper: a label with
probability `π l` is sampled with `t` fair coins by rounding `π l` down to a
multiple of `2⁻ᵗ`, and the leftover mass is routed to a reject outcome. The
bounds below are for an arbitrary finite probability vector; no Pauli or
circuit statement is included.
-/

@[expose] public section

open scoped BigOperators
namespace MathlibExt.Probability.DyadicTruncation

set_option autoImplicit false

/-- q_l = ⌊2^t π_l⌋/2^t -/
noncomputable def dyadicTrunc {L : Type*} (π : L → ℝ) (t : ℕ) (l : L) : ℝ := (⌊(2 : ℝ) ^ t * π l⌋₊ : ℝ) / 2 ^ t

/-- The leftover `1 - ∑ l, dyadicTrunc π t l`. For a probability vector `π` (nonnegative entries
summing to `1`) it is the mass that truncation routes to reject; for other `π` it is only this
difference. -/
noncomputable def dyadicLeftover {L : Type*} [Fintype L] (π : L → ℝ) (t : ℕ) : ℝ := 1 - ∑ l, dyadicTrunc π t l

/-- The leftover mass equals the sum of the per-label truncation errors. -/
private theorem dyadicLeftover_eq_sum_sub {L : Type*} [Fintype L] (π : L → ℝ)
    (hsum : ∑ l, π l = 1) (t : ℕ) :
    dyadicLeftover π t = ∑ l, (π l - dyadicTrunc π t l) := by
  unfold dyadicLeftover
  rw [← hsum, ← Finset.sum_sub_distrib]

theorem dyadicTrunc_nonneg {L : Type*} (π : L → ℝ) (t : ℕ) (l : L) : 0 ≤ dyadicTrunc π t l := by
  unfold dyadicTrunc
  positivity

theorem dyadicTrunc_le {L : Type*} {π : L → ℝ} (hπ : ∀ l, 0 ≤ π l) (t : ℕ) (l : L) : dyadicTrunc π t l ≤ π l := by
  unfold dyadicTrunc
  have h2 : (0 : ℝ) < 2 ^ t := by positivity
  have hle := Nat.floor_le (mul_nonneg (le_of_lt h2) (hπ l))
  rw [div_le_iff₀ h2, mul_comm (π l) ((2 : ℝ) ^ t)]
  exact hle

/-- per-label truncation error -/
theorem sub_dyadicTrunc_lt {L : Type*} {π : L → ℝ} (hπ : ∀ l, 0 ≤ π l) (t : ℕ) (l : L) : π l - dyadicTrunc π t l < 1 / 2 ^ t := by
  unfold dyadicTrunc
  have h2 : (0 : ℝ) < 2 ^ t := by positivity
  have h2ne : (2 : ℝ) ^ t ≠ 0 := ne_of_gt h2
  have h := Nat.lt_floor_add_one ((2 : ℝ) ^ t * π l)
  have hmul : π l * 2 ^ t < (⌊(2 : ℝ) ^ t * π l⌋₊ : ℝ) + 1 := by
    rw [mul_comm (π l) ((2 : ℝ) ^ t)]
    exact h
  have key : (π l - (⌊(2 : ℝ) ^ t * π l⌋₊ : ℝ) / 2 ^ t) * 2 ^ t < 1 := by
    rw [sub_mul, div_mul_cancel₀ _ h2ne]
    linarith
  have key2 : (π l - (⌊(2 : ℝ) ^ t * π l⌋₊ : ℝ) / 2 ^ t) * 2 ^ t < (1 / 2 ^ t) * 2 ^ t := by
    rw [one_div_mul_cancel h2ne]
    exact key
  exact lt_of_mul_lt_mul_right key2 (le_of_lt h2)

/-- The truncated value is a nonnegative dyadic rational with denominator `2 ^ t`. -/
theorem exists_nat_eq_dyadicTrunc {L : Type*} (π : L → ℝ) (t : ℕ) (l : L) : ∃ n : ℕ, dyadicTrunc π t l = n / 2 ^ t := by
  exact ⟨⌊(2 : ℝ) ^ t * π l⌋₊, rfl⟩

/-- For a probability mass `π l ≤ 1`, the dyadic numerator is at most
`2 ^ t`, so the truncated value is realizable with `t` fair coins. -/
theorem exists_nat_le_eq_dyadicTrunc {L : Type*} {π : L → ℝ} (hπ : ∀ l, π l ≤ 1)
    (t : ℕ) (l : L) : ∃ n : ℕ, n ≤ 2 ^ t ∧ dyadicTrunc π t l = n / 2 ^ t := by
  refine ⟨⌊(2 : ℝ) ^ t * π l⌋₊, ?_, rfl⟩
  have h2 : (0 : ℝ) < 2 ^ t := by positivity
  have hle : (2 : ℝ) ^ t * π l ≤ (2 ^ t : ℕ) := by
    have h := mul_le_mul_of_nonneg_left (hπ l) (le_of_lt h2)
    simpa using h
  exact Nat.floor_le_of_le hle

/-- reject outcome is a genuine probability -/
theorem dyadicLeftover_nonneg {L : Type*} [Fintype L] {π : L → ℝ} (hπ : ∀ l, 0 ≤ π l) (hsum : ∑ l, π l = 1) (t : ℕ) : 0 ≤ dyadicLeftover π t := by
  unfold dyadicLeftover
  have hle : ∑ l, dyadicTrunc π t l ≤ ∑ l, π l :=
    Finset.sum_le_sum (fun l _ => dyadicTrunc_le hπ t l)
  rw [hsum] at hle
  linarith

theorem dyadicLeftover_le {L : Type*} [Fintype L] {π : L → ℝ} (hπ : ∀ l, 0 ≤ π l) (hsum : ∑ l, π l = 1) (t : ℕ) : dyadicLeftover π t ≤ Fintype.card L / 2 ^ t := by
  rw [dyadicLeftover_eq_sum_sub π hsum t]
  calc ∑ l, (π l - dyadicTrunc π t l)
      ≤ ∑ _ : L, ((1 : ℝ) / 2 ^ t) :=
        Finset.sum_le_sum (fun l _ => le_of_lt (sub_dyadicTrunc_lt hπ t l))
    _ = Fintype.card L / 2 ^ t := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div]

/-- Total truncation error including the reject atom is at most `2K / 2 ^ t`. -/
theorem sum_abs_sub_dyadicTrunc_add_leftover_le {L : Type*} [Fintype L] {π : L → ℝ} (hπ : ∀ l, 0 ≤ π l) (hsum : ∑ l, π l = 1) (t : ℕ) : ∑ l, |π l - dyadicTrunc π t l| + dyadicLeftover π t ≤ 2 * Fintype.card L / 2 ^ t := by
  have habs : ∀ l, |π l - dyadicTrunc π t l| = π l - dyadicTrunc π t l :=
    fun l => abs_of_nonneg (sub_nonneg.mpr (dyadicTrunc_le hπ t l))
  have hsum' : ∑ l, |π l - dyadicTrunc π t l| = dyadicLeftover π t := by
    rw [dyadicLeftover_eq_sum_sub π hsum t]
    exact Finset.sum_congr rfl (fun l _ => habs l)
  rw [hsum']
  have hle := dyadicLeftover_le hπ hsum t
  calc dyadicLeftover π t + dyadicLeftover π t
      ≤ 2 * (Fintype.card L / 2 ^ t) := by linarith
    _ = 2 * Fintype.card L / 2 ^ t := (mul_div_assoc _ _ _).symm

/-- acceptance error; the reject outcome accepts with probability 0 so contributes no term -/
theorem abs_acceptance_sub_le {L : Type*} [Fintype L] {π : L → ℝ} (hπ : ∀ l, 0 ≤ π l) (hsum : ∑ l, π l = 1) (t : ℕ) (acc : L → ℝ) (hacc : ∀ l, acc l ∈ Set.Icc (0 : ℝ) 1) : |∑ l, π l * acc l - ∑ l, dyadicTrunc π t l * acc l| ≤ 2 * Fintype.card L / 2 ^ t := by
  have hdiff : (∑ l, π l * acc l) - (∑ l, dyadicTrunc π t l * acc l)
      = ∑ l, ((π l - dyadicTrunc π t l) * acc l) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  rw [hdiff]
  calc |∑ l, ((π l - dyadicTrunc π t l) * acc l)|
      ≤ ∑ l, |(π l - dyadicTrunc π t l) * acc l| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ l, ((π l - dyadicTrunc π t l) * acc l) :=
        Finset.sum_congr rfl (fun l _ => abs_of_nonneg
          (mul_nonneg (sub_nonneg.mpr (dyadicTrunc_le hπ t l)) (Set.mem_Icc.mp (hacc l)).1))
    _ ≤ ∑ l, (π l - dyadicTrunc π t l) := by
        apply Finset.sum_le_sum
        intro l _
        have h1 : acc l ≤ 1 := (Set.mem_Icc.mp (hacc l)).2
        have h0 : (0 : ℝ) ≤ π l - dyadicTrunc π t l := sub_nonneg.mpr (dyadicTrunc_le hπ t l)
        calc (π l - dyadicTrunc π t l) * acc l
            ≤ (π l - dyadicTrunc π t l) * 1 := mul_le_mul_of_nonneg_left h1 h0
          _ = π l - dyadicTrunc π t l := mul_one _
    _ = dyadicLeftover π t := (dyadicLeftover_eq_sum_sub π hsum t).symm
    _ ≤ 2 * Fintype.card L / 2 ^ t := by
        have hle := dyadicLeftover_le hπ hsum t
        have hnn := dyadicLeftover_nonneg hπ hsum t
        have hC : (0 : ℝ) ≤ Fintype.card L / 2 ^ t := by positivity
        calc dyadicLeftover π t
            ≤ 2 * (Fintype.card L / 2 ^ t) := by linarith
          _ = 2 * Fintype.card L / 2 ^ t := (mul_div_assoc _ _ _).symm

/-- t = max(0, ⌈log2(16K/γ)⌉): nonnegative by construction (Nat.clog) -/
noncomputable def dyadicPrecision (K : ℕ) (γ : ℝ) : ℕ := Nat.clog 2 ⌈16 * (K : ℝ) / γ⌉₊

/-- The precision choice makes `2K / 2 ^ t ≤ γ / 8`. -/
theorem two_mul_div_two_pow_dyadicPrecision_le (K : ℕ) {γ : ℝ} (hγ : 0 < γ) : 2 * (K : ℝ) / 2 ^ dyadicPrecision K γ ≤ γ / 8 := by
  unfold dyadicPrecision
  set N := ⌈16 * (K : ℝ) / γ⌉₊
  have h2t : (0 : ℝ) < 2 ^ Nat.clog 2 N := by positivity
  have hN_le : (N : ℝ) ≤ 2 ^ Nat.clog 2 N := by
    exact_mod_cast Nat.le_pow_clog (show (1 : ℕ) < 2 by norm_num) N
  have hceil : 16 * (K : ℝ) / γ ≤ (N : ℝ) := Nat.le_ceil _
  have h1 : 16 * (K : ℝ) ≤ 2 ^ Nat.clog 2 N * γ := (div_le_iff₀ hγ).mp (le_trans hceil hN_le)
  rw [div_le_iff₀ h2t, div_mul_eq_mul_div, le_div_iff₀ (show (0 : ℝ) < 8 by norm_num)]
  rw [mul_comm ((2 : ℝ) ^ Nat.clog 2 N) γ] at h1
  linarith

/-- precision size bound (arithmetic half of the charged bit complexity) -/
theorem two_pow_dyadicPrecision_le (K : ℕ) {γ : ℝ} (hγ : 0 < γ) : 2 ^ dyadicPrecision K γ ≤ 2 * max 1 ⌈16 * (K : ℝ) / γ⌉₊ := by
  unfold dyadicPrecision
  set N := ⌈16 * (K : ℝ) / γ⌉₊
  by_cases hN1 : N ≤ 1
  · rw [Nat.clog_of_right_le_one hN1, pow_zero]
    have h1 : (1 : ℕ) ≤ max 1 N := le_max_left 1 N
    omega
  · have hN1' : 1 < N := by omega
    have hpos : 0 < Nat.clog 2 N := Nat.clog_pos (show (1 : ℕ) < 2 by norm_num) hN1'
    have hpred := Nat.pow_pred_clog_lt_self 2 hN1'
    have hsplit : (Nat.clog 2 N).pred + 1 = Nat.clog 2 N := Nat.succ_pred_eq_of_pos hpos
    have hmax : max 1 N = N := max_eq_right (by omega)
    rw [hmax]
    conv_lhs => rw [← hsplit, pow_add, pow_one]
    omega

end MathlibExt.Probability.DyadicTruncation
