/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Coding.ListDecodingCapacity

open MathlibExt.Combinatorics.Coding.ListDecoding
open MathlibExt.Combinatorics.Coding.ListDecodingCapacity

-- The generic statement, with its hypotheses.
example {α : Type*} [Fintype α] [DecidableEq α] (hq : 2 ≤ Fintype.card α) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1 - 1 / (Fintype.card α : ℝ)) {L : ℕ} (hL : 1 ≤ L) (n k : ℕ)
    (hk : (k : ℝ) ≤
      (1 - Real.qaryEntropy (Fintype.card α) ρ / Real.log (Fintype.card α) - 1 / (L : ℝ)) * n) :
    ∃ C : Finset (Fin n → α), IsListDecodable C ⌊ρ * n⌋₊ L ∧ Fintype.card α ^ k ≤ L * C.card :=
  exists_isListDecodable hq hρ0 hρ1 hL n k hk

-- A non-degenerate instance: binary codes with `q ^ {⌊n/4⌋}` messages and lists of size `2`,
-- for a small radius fraction `ρ > 0` (one with `H_2(ρ) ≤ 1/4`, by continuity of the entropy at 0).
example (n : ℕ) : ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : (Fin (n / 4) → Bool) → (Fin n → Bool),
    ∀ y : Fin n → Bool,
      (Finset.univ.filter fun m => (hammingDist y (C m) : ℝ) ≤ ρ * n).card ≤ 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : ContinuousAt (Real.qaryEntropy 2) 0 := Real.qaryEntropy_continuous.continuousAt
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.mp hc (Real.log 2 / 4) (by positivity)
  set ρ := min (δ / 2) (1 / 4) with hρ
  have hρ0 : 0 < ρ := lt_min (by positivity) (by norm_num)
  have hρ1 : ρ ≤ 1 / 4 := min_le_right _ _
  have hH : Real.qaryEntropy 2 ρ ≤ Real.log 2 / 4 := by
    have h := hδc (x := ρ) (by
      rw [Real.dist_eq, sub_zero, abs_of_pos hρ0]
      exact (min_le_left _ _).trans_lt (by linarith))
    rw [Real.dist_eq, Real.qaryEntropy_zero, sub_zero] at h
    exact (le_abs_self _).trans h.le
  refine ⟨ρ, hρ0, exists_encoding_listDecodable (α := Bool) (by simp) hρ0
    (by simp; linarith) (L := 2) (by norm_num) n (n / 4) ?_⟩
  simp only [Fintype.card_bool, Nat.cast_ofNat]
  have h1 : Real.qaryEntropy 2 ρ / Real.log 2 ≤ 1 / 4 := by
    rw [div_le_iff₀ hlog]; linarith
  have h2 : ((n / 4 : ℕ) : ℝ) ≤ n / 4 := Nat.cast_div_le
  have h3 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

-- The converse, with its hypotheses.
example {α : Type*} [Fintype α] [DecidableEq α] (hq : 2 ≤ Fintype.card α) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1 - 1 / (Fintype.card α : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ C : Finset (Fin n → α),
      Real.exp (n * (Real.log (Fintype.card α) - Real.qaryEntropy (Fintype.card α) ρ +
        ε * Real.log (Fintype.card α))) ≤ C.card →
      ∃ y : Fin n → α, Real.exp (ε * n / 2 * Real.log (Fintype.card α)) ≤
        ((C.filter fun c => (hammingDist y c : ℝ) ≤ ρ * n).card : ℝ) :=
  exists_many_in_ball hq hρ0 hρ1 hε

-- A non-vacuous instance of the converse: binary, `ε = 1/4`, and a radius fraction `ρ < 1/2`
-- with `H_2(ρ) ≥ 1/2` bit (by continuity of the entropy at `1/2`). The whole space `{0,1}ⁿ` has
-- enough words, so for large `n` some ball of radius `ρn` holds at least `2^{n/8}` words.
example : ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 / 2 ∧ ∃ N : ℕ, ∀ n ≥ N, ∃ y : Fin n → Bool,
    Real.exp (1 / 4 * n / 2 * Real.log 2) ≤
      (((Finset.univ : Finset (Fin n → Bool)).filter
        fun c => (hammingDist y c : ℝ) ≤ ρ * n).card : ℝ) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : ContinuousAt (Real.qaryEntropy 2) (1 / 2) := Real.qaryEntropy_continuous.continuousAt
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.mp hc (Real.log 2 / 2) (by positivity)
  set ρ := max (1 / 2 - δ / 2) (1 / 4) with hρ
  have hρ0 : 0 < ρ := lt_max_of_lt_right (by norm_num)
  have hρ1 : ρ < 1 / 2 := max_lt (by linarith) (by norm_num)
  have hH : Real.log 2 / 4 ≤ Real.qaryEntropy 2 ρ := by
    have h := hδc (x := ρ) (by
      rw [Real.dist_eq, abs_lt]
      constructor
      · have : 1 / 2 - δ / 2 ≤ ρ := le_max_left _ _
        linarith
      · linarith)
    rw [Real.dist_eq, abs_lt] at h
    have h12 : Real.qaryEntropy 2 (1 / 2) = Real.log 2 := by
      rw [Real.qaryEntropy_two, one_div, Real.binEntropy_two_inv]
    linarith [h.1]
  obtain ⟨N, hN⟩ := exists_many_in_ball (α := Bool) (by simp) hρ0
    (by simp; linarith) (ε := 1 / 4) (by norm_num)
  refine ⟨ρ, hρ0, hρ1, N, fun n hn => ?_⟩
  obtain ⟨y, hy⟩ := hN n hn Finset.univ (by
    simp only [Fintype.card_bool, Nat.cast_ofNat, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin]
    push_cast
    rw [← Real.exp_log (by positivity : (0 : ℝ) < 2 ^ n), Real.log_pow]
    refine Real.exp_le_exp.mpr ?_
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith)
  exact ⟨y, by simpa using hy⟩
