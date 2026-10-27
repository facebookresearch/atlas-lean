/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.MetricSpace.Cauchy

import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Dirichlet's test with an explicit error bound

Mathlib's `Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded` shows that
`∑ f i • z i` converges when `f` decreases to `0` and the partial sums of `z` are bounded.
This file records the quantitative form of this test: if `f` is nonincreasing and nonnegative
from `m` on, and every sum `∑_{m ≤ i < k} z i` has norm at most `b`, then every block
`∑_{m ≤ i < n} f i • z i` has norm at most `b * f m` (Abel's inequality). Consequently the tail
of the series beyond `m` is bounded by `b * f m`.

## Main statements

* `norm_sum_Ico_smul_le_of_antitoneOn`: Abel's inequality for a block of the series.
* `norm_sub_sum_range_smul_le_of_tendsto`: the tail of a convergent series is at most `b * f m`.
* `cauchySeq_sum_range_smul_of_antitoneOn`: Dirichlet's test for a sequence that is only
  eventually nonincreasing.
* `exists_tendsto_sum_range_smul_and_norm_sub_le`: Dirichlet's test together with the tail
  bound.
-/

@[expose] public section

open Filter Finset

open scoped Topology

variable {E : Type*}

section Seminormed

variable [SeminormedAddCommGroup E] [NormedSpace ℝ E] {f : ℕ → ℝ} {z : ℕ → E} {m : ℕ} {b : ℝ}

/-- **Abel's inequality.** If `f` is nonincreasing and nonnegative on `[m, ∞)`, and all the
sums `∑_{m ≤ i < k} z i` have norm at most `b`, then `‖∑_{m ≤ i < n} f i • z i‖ ≤ b * f m`. -/
theorem norm_sum_Ico_smul_le_of_antitoneOn (hf : AntitoneOn f (Set.Ici m))
    (hf0 : ∀ k, m ≤ k → 0 ≤ f k) (hz : ∀ k, ‖∑ i ∈ Ico m k, z i‖ ≤ b) (n : ℕ) :
    ‖∑ i ∈ Ico m n, f i • z i‖ ≤ b * f m := by
  have hb : 0 ≤ b := by simpa using hz m
  rcases lt_or_ge n m with hnm | hmn
  · rw [Ico_eq_empty_of_le hnm.le, sum_empty, norm_zero]
    exact mul_nonneg hb (hf0 m le_rfl)
  -- Summation by parts, as an inequality proved by induction on `n`.
  have key : ∀ n, m ≤ n →
      ‖∑ i ∈ Ico m n, f i • z i - f n • ∑ i ∈ Ico m n, z i‖ ≤ b * (f m - f n) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have hmono : f (n + 1) ≤ f n :=
        hf (Set.mem_Ici.2 hmn) (Set.mem_Ici.2 (by omega)) (Nat.le_succ n)
      rw [sum_Ico_succ_top hmn, sum_Ico_succ_top hmn]
      calc ‖∑ i ∈ Ico m n, f i • z i + f n • z n - f (n + 1) • (∑ i ∈ Ico m n, z i + z n)‖
          = ‖(∑ i ∈ Ico m n, f i • z i - f n • ∑ i ∈ Ico m n, z i)
              + (f n - f (n + 1)) • (∑ i ∈ Ico m n, z i + z n)‖ := by
            congr 1
            simp only [sub_smul, smul_add]
            abel
        _ ≤ b * (f m - f n) + (f n - f (n + 1)) * b := by
            refine (norm_add_le _ _).trans (add_le_add ih ?_)
            rw [norm_smul, Real.norm_of_nonneg (by linarith), ← sum_Ico_succ_top hmn]
            exact mul_le_mul_of_nonneg_left (hz _) (by linarith)
        _ = b * (f m - f (n + 1)) := by ring
  have h1 := key n hmn
  have h2 : ‖f n • ∑ i ∈ Ico m n, z i‖ ≤ f n * b := by
    rw [norm_smul, Real.norm_of_nonneg (hf0 n hmn)]
    exact mul_le_mul_of_nonneg_left (hz n) (hf0 n hmn)
  calc ‖∑ i ∈ Ico m n, f i • z i‖
      = ‖(∑ i ∈ Ico m n, f i • z i - f n • ∑ i ∈ Ico m n, z i)
          + f n • ∑ i ∈ Ico m n, z i‖ := by rw [sub_add_cancel]
    _ ≤ b * (f m - f n) + f n * b := (norm_add_le _ _).trans (add_le_add h1 h2)
    _ = b * f m := by ring

/-- **The tail of a series in Dirichlet's test.** If `f` is nonincreasing and nonnegative on
`[m, ∞)`, all the sums `∑_{m ≤ i < k} z i` have norm at most `b`, and the series `∑ f i • z i`
converges to `S`, then `‖S - ∑_{i < m} f i • z i‖ ≤ b * f m`. -/
theorem norm_sub_sum_range_smul_le_of_tendsto (hf : AntitoneOn f (Set.Ici m))
    (hf0 : ∀ k, m ≤ k → 0 ≤ f k) (hz : ∀ k, ‖∑ i ∈ Ico m k, z i‖ ≤ b) {S : E}
    (hS : Tendsto (fun n ↦ ∑ i ∈ range n, f i • z i) atTop (𝓝 S)) :
    ‖S - ∑ i ∈ range m, f i • z i‖ ≤ b * f m := by
  refine le_of_tendsto ((hS.sub_const _).norm) ?_
  filter_upwards [eventually_ge_atTop m] with n hn
  rw [← sum_Ico_eq_sub _ hn]
  exact norm_sum_Ico_smul_le_of_antitoneOn hf hf0 hz n

end Seminormed

section Normed

variable [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℕ → ℝ} {z : ℕ → E} {m : ℕ} {b : ℝ}

/-- A function that is nonincreasing on `[m, ∞)` and tends to `0` is nonnegative there. -/
theorem AntitoneOn.nonneg_of_tendsto_zero {f : ℕ → ℝ} {m : ℕ} (hf : AntitoneOn f (Set.Ici m))
    (hf0 : Tendsto f atTop (𝓝 0)) {k : ℕ} (hk : m ≤ k) : 0 ≤ f k := by
  refine le_of_tendsto hf0 ?_
  filter_upwards [eventually_ge_atTop k] with j hj
  exact hf (Set.mem_Ici.2 hk) (Set.mem_Ici.2 (hk.trans hj)) hj

/-- **Dirichlet's test** for a sequence that is nonincreasing from `m` on: if `f` tends to `0`
and the sums `∑_{m ≤ i < k} z i` are bounded, then `∑ f i • z i` is a Cauchy series. -/
theorem cauchySeq_sum_range_smul_of_antitoneOn (hf : AntitoneOn f (Set.Ici m))
    (hf0 : Tendsto f atTop (𝓝 0)) (hz : ∀ k, ‖∑ i ∈ Ico m k, z i‖ ≤ b) :
    CauchySeq fun n ↦ ∑ i ∈ range n, f i • z i := by
  have hnn := fun k (hk : m ≤ k) ↦ hf.nonneg_of_tendsto_zero hf0 hk
  -- Sums of `z` over blocks starting at any `j ≥ m` are bounded by `2 * b`.
  have hz' : ∀ j, m ≤ j → ∀ k, ‖∑ i ∈ Ico j k, z i‖ ≤ 2 * b := by
    intro j hj k
    have hb : 0 ≤ b := by simpa using hz m
    rcases lt_or_ge k j with hkj | hjk
    · rw [Ico_eq_empty_of_le hkj.le, sum_empty, norm_zero]
      positivity
    · have h := sum_Ico_consecutive z hj hjk
      calc ‖∑ i ∈ Ico j k, z i‖ = ‖∑ i ∈ Ico m k, z i - ∑ i ∈ Ico m j, z i‖ := by
            rw [← h, add_sub_cancel_left]
        _ ≤ b + b := (norm_sub_le _ _).trans (add_le_add (hz k) (hz j))
        _ = 2 * b := by ring
  rw [← cauchySeq_shift m]
  refine cauchySeq_of_le_tendsto_0' (fun n ↦ 2 * b * f (n + m)) (fun n k hnk ↦ ?_) ?_
  · rw [dist_eq_norm, norm_sub_rev, ← sum_Ico_eq_sub _ (by omega)]
    exact norm_sum_Ico_smul_le_of_antitoneOn (hf.mono (Set.Ici_subset_Ici.2 (by omega)))
      (fun k hk ↦ hnn k (by omega)) (hz' (n + m) (by omega)) _
  · simpa using (hf0.comp (tendsto_add_atTop_nat m)).const_mul (2 * b)

/-- **Dirichlet's test with an error bound.** If `f` is nonincreasing on `[m, ∞)` and tends to
`0`, and all the sums `∑_{m ≤ i < k} z i` have norm at most `b`, then `∑ f i • z i` converges,
and its tail beyond `m` has norm at most `b * f m`. -/
theorem exists_tendsto_sum_range_smul_and_norm_sub_le [CompleteSpace E]
    (hf : AntitoneOn f (Set.Ici m)) (hf0 : Tendsto f atTop (𝓝 0))
    (hz : ∀ k, ‖∑ i ∈ Ico m k, z i‖ ≤ b) :
    ∃ S : E, Tendsto (fun n ↦ ∑ i ∈ range n, f i • z i) atTop (𝓝 S) ∧
      ‖S - ∑ i ∈ range m, f i • z i‖ ≤ b * f m := by
  obtain ⟨S, hS⟩ := cauchySeq_tendsto_of_complete (cauchySeq_sum_range_smul_of_antitoneOn hf hf0 hz)
  exact ⟨S, hS, norm_sub_sum_range_smul_le_of_tendsto hf
    (fun k hk ↦ hf.nonneg_of_tendsto_zero hf0 hk) hz hS⟩

end Normed
