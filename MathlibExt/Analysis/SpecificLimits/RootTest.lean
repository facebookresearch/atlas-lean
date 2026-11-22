/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Cauchy's root test for series

For a series `∑ n, f n`, if the `n`-th roots `‖f n‖ ^ (1 / n)` tend to a limit
`l < 1`, then the series converges (absolutely); if they tend to a limit
`l > 1`, then the series diverges. This is the root-test counterpart of
Mathlib's ratio test (`summable_of_ratio_test_tendsto_lt_one` and
`not_summable_of_ratio_test_tendsto_gt_one`), which Mathlib does not provide.

## Main results

* `summable_norm_of_root_test_tendsto_lt_one`: absolute convergence when the root limit is `< 1`.
* `summable_of_root_test_tendsto_lt_one`: convergence in a complete normed group.
* `not_summable_of_root_test_tendsto_gt_one`: divergence when the root limit is `> 1`.

Source: `v1/Atlas/RealAnalysis/targets.yaml`, Theorem (Root Test),
"Series section": if `L = lim |x n| ^ (1/n)` exists, then `L < 1` implies
`∑ |x n|` converges and `L > 1` implies `∑ x n` diverges. The v1
formalization `Series.root_test` in
`v1/Atlas/RealAnalysis/code/Series/ConvergenceTests.lean` states this only for
`ℝ`-valued series, as a single conjunction. Here it is generalized to
normed groups, following Mathlib's ratio test, and split into absolute
convergence and divergence. Ordinary convergence is a corollary in a complete
normed group.
-/

@[expose] public section

open scoped Topology

variable {α : Type*} {f : ℕ → α}

/-- **Cauchy's root test, absolute convergence case.** If `‖f n‖ ^ (1 / n)` tends
to a limit `l < 1`, then `∑ n, ‖f n‖` converges. -/
theorem summable_norm_of_root_test_tendsto_lt_one [NormedAddCommGroup α]
    {l : ℝ} (hl : l < 1)
    (h : Filter.Tendsto (fun n => ‖f n‖ ^ ((1 : ℝ) / n)) Filter.atTop (𝓝 l)) :
    Summable (fun n => ‖f n‖) := by
  obtain ⟨r, hLr, hr1⟩ := exists_between hl
  have hr0 : 0 ≤ r := by
    have hL0 : 0 ≤ l := by
      apply ge_of_tendsto h
      apply Filter.Eventually.of_forall
      intro n
      exact Real.rpow_nonneg (norm_nonneg _) _
    linarith
  have hev : ∀ᶠ n in Filter.atTop, ‖f n‖ ^ ((1 : ℝ) / n) < r := h (Iio_mem_nhds hLr)
  apply Summable.of_norm_bounded_eventually_nat
    (g := fun n => r ^ n) (summable_geometric_of_lt_one hr0 hr1)
  have hev1 : ∀ᶠ n in Filter.atTop, 1 ≤ n :=
    Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩
  apply (hev.and hev1).mono
  intro n ⟨hn_lt, hn_pos⟩
  rw [norm_norm]
  have hn_ne : (n : ℕ) ≠ 0 := by omega
  have h_eq : (1 : ℝ) / (↑n : ℝ) = (↑n : ℝ)⁻¹ := one_div _
  rw [h_eq] at hn_lt
  have h1 : (‖f n‖ ^ ((↑n : ℝ)⁻¹)) ^ n ≤ r ^ n := by
    apply pow_le_pow_left₀ (Real.rpow_nonneg (norm_nonneg _) _)
    exact le_of_lt hn_lt
  rwa [Real.rpow_inv_natCast_pow (norm_nonneg _) hn_ne] at h1

/-- **Cauchy's root test, convergence case.** If `‖f n‖ ^ (1 / n)` tends to a
limit `l < 1`, then `∑ n, f n` converges. -/
theorem summable_of_root_test_tendsto_lt_one [NormedAddCommGroup α] [CompleteSpace α]
    {l : ℝ} (hl : l < 1)
    (h : Filter.Tendsto (fun n => ‖f n‖ ^ ((1 : ℝ) / n)) Filter.atTop (𝓝 l)) :
    Summable f :=
  (summable_norm_of_root_test_tendsto_lt_one hl h).of_norm

/-- **Cauchy's root test, divergence case.** If `‖f n‖ ^ (1 / n)` tends to a
limit `l > 1`, then `∑ n, f n` diverges. -/
theorem not_summable_of_root_test_tendsto_gt_one [SeminormedAddCommGroup α]
    {l : ℝ} (hl : 1 < l)
    (h : Filter.Tendsto (fun n => ‖f n‖ ^ ((1 : ℝ) / n)) Filter.atTop (𝓝 l)) :
    ¬Summable f := by
  have hev : ∀ᶠ n in Filter.atTop, 1 < ‖f n‖ ^ ((1 : ℝ) / n) := h (Ioi_mem_nhds hl)
  have hev1 : ∀ᶠ n in Filter.atTop, 1 < ‖f n‖ := by
    have hev_pos : ∀ᶠ n in Filter.atTop, 1 ≤ n :=
      Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩
    apply (hev.and hev_pos).mono
    intro n ⟨hn_gt, hn_pos⟩
    have hn_ne : (n : ℕ) ≠ 0 := by omega
    have h_eq : (1 : ℝ) / (↑n : ℝ) = (↑n : ℝ)⁻¹ := one_div _
    rw [h_eq] at hn_gt
    have h1 : (1 : ℝ) ^ n < (‖f n‖ ^ ((↑n : ℝ)⁻¹)) ^ n := by
      apply pow_lt_pow_left₀ hn_gt (le_of_lt zero_lt_one) hn_ne
    rw [one_pow, Real.rpow_inv_natCast_pow (norm_nonneg _) hn_ne] at h1
    exact h1
  intro hsum
  have h0 := hsum.tendsto_atTop_zero
  have hnorm0 : Filter.Tendsto (fun n => ‖f n‖) Filter.atTop (𝓝 0) := by
    have hnorm := h0.norm
    simpa using hnorm
  have h2 : ∀ᶠ n in Filter.atTop, ‖f n‖ < 1 := hnorm0 (Iio_mem_nhds one_pos)
  obtain ⟨n, hn1, hn2⟩ := (h2.and hev1).exists
  linarith
