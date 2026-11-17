/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecificLimits.DirichletTest
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Tests for the quantitative Dirichlet test

The alternating harmonic series `∑ (-1)ⁱ / (i + 1)` is the model example.
-/

@[expose] public section

open Filter Finset

/-- The partial sums of `(-1)ⁱ` are `0` or `1`. -/
private lemma norm_sum_neg_one_pow_le (m k : ℕ) :
    ‖∑ i ∈ Ico m k, ((-1 : ℝ) ^ i)‖ ≤ 1 := by
  have key : ∀ n : ℕ, (∑ i ∈ range n, ((-1 : ℝ) ^ i)) = (1 - (-1) ^ n) / 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, ih, pow_succ]; ring
  rcases le_total m k with hmk | hkm
  · rw [sum_Ico_eq_sub _ hmk, key, key, Real.norm_eq_abs]
    rcases neg_one_pow_eq_or ℝ m with h1 | h1 <;> rcases neg_one_pow_eq_or ℝ k with h2 | h2 <;>
      rw [h1, h2] <;> norm_num
  · rw [Ico_eq_empty_of_le hkm, sum_empty, norm_zero]
    exact zero_le_one

private lemma antitone_inv_succ : AntitoneOn (fun i : ℕ => 1 / ((i : ℝ) + 1)) (Set.Ici 0) :=
  fun a _ b _ hab => by
    simp only
    gcongr

/-- **Dirichlet with error bound.** The alternating harmonic series converges, and its sum
lies within `f 0 = 1` of the empty partial sum. -/
example : ∃ S : ℝ, Tendsto (fun n => ∑ i ∈ range n, (1 / ((i : ℝ) + 1)) • ((-1 : ℝ) ^ i)) atTop
    (nhds S) ∧ ‖S - ∑ i ∈ range 0, (1 / ((i : ℝ) + 1)) • ((-1 : ℝ) ^ i)‖ ≤ 1 * (1 / (0 + 1)) := by
  have h := exists_tendsto_sum_range_smul_and_norm_sub_le (m := 0) (b := 1) antitone_inv_succ
    tendsto_one_div_add_atTop_nhds_zero_nat (norm_sum_neg_one_pow_le 0)
  simpa using h

/-- The tail bound beyond `m = 3`: `‖S - (1 - 1/2 + 1/3)‖ ≤ 1/4`. -/
example {S : ℝ} (hS : Tendsto (fun n => ∑ i ∈ range n, (1 / ((i : ℝ) + 1)) • ((-1 : ℝ) ^ i))
    atTop (nhds S)) :
    ‖S - ∑ i ∈ range 3, (1 / ((i : ℝ) + 1)) • ((-1 : ℝ) ^ i)‖ ≤ 1 * (1 / ((3 : ℕ) + 1)) :=
  norm_sub_sum_range_smul_le_of_tendsto (antitone_inv_succ.mono (Set.Ici_subset_Ici.mpr
    (Nat.zero_le 3))) (fun _ _ => by positivity) (norm_sum_neg_one_pow_le 3) hS

/-- Abel's inequality. -/
example (n : ℕ) : ‖∑ i ∈ Ico 0 n, (1 / ((i : ℝ) + 1)) • ((-1 : ℝ) ^ i)‖ ≤ 1 * (1 / ((0 : ℕ) + 1)) :=
  norm_sum_Ico_smul_le_of_antitoneOn antitone_inv_succ (fun _ _ => by positivity)
    (norm_sum_neg_one_pow_le 0) n

example : CauchySeq fun n => ∑ i ∈ range n, (1 / ((i : ℝ) + 1)) • ((-1 : ℝ) ^ i) :=
  cauchySeq_sum_range_smul_of_antitoneOn antitone_inv_succ tendsto_one_div_add_atTop_nhds_zero_nat
    (norm_sum_neg_one_pow_le 0)

/-- Monotone only from `m = 2` on: `f = (5, 0, 1/3, 1/4, …)`. -/
example (k : ℕ) (hk : 2 ≤ k) :
    0 ≤ (fun i : ℕ => if i = 0 then (5 : ℝ) else if i = 1 then 0 else 1 / ((i : ℝ) + 1)) k := by
  refine AntitoneOn.nonneg_of_tendsto_zero (m := 2)
    (f := fun i : ℕ => if i = 0 then (5 : ℝ) else if i = 1 then 0 else 1 / ((i : ℝ) + 1))
    (fun a ha b hb hab => ?_) ?_ hk
  · simp only [Set.mem_Ici] at ha hb
    simp only [show a ≠ 0 by omega, show a ≠ 1 by omega, show b ≠ 0 by omega,
      show b ≠ 1 by omega, ite_false]
    gcongr
  · refine (tendsto_one_div_add_atTop_nhds_zero_nat).congr' ?_
    filter_upwards [eventually_ge_atTop 2] with i hi
    simp [show i ≠ 0 by omega, show i ≠ 1 by omega]
