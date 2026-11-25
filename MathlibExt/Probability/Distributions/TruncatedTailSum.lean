/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Truncated curtate expectation as a finite tail sum

For a lifetime `T` on a probability space and a finite horizon `n`, the
expectation of the truncated curtate lifetime `min ⌊T⌋₊ n` is the finite
tail sum `∑ k ∈ Finset.Icc 1 n, P (k ≤ T)`
(`integral_min_natFloor_eq_sum`). The integer tail is nonstrict: an atom at
`T = 1` contributes `1`, where a strict tail would contribute `0`. No
unbounded-tail summability or limit in `n` is claimed.
-/

@[expose] public section

open MeasureTheory

namespace MathlibExt.Probability.Finance.CurtateTruncation

/-- Pointwise count: `min ⌊t⌋₊ n` is the number of `k ∈ [1, n]` with `(k : ℝ) ≤ t`. -/
private theorem min_natFloor_eq_sum_boole (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    ((min ⌊t⌋₊ n : ℕ) : ℝ) = ∑ k ∈ Finset.Icc 1 n, (if (k : ℝ) ≤ t then (1:ℝ) else 0) := by
  classical
  have hiff : ∀ k : ℕ, ((k : ℝ) ≤ t ↔ k ≤ ⌊t⌋₊) := fun k => (Nat.le_floor_iff ht).symm
  simp only [hiff, Finset.sum_boole]
  have hset : ({x ∈ Finset.Icc 1 n | x ≤ ⌊t⌋₊} : Finset ℕ)
      = Finset.Icc 1 (min ⌊t⌋₊ n) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, le_min_iff]
    tauto
  rw [hset, Nat.card_Icc, Nat.add_sub_cancel]

/-- Truncated curtate expectation as a finite tail sum: for a lifetime `T`
on a probability space, the expectation of `min ⌊T⌋₊ n` is the sum over
`k = 1, …, n` of the probabilities `P (k ≤ T)`. -/
theorem integral_min_natFloor_eq_sum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → ℝ) (hT : Measurable T)
    (hTnn : 0 ≤ᵐ[μ] T) (n : ℕ) :
    ∫ ω, (min ⌊T ω⌋₊ n : ℝ) ∂μ =
      ∑ k ∈ Finset.Icc 1 n, (μ {ω | (k : ℝ) ≤ T ω}).toReal := by
  classical
  have hmeas : ∀ k : ℕ, MeasurableSet {ω | (k : ℝ) ≤ T ω} :=
    fun k => hT measurableSet_Ici
  have hterm : ∀ k : ℕ, ∀ ω : Ω, ({ω | (k : ℝ) ≤ T ω}).indicator (fun _ => (1:ℝ)) ω
      = (if (k : ℝ) ≤ T ω then (1:ℝ) else 0) := by
    intro k ω
    by_cases h : (k : ℝ) ≤ T ω
    · simp [h]
    · simp [h]
  have hTnn' : ∀ᵐ ω ∂μ, 0 ≤ T ω := hTnn
  have hEq : (fun ω => (min ⌊T ω⌋₊ n : ℝ)) =ᵐ[μ]
      (fun ω => ∑ k ∈ Finset.Icc 1 n, ({ω | (k : ℝ) ≤ T ω}).indicator (fun _ => (1:ℝ)) ω) := by
    filter_upwards [hTnn'] with ω hω
    show (min ⌊T ω⌋₊ n : ℝ) =
      ∑ k ∈ Finset.Icc 1 n, ({ω | (k : ℝ) ≤ T ω}).indicator (fun _ => (1:ℝ)) ω
    rw [← Nat.cast_min, min_natFloor_eq_sum_boole (T ω) hω n]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    exact (hterm k ω).symm
  have hInt : ∀ k ∈ Finset.Icc 1 n,
      Integrable (({ω | (k : ℝ) ≤ T ω}).indicator (fun _ => (1:ℝ))) μ := by
    intro k _
    exact (integrable_const (1:ℝ)).indicator (hmeas k)
  calc ∫ ω, (min ⌊T ω⌋₊ n : ℝ) ∂μ
      = ∫ ω, ∑ k ∈ Finset.Icc 1 n, ({ω | (k : ℝ) ≤ T ω}).indicator (fun _ => (1:ℝ)) ω ∂μ :=
        integral_congr_ae hEq
    _ = ∑ k ∈ Finset.Icc 1 n, ∫ ω, ({ω | (k : ℝ) ≤ T ω}).indicator (fun _ => (1:ℝ)) ω ∂μ :=
        integral_finsetSum _ hInt
    _ = ∑ k ∈ Finset.Icc 1 n, (μ {ω | (k : ℝ) ≤ T ω}).toReal := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [integral_indicator_const (1:ℝ) (hmeas k), smul_eq_mul, mul_one, Measure.real_def]

end MathlibExt.Probability.Finance.CurtateTruncation
