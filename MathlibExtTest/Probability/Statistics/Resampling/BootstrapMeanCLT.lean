/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Resampling.BootstrapMeanCLT

/-!
# Tests for the bootstrap mean CLT

Non-vacuity with the alternating sequence `(-1) ^ i` (limit `N(0, 1)`), and boundary checks: a
constant sequence has zero row variances, the empty row has row sum `0`, the empirical law of no
points is `0`, and `x i = i` violates the Cesàro second-moment hypothesis.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Complex Finset
open scoped Topology BoundedContinuousFunction NNReal ENNReal

namespace BootstrapMeanCLTTest

open MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction NNReal ENNReal

/-- Non-vacuity: the alternating sequence `x i = (-1) ^ i` has empirical mean `→ 0` and
empirical second moment `→ 1 = 1 ^ 2 + 0 ^ 2`, so the bootstrap mean law converges to
`N(0, 1)`. Prove via `tendsto_integral_bootstrapMean_law`. -/
example (f : ℝ →ᵇ ℝ) :
    Tendsto (fun n : ℕ => ∫ y, f y ∂(Measure.map
        (fun y : Fin n → ℝ => Real.sqrt n *
          ((n : ℝ)⁻¹ * ∑ i, y i - empiricalMean (fun i => (-1 : ℝ) ^ i) n))
        (Measure.pi fun _ : Fin n => empiricalLaw (fun i => (-1 : ℝ) ^ i) n)))
      atTop (𝓝 (∫ y, f y ∂(gaussianReal 0 ⟨(1 : ℝ) ^ 2, sq_nonneg 1⟩))) := by
  have hsum : ∀ n : ℕ, ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i = (1 - (-1) ^ n) / 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  have hmean : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i) atTop
      (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) tendsto_inv_atTop_nhds_zero_nat
    rw [hsum, norm_mul, norm_inv, Real.norm_natCast]
    refine mul_le_of_le_one_right (by positivity) ?_
    rcases neg_one_pow_eq_or ℝ n with h | h <;> rw [h] <;> norm_num
  have hsq : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ((-1 : ℝ) ^ i) ^ 2) atTop
      (𝓝 ((1 : ℝ) ^ 2 + 0 ^ 2)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have h1 : ∀ i : ℕ, ((-1 : ℝ) ^ i) ^ 2 = 1 := fun i => by
      rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    simp only [h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [inv_mul_cancel₀ (by exact_mod_cast hn.ne')]
    norm_num
  exact tendsto_integral_bootstrapMean_law (fun i => (-1 : ℝ) ^ i) one_pos hmean hsq f

/-- Boundary: a constant sequence has empirical variance `0`, so the row variances are `0`
and the hypothesis `0 < s` of the CLT cannot hold. -/
example (c : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n,
      ∫ ω, (bootstrapRow (fun _ => c) n k ω) ^ 2 ∂(bootstrapMeasure fun _ => c) = 0 := by
  refine Finset.sum_eq_zero fun k hk => ?_
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le k) (Finset.mem_range.1 hk)
  have hmean : empiricalMean (fun _ => c) n = c := by
    rw [empiricalMean_eq, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ (by exact_mod_cast hn.ne'), one_mul]
  have hlaw : empiricalLaw (fun _ => c) (max n 1) = Measure.dirac c := by
    rw [max_eq_left hn, empiricalLaw_eq, Finset.sum_const, Finset.card_range,
      ← Nat.cast_smul_eq_nsmul ℝ≥0∞, smul_smul,
      ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (ENNReal.natCast_ne_top n), one_smul]
  have hmp : MeasurePreserving (fun ω : ℕ → ℕ → ℝ => ω n k) (bootstrapMeasure fun _ => c)
      (Measure.dirac c) := by
    rw [← hlaw]
    exact (measurePreserving_eval_infinitePi
        (fun _ : ℕ => empiricalLaw (fun _ => c) (max n 1)) k).comp
      (measurePreserving_eval_infinitePi
        (fun n : ℕ => Measure.infinitePi fun _ : ℕ => empiricalLaw (fun _ => c) (max n 1)) n)
  calc ∫ ω, (bootstrapRow (fun _ => c) n k ω) ^ 2 ∂(bootstrapMeasure fun _ => c)
      = ∫ ω, (fun y : ℝ => ((y - c) / Real.sqrt n) ^ 2) (ω n k)
          ∂(bootstrapMeasure fun _ => c) := by
        simp only [bootstrapRow, hmean]
    _ = ∫ y, ((y - c) / Real.sqrt n) ^ 2 ∂(Measure.dirac c) := by
        rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable
          (Continuous.aestronglyMeasurable (by fun_prop))]
    _ = 0 := by simp

/-- Boundary: the empty row `n = 0` has row sum `0`. -/
example (x : ℕ → ℝ) :
    Measure.map (fun ω => ∑ k ∈ Finset.range 0, bootstrapRow x 0 k ω) (bootstrapMeasure x) =
      Measure.dirac 0 := by
  have : IsProbabilityMeasure (bootstrapMeasure x) := by
    unfold bootstrapMeasure
    infer_instance
  simp only [Finset.range_zero, Finset.sum_empty, Measure.map_const, measure_univ, one_smul]

/-- Boundary: the empirical law of zero points is the zero measure. -/
example (x : ℕ → ℝ) : empiricalLaw x 0 = 0 := by
  simp [empiricalLaw_eq]

/-- Boundary: the sequence `x i = i` violates the Cesàro second-moment hypothesis. -/
example : ¬ ∃ c : ℝ,
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ((i : ℕ) : ℝ) ^ 2) atTop (𝓝 c) := by
  rintro ⟨c, hc⟩
  have hlow : ∀ m : ℕ, (m : ℝ) + -1 ≤
      ((m + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (m + 1), ((i : ℕ) : ℝ) ^ 2 := by
    intro m
    have h1 : (m : ℝ) ^ 2 ≤ ∑ i ∈ Finset.range (m + 1), ((i : ℕ) : ℝ) ^ 2 :=
      Finset.single_le_sum (f := fun i : ℕ => ((i : ℕ) : ℝ) ^ 2) (fun i _ => sq_nonneg _)
        (Finset.self_mem_range_succ m)
    rw [le_inv_mul_iff₀ (by positivity)]
    push_cast
    nlinarith [h1]
  have h2 : Tendsto (fun m : ℕ => (m : ℝ) + -1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (-1) tendsto_natCast_atTop_atTop
  exact not_tendsto_nhds_of_tendsto_atTop (tendsto_atTop_mono hlow h2) c
    (hc.comp (tendsto_add_atTop_nat 1))

end BootstrapMeanCLTTest
