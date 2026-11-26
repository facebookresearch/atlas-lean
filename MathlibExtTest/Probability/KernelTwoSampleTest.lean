/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.KernelTwoSampleTest
import MathlibExtTest.Probability.KernelMeanEmbedding

/-! # Tests for concentration of the biased empirical MMD -/

open MeasureTheory MathlibExt.Probability.KernelMeanEmbedding
open MathlibExt.Probability.KernelTwoSampleTestWanted
open MathlibExtTest.Probability.KernelMeanEmbedding

namespace MathlibExtTest.Probability.KernelTwoSampleTest

/-- With the two-point delta kernel and sample sizes 100 and 400, the threshold is
`3/10 + ε` and the exponential rate is `40 ε²`. -/
example (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ε : ℝ} (hε : 0 < ε) :
    ((Measure.pi fun _ : Fin 100 => μ).prod (Measure.pi fun _ : Fin 400 => ν)).real
        {z | 3 / 10 + ε < |mmdBiased H₂ z.1 z.2 - mmd H₂ μ ν|} ≤
      2 * Real.exp (-(40 * ε ^ 2)) := by
  have hk (x y : S) : 0 ≤ kernelValue H₂ x y ∧ kernelValue H₂ x y ≤ 1 := by
    rw [kernelValue_H₂]
    rcases x with ⟨x, hx⟩
    rcases y with ⟨y, hy⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> norm_num [e]
  have h := measureReal_abs_mmdBiased_sub_mmd_gt_le (m := 100) (n := 400)
    .of_discrete hk μ ν hε
  have h₁ : √100 = 10 := (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  have h₂ : √400 = 20 := (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  norm_num [Real.sqrt_div, h₁, h₂] at h
  convert h using 1
  congr 2
  ring

/-- The zero-kernel endpoint reduces the threshold to ε and the stated upper bound to 2. -/
example {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [RKHS ℝ H X ℝ] (hφ : StronglyMeasurable (featureMap H))
    (hk : ∀ x y, kernelValue H x y = 0) (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {m n : ℕ} [NeZero m] [NeZero n]
    {ε : ℝ} (hε : 0 < ε) :
    ((Measure.pi fun _ : Fin m => μ).prod (Measure.pi fun _ : Fin n => ν)).real
        {z | ε < |mmdBiased H z.1 z.2 - mmd H μ ν|} ≤ 2 := by
  simpa using measureReal_abs_mmdBiased_sub_mmd_gt_le (m := m) (n := n) (K := 0)
    hφ (fun x y => by simp [hk]) μ ν hε

/-- At the zero kernel every feature vector vanishes, so both discrepancies are `0` and the event
is empty: its probability is `0`, far below the bound `2` of the previous example. -/
example {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [RKHS ℝ H X ℝ] (hk : ∀ x y, kernelValue H x y = 0) (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {m n : ℕ} [NeZero m] [NeZero n]
    {ε : ℝ} (hε : 0 < ε) :
    ((Measure.pi fun _ : Fin m => μ).prod (Measure.pi fun _ : Fin n => ν)).real
        {z | ε < |mmdBiased H z.1 z.2 - mmd H μ ν|} = 0 := by
  have hφ : featureMap H = fun _ : X => (0 : H) :=
    funext fun x => norm_eq_zero.mp (by rw [norm_featureMap, hk, Real.sqrt_zero])
  have hint (ρ : Measure X) : Integrable (featureMap H) ρ := hφ ▸ integrable_zero X H ρ
  have hempty : {z : (Fin m → X) × (Fin n → X) | ε < |mmdBiased H z.1 z.2 - mmd H μ ν|} = ∅ := by
    ext z
    simp [mmdBiased_eq, mmd_eq_norm_sub (hint μ) (hint ν), empiricalEmbedding, meanEmbedding, hφ,
      hε.le]
  rw [hempty, measureReal_empty]

end MathlibExtTest.Probability.KernelTwoSampleTest
