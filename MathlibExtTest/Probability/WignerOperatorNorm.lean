/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.WignerOperatorNorm

open MeasureTheory ProbabilityTheory Real
open MathlibExt.Probability.WignerOperatorNormWanted
open MathlibExt.Analysis.WignerSemicircleWanted.Analysis.WignerSemicircleProblem

-- At dimension zero the strict upper-tail event is empty, even at threshold zero.
example {Ω : Type*} (X : ℕ → ℕ → Ω → ℝ) (A : ℝ) :
    {ω | A * √(0 : ℝ) < ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (wignerMatrix X 0 ω)‖} = ∅ := by
  ext ω
  simp [ContinuousLinearMap.opNorm_subsingleton]

-- Fixing A at its allowed endpoint gives exponential decay in the dimension.
example {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω) [hP : IsProbabilityMeasure P]
    (X : ℕ → ℕ → Ω → ℝ) (hm : ∀ i j, Measurable (X i j))
    (hi : iIndepFun (fun ij : {p : ℕ × ℕ // p.1 ≤ p.2} => X ij.val.1 ij.val.2) P)
    (hz : ∀ i j, i ≤ j → ∫ ω, X i j ω ∂P = 0)
    (hb : ∀ i j, i ≤ j → ∀ ω, |X i j ω| ≤ 1) :
    ∃ C > 0, ∃ k > 0, ∀ n : ℕ,
      P.real {ω | C * √n < ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (wignerMatrix X n ω)‖} ≤
        C * exp (-k * n) := by
  obtain ⟨C, hC, c, hc, h⟩ := wigner_opNorm_upper_tail
  refine ⟨C, hC, c * C, mul_pos hc hC, fun n => ?_⟩
  simpa only [neg_mul] using h Ω m P hP X hm hi hz hb n C le_rfl
