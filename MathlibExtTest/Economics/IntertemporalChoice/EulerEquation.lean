/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.IntertemporalChoice.EulerEquation
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

namespace MathlibExtTest.Economics.IntertemporalChoice.EulerEquation

/-- Test section: concrete instance `u c = 4 * c - c ^ 2`, `β = 1`, `r = 1`,
`y₀ = 2`, `y₁ = 0`, `c₀ = 6/5`, so `c₁ = 8/5`. -/
theorem quad_hasDerivAt (x : ℝ) :
    HasDerivAt (fun c : ℝ => 4 * c - c ^ 2) (4 - 2 * x) x := by
  have h1 : HasDerivAt (fun c : ℝ => (4:ℝ) * c) 4 x := by
    simpa using (hasDerivAt_id x).const_mul (4:ℝ)
  have h2 : HasDerivAt (fun c : ℝ => c ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have h := h1.sub h2
  exact h

example : MathlibExt.Economics.IntertemporalChoice.secondPeriodConsumption 1 2 0 (6/5) = 8/5 := by
  unfold MathlibExt.Economics.IntertemporalChoice.secondPeriodConsumption
  norm_num

example : IsMaxOn (MathlibExt.Economics.IntertemporalChoice.lifetimeUtility (fun c : ℝ => 4 * c - c ^ 2) 1 1 2 0) (MathlibExt.Economics.IntertemporalChoice.feasibleConsumption 1 2 0) (6/5) := by
  intro c _
  simp only [Set.mem_ofPred_eq]
  unfold MathlibExt.Economics.IntertemporalChoice.lifetimeUtility
    MathlibExt.Economics.IntertemporalChoice.secondPeriodConsumption
  nlinarith [sq_nonneg (c - 6/5)]

example : deriv (fun c : ℝ => 4 * c - c ^ 2) (6/5)
    = 1 * (1 + 1) * deriv (fun c : ℝ => 4 * c - c ^ 2) (8/5) := by
  have hspc : MathlibExt.Economics.IntertemporalChoice.secondPeriodConsumption 1 2 0 (6/5) = 8/5 := by
    unfold MathlibExt.Economics.IntertemporalChoice.secondPeriodConsumption
    norm_num
  have hmax : IsMaxOn (MathlibExt.Economics.IntertemporalChoice.lifetimeUtility (fun c : ℝ => 4 * c - c ^ 2) 1 1 2 0) (MathlibExt.Economics.IntertemporalChoice.feasibleConsumption 1 2 0) (6/5) := by
    intro c _
    simp only [Set.mem_ofPred_eq]
    unfold MathlibExt.Economics.IntertemporalChoice.lifetimeUtility
      MathlibExt.Economics.IntertemporalChoice.secondPeriodConsumption
    nlinarith [sq_nonneg (c - 6/5)]
  have hc₀ : (0:ℝ) < 6/5 := by norm_num
  have hc₁ : (0:ℝ) < MathlibExt.Economics.IntertemporalChoice.secondPeriodConsumption 1 2 0 (6/5) := by
    rw [hspc]
    norm_num
  have hu₀ : DifferentiableAt ℝ (fun c : ℝ => 4 * c - c ^ 2) (6/5) :=
    (quad_hasDerivAt (6/5)).differentiableAt
  have hu₁ : DifferentiableAt ℝ (fun c : ℝ => 4 * c - c ^ 2)
      (MathlibExt.Economics.IntertemporalChoice.secondPeriodConsumption 1 2 0 (6/5)) := by
    rw [hspc]
    exact (quad_hasDerivAt (8/5)).differentiableAt
  have h := MathlibExt.Economics.IntertemporalChoice.euler_equation hmax hc₀ hc₁ hu₀ hu₁
  rw [hspc] at h
  exact h

example : deriv (fun c : ℝ => 4 * c - c ^ 2) (6/5) = 8/5 := by
  have h := (quad_hasDerivAt (6/5 : ℝ)).deriv
  norm_num at h
  exact h

example : 1 * (1 + 1) * deriv (fun c : ℝ => 4 * c - c ^ 2) (8/5) = 8/5 := by
  have h := (quad_hasDerivAt (8/5 : ℝ)).deriv
  norm_num at h
  rw [h]
  norm_num

end MathlibExtTest.Economics.IntertemporalChoice.EulerEquation
