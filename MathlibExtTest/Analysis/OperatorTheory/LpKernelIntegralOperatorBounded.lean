/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.OperatorTheory.LpKernelIntegralOperatorBounded
import Mathlib.Tactic.NormNum

open MeasureTheory Filter
open scoped ENNReal

namespace MathlibExt.Analysis.OperatorTheory.LpKernelIntegralOperatorBoundedWanted.Tests

local notation "μ" => Measure.restrict volume (Set.Ioo (0 : ℝ) 1)

local instance factOneLeTwo : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩

private theorem one_memLp : MemLp (fun _ : ℝ => (1 : ℝ)) 2 μ := memLp_const 1

-- The unit kernel sends the constant-one input to the constant-one output.
example :
    ∃ A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ,
      ∀ᵐ x ∂μ, Integrable (fun _ : ℝ => (1 : ℝ)) μ ∧ A (one_memLp.toLp _) x = 1 := by
  have hConjugate : (1 : ENNReal) / 2 + 1 / 2 = 1 := by
    simpa only [one_div] using ENNReal.inv_two_add_inv_two
  have hKernel : MemLp (fun _ : ℝ × ℝ => (1 : ℝ)) 2 ((μ).prod μ) := memLp_const 1
  obtain ⟨hIntegrable, A, hA⟩ :=
    integrable_kernel_mul_and_exists_clm_integral_operator 2 2
      (by norm_num) (by norm_num) hConjugate _ hKernel
  let f := one_memLp.toLp _
  have hf : (f : ℝ → ℝ) =ᵐ[μ] fun _ => 1 := one_memLp.coeFn_toLp
  have hMeasure : μ Set.univ = 1 := by
    norm_num [Measure.restrict_apply, Real.volume_Ioo]
  refine ⟨A, ?_⟩
  filter_upwards [hIntegrable f, hA f] with x hInt hx
  constructor
  · exact (by simpa only [one_mul] using hInt : Integrable f μ).congr hf
  calc
    A f x = ∫ y, f y ∂μ := by simpa only [one_mul] using hx
    _ = ∫ _ : ℝ, (1 : ℝ) ∂μ := integral_congr_ae hf
    _ = 1 := by simp [integral_const, measureReal_def, hMeasure]

end MathlibExt.Analysis.OperatorTheory.LpKernelIntegralOperatorBoundedWanted.Tests
