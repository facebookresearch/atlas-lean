/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.MeasureTheory.Function.LipschitzIffAbsContBoundedDeriv
import Mathlib.Analysis.Calculus.ContDiff.Operations

open MeasureTheory Filter
open MathlibExt.MeasureTheory.LipschitzIffAbsContBoundedDerivWanted

-- The forward implication includes functions with a corner.
example : (∀ a b : ℝ, AbsolutelyContinuousOnInterval (fun x : ℝ => |x|) a b) ∧
    (∀ᵐ x ∂(volume : Measure ℝ), ‖deriv (fun y : ℝ => |y|) x‖ ≤ 1) := by
  have hf : LipschitzWith 1 (fun x : ℝ => |x|) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using abs_abs_sub_abs_le_abs_sub x y
  exact (lipschitzWith_iff_absolutelyContinuous_and_ae_norm_deriv_le _ 1).mp hf

-- The converse does not require a positive Lipschitz constant.
example : LipschitzWith 0 (fun _ : ℝ => (7 : ℝ)) := by
  apply (lipschitzWith_iff_absolutelyContinuous_and_ae_norm_deriv_le _ 0).mpr
  refine ⟨fun a b => ?_, Eventually.of_forall fun x => ?_⟩
  · have h : ContDiff ℝ 1 (fun _ : ℝ => (7 : ℝ)) := contDiff_const
    exact h.contDiffOn.absolutelyContinuousOnInterval
  · simp [deriv_const]
