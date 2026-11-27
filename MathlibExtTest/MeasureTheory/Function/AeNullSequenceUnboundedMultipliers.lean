/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.MeasureTheory.Function.AeNullSequenceUnboundedMultipliers

open Filter MeasureTheory Set
open MathlibExt.MeasureTheory.AeNullSequenceUnboundedMultipliersWanted
open scoped Topology

-- The sequence varies in both x and n and is nonzero on a set of positive measure.
example : ∃ c : ℕ → ℝ, Tendsto (fun n => |c n|) atTop atTop ∧
    (∀ᵐ x ∂volume.restrict (Icc (0 : ℝ) 1),
      Tendsto (fun n : ℕ => c n * (x * ((n : ℝ) + 1)⁻¹)) atTop (𝓝 0)) := by
  apply exists_tendsto_abs_atTop_and_ae_tendsto_mul_zero (fun n x => x * ((n : ℝ) + 1)⁻¹)
  · exact fun _ => measurable_id.mul measurable_const
  · have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hden
    exact Eventually.of_forall fun x => by simpa only [mul_zero] using hinv.const_mul x
