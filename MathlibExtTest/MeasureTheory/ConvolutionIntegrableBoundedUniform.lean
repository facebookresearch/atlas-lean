/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.MeasureTheory.ConvolutionIntegrableBoundedUniform
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory Set
open MathlibExt.MeasureTheory.ConvolutionIntegrableBoundedUniformWanted

-- The bounded factor is discontinuous, and both factors have nonzero integrals.
example :
    let f := (Icc (0 : Fin 1 → ℝ) 1).indicator (fun _ => (2 : ℝ))
    let g := (Icc (1 : Fin 1 → ℝ) 3).indicator (fun _ => (-1 : ℝ))
    UniformContinuous (fun x => ∫ y, f (x - y) * g y) := by
  dsimp only
  apply uniformContinuous_convolution_integrable_bounded 1
  · refine (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const ?_ (by simp))
    rw [Real.volume_Icc_pi]
    simp
  · exact measurable_const.indicator measurableSet_Icc
  · refine isBounded_iff_forall_norm_le.2 ⟨1, ?_⟩
    rintro _ ⟨y, rfl⟩
    by_cases hy : y ∈ Icc (1 : Fin 1 → ℝ) 3 <;> simp [hy]
