/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.MeasureTheory.Function.DilatedL1FunctionDecayAe
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory Set Filter
open MathlibExt.MeasureTheory.DilatedL1FunctionDecayAeWanted
open scoped Topology

private noncomputable def sample : ℝ → ℝ := (Icc (0 : ℝ) 1).indicator (fun _ => -2)

-- A signed, nonzero integrable function, with any strictly positive scaling exponent.
example (lam : ℝ) (hlam : 0 < lam) :
    ∀ᵐ x ∂(volume : Measure ℝ),
      Tendsto (fun n : ℕ => (n + 1 : ℝ) ^ (-lam) * sample ((n + 1) * x)) atTop (𝓝 0) := by
  have hfin : (volume : Measure ℝ) (Icc (0 : ℝ) 1) < ⊤ := isCompact_Icc.measure_lt_top
  have hint : IntegrableOn (fun _ : ℝ => (-2 : ℝ)) (Icc 0 1) volume :=
    integrableOn_const hfin.ne
  exact ae_tendsto_rpow_neg_mul_comp_mul_zero sample
    (memLp_one_iff_integrable.mpr (hint.integrable_indicator measurableSet_Icc)) lam hlam
