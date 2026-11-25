/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.Fourier.ConvolutionTranslateClosureCircle

open MeasureTheory Topology
open scoped Convolution
open MathlibExt.Analysis.Fourier.ConvolutionTranslateClosureCircleWanted

namespace MathlibExtTest.Analysis.Fourier.ConvolutionTranslateClosureCircle

local instance period_pos : Fact (0 < (2 * Real.pi : ℝ)) := ⟨by positivity⟩

-- The empty sum represents zero even when no translates are selected.
example :
    closure {u : Lp ℝ 1 (volume : Measure T) | ∃ g : T → ℝ, MemLp g 1 volume ∧
      (u : T → ℝ) =ᵐ[volume] ((fun _ : T => (0 : ℝ)) ⋆ g)} = {0} := by
  refine (closure_convolution_set_eq_closure_translate_span (fun _ => 0)
    (memLp_const 0) {0} _ ?_ rfl).trans isClosed_singleton.closure_eq
  ext u
  constructor
  · rintro rfl
    refine ⟨0, Fin.elim0, Fin.elim0, ?_⟩
    filter_upwards [Lp.coeFn_zero ℝ 1 (volume : Measure T)] with x hx
    simpa only [Pi.zero_apply, Finset.univ_eq_empty, Finset.sum_empty] using hx
  · rintro ⟨N, a, τ, hu⟩
    apply Lp.ext
    filter_upwards [hu, Lp.coeFn_zero ℝ 1 (volume : Measure T)] with x hx hz
    rw [hx, hz]
    simp

-- The convolution of the two constant ones detects the unnormalized circle measure.
example (x : T) : ((fun _ : T => (1 : ℝ)) ⋆ (fun _ => 1)) x = 2 * Real.pi := by
  simp [convolution_def, Measure.real, Real.pi_pos.le]

end MathlibExtTest.Analysis.Fourier.ConvolutionTranslateClosureCircle
