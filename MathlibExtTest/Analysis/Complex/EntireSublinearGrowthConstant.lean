/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Complex.EntireSublinearGrowthConstant

open Filter Topology
open MathlibExt.Analysis.Complex.EntireSublinearGrowthConstantWanted

-- For an affine function the limit condition detects exactly whether its linear term vanishes.
example (a b : ℂ) :
    Tendsto (fun z : ℂ => (a * z + b) / z) (comap (fun z : ℂ => ‖z‖) atTop) (𝓝 0) ↔
      a = 0 := by
  constructor
  · intro hlim
    obtain ⟨c, hc⟩ := exists_const_of_differentiable_of_tendsto_div_self_zero
      (f := fun z => a * z + b) (by fun_prop) hlim
    simpa using (hc 1).trans (hc 0).symm
  · rintro rfl
    simpa [div_eq_mul_inv] using tendsto_inv₀_cobounded.const_mul b
