/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Instrumentation.ApertureJitterBudget

@[expose] public section

open PhyslibExt.Instrumentation.ApertureJitterBudget

namespace PhyslibExtTest.Instrumentation.ApertureJitterBudget

/-- The box kernel of half-width one is an aperture kernel. -/
example : IsApertureKernel (1 : ℝ) (boxKernel (1 : ℝ)) :=
  boxKernel_isApertureKernel (by norm_num)

end PhyslibExtTest.Instrumentation.ApertureJitterBudget
