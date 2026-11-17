/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Electromagnetism.SeparableGuidePotential

@[expose] public section

open PhyslibExt.Electromagnetism.SeparableGuidePotential

namespace PhyslibExtTest.Electromagnetism.SeparableGuidePotential

/-- The separable guide potential has zero scalar potential. -/
example (c : SpeedOfLight) (a : ℝ → ℝ) (f : ℝ → ℝ → ℝ) :
    (separableGuidePotential c a f).scalarPotential c = 0 :=
  scalarPotential_separableGuidePotential c a f

end PhyslibExtTest.Electromagnetism.SeparableGuidePotential
