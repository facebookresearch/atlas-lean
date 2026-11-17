/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.UniformOhmicBar

@[expose] public section

open PhyslibExt.Circuits.UniformOhmicBar MeasureTheory Set

namespace PhyslibExtTest.Circuits.UniformOhmicBar

/-- The rectangle validation: current `12`. -/
example : terminalCurrent (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 2)
    (fun _ => ohmCurrentDensity 3 (uniformAxialField 8 4)) = 12 :=
  terminalCurrent_rectangle_example

end PhyslibExtTest.Circuits.UniformOhmicBar
