/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.MetricSpace.GromovHyperbolic
public import MathlibExt.Topology.MetricSpace.GromovHyperbolicTriangles

@[expose] public section

namespace MathlibExtTest.GromovHyperbolic

open Metric

/-- Regression test for the Gromov-product basepoint order: the real line is an `ℝ`-tree, so it
is `0`-hyperbolic (`Metric.isDeltaHyperbolic_real`). `Metric.gromovProduct w x y` is the product of
`x` and `y` at the basepoint `w`. Reading the basepoint as the third argument mixes basepoints in
the four-point inequality, and `ℝ` then fails it for every `δ`: at `w = 0`, `x = z = -R`, `y = R`
it reads `R - δ ≤ 0`. -/
example : IsDeltaHyperbolic ℝ 0 :=
  isDeltaHyperbolic_real

/-- The real line is Gromov-hyperbolic. -/
example : IsGromovHyperbolic ℝ :=
  ⟨0, isDeltaHyperbolic_real⟩

end MathlibExtTest.GromovHyperbolic
