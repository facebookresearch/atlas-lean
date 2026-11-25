/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PDE.HeatKernel

import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Tests for the heat kernel

* On `ℝ` at time `1`, the heat kernel is positive and has total mass `1`.
* On `ℝ³` at time `2`, the heat kernel solves the heat equation at the point `(1, 0, 0)`.
-/

open InnerProductSpace Laplacian
open MathlibExt.Analysis.PDE.HeatKernel

example : ∫ x : ℝ, heatKernel ℝ 1 x = 1 := integral_heatKernel one_pos

example (x : ℝ) : 0 < heatKernel ℝ 1 x := heatKernel_pos one_pos x

example : HasDerivAt (fun s => heatKernel (EuclideanSpace ℝ (Fin 3)) s (EuclideanSpace.single 0 1))
    (Δ (heatKernel (EuclideanSpace ℝ (Fin 3)) 2) (EuclideanSpace.single 0 1)) 2 :=
  heatKernel_hasDerivAt_time_eq_laplacian two_pos _
