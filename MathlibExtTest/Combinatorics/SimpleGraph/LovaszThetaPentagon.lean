/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.LovaszThetaPentagon

@[expose] public section

open MathlibExt.Combinatorics.SimpleGraph.LovaszTheta

/-! Checks for the umbrella bound on the pentagon. -/

/-- Vertices `0` and `2` of the pentagon are not adjacent, and their ribs are orthogonal. -/
example : inner ℝ (umbrella 0) (umbrella 2) = 0 := by
  rw [inner_umbrella, cos_two_pi_mul_div_five (cycleGraph_five_nonadj_diff (by decide)
    (by rw [SimpleGraph.cycleGraph_adj]; decide))]
  ring

/-- The sandwich on the pentagon: `2 = α(C₅) ≤ ϑ(C₅) ≤ √5 < 3 = χ(C̄₅)`. -/
example : ((SimpleGraph.cycleGraph 5).indepNum : ℝ) ≤ √5 :=
  (indepNum_le_lovaszTheta _).trans lovaszTheta_cycleGraph_five_le
