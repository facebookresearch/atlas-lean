/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Convex.StdSimplexWeights

/-!
# Tests for real distributions on a finite type from weight functions

* `ofWeights` reads back its coordinates.
* `normalizeWeights` of `(3, 1)` is `(3/4, 1/4)`; of the zero vector it is uniform; `normalize`
  packages it as a simplex point.
-/

namespace MathlibExtTest.StdSimplexWeights

open Convexity StdSimplex

/-- The uniform distribution on `Bool`. -/
noncomputable def half : StdSimplex ℝ Bool :=
  ofWeights (fun _ => 1 / 2) (fun _ => by norm_num) (by simp)

example (b : Bool) : half.weights b = 1 / 2 := by
  simp [half]

/-- Weights `3` on `true`, `1` on `false`. -/
def w31 : Bool → ℝ := fun b => if b then 3 else 1

example : normalizeWeights w31 true = 3 / 4 := by
  rw [normalizeWeights_of_pos (by simp [w31]; norm_num)]
  simp [w31]
  norm_num

example : normalizeWeights (fun _ : Bool => (0 : ℝ)) true = 1 / 2 := by
  simp [normalizeWeights]

example : (normalize w31 fun b => by cases b <;> simp [w31]).weights false = 1 / 4 := by
  rw [normalize_weights, normalizeWeights_of_pos (by simp [w31]; norm_num)]
  simp [w31]
  norm_num

end MathlibExtTest.StdSimplexWeights
