/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Complex.DiskToUpperHalfPlaneCayley

/-!
# Tests for the Cayley map from the unit disk to the upper half-plane
-/

open Complex

namespace MathlibExt.Analysis.Complex.DiskToUpperHalfPlaneCayleyWanted

-- The origin is the unique preimage of the imaginary unit in the disk.
example {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    I * (1 - z) / (1 + z) = I ↔ z = 0 := by
  constructor
  · intro h
    apply (bijOn_cayley_ball_upperHalfPlane _ rfl).injOn hz (Metric.mem_ball_self one_pos)
    simpa using h
  · rintro rfl
    simp

-- Every point of the real axis is excluded from the image of the open disk.
example (x : ℝ) :
    (x : ℂ) ∉ (fun z : ℂ => I * (1 - z) / (1 + z)) '' Metric.ball (0 : ℂ) 1 := by
  rw [(bijOn_cayley_ball_upperHalfPlane _ rfl).image_eq]
  simp

end MathlibExt.Analysis.Complex.DiskToUpperHalfPlaneCayleyWanted
