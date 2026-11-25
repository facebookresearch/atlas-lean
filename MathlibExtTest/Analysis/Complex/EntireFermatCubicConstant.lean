/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Complex.EntireFermatCubicConstant

open MathlibExt.Analysis.Complex.EntireFermatCubicConstantWanted

/-- The values at one point determine both functions on the whole plane. -/
example (f g : ℂ → ℂ) (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hfg : ∀ z : ℂ, f z ^ 3 + g z ^ 3 = 1) (z w : ℂ) :
    (f z, g z) = (f w, g w) := by
  obtain ⟨a, b, ha, hb⟩ := entire_cube_add_cube_eq_one_const f g hf hg hfg
  rw [ha z, ha w, hb z, hb w]
