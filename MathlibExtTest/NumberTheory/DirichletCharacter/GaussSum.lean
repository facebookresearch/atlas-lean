/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DirichletCharacter.GaussSum

/-!
# Tests for the absolute value of primitive Gauss sums
-/

@[expose] public section

namespace GaussSumTest

/-- The boundary case `q = 1`: the trivial character mod `1` is primitive and its Gauss sum has
absolute value `√1 = 1`. -/
example : ‖gaussSum (1 : DirichletCharacter ℂ 1) ZMod.stdAddChar‖ = 1 := by
  rw [DirichletCharacter.norm_gaussSum_stdAddChar_of_isPrimitive
    DirichletCharacter.isPrimitive_one_level_one]
  simp

example {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 = q := by
  rw [DirichletCharacter.norm_gaussSum_stdAddChar_of_isPrimitive hχ, Real.sq_sqrt (by positivity)]

end GaussSumTest
