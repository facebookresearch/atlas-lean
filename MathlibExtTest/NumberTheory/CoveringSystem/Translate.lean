/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CoveringSystem.Translate

/-! # Tests for translating a covering system -/

-- Translate both parity classes and a singleton class (modulus zero) by a negative integer.
example : Int.IsCoveringSystem {(-3, 2), (-2, 2), (4, 0)} := by
  let C : Finset (ℤ × ℕ) := {(0, 2), (1, 2), (7, 0)}
  have hC : Int.IsCoveringSystem C := by
    intro z
    simp [C, Int.ModEq]
    omega
  convert MetaMathlibExt.isCoveringSystem_translate C hC (-3) using 1
  decide
