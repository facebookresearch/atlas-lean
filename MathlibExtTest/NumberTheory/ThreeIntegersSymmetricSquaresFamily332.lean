/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ThreeIntegersSymmetricSquaresFamily332
import Mathlib.Tactic.NormNum

/-! # Tests for Choudhry's family (3.32) of square triples with square symmetric functions -/

namespace MathlibExtTest.NumberTheory.ThreeIntegersSymmetricSquaresFamily332

open MathlibExt.NumberTheory.ThreeIntegersSymmetricSquaresWanted

-- Evaluate the printed formulas, independently of the proof's change of variables.
private def family332Values (m n : ℤ) : ℤ × ℤ × ℤ :=
  let q := m ^ 4 - 6 * m ^ 2 * n ^ 2 + n ^ 4
  let p := m ^ 12 - 26 * m ^ 10 * n ^ 2 + 79 * m ^ 8 * n ^ 4 - 44 * m ^ 6 * n ^ 6
    + 79 * m ^ 4 * n ^ 8 - 26 * m ^ 2 * n ^ 10 + n ^ 12
  let r := m ^ 12 - 10 * m ^ 10 * n ^ 2 + 15 * m ^ 8 * n ^ 4 - 204 * m ^ 6 * n ^ 6
    + 15 * m ^ 4 * n ^ 8 - 10 * m ^ 2 * n ^ 10 + n ^ 12
  (64 * m ^ 4 * n ^ 4 * (m ^ 2 - n ^ 2) ^ 2 * p ^ 2,
    (m ^ 2 + n ^ 2) ^ 2 * q ^ 2 * p ^ 2,
    16 * m ^ 2 * n ^ 2 * (m ^ 2 - n ^ 2) ^ 4 * r ^ 2)

-- Check all six square identities at a nondegenerate pair including a negative parameter.
example :
    let (a, b, c) := family332Values (-2) 1
    a = 380064 ^ 2 ∧ b = 138565 ^ 2 ∧ c = 1091448 ^ 2 ∧
      a + b + c = 1164005 ^ 2 ∧ a * b + b * c + c * a = 444659012328 ^ 2 ∧
      a * b * c = 57479546141095680 ^ 2 := by
  norm_num [family332Values]

-- With equal absolute values, only the middle entry survives.
example :
    let (a, b, c) := family332Values 1 (-1)
    a = 0 ∧ b = 512 ^ 2 ∧ c = 0 ∧ a + b + c = 512 ^ 2 ∧
      a * b + b * c + c * a = 0 ∧ a * b * c = 0 := by
  norm_num [family332Values]

example : family332Values 0 1 = (0, 1, 0) := by
  norm_num [family332Values]

-- A client can use the public theorem without access to its proof devices.
example : HasSquareElementarySymmetricFunctions 144448644096 19200259225 1191258736704 ∧
    IsSquare (144448644096 : ℤ) ∧ IsSquare (19200259225 : ℤ) ∧
    IsSquare (1191258736704 : ℤ) := by
  have h := hasSquareElementarySymmetricFunctions_family332_and_entries_square (-2) 1
  norm_num only at h
  exact h

-- A special case of the two-check criterion, using the independently proved family (3.3).
example : HasSquareElementarySymmetricFunctions 0 1 0 ↔
    IsSquare (0 + 1 + 0 : ℤ) ∧ IsSquare (0 * 1 + 1 * 0 + 0 * 0 : ℤ) := by
  constructor
  · intro _
    exact ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩
  · intro _
    exact hasSquareElementarySymmetricFunctions_family33 1 0

end MathlibExtTest.NumberTheory.ThreeIntegersSymmetricSquaresFamily332
