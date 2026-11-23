/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CollatzArithmeticDerivative

open MetaMathlibExt

example : collatzAccelerated 0 = 0 ∧ collatzAccelerated 3 = 5 ∧ collatzAccelerated 6 = 3 :=
  ⟨rfl, rfl, rfl⟩

-- The two semiprimes in the example realize opposite residue orders.
example : (71 * 1609 % 3 = 2 ∧ 349 * 491 % 3 = 2) ∧
    (71 % 3 = 2 ∧ 1609 % 3 = 1) ∧ (349 % 3 = 1 ∧ 491 % 3 = 2) := by
  obtain ⟨hpq, hrs, h₁, h₂⟩ := isCompatibleSemiprimePair_71_1609.mod_three
  exact ⟨⟨hpq, hrs⟩, h₁.resolve_left (by decide), h₂.resolve_right (by decide)⟩

-- Both equations hold, but the first product is divisible by three.
example : 2 * (11 + 43) = 3 + 105 ∧ 2 * (11 * 43) = 3 * (3 * 105) + 1 ∧
    ¬ IsCompatibleSemiprimePair 3 105 11 43 := by
  refine ⟨rfl, rfl, fun h => ?_⟩
  exact (by decide : 3 * 105 % 3 ≠ 2) h.mod_three.1

example : 71 * 1609 % 4 = 3 ∧ 71 % 4 = 3 ∧ 1609 % 4 = 1 := by
  obtain ⟨hprod, hres⟩ := isCompatibleSemiprimePair_71_1609.mod_four
  exact ⟨hprod, hres.resolve_left (by decide)⟩

-- Both equations hold, but 62 is composite and the first product is 1 modulo 4.
example : 2 * (19 + 62) = 5 + 157 ∧ 2 * (19 * 62) = 3 * (5 * 157) + 1 ∧
    ¬ IsCompatibleSemiprimePair 5 157 19 62 := by
  refine ⟨rfl, rfl, fun h => ?_⟩
  exact (by decide : 5 * 157 % 4 ≠ 3) h.mod_four.1
