/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.FiniteFieldKakeya
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Pi

open MathlibExt.Combinatorics.FraserKakeyaWanted.Combinatorics.FraserKakeyaProblem

namespace MathlibExt.Combinatorics.FiniteFieldKakeyaThreeAIMCombinatoricsProblem245Wanted.Test

-- The zero direction gives a singleton, also in the smallest field.
example (y : Fin 3 → ZMod 2) : affineLine y 0 = {y} := by
  ext z
  simp [affineLine]

-- Every direction in the punctured binary cube still has a full affine line.
private def puncturedCube : Finset (Fin 3 → ZMod 2) := Finset.univ.erase 0

private theorem puncturedCube_isKakeya : IsKakeya (puncturedCube : Set (Fin 3 → ZMod 2)) := by
  have h : ∀ x : Fin 3 → ZMod 2, ∃ y : Fin 3 → ZMod 2, ∀ a : ZMod 2, y + a • x ≠ 0 := by
    decide
  intro x
  obtain ⟨y, hy⟩ := h x
  refine ⟨y, ?_⟩
  rintro _ ⟨a, rfl⟩
  simpa [puncturedCube] using hy a

example : ∃ c : ℝ, 0 < c ∧ c * 2 ^ 3 ≤ (7 : ℝ) := by
  obtain ⟨c, hc, h⟩ := finiteFieldKakeyaCubeLowerBound_holds
  refine ⟨c, hc, ?_⟩
  simpa [puncturedCube, Fintype.card_fun] using h (ZMod 2) puncturedCube puncturedCube_isKakeya

end MathlibExt.Combinatorics.FiniteFieldKakeyaThreeAIMCombinatoricsProblem245Wanted.Test
