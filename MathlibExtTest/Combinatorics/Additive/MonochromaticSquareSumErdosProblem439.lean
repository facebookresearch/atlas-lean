/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.MonochromaticSquareSumErdosProblem439

open MathlibExt.Combinatorics.MonochromaticSquareSumErdosProblem439Wanted

example : ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x ≠ y ∧ IsSquare (x + y) := by
  obtain ⟨x, y, hx, hy, hne, _, hsquare⟩ := monochromaticSquareSum_holds 1 (fun _ ↦ 0)
  exact ⟨x, y, hx, hy, hne, hsquare⟩

example : ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ x ≠ y ∧ x % 3 = y % 3 ∧ x + y = z * z := by
  let residue (n : ℕ) : Fin 3 := ⟨n % 3, Nat.mod_lt _ (by decide)⟩
  obtain ⟨x, y, hx, hy, hne, hcolor, z, hz⟩ := monochromaticSquareSum_holds 3 residue
  exact ⟨x, y, z, hx, hy, hne, congrArg Fin.val hcolor, hz⟩
