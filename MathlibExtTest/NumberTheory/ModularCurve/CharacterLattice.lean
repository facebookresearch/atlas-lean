/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularCurve.CharacterLattice
import Mathlib.Algebra.BigOperators.Fin

open ModularCurve

/-- The degree adds up the values: `2 - 3 + 5 = 4`. -/
example : degreeOn (Fin 3) ![2, -3, 5] = 4 := by
  rw [degreeOn_apply, Fin.sum_univ_three]
  rfl

/-- `(1, -1)` lies in the character lattice of `Fin 2`, and `(1, 0)` does not. -/
example : (![1, -1] : Fin 2 → ℤ) ∈ characterLattice (Fin 2) ∧
    (![1, 0] : Fin 2 → ℤ) ∉ characterLattice (Fin 2) := by
  simp [mem_characterLattice, Fin.sum_univ_two]

/-- The same membership read off the definition: the character lattice is the
kernel of the degree, and `(1, 0)` has degree `1`. -/
example : (![1, 0] : Fin 2 → ℤ) ∉ characterLattice (Fin 2) := by
  rw [characterLattice, LinearMap.mem_ker]
  decide

/-- With widths `1` and `2`, the width pairing of `(1, -1)` with itself is
`1 + 2 = 3`: each coordinate is weighted by its width. -/
example : widthPairing ![1, 2] (![1, -1] : Fin 2 → ℤ) ![1, -1] = 3 := by
  decide

/-- A zero width drops its coordinate from the pairing. -/
example : widthPairing ![0, 1] (![5, 1] : Fin 2 → ℤ) ![7, 1] = 1 := by
  rw [widthPairing_apply, Fin.sum_univ_two]
  rfl

/-- The width pairing is symmetric. -/
example (e : Fin 2 → ℕ) (D D' : Fin 2 → ℤ) :
    widthPairing e D D' = widthPairing e D' D :=
  widthPairing_comm e D D'
