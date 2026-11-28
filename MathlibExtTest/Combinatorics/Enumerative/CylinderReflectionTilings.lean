/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.CylinderReflectionTilings

/-! # Tests for reflection-fixed tilings of cylinders -/

open MetaMathlibExt

-- At the smallest even width, the odd shift fixes every cell but the swap fixes no tile.
example : cylinderShiftSum 2 1 (cellF 2 1) (Equiv.swap (0 : Fin 2) 1) = 2 := by
  have h : 2 * cylinderShiftSum 2 1 (cellF 2 1) (Equiv.swap (0 : Fin 2) 1) = 4 := by
    rw [cylinder_f_even 2 1 _ (by simp [sq]) (by decide)]
    decide +kernel
  omega

-- With one fixed design, the two even shifts contribute 81 each and the two odd shifts 9 each.
example : cylinderShiftSum 4 2 (cellF 4 2) (Equiv.swap (0 : Fin 3) 1) = 180 := by
  have h : 2 * cylinderShiftSum 4 2 (cellF 4 2) (Equiv.swap (0 : Fin 3) 1) = 360 := by
    rw [cylinder_f_even 4 2 _ (by simp [sq]) (by decide)]
    decide +kernel
  omega

-- Enumerate the fixed tilings over all three shifts. Each pair has four choices and its
-- fixed cell has two (the designs not swapped by the permutation).
example : cylinderShiftSum 3 1 (cellF 3 1) (Equiv.swap (0 : Fin 4) 1) = 24 := by
  rw [cylinderShiftSum]
  decide +kernel

-- At width one, the sole shift and reflection leave both rows fixed.
example : cylinderShiftSum 1 2 (cellF 1 2) (Equiv.swap (0 : Fin 3) 1) = 1 := by
  rw [cylinderShiftSum]
  decide +kernel

-- With no fixed tile design, the fixed column rules out every tiling at every shift.
example : cylinderShiftSum 3 1 (cellF 3 1) (Equiv.swap (0 : Fin 2) 1) = 0 := by
  rw [cylinderShiftSum]
  decide +kernel

-- Directly count the fixed columns for each shift at width three.
example : ∀ a : ZMod 3, Fintype.card {x : ZMod 3 // cellF 3 1 (x + a, 0) = (x, 0)} = 1 := by
  decide +kernel

-- Two rows give two reflected pairs and two fixed cells at each of the three shifts.
example : cylinderShiftSum 3 2 (cellF 3 2) (1 : Equiv.Perm (Fin 2)) = 48 := by
  rw [cylinderShiftSum]
  decide +kernel

-- A client of the closed formula with one fixed design and two pairs per shift.
example : cylinderShiftSum 3 2 (cellF 3 2) (Equiv.swap (0 : Fin 3) 1) = 27 := by
  rw [cylinder_f_odd 3 2 _ (by simp [sq]) (by decide)]
  decide +kernel
