/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.CylinderReflectionTilings

/-! # Tests for reflection-fixed tilings of an even-width cylinder -/

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
