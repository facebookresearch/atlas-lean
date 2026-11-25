/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.UnitConjecture

open MathlibExt.GroupTheory.UnitConjectureWanted.UnitConjecture

namespace MathlibExtTest.GroupTheory.UnitConjecture

-- Sending a to 1 modulo 4 and b to 0 detects the nonidentity translation a².
private def residues : generators → Multiplicative (ZMod 4)
  | .a => Multiplicative.ofAdd 1
  | .b => 1

private def quotientMap : P →* Multiplicative (ZMod 4) :=
  PresentedGroup.toGroup (f := residues) (by
    rintro w (rfl | h)
    · simp only [a, b, map_mul, map_inv, map_pow, FreeGroup.lift_apply_of]
      decide
    · obtain rfl : w = _ := h
      simp only [a, b, map_mul, map_inv, map_pow, FreeGroup.lift_apply_of]
      decide)

example (n : ℕ) (hn : n ≠ 0) : x ^ n ≠ 1 := by
  intro h
  have hx := congrArg quotientMap (theorem_A.1 x n hn h)
  have ha : quotientMap (a : P) = residues .a := PresentedGroup.toGroup.of _
  rw [x, map_pow, ha, map_one] at hx
  exact (by decide : residues .a ^ 2 ≠ 1) hx

-- Under augmentation every group element contributes one, so the sum has odd support.
example : MonoidAlgebra.lift (ZMod 2) (ZMod 2) P (1 : P →* ZMod 2) u = 1 := by
  simp only [u, p, q, r, s, map_add, map_mul, map_one, MonoidAlgebra.lift_of, MonoidHom.one_apply]
  decide

example : u ≠ (1 : R) :=
  fun h => theorem_A.2.2 ⟨1, h.trans (MonoidAlgebra.of (ZMod 2) P).map_one.symm⟩

end MathlibExtTest.GroupTheory.UnitConjecture
