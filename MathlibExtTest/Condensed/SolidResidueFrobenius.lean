/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Condensed.SolidTorsionFrobeniusModels
import Mathlib.Data.ZMod.Basic

/-! The residue construction is exercised on a nonperfect characteristic-two
polynomial ring, where Frobenius sends X to X squared, and on the zero ring.
This checks the actual ring map and its multiplicative/additive laws,
including the boundary that has no nontrivial characteristic instance.
-/

open MathlibExt.Condensed.SolidTorsionFrobeniusModels

noncomputable section

private abbrev R := ULift.{1} (Polynomial (ZMod 2))
private theorem prime_zero : (2 : R) = 0 := by
  apply ULift.ext
  change (2 : Polynomial (ZMod 2)) = 0
  exact CharP.cast_eq_zero _ 2
private def F : R →+* R := residueFrobenius 2 R prime_zero

example : F (ULift.up Polynomial.X) = ULift.up (Polynomial.X ^ 2) := by
  exact residueFrobenius_apply 2 R prime_zero _

example : F (ULift.up (Polynomial.X + 1)) =
    ULift.up (Polynomial.X ^ 2 + 1) := by
  change F ((ULift.up Polynomial.X : R) + 1) =
    (ULift.up (Polynomial.X ^ 2) : R) + 1
  rw [F, map_add, map_one]
  rw [residueFrobenius_apply]
  rfl

example : F (ULift.up (Polynomial.X * Polynomial.X)) =
    ULift.up (Polynomial.X ^ 2 * Polynomial.X ^ 2) := by
  change F ((ULift.up Polynomial.X : R) * ULift.up Polynomial.X) =
    (ULift.up (Polynomial.X ^ 2) : R) * ULift.up (Polynomial.X ^ 2)
  rw [F, map_mul]
  rw [residueFrobenius_apply]
  rfl

private abbrev Z := ULift.{1} (ZMod 1)
private theorem zero_ring_prime : (2 : Z) = 0 := Subsingleton.elim _ _
example : residueFrobenius 2 Z zero_ring_prime = RingHom.id Z := by
  ext a
  exact Subsingleton.elim _ _

#print axioms MathlibExt.Condensed.SolidTorsionFrobeniusModels.residueFrobenius_apply
