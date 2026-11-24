/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Algebra.Ring.ULift
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Three genuinely distinct coefficient universes for scalar API clients

The first map squares the polynomial variable and lifts Type 0 to Type 1.
The second lowers only that carrier, shifts the variable, and lifts to Type 2.
Their composition therefore sends X to (X + 1)^2, retaining map order.
-/

public section

namespace MathlibExtTest.ScalarMixed

/-- The original coefficient ring in universe zero. -/
abbrev R0 : Type 0 := Polynomial ℤ
/-- The first coefficient target lives literally in universe one. -/
abbrev R1 : Type 1 := ULift.{1} R0
/-- The second coefficient target lives literally in universe two. -/
abbrev R2 : Type 2 := ULift.{2} R0

/-- A nontrivial unital scalar map from universe zero to universe one. -/
noncomputable def squareToLiftOne : R0 →+* R1 :=
  ((ULift.ringEquiv : R1 ≃+* R0).symm.toRingHom).comp
    (Polynomial.eval₂RingHom Polynomial.C (Polynomial.X ^ 2))

/-- A nontrivial unital scalar map from universe one to universe two. -/
noncomputable def shiftLiftOneToTwo : R1 →+* R2 :=
  ((ULift.ringEquiv : R2 ≃+* R0).symm.toRingHom).comp
    ((Polynomial.eval₂RingHom Polynomial.C (Polynomial.X + 1)).comp
      (ULift.ringEquiv : R1 ≃+* R0).toRingHom)

/-- The first map retains its actual squared-variable value. -/
theorem square_X : squareToLiftOne (Polynomial.X : R0) =
    (ULift.up (Polynomial.X ^ 2) : R1) := by
  simp [squareToLiftOne, ULift.ringEquiv]

/-- The second map retains its actual shifted-variable value. -/
theorem shift_X : shiftLiftOneToTwo (ULift.up (Polynomial.X : R0)) =
    (ULift.up (Polynomial.X + 1) : R2) := by
  simp [shiftLiftOneToTwo, ULift.ringEquiv]

/-- Composition is ordered: shift follows square, producing (X + 1)^2. -/
theorem shift_square_X : shiftLiftOneToTwo (squareToLiftOne (Polynomial.X : R0)) =
    (ULift.up ((Polynomial.X + 1) ^ 2) : R2) := by
  simp [squareToLiftOne, shiftLiftOneToTwo, ULift.ringEquiv]

/-- Both a variable and its unit translate remain nonconstant under the first map. -/
theorem square_X_add_one : squareToLiftOne ((Polynomial.X : R0) + 1) =
    (ULift.up (Polynomial.X ^ 2 + 1) : R1) := by
  simp [squareToLiftOne, ULift.ringEquiv]

end MathlibExtTest.ScalarMixed
