/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RepresentationTheory.TwistByCharacter

/-! Tests for `MathlibExt.RepresentationTheory.TwistByCharacter`. -/

set_option autoImplicit false

#check @Representation.twistByCharacter
#check @Representation.twistByCharacter_apply
#check @Representation.twistByCharacter_zero
#check @Representation.twistByCharacter_twistByCharacter

/-- The sign character of `ℤˣ` twists the trivial representation on `ℤ`: `-1` acts by `-1`. -/
example :
    (Representation.trivial ℤ ℤˣ ℤ).twistByCharacter (MonoidHom.id ℤˣ) 1 (-1) 1 = -1 := by
  simp [Representation.twistByCharacter_apply]

/-- Twisting by an even power of the sign character gives back the trivial action. -/
example (a : ℤ) :
    (Representation.trivial ℤ ℤˣ ℤ).twistByCharacter (MonoidHom.id ℤˣ) 2 (-1) a = a := by
  simp [Representation.twistByCharacter_apply]

/-- The twist by `χ ^ 0` of any representation is the representation itself. -/
example {R G A : Type*} [CommRing R] [Monoid G] [AddCommGroup A] [Module R A]
    (ρ : Representation R G A) (χ : G →* Rˣ) (g : G) (a : A) :
    ρ.twistByCharacter χ 0 g a = ρ g a := by
  rw [Representation.twistByCharacter_zero]

/-- Twisting by `χ ^ 1` and then by `χ ^ (-1)` gives back the representation. -/
example {R G A : Type*} [CommRing R] [Monoid G] [AddCommGroup A] [Module R A]
    (ρ : Representation R G A) (χ : G →* Rˣ) :
    (ρ.twistByCharacter χ 1).twistByCharacter χ (-1) = ρ := by
  rw [Representation.twistByCharacter_twistByCharacter, add_neg_cancel,
    Representation.twistByCharacter_zero]

#print axioms Representation.twistByCharacter
#print axioms Representation.twistByCharacter_apply
#print axioms Representation.twistByCharacter_zero
#print axioms Representation.twistByCharacter_twistByCharacter
