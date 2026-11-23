/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.ClassicalProcesses.SessionReading

/-!
# Tests for the CP session reading

One calculation for each proposition constructor in the image, the two
undefined cases, and the collapse of the two multiplicative units.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.ClassicalProcesses

namespace SessionReadingTests

/-- Two test atoms. -/
inductive TestAtom where
  | left : TestAtom
  | right : TestAtom
deriving DecidableEq, Repr

/-- The proposition `A` used as an opaque payload in the tests. -/
def propA : Logic.CLL.Proposition TestAtom := .atom .left

/-- The proposition `B` used as an opaque payload in the tests. -/
def propB : Logic.CLL.Proposition TestAtom := .atom .right

/-- The unit `1` reads as `end`. -/
theorem sessionReading_one :
    sessionReading (Atom := TestAtom) .one = some .end := by
  rfl

/-- The unit `⊥` also reads as `end`. -/
theorem sessionReading_bot :
    sessionReading (Atom := TestAtom) .bot = some .end := by
  rfl

/-- The two multiplicative units have the same session reading. -/
theorem sessionReading_one_bot_collapse :
    sessionReading (Atom := TestAtom) .one =
      sessionReading (Atom := TestAtom) .bot := by
  rfl

/-- The additive zero reads as empty external choice. -/
theorem sessionReading_zero :
    sessionReading (Atom := TestAtom) .zero = some (.branch .nil) := by
  rfl

/-- The additive top reads as empty internal choice. -/
theorem sessionReading_top :
    sessionReading (Atom := TestAtom) .top = some (.select .nil) := by
  rfl

/-- Tensor reads as receive with the first proposition as payload. -/
theorem sessionReading_tensor :
    sessionReading (.tensor propA .one) = some (.recv propA .end) := by
  rfl

/-- Par reads as send with the dual of the first proposition as
payload. -/
theorem sessionReading_parr :
    sessionReading (.parr propB .one) =
      some (.send propB.dual .end) := by
  rfl

/-- Additive disjunction reads as two-entry external choice. -/
theorem sessionReading_oplus :
    sessionReading
        (.oplus .one .bot : Logic.CLL.Proposition TestAtom) =
      some (.branch (.cons .left .end (.cons .right .end .nil))) := by
  rfl

/-- Additive conjunction reads as two-entry internal choice. -/
theorem sessionReading_with :
    sessionReading
        (.with .one .bot : Logic.CLL.Proposition TestAtom) =
      some (.select (.cons .left .end (.cons .right .end .nil))) := by
  rfl

/-- Atoms have no session reading. -/
theorem sessionReading_atom :
    sessionReading propA = none := by
  rfl

/-- Exponentials have no session reading. -/
theorem sessionReading_bang :
    sessionReading (.bang .one : Logic.CLL.Proposition TestAtom) =
      none := by
  rfl

end SessionReadingTests

end Cslib.ClassicalProcesses
