/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Decidability.RiceApplications

@[expose] public section

/-!
# Tests for emptiness and equivalence of programs

The classification of `E` and `EQ`, and a check that the reduction used for `EQ` produces the
intended code.
-/

set_option autoImplicit false

open Cslib.Decidability
open Nat.Partrec (Code)

namespace CSLibExtTest.Computability.Decidability.RiceApplications

/-- `E` is co-recognizable but neither recognizable nor decidable. -/
example : TM2CoRecognizable EmptyCode ∧ ¬TM2Recognizable EmptyCode ∧ ¬TM2Decidable EmptyCode :=
  ⟨tm2CoRecognizable_empty, not_tm2Recognizable_empty, not_tm2Decidable_empty⟩

/-- `EQ` is neither recognizable nor co-recognizable. -/
example : ¬TM2Recognizable EqCode ∧ ¬TM2CoRecognizable EqCode :=
  ⟨not_tm2Recognizable_eq, not_tm2CoRecognizable_eq⟩

/-- The identity code is not empty. -/
example : ¬EmptyCode Code.id := fun h ↦ h 0 (by simp [Code.eval_id])

/-- On a code that halts on `0` (the identity), the reduction code is the constant `0`. -/
example (n : ℕ) : (haltsOnZeroCode Code.id).eval n = Part.some 0 := by
  rw [eval_haltsOnZeroCode, Code.eval_id]
  rfl

/-- `EQ` compares languages, not functions: the constant codes `0` and `1` both halt everywhere. -/
example : EqCode (Code.const 0, Code.const 1) :=
  eqCode_iff.mpr fun n ↦ by simp [Code.eval_const]

end CSLibExtTest.Computability.Decidability.RiceApplications
