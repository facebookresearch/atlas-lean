/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Decidability.Totality

@[expose] public section

/-!
# Tests for totality of programs
-/

set_option autoImplicit false

open Cslib.Decidability
open Nat.Partrec (Code)

namespace CSLibExtTest.Computability.Decidability.Totality

/-- `TOTAL` is neither recognizable nor co-recognizable, hence undecidable. -/
example : ¬TM2Recognizable TotalCode ∧ ¬TM2CoRecognizable TotalCode ∧ ¬TM2Decidable TotalCode :=
  ⟨not_tm2Recognizable_total, not_tm2CoRecognizable_total, not_tm2Decidable_total⟩

/-- The identity is total. -/
example : TotalCode Code.id := fun n ↦ by simp [Code.eval_id]

/-- A code defined nowhere is not total. -/
example : ∃ e : Code, ¬TotalCode e := by
  obtain ⟨e, he⟩ := exists_code_empty
  exact ⟨e, fun h ↦ by simpa [he] using h 0⟩

/-- `untilHaltsFun` on the identity (which halts on `0` within one step): it outputs `0` at
step bound `0` and loops from step bound `1` on. -/
example : untilHaltsFun Code.id 0 = Part.some 0 := by simp [untilHaltsFun, Code.evaln]

example : untilHaltsFun Code.id 1 = Part.none := by
  simp [untilHaltsFun, Code.evaln, Code.id, Seq.seq]

end CSLibExtTest.Computability.Decidability.Totality
