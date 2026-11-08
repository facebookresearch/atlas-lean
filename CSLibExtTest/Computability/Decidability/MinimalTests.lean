/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Decidability.Minimal

@[expose] public section

/-!
# Tests for minimal programs
-/

set_option autoImplicit false

open Cslib.Decidability Encodable
open Nat.Partrec (Code)

namespace CSLibExtTest.Computability.Decidability.Minimal

/-- `MIN` is not recognizable, hence not decidable. -/
example : ¬TM2Recognizable MinimalCode := not_tm2Recognizable_minimalCode

example : ¬TM2Decidable MinimalCode := fun h ↦ not_tm2Recognizable_minimalCode h.tm2Recognizable

/-- The code with the smallest encoding has description length `0`, so it is minimal. -/
example : MinimalCode (Denumerable.ofNat Code 0) := fun d hd ↦ by
  simp [descLength, Denumerable.encode_ofNat] at hd

/-- Description lengths tie: the codes encoded by `2` and `3` both have two binary digits. -/
example : descLength (Denumerable.ofNat Code 2) = descLength (Denumerable.ofNat Code 3) := by
  simp only [descLength, Denumerable.encode_ofNat]
  decide

/-- Minimal codes exist above every bound. -/
example : ∃ D : Code, MinimalCode D ∧ 1000 < encode D := exists_minimalCode_gt 1000

end CSLibExtTest.Computability.Decidability.Minimal
