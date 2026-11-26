/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Distributed.KSetAgreement
import Mathlib.Data.Fintype.Basic

/-! # Tests for k-set agreement outcomes -/

namespace Cslib.Distributed.KSetAgreement.Tests

-- Processes `0` and `1` are correct and decide `0`; faulty process `2` decides `1`,
-- the input of silent faulty process `3`.
private abbrev mixed : Outcome (Fin 4) (Fin 3) where
  input p := if p = 3 then 1 else 0
  decision p := if p = 3 then none else some (if p = 2 then 1 else 0)
  correct p := p = 0 ∨ p = 1

example : mixed.decidedValues = {0, 1} := by decide

example : mixed.IsKSetAgreement 2 := by
  unfold Outcome.IsKSetAgreement Outcome.Valid Outcome.Agrees Outcome.Terminates
  decide

-- The decision of a faulty process still counts toward agreement.
example : ¬ mixed.Agrees 1 := by
  unfold Outcome.Agrees
  decide

private abbrev silentCorrect : Outcome (Fin 4) (Fin 3) :=
  { mixed with correct := fun p => p ≠ 2 }

example : ¬ silentCorrect.Terminates := by
  unfold Outcome.Terminates
  decide

-- An unproposed decision by a faulty process still violates validity.
private abbrev unproposed : Outcome (Fin 4) (Fin 3) :=
  { mixed with decision := fun p => if p = 2 then some 2 else mixed.decision p }

example : ¬ unproposed.Valid := by
  unfold Outcome.Valid
  decide

private abbrev unanimous : Outcome (Fin 4) (Fin 3) :=
  { mixed with decision := fun p => if p = 3 then none else some 0 }

example : unanimous.IsKSetAgreement 1 := by
  apply (unanimous.isKSetAgreement_one_iff).2
  unfold Outcome.Valid Outcome.Terminates
  decide

example : ¬ unanimous.Agrees 0 := by
  unfold Outcome.Agrees
  decide

private abbrev silent : Outcome (Fin 4) (Fin 3) :=
  { mixed with decision := fun _ => none, correct := fun _ => False }

example : silent.IsKSetAgreement 0 := by
  unfold Outcome.IsKSetAgreement Outcome.Valid Outcome.Agrees Outcome.Terminates
  decide

end Cslib.Distributed.KSetAgreement.Tests
