/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.LucasSequenceNegation

/-! # Regression tests for Lucas sequence signs -/

open MetaMathlibExt

private def params : LucasSequenceParams := ⟨3, 2, by decide⟩
private def negParams : LucasSequenceParams := ⟨-3, 2, by decide⟩
private def zeroPParams : LucasSequenceParams := ⟨0, -2, by decide⟩

example : lucasU negParams 0 = 0 ∧ lucasV negParams 0 = 2 :=
  lucasU_lucasV_neg_p params 0

-- At even indices only U changes sign; at odd indices only V does.
example : lucasU negParams 2 = -3 ∧ lucasV negParams 2 = 5 :=
  lucasU_lucasV_neg_p params 2

example : lucasU negParams 3 = 7 ∧ lucasV negParams 3 = -9 :=
  lucasU_lucasV_neg_p params 3

-- Negation can fix the first parameter, and the second parameter can be negative.
example : lucasU zeroPParams 3 = 2 ∧ lucasV zeroPParams 3 = 0 :=
  lucasU_lucasV_neg_p zeroPParams 3
