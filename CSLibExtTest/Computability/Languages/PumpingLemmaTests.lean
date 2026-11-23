/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `7f0f951227ee766bba21a6d5a5e56d9065fe85aa`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

module

public import CSLibExt.Computability.Languages.PumpingLemma

@[expose] public section

namespace Cslib.Language

example : pump [0] [1, 2] [3] 3 = [0, 1, 2, 1, 2, 1, 2, 3] := by
  decide

example : pump [0] [1, 2] [3] 0 = [0, 3] := by
  simp

example {Symbol : Type*} {l : Language Symbol} (hl : l.IsRegular) :
    IsPumpingLength l (IsRegular.pumpingLength hl) :=
  IsRegular.pumpingLength_spec hl

example {Symbol : Type*} :
    IsRegular.pumpingLength (Symbol := Symbol) IsRegular.zero = 0 := by
  rw [IsRegular.pumpingLength_eq_zero_iff]

end Cslib.Language
