/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Concrete acyclic auxiliary paths evaluated in the original independent C422/S/Q group. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422TPathData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522WordPrograms

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The exact positive path program uses only earlier paths and actual original source symbols. -/
def y422TPathProgram : Y522WordProgram 9 9033 := fun i =>
  if h : i = 0 then .one
  else .appendGenerator ⟨(y422TPathData i).1, y422TPathData_prior i h⟩ (y422TPathData i).2

/-- Actual source-path values in the original independent C422/S/Q group. -/
noncomputable def y422TPathValue : Fin 9033 → Y422Presentation :=
  y522WordProgramValue y422TPathProgram (fun v => (PresentedGroup.of v : Y422Presentation))

/-- The initial auxiliary path is the actual group identity. -/
theorem y422TPathValue_zero : y422TPathValue 0 = 1 := by
  rw [y422TPathValue, y522WordProgramValue_eq]
  rw [show y422TPathProgram 0 = .one from rfl]
  rfl

/-- Each auxiliary path is its strictly earlier actual path followed by its actual source letter. -/
theorem y422TPathValue_step (i : Fin 9033) (hi : i ≠ 0) :
    y422TPathValue i =
      y422TPathValue ⟨(y422TPathData i).1, (y422TPathData_prior i hi).trans i.isLt⟩ *
        (fun v => (PresentedGroup.of v : Y422Presentation)) (y422TPathData i).2 := by
  rw [y422TPathValue, y522WordProgramValue_eq]
  simp only [y422TPathProgram, dite_eq_right hi, y522InstructionValue]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
