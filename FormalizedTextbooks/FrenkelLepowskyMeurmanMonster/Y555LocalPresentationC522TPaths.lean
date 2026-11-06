/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Concrete acyclic auxiliary paths evaluated in the original independent Y555 group. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522TPathData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522AuxGenerators

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The exact positive path program uses only earlier paths and actual original source symbols. -/
def y522TPathProgram : Y522WordProgram 11 1795 := fun i =>
  if h : i = 0 then .one
  else .appendGenerator ⟨(y522TPathData i).1, y522TPathData_prior i h⟩ (y522TPathData i).2

/-- Actual source-path values in the original independent Y555 group. -/
noncomputable def y522TPathValue : Fin 1795 → BimonsterPresentation :=
  y522WordProgramValue y522TPathProgram y522AuxGenerator

/-- The initial auxiliary path is the actual group identity. -/
theorem y522TPathValue_zero : y522TPathValue 0 = 1 := by
  rw [y522TPathValue, y522WordProgramValue_eq]
  rw [show y522TPathProgram 0 = .one from rfl]
  rfl

/-- Each auxiliary path is its strictly earlier actual path followed by its actual source letter. -/
theorem y522TPathValue_step (i : Fin 1795) (hi : i ≠ 0) :
    y522TPathValue i =
      y522TPathValue ⟨(y522TPathData i).1, (y522TPathData_prior i hi).trans i.isLt⟩ *
        y522AuxGenerator (y522TPathData i).2 := by
  rw [y522TPathValue, y522WordProgramValue_eq]
  simp only [y522TPathProgram, dite_eq_right hi, y522InstructionValue]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
