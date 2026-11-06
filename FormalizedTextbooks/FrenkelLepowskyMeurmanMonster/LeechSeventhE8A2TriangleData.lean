/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2Intrinsic
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhSection

/-! Original finite root addresses of the seventh matrix's physical triangle. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Candidate 537 consists of the original three difference roots on coordinates 16, 17 and 19. -/
theorem leechSeventhE8A2_triangle_indices :
    leechSeventhE8A2Indices 537 = ![22, 24, 26] := by decide +kernel

/-- The three actual finite triangle roots have these literal original integer coordinates. -/
theorem leechSeventhE8A2_triangle_local (j : Fin 3) :
    leechSeventhE8RootLocal (leechSeventhE8A2Indices 537 j) =
      (![![0, 0, 0, 0, 4, -4, 0, 0], ![0, 0, 0, 0, 4, 0, 0, -4],
        ![0, 0, 0, 0, 0, 4, 0, -4]] : Fin 3 → Fin 8 → ℤ) j := by
  rw [leechSeventhE8A2_triangle_indices]
  fin_cases j <;> decide +kernel

/-- Every genuine triangle root belongs to the seventh actual octad section. -/
theorem leechSeventhE8A2_triangle_supported (j : Fin 3) :
    leechSeventhE8Root (leechSeventhE8A2Indices 537 j) ∈
      generatedAxisE8CoordinateSection (golayOctadWord generatedSeventhSectionOctad) := by
  change ∀ i, golayOctadWord generatedSeventhSectionOctad i = 0 →
    (leechSeventhE8Root (leechSeventhE8A2Indices 537 j)).val i = 0
  intro i hi
  have hz : ¬ (12 ≤ i.val ∧ i.val < 20) := by
    intro h
    exact ((generatedSeventh_section_octad_support i).mpr h) hi
  rw [leechSeventhE8Root_physical, leechSeventhE8A2_triangle_local]
  fin_cases j <;> fin_cases i
  all_goals first
    | exact False.elim (hz (by decide))
    | norm_num [generatedFifthFrameInsert]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
