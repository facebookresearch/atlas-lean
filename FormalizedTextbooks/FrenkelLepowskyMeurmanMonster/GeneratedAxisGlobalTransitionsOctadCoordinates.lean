/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOctadCatalog

/-! Exact increasing physical coordinates of all759 original actual Golay octads. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

-- The finite certificate ranges over all759 octads and their eight physical coordinates.
set_option maxRecDepth 10000

set_option maxHeartbeats 20000000 in
-- Check all6072 original support memberships using the already finite source code table.
private theorem coordinate_mem (j : Fin 759) (k : Fin 8) :
    generatedAxisGlobalOctadCoordinatesData j k ∈
      golayMaskSupport (golayEncodedMask (generatedAxisGlobalOctadCodeData j).val) := by
  have h : ∀ j : Fin 759, ∀ k : Fin 8,
      generatedAxisGlobalOctadCoordinatesData j k ∈
        golayMaskSupport (golayEncodedMask (generatedAxisGlobalOctadCodeData j).val) := by
    decide +kernel
  exact h j k

set_option maxHeartbeats 20000000 in
-- Adjacent checks determine the exact increasing order of each octad's eight coordinates.
private theorem coordinate_adjacent : ∀ j : Fin 759, ∀ k : Fin 7,
    generatedAxisGlobalOctadCoordinatesData j (Fin.castSucc k) <
      generatedAxisGlobalOctadCoordinatesData j k.succ := by
  decide +kernel

/-- Every displayed physical coordinate is the actual coordinate at the original octad index. -/
theorem generatedAxisGlobalOctadCoordinatesData_actual (j : Fin 759) (k : Fin 8) :
    generatedAxisGlobalOctadCoordinatesData j k = golayOctadCoordinate j k := by
  have hm : StrictMono (generatedAxisGlobalOctadCoordinatesData j) :=
    Fin.strictMono_iff_lt_succ.mpr (coordinate_adjacent j)
  have hmem : ∀ k, generatedAxisGlobalOctadCoordinatesData j k ∈
      golayMaskSupport (golayEncodedMask (golayOctadLabel j).val) := by
    intro k
    rw [← generatedAxisGlobalOctadCodeData_actual]
    exact coordinate_mem j k
  have h := Finset.orderEmbOfFin_unique (golayOctad_support_card j) hmem hm
  exact congrFun h k

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
