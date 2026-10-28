/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSectionPermutation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowRootsData

/-! Exact original integer transport of the lower short directions to a coordinate octad. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option maxRecDepth 20000

/-- The genuine Golay generator sign needed before the original permutation word. -/
def generatedNinthSectionSign : golayCode :=
  ⟨golayEncoder (golayLabelCoefficients 32), ⟨_, rfl⟩⟩

/-- Physical coordinates and signs of the eight transported original short directions. -/
def generatedNinthSectionRootData : Fin 8 → Fin 24 × Fin 24 × ℤ × ℤ :=
  ![(4, 5, -1, -1), (12, 13, -1, 1), (0, 1, -1, -1), (0, 1, -1, 1),
    (8, 9, -1, -1), (8, 9, -1, 1), (12, 13, -1, -1), (4, 5, 1, -1)]

/-- Unit physical integer vectors after the complete original spatial transport. -/
def generatedNinthSectionRootCoordinates (r : Fin 8) (i : Fin 24) : ℤ :=
  if i = (generatedNinthSectionRootData r).1 then (generatedNinthSectionRootData r).2.2.1
  else if i = (generatedNinthSectionRootData r).2.1 then
    (generatedNinthSectionRootData r).2.2.2 else 0

/-- The destination coordinate support has its original finite Golay label. -/
def generatedNinthSectionCode : Fin 4096 := 2396

/-- The original destination code is an actual Golay octad. -/
theorem generatedNinth_section_code_mem : generatedNinthSectionCode ∈ golayOctads := by
  simp only [golayOctads, Finset.mem_filter, Finset.mem_univ, true_and]
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Bind all 192 transported integer coordinates through the original permutation word.
/-- The source sign, source permutation and inverse Xi give the exact physical vectors. -/
theorem generatedNinth_section_root_certificate : ∀ r : Fin 8,
    (2 : ℤ) • generatedNinthSectionRootCoordinates r =
      co1XiNumerator.transpose *ᵥ
        golayIntegerPermute generatedNinthSectionPermutation.val
          (golayIntegerSign generatedNinthSectionSign.val
            (generatedNinthLowRootCoordinates r)) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Check all 576 coordinate projection entries against the eight source short directions.
/-- The eight transported directions give twice the original coordinate-octad projection. -/
theorem generatedNinth_section_root_outer : ∀ i j : Fin 24,
    (∑ r : Fin 8, generatedNinthSectionRootCoordinates r i *
      generatedNinthSectionRootCoordinates r j) =
        if i = j ∧ (golayEncodedMask generatedNinthSectionCode.val).testBit i.val = true
          then 2 else 0 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
