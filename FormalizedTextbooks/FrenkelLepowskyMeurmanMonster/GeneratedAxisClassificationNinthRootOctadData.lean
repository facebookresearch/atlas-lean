/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthComplementData

/-! Genuine Golay octads formed by four of the eight lower short directions. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- Original code labels of the fourteen four-direction octads. -/
def generatedNinthRootOctadCode : Fin 14 → Fin 4096 :=
  ![3883, 2372, 2308, 2703, 2767, 3232, 3296, 907, 971, 1444, 1508, 1647, 1583, 64]

/-- The original four lower directions supporting each genuine octad. -/
def generatedNinthRootOctadDirections : Fin 14 → Fin 4 → Fin 8 :=
  ![![0, 1, 2, 5],
    ![0, 1, 3, 4],
    ![0, 1, 6, 7],
    ![0, 2, 3, 7],
    ![0, 2, 4, 6],
    ![0, 3, 5, 6],
    ![0, 4, 5, 7],
    ![1, 2, 3, 6],
    ![1, 2, 4, 7],
    ![1, 3, 5, 7],
    ![1, 4, 5, 6],
    ![2, 3, 4, 5],
    ![2, 5, 6, 7],
    ![3, 4, 6, 7]]

/-- Each displayed code is the exact union of its four physical coordinate pairs. -/
theorem generatedNinth_root_octad_mask : ∀ j : Fin 14, ∀ i : Fin 24,
    (golayEncodedMask (generatedNinthRootOctadCode j).val).testBit i.val = true ↔
      ∃ k : Fin 4, generatedNinthLowRootCoordinates
        (generatedNinthRootOctadDirections j k) i ≠ 0 := by
  decide +kernel

/-- Every four-direction union is an actual Golay octad. -/
theorem generatedNinth_root_octad_mem : ∀ j : Fin 14,
    generatedNinthRootOctadCode j ∈ golayOctads := by
  intro j
  simp only [golayOctads, Finset.mem_filter, Finset.mem_univ, true_and]
  revert j
  decide +kernel

/-- The fourteen displayed original code labels are distinct. -/
theorem generatedNinth_root_octad_injective :
    Function.Injective generatedNinthRootOctadCode := by
  decide +kernel

/-- The preferred pair signs have even negative parity on each octad union. -/
theorem generatedNinth_root_octad_even : ∀ j : Fin 14,
    (∑ k : Fin 4, if (generatedNinthLowRootData
      (generatedNinthRootOctadDirections j k)).1 = 0 then 1 else 0) % 2 = 0 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
