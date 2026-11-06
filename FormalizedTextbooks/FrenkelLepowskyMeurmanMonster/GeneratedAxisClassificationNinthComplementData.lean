/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowRootsData

/-! The unused physical coordinates form an original Golay octad. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The original code label of the eight coordinates outside the lower short directions. -/
def generatedNinthComplementCode : Fin 4096 := 1899

/-- The original complement mask is the actual Golay encoding of this code label. -/
theorem generatedNinth_complement_mask :
    golayEncodedMask generatedNinthComplementCode.val = 1317672 := by
  decide +kernel

/-- The unused physical coordinates constitute a genuine octad. -/
theorem generatedNinth_complement_code_mem : generatedNinthComplementCode ∈ golayOctads := by
  simp only [golayOctads, Finset.mem_filter, Finset.mem_univ, true_and]
  decide +kernel

/-- The exact complement consists of these eight original physical coordinates. -/
def generatedNinthComplementCoordinates : Fin 8 → Fin 24 := ![3, 5, 8, 9, 11, 12, 18, 20]

/-- Complement membership is precisely the genuine Golay support predicate. -/
theorem generatedNinth_complement_coordinates : ∀ i : Fin 24,
    (∃ k : Fin 8, generatedNinthComplementCoordinates k = i) ↔
      (golayEncodedMask generatedNinthComplementCode.val).testBit i.val = true := by
  decide +kernel

/-- All eight lower short directions vanish exactly on the complement octad. -/
theorem generatedNinth_complement_low_root_zero : ∀ i : Fin 24,
    (∀ r : Fin 8, generatedNinthLowRootCoordinates r i = 0) ↔
      (golayEncodedMask generatedNinthComplementCode.val).testBit i.val = true := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
