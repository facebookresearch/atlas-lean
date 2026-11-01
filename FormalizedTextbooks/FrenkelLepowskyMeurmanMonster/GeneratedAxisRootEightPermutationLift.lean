/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalLift
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismGeneration

/-! Arbitrary literal original Mathieu words retain their genuine local spin lifts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original source permutation fibers evaluated in the same order as an actual Mathieu word. -/
def generatedRootEightPermutationWordFiber (w : List (Fin 4)) : localFiberSubgroup :=
  (w.map generatedFifthRootEightCanonicalFiberLetter).prod

/-- The corresponding complete local element retains the original source Parker phases. -/
def generatedRootEightPermutationWordLocal (w : List (Fin 4)) : H :=
  localFiberIntoH (generatedRootEightPermutationWordFiber w)

/-- The canonical transport letters are precisely the original Mathieu generating letters. -/
theorem generatedRootEight_permutation_letter_eq (k : Fin 4) :
    generatedFifthRootEightCanonicalPermutationLetter k = golayGeneratingLetter k := rfl

/-- Every entire source permutation word has its actual original Conway projection. -/
theorem generatedRootEight_permutation_word_fiber_spatial (w : List (Fin 4)) :
    (generatedRootEightPermutationWordFiber w).val.2 =
      golayPermutationIsometry (golayGeneratingWord w) := by
  change generatedFourthMonomialSpatialProjection (generatedRootEightPermutationWordFiber w) =
    golayPermutationHom (golayGeneratingWord w)
  rw [generatedRootEightPermutationWordFiber, golayGeneratingWord,
    map_list_prod, map_list_prod]
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro k _
  simp only [Function.comp_apply]
  rw [generatedFifthRootEight_canonical_fiber_letter_spatial,
    generatedRootEight_permutation_letter_eq]

/-- Every literal source word projects to the quotient of the same genuine Mathieu isometry. -/
theorem generatedRootEight_permutation_word_local_projection (w : List (Fin 4)) :
    projH (generatedRootEightPermutationWordLocal w) =
      QuotientGroup.mk' signsSubgroup (golayPermutationIsometry (golayGeneratingWord w)) := by
  change QuotientGroup.mk' signsSubgroup (generatedRootEightPermutationWordFiber w).val.2 = _
  rw [generatedRootEight_permutation_word_fiber_spatial]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
