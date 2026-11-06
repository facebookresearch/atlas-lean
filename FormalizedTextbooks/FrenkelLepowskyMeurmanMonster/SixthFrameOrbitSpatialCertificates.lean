/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SixthFrameOrbitDataSpatial
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsGolayData

/-! Source-word and physical-coordinate checks for the fifteen monomial basis certificates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Original forward words and all three inverse coordinate tables agree exactly. -/
theorem sixthFrameOrbit_word_check : ∀ i : Fin 24,
    golayGeneratingWordArray leechRootedA2SixthPermutationTransportWord i =
      sixthFrameOrbitBForward i ∧
    golayGeneratingWordArray leechRootedA2SixthPermutationTransportWord
      (sixthFrameOrbitBInverse i) = i ∧
    golayGeneratingWordArray leechRootedA2SixthXiTransportWord i =
      sixthFrameOrbitCForward i ∧
    golayGeneratingWordArray leechRootedA2SixthXiTransportWord (sixthFrameOrbitCInverse i) = i ∧
    golayGeneratingWordArray leechRootedA2SixthPermutationSwapWord
      (sixthFrameOrbitSwapInverse i) = i := by
  decide +kernel

/-- The conjugated original target permutations have the literal physical input indices. -/
theorem sixthFrameOrbit_conjugated_input_check : ∀ k : Fin 3, ∀ i : Fin 24,
    sixthFrameOrbitBForward
      (representativePermutationPhysicalImages ((![(0 : Fin 83), 1, 3] : Fin 3 → Fin 83) k)
        (sixthFrameOrbitBInverse i)) =
      sixthFrameOrbitSpatialInput ⟨k.val + 10, by omega⟩ i := by
  decide +kernel

/-- All original sign bits match the displayed integer signs and identity input indices. -/
theorem sixthFrameOrbit_sign_check : ∀ k : Fin 10, ∀ i : Fin 24,
    ((sourceGeneratedSignCode (sixthFrameOrbitSignLabels k)).val i = 0 ↔
      sixthFrameOrbitSpatialSign (Fin.castAdd 6 k) i = 1) ∧
    (sixthFrameOrbitSpatialSign (Fin.castAdd 6 k) i = 1 ∨
      sixthFrameOrbitSpatialSign (Fin.castAdd 6 k) i = -1) ∧
    sixthFrameOrbitSpatialInput (Fin.castAdd 6 k) i = i := by
  decide +kernel

/-- All six actual permutation cases have identity scalar coefficient. -/
theorem sixthFrameOrbit_permutation_sign_check : ∀ k : Fin 6, ∀ i : Fin 24,
    sixthFrameOrbitSpatialSign (Fin.natAdd 10 k) i = 1 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
