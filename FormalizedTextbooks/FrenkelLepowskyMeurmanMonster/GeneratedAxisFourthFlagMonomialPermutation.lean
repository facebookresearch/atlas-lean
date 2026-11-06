/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismPermutations

/-! A literal Golay permutation preserving the fourth flag's coordinate octad.
The selected signed short line is not asserted to be preserved here. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- Fix the first eight coordinates and exchange consecutive coordinates thereafter. -/
def generatedFourthFlagCorrectionCoordinates : Fin 24 → Fin 24 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 13, 12, 15, 14,
    17, 16, 19, 18, 21, 20, 23, 22]

private theorem correction_involution : ∀ i : Fin 24,
    generatedFourthFlagCorrectionCoordinates
      (generatedFourthFlagCorrectionCoordinates i) = i := by decide +kernel

/-- The correction is an actual coordinate permutation, with the same inverse. -/
def generatedFourthFlagCorrectionPermutation : Equiv.Perm (Fin 24) where
  toFun := generatedFourthFlagCorrectionCoordinates
  invFun := generatedFourthFlagCorrectionCoordinates
  left_inv := by exact correction_involution
  right_inv := by exact correction_involution

private def correctionGeneratorLabels : Fin 12 → Fin 4096 :=
  ![1, 2, 4, 8, 16, 47, 76, 134, 268, 522, 1055, 2048]

private theorem correction_generator_images : ∀ (j : Fin 12) (i : Fin 24),
    (golayGeneratorBit j (generatedFourthFlagCorrectionCoordinates i) : ZMod 2) =
      golayEncoder (golayLabelCoefficients (correctionGeneratorLabels j)) i := by
  decide +kernel

private def correctionLinear :
    (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) where
  toFun := golayPermute generatedFourthFlagCorrectionPermutation
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem correction_preserves (c : Fin 24 → ZMod 2) (hc : c ∈ golayCode) :
    golayPermute generatedFourthFlagCorrectionPermutation c ∈ golayCode := by
  obtain ⟨a, rfl⟩ := hc
  have ha : a = ∑ j, a j • (Pi.single j 1 : Fin 12 → ZMod 2) := by
    ext i
    simp [Pi.single_apply]
  change correctionLinear.comp golayEncoder a ∈ golayCode
  rw [ha, map_sum]
  apply golayCode.sum_mem
  intro j _
  rw [map_smul]
  apply golayCode.smul_mem
  have hrow : golayEncoder (Pi.single j 1) =
      fun i => (golayGeneratorBit j i : ZMod 2) := by
    ext i
    simp [golayEncoder, Pi.single_apply, ite_mul]
  change golayPermute generatedFourthFlagCorrectionPermutation
    (golayEncoder (Pi.single j 1)) ∈ golayCode
  rw [hrow]
  exact ⟨golayLabelCoefficients (correctionGeneratorLabels j),
    funext (correction_generator_images j) |>.symm⟩

/-- The literal correction preserves the actual Golay code in both directions. -/
def generatedFourthFlagCorrectionGolay : golayAutomorphismSubgroup :=
  ⟨generatedFourthFlagCorrectionPermutation, by
    intro c
    constructor
    · exact correction_preserves c
    · intro hc
      have h := correction_preserves _ hc
      have hi : golayPermute generatedFourthFlagCorrectionPermutation
          (golayPermute generatedFourthFlagCorrectionPermutation c) = c := by
        ext i
        exact congrArg c (correction_involution i)
      rwa [hi] at h⟩

/-- The correction acts on the genuine Leech lattice by the literal permutation. -/
def generatedFourthFlagCorrectionLeech : leechIsomSubgroup :=
  golayPermutationIsometry generatedFourthFlagCorrectionGolay

/-- Coordinate formula for the actual correction, including its inverse convention. -/
theorem generatedFourthFlagCorrectionLeech_apply (x : Fin 24 → ℝ) (i : Fin 24) :
    generatedFourthFlagCorrectionLeech.val x i =
      x (generatedFourthFlagCorrectionCoordinates i) := rfl

/-- The correction preserves the actual code word on coordinates four through eleven. -/
theorem generatedFourthFlagCorrection_word :
    golayPermute generatedFourthFlagCorrectionPermutation
      (golayEncoder (golayLabelCoefficients 14)) =
      golayEncoder (golayLabelCoefficients 14) := by
  decide +kernel

/-- The correction sends coordinates nine and ten to eight and eleven. -/
theorem generatedFourthFlagCorrection_pair :
    generatedFourthFlagCorrectionCoordinates 9 = 8 ∧
      generatedFourthFlagCorrectionCoordinates 10 = 11 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
