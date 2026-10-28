/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationTensorData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpinPlan4Valid

/-! Full original tensor transport and Parker phase for monomial word 4. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 10000

set_option maxHeartbeats 16000000 in
-- Check128 actual support addresses, spatial columns and original signed unit weights.
/-- Every original tensor support coordinate is fixed with the genuine Parker phase. -/
theorem generatedFifth_monomial_permutation_tensor_certificate_4 :
    ∀ j : Fin 64, ∀ b : ZMod 2,
      generatedFifthMonomialPermutationModelLabel 4
        (generatedFifthXiTensorAddress j b +
          spinTranslation (generatedFifthMonomialPermutationCorrection 4)) =
        generatedFifthXiTensorAddress (generatedFifthMonomialPermutationTensorSource 4 j)
          (b + generatedFifthMonomialPermutationTensorBit 4 j) ∧
      (generatedFifthMonomialSpatialPermutation 4).val.symm
        (generatedFifthOddRootOutputData j).2 =
          (generatedFifthOddRootOutputData (generatedFifthMonomialPermutationTensorSource 4 j)).2 ∧
      nortonUIntegerSign (spinPhase (generatedFifthMonomialPermutationCorrection 4)
        (generatedFifthXiTensorAddress j b) +
        generatedFifthMonomialPermutationModelPhase 4
          (generatedFifthXiTensorAddress j b +
            spinTranslation (generatedFifthMonomialPermutationCorrection 4))) *
        generatedFifthXiTensorWeight (generatedFifthMonomialPermutationTensorSource 4 j)
          (b + generatedFifthMonomialPermutationTensorBit 4 j) =
            generatedFifthXiTensorWeight j b := by
  have hc :
    ∀ j : Fin 64, ∀ b : ZMod 2,
      generatedFifthMonomialPermutationModelLabel 4
        (generatedFifthXiTensorAddress j b +
          spinTranslation (generatedFifthMonomialPermutationCorrection 4)) =
        generatedFifthXiTensorAddress (generatedFifthMonomialPermutationTensorSource 4 j)
          (b + generatedFifthMonomialPermutationTensorBit 4 j) ∧
      generatedFifthMonomialSpatialForward 4
        (generatedFifthOddRootOutputData (generatedFifthMonomialPermutationTensorSource 4 j)).2 =
          (generatedFifthOddRootOutputData j).2 ∧
      nortonUIntegerSign (spinPhase (generatedFifthMonomialPermutationCorrection 4)
        (generatedFifthXiTensorAddress j b) +
        generatedFifthMonomialPermutationModelPhase 4
          (generatedFifthXiTensorAddress j b +
            spinTranslation (generatedFifthMonomialPermutationCorrection 4))) *
        generatedFifthXiTensorWeight (generatedFifthMonomialPermutationTensorSource 4 j)
          (b + generatedFifthMonomialPermutationTensorBit 4 j) =
            generatedFifthXiTensorWeight j b := by
    decide +kernel
  intro j b
  rcases hc j b with ⟨ht, hcol, hw⟩
  refine ⟨ht, ?_, hw⟩
  have hf : (generatedFifthMonomialSpatialPermutation 4).val
      (generatedFifthOddRootOutputData (generatedFifthMonomialPermutationTensorSource 4 j)).2 =
        (generatedFifthOddRootOutputData j).2 := by
    rw [generatedFifthMonomialSpatial_forward]
    exact hcol
  rw [← hf, Equiv.symm_apply_apply]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
