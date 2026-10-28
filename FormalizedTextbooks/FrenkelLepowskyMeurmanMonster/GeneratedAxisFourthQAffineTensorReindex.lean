/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQAffineTensorPair

/-! Reindex the entire original signed Y tensor into its twenty-eight affine states. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The exact packed tensor of the twenty-eight original affine states. -/
def generatedFourthQAffineTensorPacked : SpinIndex → Fin 24 → ℝ :=
  ∑ k : Fin 28, (qSign (generatedFourthQAffineTensorScalePhases k) / Real.sqrt 2) •
    generatedFourthQAffineTensorState k

/-- The full original signed 56-term tensor equals the packed affine tensor exactly. -/
theorem generatedFourthQAffineTensor_signed_sum :
    (∑ j : Fin 56, qSign (generatedFourthOddCoefficientPhaseData j) •
      trialityYTensor (generatedFourthOddRootOutputData j).1
        (generatedFourthOddRootOutputData j).2) = generatedFourthQAffineTensorPacked := by
  let F (j : Fin 56) := qSign (generatedFourthOddCoefficientPhaseData j) •
    trialityYTensor (generatedFourthOddRootOutputData j).1
      (generatedFourthOddRootOutputData j).2
  let E := Equiv.ofBijective generatedFourthQAffineTensorPairIndex
    generatedFourthQAffineTensorPairIndex_bijective
  calc
    _ = ∑ x : Fin 28 × Fin 2, F (generatedFourthQAffineTensorPairIndex x) :=
      (E.sum_comp F).symm
    _ = ∑ k : Fin 28, ∑ s : Fin 2, F (generatedFourthQAffineTensorPairIndex (k, s)) :=
      Fintype.sum_prod_type _
    _ = generatedFourthQAffineTensorPacked := by
      apply Finset.sum_congr rfl
      intro k _
      exact generatedFourthQAffineTensor_pair k

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
