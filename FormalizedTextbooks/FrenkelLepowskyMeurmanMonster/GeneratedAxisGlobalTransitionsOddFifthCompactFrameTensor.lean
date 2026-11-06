/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsComparisonMonomialWordSources
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthFrameTensor

/-! Complete original Fifth frame tensor formulas from bounded signed permutation models. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The complete original root-three comparison frame in bounded rational coordinates. -/
def generatedAxisGlobalOddFifthCompactFrameTensor (k : Fin 2)
    (T : GeneratedAxisGlobalRationalTensor) : GeneratedAxisGlobalRationalTensor :=
  generatedAxisGlobalRationalTensorQ (generatedAxisGlobalOddFifthComparisonQ k)
    (generatedAxisGlobalComparisonMonomialTensor (Fin.natAdd 6 k)
      (generatedAxisGlobalRationalTensorXiCached
        (generatedAxisGlobalRationalTensorSign (generatedAxisGlobalOddFifthComparisonSign k) 0
          (generatedAxisGlobalComparisonMonomialTensor 5 T))))

/-- Checked bounded signed plans bind every actual physical tensor coefficient of both full frames. -/
theorem generatedAxisGlobalOddFifthCompactFrameTensor_actual (k : Fin 2)
    (hc : ∀ j : Fin 8, representativeSpinPlanValid generatedFourthMonomialLetterModel
      representativeSpinIdentityModel (generatedAxisGlobalComparisonMonomialPlan j))
    (T : GeneratedAxisGlobalRationalTensor) :
    localTensorRepresentation (generatedAxisGlobalOddFifthComparisonFiber k)
      (generatedAxisGlobalRationalTensorReal T) =
      generatedAxisGlobalRationalTensorReal (generatedAxisGlobalOddFifthCompactFrameTensor k T) := by
  have hpre : generatedAxisGlobalOddFifthComparisonPreLetters =
      generatedAxisGlobalComparisonMonomialOriginalLetters 5 := rfl
  have hpost : generatedAxisGlobalOddFifthComparisonPostLetters k =
      generatedAxisGlobalComparisonMonomialOriginalLetters (Fin.natAdd 6 k) := by
    fin_cases k <;> rfl
  rw [generatedAxisGlobalOddFifthComparisonFiber, hpre, hpost]
  simp only [map_mul, LinearEquiv.mul_apply]
  rw [generatedAxisGlobalComparisonMonomialWordTensor_actual _ (hc _),
    generatedAxisGlobalRationalTensorSign_actual,
    generatedAxisGlobalRationalTensorXiCached_actual,
    generatedAxisGlobalComparisonMonomialWordTensor_actual _ (hc _),
    generatedAxisGlobalRationalTensorQ_actual]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
