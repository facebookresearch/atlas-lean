/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsComparisonMonomialPlanSoundness

/-! Literal original source-word identities of the bounded signed permutation plans. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The exact original source-letter spelling of each comparison permutation stretch. -/
def generatedAxisGlobalComparisonMonomialOriginalLetters : Fin 8 → List (Fin 10) :=
  ![[8, 6, 8, 6, 6, 8, 6, 6, 6, 8, 7, 7, 7],
    [6, 8, 7, 8, 7, 8, 6, 8, 6, 8, 6, 6, 8, 6, 6, 8],
    [6, 6, 6, 8, 7, 8, 7, 7, 8, 6, 6, 6, 8, 6, 8, 7, 8],
    [6, 6, 6, 8, 7, 8, 7, 7, 8, 6, 6, 6, 8, 6, 8, 7, 8],
    [6, 6],
    [8, 6, 8, 7, 8, 6],
    [7, 8, 7, 8, 6, 8, 6, 8, 6, 6, 8, 6, 8, 6, 8, 6, 6, 6, 8],
    [7, 7, 8, 7, 7, 7, 8, 6, 8, 6, 6, 8, 6, 6, 6, 6, 8, 6, 8, 7, 8]]

/-- The compact plans retain exactly the whole genuine original source fiber words. -/
theorem generatedAxisGlobalComparisonMonomialWord_sources (k : Fin 8) :
    ((generatedAxisGlobalComparisonMonomialWord k).map generatedFourthMonomialFiberLetter).prod =
      ((generatedAxisGlobalComparisonMonomialOriginalLetters k).map
        generatedAxisGlobalOddSourceFiberLetter).prod := by
  fin_cases k <;> rfl

/-- Every original source permutation stretch has its complete compact rational tensor formula. -/
theorem generatedAxisGlobalComparisonMonomialWordTensor_actual (k : Fin 8)
    (hc : representativeSpinPlanValid generatedFourthMonomialLetterModel
      representativeSpinIdentityModel (generatedAxisGlobalComparisonMonomialPlan k))
    (T : GeneratedAxisGlobalRationalTensor) :
    localTensorRepresentation (((generatedAxisGlobalComparisonMonomialOriginalLetters k).map
      generatedAxisGlobalOddSourceFiberLetter).prod) (generatedAxisGlobalRationalTensorReal T) =
      generatedAxisGlobalRationalTensorReal (generatedAxisGlobalComparisonMonomialTensor k T) := by
  rw [← generatedAxisGlobalComparisonMonomialWord_sources]
  exact generatedAxisGlobalComparisonMonomialTensor_actual k hc T

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
