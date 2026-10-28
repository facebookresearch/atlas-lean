/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsComparisonMonomialFastTensor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsComparisonSparseBitFrames

/-! The whole original Fourth frame reuses exact complete monomial tensor evaluations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- Every original Q phase, sign, Gaussian input, and permutation column is retained. -/
def generatedAxisGlobalOddFourthFastFrameTensor (k : Fin 4)
    (T : GeneratedAxisGlobalRationalTensor) : GeneratedAxisGlobalRationalTensor :=
  generatedAxisGlobalRationalTensorQ (generatedAxisGlobalOddFourthComparisonQ k)
    (generatedAxisGlobalRationalTensorSign 16 0
      (generatedAxisGlobalComparisonMonomialFastTensor (Fin.castAdd 4 k)
        (generatedAxisGlobalOddFourthCompactXiTensor k
          (if k.val < 2 then generatedAxisGlobalComparisonMonomialFastTensor 4 T else T))))

/-- Every coefficient is exactly the entire previously certified original frame. -/
theorem generatedAxisGlobalOddFourthFastFrameTensor_eq (k : Fin 4)
    (T : GeneratedAxisGlobalRationalTensor) :
    generatedAxisGlobalOddFourthFastFrameTensor k T = generatedAxisGlobalOddFourthSparseBitFrameTensor k T := by
  simp only [generatedAxisGlobalOddFourthFastFrameTensor, generatedAxisGlobalOddFourthSparseBitFrameTensor,
    generatedAxisGlobalComparisonMonomialFastTensor_eq]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
