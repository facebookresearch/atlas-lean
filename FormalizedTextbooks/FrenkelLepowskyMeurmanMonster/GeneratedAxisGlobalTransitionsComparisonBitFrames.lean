/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsComparisonMonomialBitTensor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthCompactFrameTensorUnconditional
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthCompactFrameTensorUnconditional

/-! Whole original comparison frames with exact bounded spin bit evaluation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- Complete original Fourth frame tensor, retaining both genuine Xi directions and every source sign. -/
def generatedAxisGlobalOddFourthBitFrameTensor (k : Fin 4)
    (T : GeneratedAxisGlobalRationalTensor) : GeneratedAxisGlobalRationalTensor :=
  generatedAxisGlobalRationalTensorQ (generatedAxisGlobalOddFourthComparisonQ k)
    (generatedAxisGlobalRationalTensorSign 16 0
      (generatedAxisGlobalComparisonMonomialBitTensor (Fin.castAdd 4 k)
        (generatedAxisGlobalOddFourthCompactXiTensor k
          (if k.val < 2 then generatedAxisGlobalComparisonMonomialBitTensor 4 T else T))))

/-- The entire bit frame is the complete previously certified original Fourth tensor formula. -/
theorem generatedAxisGlobalOddFourthBitFrameTensor_eq (k : Fin 4)
    (T : GeneratedAxisGlobalRationalTensor) :
    generatedAxisGlobalOddFourthBitFrameTensor k T = generatedAxisGlobalOddFourthCompactFrameTensor k T := by
  simp only [generatedAxisGlobalOddFourthBitFrameTensor, generatedAxisGlobalOddFourthCompactFrameTensor,
    generatedAxisGlobalComparisonMonomialBitTensor_eq]

/-- The bounded bit formula is the whole actual original Fourth comparison action. -/
theorem generatedAxisGlobalOddFourthBitFrameTensor_actual (k : Fin 4)
    (T : GeneratedAxisGlobalRationalTensor) :
    localTensorRepresentation (generatedAxisGlobalOddFourthComparisonFiber k)
      (generatedAxisGlobalRationalTensorReal T) =
      generatedAxisGlobalRationalTensorReal (generatedAxisGlobalOddFourthBitFrameTensor k T) := by
  rw [generatedAxisGlobalOddFourthBitFrameTensor_eq]
  exact generatedAxisGlobalOddFourthCompactFrameTensor_unconditional k T

/-- Complete original Fifth frame tensor with all original source signs and the full Q correction. -/
def generatedAxisGlobalOddFifthBitFrameTensor (k : Fin 2)
    (T : GeneratedAxisGlobalRationalTensor) : GeneratedAxisGlobalRationalTensor :=
  generatedAxisGlobalRationalTensorQ (generatedAxisGlobalOddFifthComparisonQ k)
    (generatedAxisGlobalComparisonMonomialBitTensor (Fin.natAdd 6 k)
      (generatedAxisGlobalRationalTensorXiCached
        (generatedAxisGlobalRationalTensorSign (generatedAxisGlobalOddFifthComparisonSign k) 0
          (generatedAxisGlobalComparisonMonomialBitTensor 5 T))))

/-- The entire bit frame is the complete previously certified original Fifth tensor formula. -/
theorem generatedAxisGlobalOddFifthBitFrameTensor_eq (k : Fin 2)
    (T : GeneratedAxisGlobalRationalTensor) :
    generatedAxisGlobalOddFifthBitFrameTensor k T = generatedAxisGlobalOddFifthCompactFrameTensor k T := by
  simp only [generatedAxisGlobalOddFifthBitFrameTensor, generatedAxisGlobalOddFifthCompactFrameTensor,
    generatedAxisGlobalComparisonMonomialBitTensor_eq]

/-- The bounded bit formula is the whole actual original Fifth comparison action. -/
theorem generatedAxisGlobalOddFifthBitFrameTensor_actual (k : Fin 2)
    (T : GeneratedAxisGlobalRationalTensor) :
    localTensorRepresentation (generatedAxisGlobalOddFifthComparisonFiber k)
      (generatedAxisGlobalRationalTensorReal T) =
      generatedAxisGlobalRationalTensorReal (generatedAxisGlobalOddFifthBitFrameTensor k T) := by
  rw [generatedAxisGlobalOddFifthBitFrameTensor_eq]
  exact generatedAxisGlobalOddFifthCompactFrameTensor_unconditional k T

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
