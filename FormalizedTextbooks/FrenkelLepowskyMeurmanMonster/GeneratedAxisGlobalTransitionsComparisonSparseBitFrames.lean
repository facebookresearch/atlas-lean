/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsComparisonMonomialBitTensorSparse
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsComparisonBitFrames

/-! Complete original signed tensor frames with proven zero-input phase guards. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- Whole original Fourth frame, with its true incoming permutation phases guarded only on zero coefficients. -/
def generatedAxisGlobalOddFourthSparseBitFrameTensor (k : Fin 4)
    (T : GeneratedAxisGlobalRationalTensor) : GeneratedAxisGlobalRationalTensor :=
  generatedAxisGlobalRationalTensorQ (generatedAxisGlobalOddFourthComparisonQ k)
    (generatedAxisGlobalRationalTensorSign 16 0
      (generatedAxisGlobalComparisonMonomialBitTensorSparse (Fin.castAdd 4 k)
        (generatedAxisGlobalOddFourthCompactXiTensor k
          (if k.val < 2 then generatedAxisGlobalComparisonMonomialBitTensorSparse 4 T else T))))

/-- The complete guarded original Fourth frame is the entire previously certified bit frame. -/
theorem generatedAxisGlobalOddFourthSparseBitFrameTensor_eq (k : Fin 4)
    (T : GeneratedAxisGlobalRationalTensor) :
    generatedAxisGlobalOddFourthSparseBitFrameTensor k T = generatedAxisGlobalOddFourthBitFrameTensor k T := by
  simp only [generatedAxisGlobalOddFourthSparseBitFrameTensor, generatedAxisGlobalOddFourthBitFrameTensor,
    generatedAxisGlobalComparisonMonomialBitTensorSparse_eq]

/-- Whole original Fifth frame, retaining all true source signs and zero-input phase guards. -/
def generatedAxisGlobalOddFifthSparseBitFrameTensor (k : Fin 2)
    (T : GeneratedAxisGlobalRationalTensor) : GeneratedAxisGlobalRationalTensor :=
  generatedAxisGlobalRationalTensorQ (generatedAxisGlobalOddFifthComparisonQ k)
    (generatedAxisGlobalComparisonMonomialBitTensorSparse (Fin.natAdd 6 k)
      (generatedAxisGlobalRationalTensorXiCached
        (generatedAxisGlobalRationalTensorSign (generatedAxisGlobalOddFifthComparisonSign k) 0
          (generatedAxisGlobalComparisonMonomialBitTensorSparse 5 T))))

/-- The complete guarded original Fifth frame is the entire previously certified bit frame. -/
theorem generatedAxisGlobalOddFifthSparseBitFrameTensor_eq (k : Fin 2)
    (T : GeneratedAxisGlobalRationalTensor) :
    generatedAxisGlobalOddFifthSparseBitFrameTensor k T = generatedAxisGlobalOddFifthBitFrameTensor k T := by
  simp only [generatedAxisGlobalOddFifthSparseBitFrameTensor, generatedAxisGlobalOddFifthBitFrameTensor,
    generatedAxisGlobalComparisonMonomialBitTensorSparse_eq]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
