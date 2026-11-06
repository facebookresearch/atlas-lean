/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsIntegerOddFourthOutgoingTensor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthFastFrameTensor

/-! The entire original Fourth frame has denominator five hundred twelve in physical tensor coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Every original source, both Xi orientations, every sign input, and full Q phase of the whole frame. -/
def generatedAxisGlobalIntegerOddFourthFrameTensor (k : Fin 4) : GeneratedAxisGlobalIntegerTensor :=
  let N := generatedAxisGlobalIntegerOddFourthOutgoingTensor k
  let P := if k.val < 2 then generatedAxisGlobalIntegerTensorMonomial 4 N else N
  let X := if k = 0 ∨ k = 3 then generatedAxisGlobalIntegerTensorXiInverse P
    else generatedAxisGlobalIntegerTensorXi P
  generatedAxisGlobalIntegerTensorQ (generatedAxisGlobalOddFourthComparisonQ k)
    (generatedAxisGlobalIntegerTensorSign 16 0
      (generatedAxisGlobalIntegerTensorMonomial (Fin.castAdd 4 k) X))

/-- Denominator five hundred twelve restores every coefficient of the original full rational frame. -/
theorem generatedAxisGlobalIntegerOddFourthFrameTensor_rat (k : Fin 4) :
    generatedAxisGlobalOddFourthFastFrameTensor k (generatedAxisGlobalOddFourthPhysicalOutgoingTensor k) =
      generatedAxisGlobalIntegerTensorRat (generatedAxisGlobalIntegerOddFourthFrameTensor k) 512 := by
  let N := generatedAxisGlobalIntegerOddFourthOutgoingTensor k
  let P := if k.val < 2 then generatedAxisGlobalIntegerTensorMonomial 4 N else N
  let X := if k = 0 ∨ k = 3 then generatedAxisGlobalIntegerTensorXiInverse P
    else generatedAxisGlobalIntegerTensorXi P
  have hp :
      (if k.val < 2 then generatedAxisGlobalComparisonMonomialFastTensor 4
          (generatedAxisGlobalOddFourthPhysicalOutgoingTensor k)
        else generatedAxisGlobalOddFourthPhysicalOutgoingTensor k) =
      generatedAxisGlobalIntegerTensorRat P 16 := by
    rw [← generatedAxisGlobalIntegerOddFourthOutgoingTensor_rat]
    dsimp only [P, N]
    by_cases hk : k.val < 2
    · simp only [hk, ↓reduceIte]
      exact generatedAxisGlobalIntegerTensorMonomial_rat 4 _ 16 (by norm_num)
    · simp only [hk, ↓reduceIte]
  have hx : generatedAxisGlobalOddFourthCompactXiTensor k
      (if k.val < 2 then generatedAxisGlobalComparisonMonomialFastTensor 4
          (generatedAxisGlobalOddFourthPhysicalOutgoingTensor k)
        else generatedAxisGlobalOddFourthPhysicalOutgoingTensor k) =
      generatedAxisGlobalIntegerTensorRat X (16*16) := by
    rw [hp]
    dsimp only [X, generatedAxisGlobalOddFourthCompactXiTensor]
    by_cases hk : k = 0 ∨ k = 3
    · simp only [hk, ↓reduceIte]
      exact generatedAxisGlobalIntegerTensorXiInverse_rat P 16 (by norm_num)
    · simp only [hk, ↓reduceIte]
      exact generatedAxisGlobalIntegerTensorXi_rat P 16 (by norm_num)
  unfold generatedAxisGlobalOddFourthFastFrameTensor
  rw [hx, generatedAxisGlobalIntegerTensorMonomial_rat (Fin.castAdd 4 k) X (16*16) (by norm_num),
    generatedAxisGlobalIntegerTensorSign_rat, generatedAxisGlobalIntegerTensorQ_rat]
  change generatedAxisGlobalIntegerTensorRat (generatedAxisGlobalIntegerOddFourthFrameTensor k)
      (2*(16*16)) = generatedAxisGlobalIntegerTensorRat (generatedAxisGlobalIntegerOddFourthFrameTensor k) 512
  congr 1
  norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
