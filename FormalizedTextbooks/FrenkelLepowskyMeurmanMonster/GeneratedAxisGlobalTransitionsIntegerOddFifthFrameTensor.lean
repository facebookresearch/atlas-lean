/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsIntegerOddFifthOutgoingTensor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsComparisonSparseBitFrames

/-! The entire original signed root-three frame restores its exact denominator five hundred twelve. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Every pre-action, actual sign, original Gaussian, post-action, and complete Q phase. -/
def generatedAxisGlobalIntegerOddFifthFrameTensor (k : Fin 2) : GeneratedAxisGlobalIntegerTensor :=
  generatedAxisGlobalIntegerTensorQ (generatedAxisGlobalOddFifthComparisonQ k)
    (generatedAxisGlobalIntegerTensorMonomial (Fin.natAdd 6 k)
      (generatedAxisGlobalIntegerTensorXi
        (generatedAxisGlobalIntegerTensorSign (generatedAxisGlobalOddFifthComparisonSign k) 0
          (generatedAxisGlobalIntegerTensorMonomial 5 (generatedAxisGlobalIntegerOddFifthOutgoingTensor k)))))

/-- Every coordinate equals the complete original rational comparison frame. -/
theorem generatedAxisGlobalIntegerOddFifthFrameTensor_original (k : Fin 2) :
    generatedAxisGlobalOddFifthSparseBitFrameTensor k (generatedAxisGlobalOddFifthOutgoingTensor k) =
      generatedAxisGlobalIntegerTensorRat (generatedAxisGlobalIntegerOddFifthFrameTensor k) 512 := by
  unfold generatedAxisGlobalOddFifthSparseBitFrameTensor
  simp_rw [← generatedAxisGlobalComparisonMonomialFastTensor_eq]
  rw [← generatedAxisGlobalIntegerOddFifthOutgoingTensor_rat,
    generatedAxisGlobalIntegerTensorMonomial_rat 5 _ 16 (by norm_num),
    generatedAxisGlobalIntegerTensorSign_rat,
    generatedAxisGlobalIntegerTensorXi_rat _ (2*16) (by norm_num),
    generatedAxisGlobalIntegerTensorMonomial_rat (Fin.natAdd 6 k) _ (16*(2*16)) (by norm_num),
    generatedAxisGlobalIntegerTensorQ_rat]
  change generatedAxisGlobalIntegerTensorRat (generatedAxisGlobalIntegerOddFifthFrameTensor k)
      (16*(2*16)) = generatedAxisGlobalIntegerTensorRat (generatedAxisGlobalIntegerOddFifthFrameTensor k) 512
  congr 1
  norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
