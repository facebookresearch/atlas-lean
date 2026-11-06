/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthComparisonWords
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalTensorWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthTensor

/-! Whole genuine rational tensor binding for the four actual Fourth comparison frames. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The same original frame words in the seven-letter genuine rational tensor alphabet. -/
def generatedAxisGlobalOddFourthTensorLetters : Fin 4 → List (Fin 7) :=
  ![[2, 5, 3, 5, 3, 3, 5, 3, 3, 3, 5, 4, 4, 4, 1, 3, 3],
    [2, 3, 5, 4, 5, 4, 5, 3, 5, 3, 5, 3, 3, 5, 3, 3, 5, 0, 3, 3],
    [2, 3, 3, 3, 5, 4, 5, 4, 4, 5, 3, 3, 3, 5, 3, 5, 4, 5, 0],
    [2, 3, 3, 3, 5, 4, 5, 4, 4, 5, 3, 3, 3, 5, 3, 5, 4, 5, 1]]

/-- Every physical rational coefficient after the full genuine frame and central correction. -/
def generatedAxisGlobalOddFourthFrameTensor (k : Fin 4) (T : GeneratedAxisGlobalRationalTensor) :
    GeneratedAxisGlobalRationalTensor :=
  generatedAxisGlobalRationalTensorQ (generatedAxisGlobalOddFourthComparisonQ k)
    (generatedAxisGlobalRationalTensorFrameWord (generatedAxisGlobalOddFourthTensorLetters k) T)

/-- The alphabet change preserves the complete actual source fiber word. -/
theorem generatedAxisGlobalOddFourthTensorLetters_word (k : Fin 4) :
    ((generatedAxisGlobalOddFourthTensorLetters k).map (fun l =>
      generatedAxisGlobalOddSourceFiberLetter (generatedAxisGlobalRationalFrameLetter l))).prod =
    ((generatedAxisGlobalOddFourthComparisonLetters k).map
      generatedAxisGlobalOddSourceFiberLetter).prod := by
  fin_cases k <;> rfl

/-- This complete rational formula is the genuine original tensor action at all coordinates. -/
theorem generatedAxisGlobalOddFourthFrameTensor_actual (k : Fin 4)
    (T : GeneratedAxisGlobalRationalTensor) :
    localTensorRepresentation (generatedAxisGlobalOddFourthComparisonFiber k)
      (generatedAxisGlobalRationalTensorReal T) =
        generatedAxisGlobalRationalTensorReal (generatedAxisGlobalOddFourthFrameTensor k T) := by
  rw [generatedAxisGlobalOddFourthComparisonFiber, map_mul, LinearEquiv.mul_apply,
    ← generatedAxisGlobalOddFourthTensorLetters_word,
    generatedAxisGlobalRationalTensorFrameWord_actual,
    generatedAxisGlobalRationalTensorQ_actual]
  rfl

/-- Every genuine Griess output tensor coordinate uses the same complete physical formula. -/
theorem generatedAxisGlobalOddFourthFrameGriessTensor_actual (k : Fin 4) (x : GriessSpace)
    (T : GeneratedAxisGlobalRationalTensor)
    (hx : (griessConwayEncode x).2.2 = generatedAxisGlobalRationalTensorReal T) :
    (griessConwayEncode (rhoLocal (generatedAxisGlobalOddFourthComparisonLocal k) x)).2.2 =
      generatedAxisGlobalRationalTensorReal (generatedAxisGlobalOddFourthFrameTensor k T) := by
  change (griessConwayEncode (rhoLocal
    (localFiberIntoH (generatedAxisGlobalOddFourthComparisonFiber k)) x)).2.2 = _
  rw [generatedFourth_local_tensor, hx]
  exact generatedAxisGlobalOddFourthFrameTensor_actual k T

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
