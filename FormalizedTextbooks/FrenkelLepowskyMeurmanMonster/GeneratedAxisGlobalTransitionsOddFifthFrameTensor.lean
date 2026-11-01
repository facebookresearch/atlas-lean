/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthComparisonWords
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalTensorWord

/-! All original physical tensor coefficients after the two genuine Fifth comparison frames. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The same genuine original initial permutation word. -/
def generatedAxisGlobalOddFifthTensorPreLetters : List (Fin 7) := [5, 3, 5, 4, 5, 3]

/-- The complete original post-Xi permutation words in the rational tensor alphabet. -/
def generatedAxisGlobalOddFifthTensorPostLetters : Fin 2 → List (Fin 7) :=
  ![[4, 5, 4, 5, 3, 5, 3, 5, 3, 3, 5, 3, 5, 3, 5, 3, 3, 3, 5],
    [4, 4, 5, 4, 4, 4, 5, 3, 5, 3, 3, 5, 3, 3, 3, 3, 5, 3, 5, 4, 5]]

/-- Every exact physical rational output coefficient of the complete genuine frame. -/
def generatedAxisGlobalOddFifthFrameTensor (k : Fin 2) (T : GeneratedAxisGlobalRationalTensor) :
    GeneratedAxisGlobalRationalTensor :=
  generatedAxisGlobalRationalTensorQ (generatedAxisGlobalOddFifthComparisonQ k)
    (generatedAxisGlobalRationalTensorFrameWord (generatedAxisGlobalOddFifthTensorPostLetters k)
      (generatedAxisGlobalRationalTensorXiCached
        (generatedAxisGlobalRationalTensorSign (generatedAxisGlobalOddFifthComparisonSign k) 0
          (generatedAxisGlobalRationalTensorFrameWord generatedAxisGlobalOddFifthTensorPreLetters T))))

/-- The initial alphabet change is exactly the original source fiber word. -/
theorem generatedAxisGlobalOddFifthTensorPreLetters_word :
    (generatedAxisGlobalOddFifthTensorPreLetters.map (fun l =>
      generatedAxisGlobalOddSourceFiberLetter (generatedAxisGlobalRationalFrameLetter l))).prod =
    (generatedAxisGlobalOddFifthComparisonPreLetters.map
      generatedAxisGlobalOddSourceFiberLetter).prod := by rfl

/-- Each final alphabet change preserves the entire original source fiber product. -/
theorem generatedAxisGlobalOddFifthTensorPostLetters_word (k : Fin 2) :
    ((generatedAxisGlobalOddFifthTensorPostLetters k).map (fun l =>
      generatedAxisGlobalOddSourceFiberLetter (generatedAxisGlobalRationalFrameLetter l))).prod =
    ((generatedAxisGlobalOddFifthComparisonPostLetters k).map
      generatedAxisGlobalOddSourceFiberLetter).prod := by
  fin_cases k <;> rfl

/-- The complete rational expression is the genuine original physical tensor action. -/
theorem generatedAxisGlobalOddFifthFrameTensor_actual (k : Fin 2)
    (T : GeneratedAxisGlobalRationalTensor) :
    localTensorRepresentation (generatedAxisGlobalOddFifthComparisonFiber k)
      (generatedAxisGlobalRationalTensorReal T) =
        generatedAxisGlobalRationalTensorReal (generatedAxisGlobalOddFifthFrameTensor k T) := by
  rw [generatedAxisGlobalOddFifthComparisonFiber, map_mul, map_mul, map_mul, map_mul]
  simp only [LinearEquiv.mul_apply]
  rw [← generatedAxisGlobalOddFifthTensorPreLetters_word,
    ← generatedAxisGlobalOddFifthTensorPostLetters_word,
    generatedAxisGlobalRationalTensorFrameWord_actual,
    generatedAxisGlobalRationalTensorSign_actual,
    generatedAxisGlobalRationalTensorXiCached_actual,
    generatedAxisGlobalRationalTensorFrameWord_actual,
    generatedAxisGlobalRationalTensorQ_actual]
  rfl

/-- All genuine Griess tensor coefficients are exactly the complete physical rational formula. -/
theorem generatedAxisGlobalOddFifthFrameGriessTensor_actual (k : Fin 2) (x : GriessSpace)
    (T : GeneratedAxisGlobalRationalTensor)
    (hx : (griessConwayEncode x).2.2 = generatedAxisGlobalRationalTensorReal T) :
    (griessConwayEncode (rhoLocal (generatedAxisGlobalOddFifthComparisonLocal k) x)).2.2 =
      generatedAxisGlobalRationalTensorReal (generatedAxisGlobalOddFifthFrameTensor k T) := by
  change (griessConwayEncode (rhoLocal
    (localFiberIntoH (generatedAxisGlobalOddFifthComparisonFiber k)) x)).2.2 = _
  rw [generatedFourth_local_tensor, hx]
  exact generatedAxisGlobalOddFifthFrameTensor_actual k T

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
