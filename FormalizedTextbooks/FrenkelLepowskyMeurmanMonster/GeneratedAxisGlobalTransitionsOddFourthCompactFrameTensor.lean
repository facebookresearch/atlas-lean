/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsComparisonMonomialWordSources
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthFrameTensor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalTensorXiInverseCached

/-! Whole original Fourth frame tensors with bounded signed permutation models. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The actual forward/inverse Xi letter between the permutation stretches. -/
def generatedAxisGlobalOddFourthCompactXiLetter : Fin 4 → Fin 7 := ![1, 0, 0, 1]

/-- Only the first two original frame words have the initial two-letter permutation stretch. -/
def generatedAxisGlobalOddFourthCompactPreLetters (k : Fin 4) : List (Fin 10) :=
  if k.val < 2 then generatedAxisGlobalComparisonMonomialOriginalLetters 4 else []

/-- Original full comparison words split into genuine original factors in precisely their order. -/
theorem generatedAxisGlobalOddFourthCompactLetters (k : Fin 4) :
    generatedAxisGlobalOddFourthComparisonLetters k =
      [2] ++ generatedAxisGlobalComparisonMonomialOriginalLetters (Fin.castAdd 4 k) ++
        [generatedAxisGlobalRationalFrameLetter (generatedAxisGlobalOddFourthCompactXiLetter k)] ++
          generatedAxisGlobalOddFourthCompactPreLetters k := by
  fin_cases k <;> rfl

/-- Exact factorization in the original local fiber, retaining the full central correction. -/
theorem generatedAxisGlobalOddFourthCompactFiber (k : Fin 4) :
    generatedAxisGlobalOddFourthComparisonFiber k =
    localFiberIncl (generatedAxisGlobalOddFourthComparisonQ k) *
      (generatedFifthSignFiber 16 0 *
        (((generatedAxisGlobalComparisonMonomialOriginalLetters (Fin.castAdd 4 k)).map
          generatedAxisGlobalOddSourceFiberLetter).prod *
          (generatedAxisGlobalOddSourceFiberLetter
            (generatedAxisGlobalRationalFrameLetter (generatedAxisGlobalOddFourthCompactXiLetter k)) *
            ((generatedAxisGlobalOddFourthCompactPreLetters k).map
              generatedAxisGlobalOddSourceFiberLetter).prod))) := by
  rw [generatedAxisGlobalOddFourthComparisonFiber, generatedAxisGlobalOddFourthCompactLetters]
  simp only [List.map_append, List.prod_append, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  rfl

/-- Both genuine Xi signs use one complete original64-input Gaussian formula. -/
def generatedAxisGlobalOddFourthCompactXiTensor (k : Fin 4)
    (T : GeneratedAxisGlobalRationalTensor) : GeneratedAxisGlobalRationalTensor :=
  if k = 0 ∨ k = 3 then generatedAxisGlobalRationalTensorXiInverseCached T
  else generatedAxisGlobalRationalTensorXiCached T

/-- The compact forward/inverse Gaussian is exactly the genuine original frame letter. -/
theorem generatedAxisGlobalOddFourthCompactXiTensor_actual (k : Fin 4)
    (T : GeneratedAxisGlobalRationalTensor) :
    localTensorRepresentation (generatedAxisGlobalOddSourceFiberLetter
      (generatedAxisGlobalRationalFrameLetter (generatedAxisGlobalOddFourthCompactXiLetter k)))
      (generatedAxisGlobalRationalTensorReal T) =
        generatedAxisGlobalRationalTensorReal (generatedAxisGlobalOddFourthCompactXiTensor k T) := by
  fin_cases k
  · exact generatedAxisGlobalRationalTensorXiInverseCached_actual T
  · exact generatedAxisGlobalRationalTensorXiCached_actual T
  · exact generatedAxisGlobalRationalTensorXiCached_actual T
  · exact generatedAxisGlobalRationalTensorXiInverseCached_actual T

/-- The complete physical tensor formula uses the actual original phases of all permutation stretches. -/
def generatedAxisGlobalOddFourthCompactFrameTensor (k : Fin 4)
    (T : GeneratedAxisGlobalRationalTensor) : GeneratedAxisGlobalRationalTensor :=
  generatedAxisGlobalRationalTensorQ (generatedAxisGlobalOddFourthComparisonQ k)
    (generatedAxisGlobalRationalTensorSign 16 0
      (generatedAxisGlobalComparisonMonomialTensor (Fin.castAdd 4 k)
        (generatedAxisGlobalOddFourthCompactXiTensor k
          (if k.val < 2 then generatedAxisGlobalComparisonMonomialTensor 4 T else T))))

/-- Checked bounded spin plans give the entire actual original frame tensor at every physical coordinate. -/
theorem generatedAxisGlobalOddFourthCompactFrameTensor_actual (k : Fin 4)
    (hc : ∀ j : Fin 5, representativeSpinPlanValid generatedFourthMonomialLetterModel
      representativeSpinIdentityModel (generatedAxisGlobalComparisonMonomialPlan (Fin.castAdd 3 j)))
    (T : GeneratedAxisGlobalRationalTensor) :
    localTensorRepresentation (generatedAxisGlobalOddFourthComparisonFiber k)
      (generatedAxisGlobalRationalTensorReal T) =
      generatedAxisGlobalRationalTensorReal (generatedAxisGlobalOddFourthCompactFrameTensor k T) := by
  have hindex : Fin.castAdd 3 (Fin.castAdd 1 k) = Fin.castAdd 4 k := rfl
  have hpost := hc (Fin.castAdd 1 k)
  rw [hindex] at hpost
  have hpre : localTensorRepresentation
      (((generatedAxisGlobalOddFourthCompactPreLetters k).map
        generatedAxisGlobalOddSourceFiberLetter).prod) (generatedAxisGlobalRationalTensorReal T) =
      generatedAxisGlobalRationalTensorReal
        (if k.val < 2 then generatedAxisGlobalComparisonMonomialTensor 4 T else T) := by
    by_cases h : k.val < 2
    · rw [generatedAxisGlobalOddFourthCompactPreLetters, ite_eq_left h, ite_eq_left h]
      exact generatedAxisGlobalComparisonMonomialWordTensor_actual 4 (hc 4) T
    · simp [generatedAxisGlobalOddFourthCompactPreLetters, h]
  rw [generatedAxisGlobalOddFourthCompactFiber]
  simp only [map_mul, LinearEquiv.mul_apply]
  rw [hpre, generatedAxisGlobalOddFourthCompactXiTensor_actual,
    generatedAxisGlobalComparisonMonomialWordTensor_actual (Fin.castAdd 4 k) hpost,
    generatedAxisGlobalRationalTensorSign_actual,
    generatedAxisGlobalRationalTensorQ_actual]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
