/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsIntegerOddFourthFrameTensor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthMiddlePairingParts

/-! Complete original odd pairing packets are integer numerators with denominator one thousand twenty four. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- The integer model equals every coefficient of the whole original source frame. -/
theorem generatedAxisGlobalIntegerOddFourthFrameTensor_original (k : Fin 4) :
    generatedAxisGlobalOddFourthSparseBitFrameTensor k (generatedAxisGlobalOddFourthOutgoingTensor k) =
      generatedAxisGlobalIntegerTensorRat (generatedAxisGlobalIntegerOddFourthFrameTensor k) 512 := by
  rw [← generatedAxisGlobalOddFourthFastFrameTensor_eq,
    ← generatedAxisGlobalOddFourthPhysicalOutgoingTensor_eq,
    generatedAxisGlobalIntegerOddFourthFrameTensor_rat]

/-- Every canonical coefficient and both physical source rows of each original eight-term packet. -/
def generatedAxisGlobalIntegerOddFourthOddPairingPart (k : Fin 4) (b : Fin 7) : ℤ :=
  ∑ j : Fin 8,
    let p := finProdFinEquiv (b,j)
    let d := (generatedFourthOddRootOutputData p).1
    let i := (generatedFourthOddRootOutputData p).2
    let c := generatedAxisGlobalIntSign (generatedFourthOddCoefficientPhaseData p)
    let z : ℤ := if (golayEncodedMask d.val).testBit i.val then -1 else 1
    c*z*(generatedAxisGlobalIntegerOddFourthFrameTensor k ⟨d.val, by omega⟩ i -
      generatedAxisGlobalIntegerOddFourthFrameTensor k ⟨d.val+2048, by omega⟩ i)

/-- The complete original rational odd packet is restored by its exact integer denominator. -/
theorem generatedAxisGlobalIntegerOddFourthOddPairingPart_rat (k : Fin 4) (b : Fin 7) :
    generatedAxisGlobalOddFourthMiddleOddPairingPart k b =
      (generatedAxisGlobalIntegerOddFourthOddPairingPart k b : ℚ) / 1024 := by
  unfold generatedAxisGlobalOddFourthMiddleOddPairingPart
    generatedAxisGlobalIntegerOddFourthOddPairingPart
  rw [Int.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [generatedAxisGlobalOddFourthMiddleCoefficientBitQ,
    generatedAxisGlobalCanonicalFourthMiddleShortCoefficient,
    generatedAxisGlobalOddFourthMiddleShortSparseBitQ]
  rw [generatedAxisGlobalIntegerOddFourthFrameTensor_original]
  dsimp only [generatedAxisGlobalIntegerTensorRat]
  by_cases hc : (generatedAxisGlobalIntSign
      (generatedFourthOddCoefficientPhaseData (finProdFinEquiv (b,j))) : ℚ) = 0
  · have hz : generatedAxisGlobalIntSign
        (generatedFourthOddCoefficientPhaseData (finProdFinEquiv (b,j))) = 0 := by exact_mod_cast hc
    simp only [hz, ↓reduceIte, zero_mul, Int.cast_zero, zero_div]
  · simp only [hc, ↓reduceIte]
    cases hb : (golayEncodedMask (generatedFourthOddRootOutputData (finProdFinEquiv (b,j))).1.val).testBit
      (generatedFourthOddRootOutputData (finProdFinEquiv (b,j))).2.val
    all_goals
      simp only [Bool.false_eq_true, ↓reduceIte, Int.cast_mul, Int.cast_sub, Int.cast_neg, Int.cast_one]
      ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
