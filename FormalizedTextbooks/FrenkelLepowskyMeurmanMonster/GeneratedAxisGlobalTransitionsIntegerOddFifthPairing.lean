/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsIntegerOddFifthFrameTensor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingParts

/-! Complete original odd pairing packets are integer numerators with denominator one thousand twenty four. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Every canonical coefficient and both physical source rows of each original eight-term packet. -/
def generatedAxisGlobalIntegerOddFifthOddPairingPart (k : Fin 2) (b : Fin 8) : ℤ :=
  ∑ j : Fin 8,
    let p := finProdFinEquiv (b,j)
    let d := (generatedFifthOddRootOutputData p).1
    let i := (generatedFifthOddRootOutputData p).2
    let c := generatedAxisGlobalIntSign (generatedFifthOddCoefficientPhaseData p)
    let z : ℤ := if (golayEncodedMask d.val).testBit i.val then -1 else 1
    c*z*(generatedAxisGlobalIntegerOddFifthFrameTensor k ⟨d.val, by omega⟩ i -
      generatedAxisGlobalIntegerOddFifthFrameTensor k ⟨d.val+2048, by omega⟩ i)

/-- The complete original rational odd packet is restored by its exact integer denominator. -/
theorem generatedAxisGlobalIntegerOddFifthOddPairingPart_rat (k : Fin 2) (b : Fin 8) :
    generatedAxisGlobalOddFifthMiddleOddPairingPart k b =
      (generatedAxisGlobalIntegerOddFifthOddPairingPart k b : ℚ) / 1024 := by
  unfold generatedAxisGlobalOddFifthMiddleOddPairingPart
    generatedAxisGlobalIntegerOddFifthOddPairingPart
  rw [Int.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [generatedAxisGlobalCanonicalFifthMiddleShortCoefficient,
    generatedAxisGlobalOddFifthMiddleShortBitQ]
  rw [generatedAxisGlobalIntegerOddFifthFrameTensor_original]
  dsimp only [generatedAxisGlobalIntegerTensorRat]
  by_cases hc : (generatedAxisGlobalIntSign
      (generatedFifthOddCoefficientPhaseData (finProdFinEquiv (b,j))) : ℚ) = 0
  · have hz : generatedAxisGlobalIntSign
        (generatedFifthOddCoefficientPhaseData (finProdFinEquiv (b,j))) = 0 := by exact_mod_cast hc
    simp only [hz, ↓reduceIte, zero_mul, Int.cast_zero, zero_div]
  · simp only [hc, ↓reduceIte]
    cases hb : (golayEncodedMask (generatedFifthOddRootOutputData (finProdFinEquiv (b,j))).1.val).testBit
      (generatedFifthOddRootOutputData (finProdFinEquiv (b,j))).2.val
    all_goals
      simp only [Bool.false_eq_true, ↓reduceIte, Int.cast_mul, Int.cast_sub, Int.cast_neg, Int.cast_one]
      ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
