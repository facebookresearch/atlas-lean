/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingPartCheck01Matrix00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingPartCheck01Matrix01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingPartCheck01Matrix02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingPartCheck01Matrix03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingPartCheck01Odd00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingPartCheck01Odd01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingPartCheck01Odd02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingPartCheck01Odd03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingPartCheck01Odd04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingPartCheck01Odd05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingPartCheck01Odd06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingPartCheck01Odd07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingPartCheck01Even00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingPartCheck01Even01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingPartCheck01Even02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingPartCheck01Even03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingPartCheck01Even04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingPartCheck01Even05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingPartCheck01Even06

/-! The entire original pairing is assembled from every proved finite packet. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- Every original coefficient contributes to the exact complete pairing 128. -/
theorem generatedAxisGlobalOddFifthMiddlePairingBoundedCheck01 :
    generatedAxisGlobalOddFifthMiddlePairingBitQ 1 = 128 := by
  rw [generatedAxisGlobalOddFifthMiddlePairingParts_complete]
  have hM : (∑ b : Fin 4, generatedAxisGlobalOddFifthMiddleMatrixPairingPart 1 b) = 8 := by
    rw [show (∑ b : Fin 4, generatedAxisGlobalOddFifthMiddleMatrixPairingPart 1 b) =
      generatedAxisGlobalOddFifthMiddleMatrixPairingPart 1 0 +
        generatedAxisGlobalOddFifthMiddleMatrixPairingPart 1 1 +
          generatedAxisGlobalOddFifthMiddleMatrixPairingPart 1 2 +
            generatedAxisGlobalOddFifthMiddleMatrixPairingPart 1 3 by
      simp [Fin.sum_univ_succ]; ring]
    rw [generatedAxisGlobalOddFifthMiddlePairingPartCheck01Matrix00,
      generatedAxisGlobalOddFifthMiddlePairingPartCheck01Matrix01,
      generatedAxisGlobalOddFifthMiddlePairingPartCheck01Matrix02,
      generatedAxisGlobalOddFifthMiddlePairingPartCheck01Matrix03]
    norm_num
  have hOdd (b : Fin 8) : generatedAxisGlobalOddFifthMiddleOddPairingPart 1 b = 8 := by
    fin_cases b
    · exact generatedAxisGlobalOddFifthMiddlePairingPartCheck01Odd00
    · exact generatedAxisGlobalOddFifthMiddlePairingPartCheck01Odd01
    · exact generatedAxisGlobalOddFifthMiddlePairingPartCheck01Odd02
    · exact generatedAxisGlobalOddFifthMiddlePairingPartCheck01Odd03
    · exact generatedAxisGlobalOddFifthMiddlePairingPartCheck01Odd04
    · exact generatedAxisGlobalOddFifthMiddlePairingPartCheck01Odd05
    · exact generatedAxisGlobalOddFifthMiddlePairingPartCheck01Odd06
    · exact generatedAxisGlobalOddFifthMiddlePairingPartCheck01Odd07
  have hEven (b : Fin 7) : generatedAxisGlobalOddFifthMiddleEvenPairingPart 1 b = 8 := by
    fin_cases b
    · exact generatedAxisGlobalOddFifthMiddlePairingPartCheck01Even00
    · exact generatedAxisGlobalOddFifthMiddlePairingPartCheck01Even01
    · exact generatedAxisGlobalOddFifthMiddlePairingPartCheck01Even02
    · exact generatedAxisGlobalOddFifthMiddlePairingPartCheck01Even03
    · exact generatedAxisGlobalOddFifthMiddlePairingPartCheck01Even04
    · exact generatedAxisGlobalOddFifthMiddlePairingPartCheck01Even05
    · exact generatedAxisGlobalOddFifthMiddlePairingPartCheck01Even06
  rw [hM]
  simp only [hOdd, hEven, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
