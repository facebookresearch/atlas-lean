/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingPartCheck00Matrix00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingPartCheck00Matrix01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingPartCheck00Matrix02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingPartCheck00Matrix03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingPartCheck00Odd00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingPartCheck00Odd01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingPartCheck00Odd02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingPartCheck00Odd03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingPartCheck00Odd04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingPartCheck00Odd05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingPartCheck00Odd06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingPartCheck00Odd07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingPartCheck00Even00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingPartCheck00Even01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingPartCheck00Even02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingPartCheck00Even03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingPartCheck00Even04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingPartCheck00Even05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMiddlePairingPartCheck00Even06

/-! The entire original pairing is assembled from every proved finite packet. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- Every original coefficient contributes to the exact complete pairing 128. -/
theorem generatedAxisGlobalOddFifthMiddlePairingBoundedCheck00 :
    generatedAxisGlobalOddFifthMiddlePairingBitQ 0 = 128 := by
  rw [generatedAxisGlobalOddFifthMiddlePairingParts_complete]
  have hM : (∑ b : Fin 4, generatedAxisGlobalOddFifthMiddleMatrixPairingPart 0 b) = 8 := by
    rw [show (∑ b : Fin 4, generatedAxisGlobalOddFifthMiddleMatrixPairingPart 0 b) =
      generatedAxisGlobalOddFifthMiddleMatrixPairingPart 0 0 +
        generatedAxisGlobalOddFifthMiddleMatrixPairingPart 0 1 +
          generatedAxisGlobalOddFifthMiddleMatrixPairingPart 0 2 +
            generatedAxisGlobalOddFifthMiddleMatrixPairingPart 0 3 by
      simp [Fin.sum_univ_succ]; ring]
    rw [generatedAxisGlobalOddFifthMiddlePairingPartCheck00Matrix00,
      generatedAxisGlobalOddFifthMiddlePairingPartCheck00Matrix01,
      generatedAxisGlobalOddFifthMiddlePairingPartCheck00Matrix02,
      generatedAxisGlobalOddFifthMiddlePairingPartCheck00Matrix03]
    norm_num
  have hOdd (b : Fin 8) : generatedAxisGlobalOddFifthMiddleOddPairingPart 0 b = 8 := by
    fin_cases b
    · exact generatedAxisGlobalOddFifthMiddlePairingPartCheck00Odd00
    · exact generatedAxisGlobalOddFifthMiddlePairingPartCheck00Odd01
    · exact generatedAxisGlobalOddFifthMiddlePairingPartCheck00Odd02
    · exact generatedAxisGlobalOddFifthMiddlePairingPartCheck00Odd03
    · exact generatedAxisGlobalOddFifthMiddlePairingPartCheck00Odd04
    · exact generatedAxisGlobalOddFifthMiddlePairingPartCheck00Odd05
    · exact generatedAxisGlobalOddFifthMiddlePairingPartCheck00Odd06
    · exact generatedAxisGlobalOddFifthMiddlePairingPartCheck00Odd07
  have hEven (b : Fin 7) : generatedAxisGlobalOddFifthMiddleEvenPairingPart 0 b = 8 := by
    fin_cases b
    · exact generatedAxisGlobalOddFifthMiddlePairingPartCheck00Even00
    · exact generatedAxisGlobalOddFifthMiddlePairingPartCheck00Even01
    · exact generatedAxisGlobalOddFifthMiddlePairingPartCheck00Even02
    · exact generatedAxisGlobalOddFifthMiddlePairingPartCheck00Even03
    · exact generatedAxisGlobalOddFifthMiddlePairingPartCheck00Even04
    · exact generatedAxisGlobalOddFifthMiddlePairingPartCheck00Even05
    · exact generatedAxisGlobalOddFifthMiddlePairingPartCheck00Even06
  rw [hM]
  simp only [hOdd, hEven, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
