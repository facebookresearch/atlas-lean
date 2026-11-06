/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhRepresentative
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQAffineFamilyCoordinates

/-! Genuine preferred-Q transports through all seven original local generators. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The actual original conjugation formula for each of the three local generators. -/
def generatedSeventhQGenerator (k : Fin 3) (q : Q) : Q :=
  if k = 0 then monsterSourcePermutationImage 0 q else
    if k = 1 then monsterSourcePermutationImage 1 q else
      xiSpinGImage (xiSpinGammaImage q)

/-- The original seven local generators in application order. -/
def generatedSeventhQWord : List (Fin 3) := [2, 0, 1, 0, 2, 1, 2]

/-- The full actual Q coordinate formula, retaining each central coefficient. -/
def generatedSeventhQImage (q : Q) : Q :=
  generatedSeventhQWord.foldl (fun x k => generatedSeventhQGenerator k x) q

/-- Each original preferred pair lift and its seven actual successors. -/
def generatedSeventhQCache : Fin 3 → Fin 8 → Q :=
  ![![generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
        (golayLabelCoefficients 1360) 0,
      generatedAxisFourthQFromSpin (golayLabelCoefficients 2048)
        (golayLabelCoefficients 1360) 1,
      generatedAxisFourthQFromSpin (golayLabelCoefficients 2048)
        (golayLabelCoefficients 1898) 1,
      generatedAxisFourthQFromSpin (golayLabelCoefficients 2048)
        (golayLabelCoefficients 1127) 1,
      generatedAxisFourthQFromSpin (golayLabelCoefficients 2048)
        (golayLabelCoefficients 1504) 1,
      generatedAxisFourthQFromSpin (golayLabelCoefficients 2048)
        (golayLabelCoefficients 480) 0,
      generatedAxisFourthQFromSpin (golayLabelCoefficients 2048)
        (golayLabelCoefficients 480) 0,
      generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
        (golayLabelCoefficients 1504) 0],
    ![generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
        (golayLabelCoefficients 2032) 0,
      generatedAxisFourthQFromSpin (golayLabelCoefficients 2048)
        (golayLabelCoefficients 2032) 1,
      generatedAxisFourthQFromSpin (golayLabelCoefficients 2048)
        (golayLabelCoefficients 1942) 1,
      generatedAxisFourthQFromSpin (golayLabelCoefficients 2048)
        (golayLabelCoefficients 1179) 1,
      generatedAxisFourthQFromSpin (golayLabelCoefficients 2048)
        (golayLabelCoefficients 1648) 1,
      generatedAxisFourthQFromSpin (golayLabelCoefficients 2048)
        (golayLabelCoefficients 624) 0,
      generatedAxisFourthQFromSpin (golayLabelCoefficients 2048)
        (golayLabelCoefficients 624) 0,
      generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
        (golayLabelCoefficients 1648) 0],
    ![generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
        (golayLabelCoefficients 672) 0,
      generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
        (golayLabelCoefficients 672) 0,
      generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
        (golayLabelCoefficients 252) 0,
      generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
        (golayLabelCoefficients 252) 0,
      generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
        (golayLabelCoefficients 912) 0,
      generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
        (golayLabelCoefficients 912) 0,
      generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
        (golayLabelCoefficients 912) 0,
      generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
        (golayLabelCoefficients 912) 0]]

/-- All cached successors agree with the actual conjugation formula and central phase. -/
theorem generatedSeventh_q_cache_certificate : ∀ j : Fin 3,
    generatedSeventhQCache j 1 =
      generatedSeventhQGenerator 2 (generatedSeventhQCache j 0) ∧
    generatedSeventhQCache j 2 =
      generatedSeventhQGenerator 0 (generatedSeventhQCache j 1) ∧
    generatedSeventhQCache j 3 =
      generatedSeventhQGenerator 1 (generatedSeventhQCache j 2) ∧
    generatedSeventhQCache j 4 =
      generatedSeventhQGenerator 0 (generatedSeventhQCache j 3) ∧
    generatedSeventhQCache j 5 =
      generatedSeventhQGenerator 2 (generatedSeventhQCache j 4) ∧
    generatedSeventhQCache j 6 =
      generatedSeventhQGenerator 1 (generatedSeventhQCache j 5) ∧
    generatedSeventhQCache j 7 =
      generatedSeventhQGenerator 2 (generatedSeventhQCache j 6) := by
  intro j
  fin_cases j <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals apply NormalizedCocycleExtension.Extension.ext
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
