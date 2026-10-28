/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthRepresentative
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQAffineFamilyCoordinates

/-! Original preferred-Q conjugation caches for the three nonzero pair coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The actual conjugation formula of each original local generator. -/
def generatedSixthQGenerator (k : Fin 3) (q : Q) : Q :=
  if k = 0 then monsterSourcePermutationImage 0 q else
    if k = 1 then monsterSourcePermutationImage 1 q else
      xiSpinGImage (xiSpinGammaImage q)

/-- The original eight generators in application order. -/
def generatedSixthQWord : List (Fin 3) := [0, 2, 0, 1, 0, 2, 1, 2]

/-- The original coordinate formula, with every central phase retained. -/
def generatedSixthQImage (q : Q) : Q :=
  generatedSixthQWord.foldl (fun x k => generatedSixthQGenerator k x) q

/-- Every successive actual Q coordinate and central coefficient for the three input lifts. -/
def generatedSixthQCache : Fin 3 → Fin 9 → Q :=
  ![![generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
        (golayLabelCoefficients 6) 0,
      generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
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
        (golayLabelCoefficients 1037) 0,
      generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
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
        (golayLabelCoefficients 1035) 0,
      generatedAxisFourthQFromSpin (golayLabelCoefficients 0)
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

set_option maxHeartbeats 4000000 in
-- Three preferred lifts each require all eight source formula and central-phase checks.
/-- Every cached successor is the actual original Q image, including its central sign. -/
theorem generatedSixth_q_cache_certificate : ∀ j : Fin 3,
    generatedSixthQCache j 1 =
      generatedSixthQGenerator 0 (generatedSixthQCache j 0) ∧
    generatedSixthQCache j 2 =
      generatedSixthQGenerator 2 (generatedSixthQCache j 1) ∧
    generatedSixthQCache j 3 =
      generatedSixthQGenerator 0 (generatedSixthQCache j 2) ∧
    generatedSixthQCache j 4 =
      generatedSixthQGenerator 1 (generatedSixthQCache j 3) ∧
    generatedSixthQCache j 5 =
      generatedSixthQGenerator 0 (generatedSixthQCache j 4) ∧
    generatedSixthQCache j 6 =
      generatedSixthQGenerator 2 (generatedSixthQCache j 5) ∧
    generatedSixthQCache j 7 =
      generatedSixthQGenerator 1 (generatedSixthQCache j 6) ∧
    generatedSixthQCache j 8 =
      generatedSixthQGenerator 2 (generatedSixthQCache j 7) := by
  intro j
  fin_cases j <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals apply NormalizedCocycleExtension.Extension.ext
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
