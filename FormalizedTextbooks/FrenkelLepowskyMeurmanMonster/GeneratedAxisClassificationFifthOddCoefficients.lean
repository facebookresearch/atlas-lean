/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthOddRootImages
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthInputCoefficients
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMatrixCoordinates

/-! The 64 original tensor-source coefficients, with actual source and preferred-Q phases. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The exact combined coefficient signs in the 64 verified odd rows. -/
def generatedFifthOddCoefficientPhaseData : Fin 64 → ZMod 2 :=
  ![0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1,
    1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1,
    0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0]

/-- The finite coefficient signs combine the genuine inverse-Q and original input phases. -/
theorem generatedFifth_odd_coefficient_phase_certificate : ∀ j : Fin 64,
    generatedFifthOddRootPhaseData j + generatedFifthOddRootInputPhase j =
      generatedFifthOddCoefficientPhaseData j := by
  decide +kernel

/-- Actual preferred-Q conjugation gives the exact forward short-coordinate row. -/
theorem generatedFifth_odd_forward_operator (j : Fin 64) (X : GriessShortIndex → ℝ) :
    localShortOperator generatedFifthLocalFiber X (generatedFifthOddRootOutputLabel j) =
      qSign (generatedFifthOddRootPhaseData j) * X (generatedFifthOddRootInputLabel j) := by
  have hi : spinConjugation (generatedFifthLocalFiber⁻¹).val.1
      (monsterNortonShortQ (generatedFifthOddRootOutputLabel j)) =
        qCentral (generatedFifthOddRootPhaseData j) *
          monsterNortonShortQ (generatedFifthOddRootInputLabel j) := by
    simp only [monsterNortonShortQ_eq]
    exact generatedFifth_odd_inverse_Q_image j
  have h := monsterNortonShortOperator_of_Q_image _ _ _ _ hi
    (localShortOperator generatedFifthLocalFiber X)
  have hc : localShortOperator generatedFifthLocalFiber⁻¹
      (localShortOperator generatedFifthLocalFiber X) = X := by
    change (localShortOperator generatedFifthLocalFiber⁻¹).comp
      (localShortOperator generatedFifthLocalFiber) X = X
    rw [← localShortOperator_mul, inv_mul_cancel, localShortOperator_one]
    rfl
  rw [hc] at h
  calc
    _ = qSign (generatedFifthOddRootPhaseData j) *
        (qSign (generatedFifthOddRootPhaseData j) *
          localShortOperator generatedFifthLocalFiber X
            (generatedFifthOddRootOutputLabel j)) := by
      rw [← mul_assoc, qSign_sq, one_mul]
    _ = _ := by rw [← h]

/-- Each of the 64 actual middle odd-short coefficients has the verified signed unit value. -/
theorem generatedFifth_odd_middle_coefficient (j : Fin 64) :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedFifthLocalFiber)
      (sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0)))).2.1
        (generatedFifthOddRootOutputLabel j) =
          qSign (generatedFifthOddCoefficientPhaseData j) := by
  rw [generatedFourth_local_short, generatedFifth_odd_forward_operator,
    generatedFifth_original_input_coefficient, ← qSign_add,
    generatedFifth_odd_coefficient_phase_certificate]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
