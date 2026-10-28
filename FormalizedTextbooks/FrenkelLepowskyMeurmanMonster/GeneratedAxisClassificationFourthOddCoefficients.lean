/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthOddRootImages
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthInputCoefficients
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMatrixCoordinates

/-! The 56 original tensor-source coefficients, with actual source and preferred-Q phases. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The exact combined coefficient signs in the 56 verified odd rows. -/
def generatedFourthOddCoefficientPhaseData : Fin 56 → ZMod 2 :=
  ![0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0,
    0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1,
    1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1]

/-- The finite coefficient signs combine the genuine inverse-Q and original input phases. -/
theorem generatedFourth_odd_coefficient_phase_certificate : ∀ j : Fin 56,
    generatedFourthOddRootPhaseData j + generatedFourthOddRootInputPhase j =
      generatedFourthOddCoefficientPhaseData j := by
  decide +kernel

/-- Actual preferred-Q conjugation gives the exact forward short-coordinate row. -/
theorem generatedFourth_odd_forward_operator (j : Fin 56) (X : GriessShortIndex → ℝ) :
    localShortOperator generatedFourthLocalFiber X (generatedFourthOddRootOutputLabel j) =
      qSign (generatedFourthOddRootPhaseData j) * X (generatedFourthOddRootInputLabel j) := by
  have hi : spinConjugation (generatedFourthLocalFiber⁻¹).val.1
      (monsterNortonShortQ (generatedFourthOddRootOutputLabel j)) =
        qCentral (generatedFourthOddRootPhaseData j) *
          monsterNortonShortQ (generatedFourthOddRootInputLabel j) := by
    simp only [monsterNortonShortQ_eq]
    exact generatedFourth_odd_inverse_Q_image j
  have h := monsterNortonShortOperator_of_Q_image _ _ _ _ hi
    (localShortOperator generatedFourthLocalFiber X)
  have hc : localShortOperator generatedFourthLocalFiber⁻¹
      (localShortOperator generatedFourthLocalFiber X) = X := by
    change (localShortOperator generatedFourthLocalFiber⁻¹).comp
      (localShortOperator generatedFourthLocalFiber) X = X
    rw [← localShortOperator_mul, inv_mul_cancel, localShortOperator_one]
    rfl
  rw [hc] at h
  calc
    _ = qSign (generatedFourthOddRootPhaseData j) *
        (qSign (generatedFourthOddRootPhaseData j) *
          localShortOperator generatedFourthLocalFiber X
            (generatedFourthOddRootOutputLabel j)) := by
      rw [← mul_assoc, qSign_sq, one_mul]
    _ = _ := by rw [← h]

/-- Each of the 56 actual middle odd-short coefficients has the verified signed unit value. -/
theorem generatedFourth_odd_middle_coefficient (j : Fin 56) :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedFourthLocalFiber)
      (sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0)))).2.1
        (generatedFourthOddRootOutputLabel j) =
          qSign (generatedFourthOddCoefficientPhaseData j) := by
  rw [generatedFourth_local_short, generatedFourth_odd_forward_operator,
    generatedFourth_original_input_coefficient, ← qSign_add,
    generatedFourth_odd_coefficient_phase_certificate]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
