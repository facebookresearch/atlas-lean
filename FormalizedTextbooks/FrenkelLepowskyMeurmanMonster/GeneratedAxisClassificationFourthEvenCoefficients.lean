/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthEvenPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMatrixCoordinates

/-! The 63 original middle octad-source coefficients, with actual source and preferred-Q phases. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original preferred-Q and Fourier phases of each actual octad coordinate. -/
noncomputable def generatedFourthEvenCoefficientPhase (j : Fin 63) : ZMod 2 :=
  generatedFourthEvenRootPhase j + generatedFourthEvenRootInputPhase j

/-- Actual preferred-Q conjugation gives the exact forward short-coordinate row. -/
theorem generatedFourth_even_forward_operator (j : Fin 63) (X : GriessShortIndex → ℝ) :
    localShortOperator generatedFourthLocalFiber X (generatedFourthEvenRootOutputLabel j) =
      qSign (generatedFourthEvenRootPhase j) * X (generatedFourthEvenRootInputLabel j) := by
  have hi : spinConjugation (generatedFourthLocalFiber⁻¹).val.1
      (monsterNortonShortQ (generatedFourthEvenRootOutputLabel j)) =
        qCentral (generatedFourthEvenRootPhase j) *
          monsterNortonShortQ (generatedFourthEvenRootInputLabel j) := by
    simp only [monsterNortonShortQ_eq]
    exact generatedFourth_even_inverse_Q_image j
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
    _ = qSign (generatedFourthEvenRootPhase j) *
        (qSign (generatedFourthEvenRootPhase j) *
          localShortOperator generatedFourthLocalFiber X
            (generatedFourthEvenRootOutputLabel j)) := by
      rw [← mul_assoc, qSign_sq, one_mul]
    _ = _ := by rw [← h]

/-- Each of the 63 actual middle octad-short coefficients has the verified signed unit value. -/
theorem generatedFourth_even_middle_coefficient (j : Fin 63) :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedFourthLocalFiber)
      (sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0)))).2.1
        (generatedFourthEvenRootOutputLabel j) =
          qSign (generatedFourthEvenCoefficientPhase j) := by
  rw [generatedFourth_local_short, generatedFourth_even_forward_operator,
    generatedFourth_original_even_input_coefficient, ← qSign_add,
    generatedFourthEvenCoefficientPhase]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
