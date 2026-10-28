/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthEvenPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMatrixCoordinates

/-! The 56 original middle octad-source coefficients, with actual source and preferred-Q phases. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original preferred-Q and Fourier phases of each actual octad coordinate. -/
noncomputable def generatedFifthEvenCoefficientPhase (j : Fin 56) : ZMod 2 :=
  generatedFifthEvenRootPhase j + generatedFifthEvenRootInputPhase j

/-- Actual preferred-Q conjugation gives the exact forward short-coordinate row. -/
theorem generatedFifth_even_forward_operator (j : Fin 56) (X : GriessShortIndex → ℝ) :
    localShortOperator generatedFifthLocalFiber X (generatedFifthEvenRootOutputLabel j) =
      qSign (generatedFifthEvenRootPhase j) * X (generatedFifthEvenRootInputLabel j) := by
  have hi : spinConjugation (generatedFifthLocalFiber⁻¹).val.1
      (monsterNortonShortQ (generatedFifthEvenRootOutputLabel j)) =
        qCentral (generatedFifthEvenRootPhase j) *
          monsterNortonShortQ (generatedFifthEvenRootInputLabel j) := by
    simp only [monsterNortonShortQ_eq]
    exact generatedFifth_even_inverse_Q_image j
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
    _ = qSign (generatedFifthEvenRootPhase j) *
        (qSign (generatedFifthEvenRootPhase j) *
          localShortOperator generatedFifthLocalFiber X
            (generatedFifthEvenRootOutputLabel j)) := by
      rw [← mul_assoc, qSign_sq, one_mul]
    _ = _ := by rw [← h]

/-- Each of the 56 actual middle octad-short coefficients has the verified signed unit value. -/
theorem generatedFifth_even_middle_coefficient (j : Fin 56) :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedFifthLocalFiber)
      (sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0)))).2.1
        (generatedFifthEvenRootOutputLabel j) =
          qSign (generatedFifthEvenCoefficientPhase j) := by
  rw [generatedFourth_local_short, generatedFifth_even_forward_operator,
    generatedFifth_original_even_input_coefficient, ← qSign_add,
    generatedFifthEvenCoefficientPhase]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
