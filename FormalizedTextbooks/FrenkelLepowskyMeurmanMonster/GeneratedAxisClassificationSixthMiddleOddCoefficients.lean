/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMiddleOddPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMiddleOddCoordinates

/-! Exact preferred signed quarter coefficients for the complete actual middle odd-short support. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Integer numerators of the genuine preferred middle odd-short coefficients. -/
def generatedSixthMiddleOddCoefficientNumerator : Fin 276 → ℤ :=
  ![3, 3, 3, 3, 3, 3, 3, -3, 3, 3, -3, 3, 3, -3, 3, 3, -3, -3, 3, 3, 3, 3,
    -3, 1, -1, 1, -1, 1, 1, -1, 1, 1, 1, -1, 1, -1, 1, -1, -1, -1, 1, 1, 1, 1,
    1, 1, 1, -1, -1, 1, -1, 1, 1, -1, -1, -1, -1, 1, -1, 1, 1, -1, -1, -1, 1, -1,
    1, -1, 1, 1, 1, 1, 1, -1, -1, -1, 1, 1, -1, 1, 1, 1, -1, 1, 1, -1, 1, 1,
    1, 1, -1, 1, 1, -1, -1, -1, -1, -1, 1, -1, -1, 1, 1, -1, -1, 1, -1, -1, -1, -1,
    -1, -1, -1, -1, 1, -1, 1, 1, -1, -1, 1, -1, -1, -1, -1, -1, 1, 1, -1, -1, -1, 1,
    -1, 1, -1, 1, -1, 1, -1, -1, 1, 1, 1, -1, -1, 1, -1, 1, -1, -1, -1, 1, -1, 1,
    1, -1, 1, -1, 1, 1, 1, 1, -1, 1, 1, -1, -1, 1, -1, 1, 1, 1, 1, -1, 1, 1,
    -1, -1, 1, 1, 1, 1, -1, -1, 1, -1, -1, -1, 1, 1, -1, -1, -1, 1, 1, -1, 1, -1,
    1, 1, 1, -1, 1, 1, -1, -1, -1, -1, 1, -1, -1, 1, -1, -1, 1, 1, -1, -1, -1, -1,
    1, 1, 1, -1, 1, 1, 1, 1, -1, 1, -1, 1, 1, -1, 1, -1, 1, -1, 1, 1, -1, -1,
    1, -1, -1, 1, -1, 1, 1, 1, -1, -1, -1, -1, 1, -1, -1, 1, -1, 1, -1, -1, 1, 1,
    1, 1, 1, 1, 1, -1, -1, 1, 1, -1, 1, 1]

/-- The cached integer numerators include both the original pair sign and full Q phase. -/
theorem generatedSixth_middle_odd_numerator_certificate : ∀ k : Fin 276,
    (if generatedSixthMiddleOddPreferredPhase k = 0 then 1 else -1) *
      (if (generatedSixthMiddleOddSourceCoordinates k).1 = 0 then 1 else -1) *
      (if (generatedSixthMiddleOddSourceCoordinates k).2.1 = 0 ∨
          (generatedSixthMiddleOddSourceCoordinates k).2.2 = 0 then -3 else 1) =
        generatedSixthMiddleOddCoefficientNumerator k := by
  decide +kernel

private theorem sign_cast (c : ZMod 2) :
    qSign c = ((if c = 0 then 1 else -1 : ℤ) : ℝ) := by
  fin_cases c <;> norm_num [qSign]

/-- Every displayed preferred odd label has its exact actual signed quarter coefficient. -/
theorem generatedSixth_middle_odd_coefficient (k : Fin 276) :
    (griessConwayEncode
      (rhoLocal (localFiberIntoH generatedSixthLocalFiber) generatedOddAxis)).2.1
        (generatedSixthMiddleOddOutput k) =
      (generatedSixthMiddleOddCoefficientNumerator k : ℝ) / 4 := by
  rw [← generatedSixth_middle_odd_permutation]
  unfold generatedSixthMiddleShortLabel
  rw [generatedFourth_local_short, localShortOperator_image,
    generatedSixth_original_pair_coordinate]
  change qSign (generatedSixthMiddleShortPhase (generatedSixthMiddleOddInput k)) *
    ((if (generatedSixthMiddleOddInput k).1 = 0 then 1 else -1) *
      (if (griessCoordinatePair (generatedSixthMiddleOddInput k).2).1 = 0 ∨
        (griessCoordinatePair (generatedSixthMiddleOddInput k).2).2 = 0 then -3 else 1) / 4) = _
  rw [generatedSixth_middle_odd_phase, sign_cast]
  unfold generatedSixthMiddleOddInput
  rw [griessPairIndex_coordinates, ite_eq_left (generatedSixth_middle_odd_source_lt k)]
  have hc := congrArg (fun z : ℤ => (z : ℝ))
    (generatedSixth_middle_odd_numerator_certificate k)
  push_cast at hc
  simp only [Int.cast_ite, Int.cast_one, Int.cast_neg]
  calc
    _ = ((if generatedSixthMiddleOddPreferredPhase k = 0 then 1 else -1 : ℝ) *
      (if (generatedSixthMiddleOddSourceCoordinates k).1 = 0 then 1 else -1) *
      (if (generatedSixthMiddleOddSourceCoordinates k).2.1 = 0 ∨
        (generatedSixthMiddleOddSourceCoordinates k).2.2 = 0 then -3 else 1)) / 4 := by ring
    _ = _ := congrArg (fun z : ℝ => z / 4) hc

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
