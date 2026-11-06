/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthOddRootData

/-! Linearized integer odd-vector support, permitting bounded finite checks
with one shared codeword transform for all 24 distinguished coordinates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open scoped Matrix

/-- The original signed one-vector belonging to the actual Golay code label. -/
def generatedFourthOddSignVector (d : Fin 2048) : Fin 24 → ℤ := fun i =>
  if (golayEncodedMask d.val).testBit i.val then -1 else 1

/-- The odd vector differs from its signed one-vector by a single coordinate correction. -/
theorem generatedFourth_odd_integral_linear (d : Fin 2048) (i : Fin 24) :
    griessShortIntegral (Sum.inr (Sum.inr (d, i))) = generatedFourthOddSignVector d -
      (4 * generatedFourthOddSignVector d i) • (Pi.single i 1 : Fin 24 → ℤ) := by
  funext k
  simp only [griessShortIntegral, generatedFourthOddSignVector, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  by_cases hk : k = i
  · subst k
    simp only [ite_true]
    ring
  · simp only [hk, ite_false, mul_zero, sub_zero, mul_one]

/-- The actual inverse numerator uses one shared transform and a column correction. -/
theorem generatedFourth_odd_inverse_linear (d : Fin 2048) (i k : Fin 24) :
    (generatedFourthInverseNumerator *ᵥ griessShortIntegral (Sum.inr (Sum.inr (d, i)))) k =
      (generatedFourthInverseNumerator *ᵥ generatedFourthOddSignVector d) k -
        4 * generatedFourthOddSignVector d i * generatedFourthInverseNumerator k i := by
  rw [generatedFourth_odd_integral_linear, Matrix.mulVec_sub, Matrix.mulVec_smul,
    Matrix.mulVec_single_one]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
