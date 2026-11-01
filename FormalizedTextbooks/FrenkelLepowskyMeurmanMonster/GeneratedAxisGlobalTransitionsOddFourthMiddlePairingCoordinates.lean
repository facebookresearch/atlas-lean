/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthOutgoingPacket
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthPairingCriterion
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsSparsePairingCoordinates

/-! The entire actual middle pairing reduces to the original finite matrix and preferred short coefficients. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The complete actual inverse-triality comparison retains all original framed coordinates. -/
theorem generatedAxisGlobalOddFourthMiddleComparisonPacket_actual (k : Fin 4) :
    griessConwayEncode (generatedAxisGlobalOddFourthMiddleComparison k) =
      generatedAxisGlobalRationalPacketReal
        (generatedAxisGlobalRationalInverse (generatedAxisGlobalOddFourthFramedPacket k)) :=
  generatedAxisGlobalRationalInverse_actual _ _ (generatedAxisGlobalOddFourthFramedPacket_actual k)

/-- Exact finite rational expression for the entire actual middle pairing, with all zero terms retained. -/
def generatedAxisGlobalOddFourthMiddlePairingQ (k : Fin 4) : ℚ :=
  (∑ i : Fin 24, ∑ j : Fin 24,
    generatedAxisGlobalInverseMatrixQ (generatedAxisGlobalOddFourthFramedPacket k) i j *
      generatedAxisGlobalCanonicalFourthMiddleMatrixQ i j) +
  (∑ p : GeneratedAxisGlobalCanonicalFourthMiddleShortIndex,
    generatedAxisGlobalCanonicalFourthMiddleShortCoefficient p *
      generatedAxisGlobalInverseShortQ (generatedAxisGlobalOddFourthFramedPacket k)
        (generatedAxisGlobalCanonicalFourthMiddleShortLabel p))

/-- The finite expression contains the full actual Griess pairing, with no omitted constituent. -/
theorem generatedAxisGlobalOddFourthMiddlePairingQ_actual (k : Fin 4) :
    griessForm (generatedAxisGlobalOddFourthMiddleComparison k)
      generatedAxisGlobalCanonicalFourthMiddleAxis =
        (generatedAxisGlobalOddFourthMiddlePairingQ k : ℝ) := by
  have hy : (griessConwayEncode generatedAxisGlobalCanonicalFourthMiddleAxis).2.1 =
      ∑ p : GeneratedAxisGlobalCanonicalFourthMiddleShortIndex,
        (generatedAxisGlobalCanonicalFourthMiddleShortCoefficient p : ℝ) •
          Pi.single (generatedAxisGlobalCanonicalFourthMiddleShortLabel p) (1 : ℝ) :=
    generatedAxisGlobalCanonicalFourthMiddleShortPacket_actual
  have hp := generatedAxisGlobal_griessForm_sparse_coordinates
    (generatedAxisGlobalOddFourthMiddleComparison k) generatedAxisGlobalCanonicalFourthMiddleAxis
    (fun p => (generatedAxisGlobalCanonicalFourthMiddleShortCoefficient p : ℝ))
    generatedAxisGlobalCanonicalFourthMiddleShortLabel hy
  rw [hp, generatedAxisGlobalOddFourthMiddleComparisonPacket_actual,
    generatedAxisGlobalCanonicalFourthMiddleFiniteRationalPacket_actual]
  simp only [generatedAxisGlobalRationalPacketReal, generatedAxisGlobalRationalInverse,
    generatedAxisGlobalCanonicalFourthMiddleFiniteRationalPacket, Matrix.map_apply,
    generatedAxisGlobalOddFourthMiddlePairingQ, Rat.cast_add, Rat.cast_sum, Rat.cast_mul]
  simp only [Pi.zero_apply, Rat.cast_zero, zero_div, conwayTensorForm,
    LinearMap.mk₂_apply, mul_zero, Finset.sum_const_zero, add_zero]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
