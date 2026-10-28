/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthOutgoingPacket
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthPairingCriterion
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsSparsePairingCoordinates

/-! The whole actual pairing reduces to its original finite matrix and preferred short terms. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The complete actual inverse-triality comparison retains all original framed coordinates. -/
theorem generatedAxisGlobalOddFifthMiddleComparisonPacket_actual (k : Fin 2) :
    griessConwayEncode (generatedAxisGlobalOddFifthMiddleComparison k) =
      generatedAxisGlobalRationalPacketReal
        (generatedAxisGlobalRationalInverse (generatedAxisGlobalOddFifthFramedPacket k)) :=
  generatedAxisGlobalRationalInverse_actual _ _ (generatedAxisGlobalOddFifthFramedPacket_actual k)

/-- The whole actual middle pairing in exact rational coordinates, including all zero terms. -/
def generatedAxisGlobalOddFifthMiddlePairingQ (k : Fin 2) : ℚ :=
  (∑ i : Fin 24, ∑ j : Fin 24,
    generatedAxisGlobalInverseMatrixQ (generatedAxisGlobalOddFifthFramedPacket k) i j *
      generatedAxisGlobalFifthMiddleMatrixQ i j) +
  (∑ p : GeneratedAxisGlobalCanonicalFifthMiddleShortIndex,
    generatedAxisGlobalCanonicalFifthMiddleShortCoefficient p *
      generatedAxisGlobalInverseShortQ (generatedAxisGlobalOddFifthFramedPacket k)
        (generatedAxisGlobalCanonicalFifthMiddleShortLabel p))

/-- The finite expression contains the full actual Griess pairing, with no omitted constituent. -/
theorem generatedAxisGlobalOddFifthMiddlePairingQ_actual (k : Fin 2) :
    griessForm (generatedAxisGlobalOddFifthMiddleComparison k)
      generatedAxisGlobalCanonicalFifthMiddleAxis =
        (generatedAxisGlobalOddFifthMiddlePairingQ k : ℝ) := by
  have hy : (griessConwayEncode generatedAxisGlobalCanonicalFifthMiddleAxis).2.1 =
      ∑ p : GeneratedAxisGlobalCanonicalFifthMiddleShortIndex,
        (generatedAxisGlobalCanonicalFifthMiddleShortCoefficient p : ℝ) •
          Pi.single (generatedAxisGlobalCanonicalFifthMiddleShortLabel p) (1 : ℝ) :=
    generatedAxisGlobalCanonicalFifthMiddleShortPacket_actual
  have hp := generatedAxisGlobal_griessForm_sparse_coordinates
    (generatedAxisGlobalOddFifthMiddleComparison k) generatedAxisGlobalCanonicalFifthMiddleAxis
    (fun p => (generatedAxisGlobalCanonicalFifthMiddleShortCoefficient p : ℝ))
    generatedAxisGlobalCanonicalFifthMiddleShortLabel hy
  rw [hp, generatedAxisGlobalOddFifthMiddleComparisonPacket_actual,
    generatedAxisGlobalCanonicalFifthMiddleFiniteRationalPacket_actual]
  simp only [generatedAxisGlobalRationalPacketReal, generatedAxisGlobalRationalInverse,
    generatedAxisGlobalCanonicalFifthMiddleFiniteRationalPacket, Matrix.map_apply,
    generatedAxisGlobalOddFifthMiddlePairingQ, Rat.cast_add, Rat.cast_sum, Rat.cast_mul]
  simp only [Pi.zero_apply, Rat.cast_zero, zero_div, conwayTensorForm,
    LinearMap.mk₂_apply, mul_zero, Finset.sum_const_zero, add_zero]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
