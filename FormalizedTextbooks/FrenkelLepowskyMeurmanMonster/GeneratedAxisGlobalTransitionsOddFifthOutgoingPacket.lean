/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot03RationalPacket
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthCompactFrameTensorUnconditional
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalLocalMatrixWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalShortOperator
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalSignMatrix

/-! All original outgoing coefficients and the complete root-three comparison actions. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- The whole forward and inverse original root-three triality packets. -/
def generatedAxisGlobalOddFifthOutgoingPacket : Fin 2 → GeneratedAxisGlobalRationalPacket := ![
  generatedAxisGlobalRationalTriality generatedAxisGlobalOddRoot03RationalPacket,
  generatedAxisGlobalRationalInverse generatedAxisGlobalOddRoot03RationalPacket]

/-- Every packet coefficient is bound to the actual original generated word. -/
theorem generatedAxisGlobalOddFifthOutgoingPacket_actual (k : Fin 2) :
    griessConwayEncode ((generatedAxisGlobalOddFifthComparisonAction k).val generatedOddAxis) =
      generatedAxisGlobalRationalPacketReal (generatedAxisGlobalOddFifthOutgoingPacket k) := by
  fin_cases k
  · exact generatedAxisGlobalOddRoot03PositiveRationalPacket_actual
  · exact generatedAxisGlobalOddRoot03NegativeRationalPacket_actual

/-- All physical source tensor labels, retaining the actual square-root normalization. -/
def generatedAxisGlobalOddFifthOutgoingTensor (k : Fin 2) : GeneratedAxisGlobalRationalTensor :=
  fun a i => (generatedAxisGlobalOddFifthOutgoingPacket k).2.2 (golayLabelCoefficients a) i

/-- The complete original outgoing tensor is exactly the rational physical packet. -/
theorem generatedAxisGlobalOddFifthOutgoingTensor_actual (k : Fin 2) :
    (griessConwayEncode
      ((generatedAxisGlobalOddFifthComparisonAction k).val generatedOddAxis)).2.2 =
      generatedAxisGlobalRationalTensorReal (generatedAxisGlobalOddFifthOutgoingTensor k) := by
  rw [generatedAxisGlobalOddFifthOutgoingPacket_actual]
  funext t i
  simp only [generatedAxisGlobalRationalPacketReal, generatedAxisGlobalRationalTensorReal,
    generatedAxisGlobalOddFifthOutgoingTensor, generatedAxisGlobalSpinLabel_decode]

/-- The genuine full physical matrix action in its original factor order. -/
def generatedAxisGlobalOddFifthFramedMatrix (k : Fin 2) : Matrix (Fin 24) (Fin 24) ℚ :=
  generatedAxisGlobalRationalSpatialMatrixWord (generatedAxisGlobalOddFifthComparisonPostLetters k)
    (generatedAxisGlobalRationalSpatialMatrixWord [0]
      (generatedAxisGlobalRationalSignMatrix (generatedAxisGlobalOddFifthComparisonSign k)
        (generatedAxisGlobalRationalSpatialMatrixWord
          generatedAxisGlobalOddFifthComparisonPreLetters
          (generatedAxisGlobalOddFifthOutgoingPacket k).1)))

/-- The whole actual preferred-short operator, including every central phase. -/
def generatedAxisGlobalOddFifthFramedShort (k : Fin 2) : GriessShortIndex → ℚ :=
  generatedAxisGlobalRationalShortOperator (generatedAxisGlobalOddFifthComparisonFiber k)
    (generatedAxisGlobalOddFifthOutgoingPacket k).2.1

/-- The complete actual physical tensor action, using every original certified spin factor. -/
def generatedAxisGlobalOddFifthFramedTensor (k : Fin 2) : GeneratedAxisGlobalRationalTensor :=
  generatedAxisGlobalOddFifthCompactFrameTensor k (generatedAxisGlobalOddFifthOutgoingTensor k)

/-- Every complete original matrix coefficient is bound to the genuine comparison frame. -/
theorem generatedAxisGlobalOddFifthFramedMatrix_actual (k : Fin 2) :
    (griessConwayEncode (rhoLocal (generatedAxisGlobalOddFifthComparisonLocal k)
      ((generatedAxisGlobalOddFifthComparisonAction k).val generatedOddAxis))).1 =
      (generatedAxisGlobalOddFifthFramedMatrix k).map (Rat.castHom ℝ) := by
  let x := (generatedAxisGlobalOddFifthComparisonAction k).val generatedOddAxis
  let pre := ((generatedAxisGlobalOddFifthComparisonPreLetters.map
    generatedAxisGlobalOddSourceFiberLetter).prod)
  let post := (((generatedAxisGlobalOddFifthComparisonPostLetters k).map
    generatedAxisGlobalOddSourceFiberLetter).prod)
  have hpre := generatedAxisGlobalRationalLocalMatrixWord_actual
    generatedAxisGlobalOddFifthComparisonPreLetters 1 x
    (generatedAxisGlobalOddFifthOutgoingPacket k).1
    (congrArg Prod.fst (generatedAxisGlobalOddFifthOutgoingPacket_actual k))
  simp only [map_one, one_mul] at hpre
  have hsign := generatedAxisGlobalRationalSignMatrix_actual
    (generatedAxisGlobalOddFifthComparisonSign k) (rhoLocal (localFiberIntoH pre) x) _ hpre
  have hxi := generatedAxisGlobalRationalLocalMatrixWord_actual [0] 1
    (rhoLocal (generatedFifthSignLocal (generatedAxisGlobalOddFifthComparisonSign k) 0)
      (rhoLocal (localFiberIntoH pre) x)) _ hsign
  simp only [map_one, one_mul, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one] at hxi
  have hout := generatedAxisGlobalRationalLocalMatrixWord_actual
    (generatedAxisGlobalOddFifthComparisonPostLetters k)
    (generatedAxisGlobalOddFifthComparisonQ k)
    (rhoLocal (localFiberIntoH xiSpinLocalFiber)
      (rhoLocal (generatedFifthSignLocal (generatedAxisGlobalOddFifthComparisonSign k) 0)
        (rhoLocal (localFiberIntoH pre) x))) _ hxi
  have hf : generatedAxisGlobalOddFifthComparisonLocal k =
      localFiberIntoH (localFiberIncl (generatedAxisGlobalOddFifthComparisonQ k) * post) *
        localFiberIntoH xiSpinLocalFiber *
        generatedFifthSignLocal (generatedAxisGlobalOddFifthComparisonSign k) 0 *
        localFiberIntoH pre := by
    simp only [generatedAxisGlobalOddFifthComparisonLocal,
      generatedAxisGlobalOddFifthComparisonFiber,
      map_mul, generatedFifth_sign_fiber_local, pre, post, mul_assoc]
  rw [hf, map_mul, map_mul, map_mul, LinearEquiv.mul_apply,
    LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  exact hout

/-- All original framed coefficients, with honest full preferred-short and tensor operators. -/
def generatedAxisGlobalOddFifthFramedPacket (k : Fin 2) : GeneratedAxisGlobalRationalPacket :=
  (generatedAxisGlobalOddFifthFramedMatrix k,
    (generatedAxisGlobalOddFifthFramedShort k,
      fun t i => generatedAxisGlobalOddFifthFramedTensor k (generatedAxisGlobalSpinLabel t) i))

/-- The complete framed vector equals the actual original frame at every Conway coordinate. -/
theorem generatedAxisGlobalOddFifthFramedPacket_actual (k : Fin 2) :
    griessConwayEncode (rhoLocal (generatedAxisGlobalOddFifthComparisonLocal k)
      ((generatedAxisGlobalOddFifthComparisonAction k).val generatedOddAxis)) =
      generatedAxisGlobalRationalPacketReal (generatedAxisGlobalOddFifthFramedPacket k) := by
  apply Prod.ext
  · exact generatedAxisGlobalOddFifthFramedMatrix_actual k
  · change (griessConwayEncode (localGriessRepresentation
      (generatedAxisGlobalOddFifthComparisonFiber k)
      ((generatedAxisGlobalOddFifthComparisonAction k).val generatedOddAxis))).2 = _
    rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
    apply Prod.ext
    · change localShortOperator (generatedAxisGlobalOddFifthComparisonFiber k)
        (griessConwayEncode
          ((generatedAxisGlobalOddFifthComparisonAction k).val generatedOddAxis)).2.1 = _
      rw [generatedAxisGlobalOddFifthOutgoingPacket_actual]
      exact generatedAxisGlobalRationalShortOperator_actual _ _
    · rw [generatedAxisGlobalOddFifthOutgoingTensor_actual]
      exact generatedAxisGlobalOddFifthCompactFrameTensor_unconditional _ _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
