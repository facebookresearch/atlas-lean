/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot02RationalPacket
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot04RationalPacket
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthCompactFrameTensorUnconditional
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalLocalMatrixWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalShortOperator

/-! Complete actual outgoing and framed coordinate packets for the four remaining Fourth comparisons. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- The four whole rational outputs of the genuine original signed triality words. -/
def generatedAxisGlobalOddFourthOutgoingPacket : Fin 4 → GeneratedAxisGlobalRationalPacket := ![
  generatedAxisGlobalRationalTriality generatedAxisGlobalOddRoot02RationalPacket,
  generatedAxisGlobalRationalInverse generatedAxisGlobalOddRoot02RationalPacket,
  generatedAxisGlobalRationalTriality generatedAxisGlobalOddRoot04RationalPacket,
  generatedAxisGlobalRationalInverse generatedAxisGlobalOddRoot04RationalPacket]

/-- Every original outgoing matrix, short and tensor coordinate is bound to its actual generated word. -/
theorem generatedAxisGlobalOddFourthOutgoingPacket_actual (k : Fin 4) :
    griessConwayEncode ((generatedAxisGlobalOddFourthComparisonAction k).val generatedOddAxis) =
      generatedAxisGlobalRationalPacketReal (generatedAxisGlobalOddFourthOutgoingPacket k) := by
  fin_cases k
  · exact generatedAxisGlobalOddRoot02PositiveRationalPacket_actual
  · exact generatedAxisGlobalOddRoot02NegativeRationalPacket_actual
  · exact generatedAxisGlobalOddRoot04PositiveRationalPacket_actual
  · exact generatedAxisGlobalOddRoot04NegativeRationalPacket_actual

/-- The original outgoing scaled tensor in the complete physical spin labels. -/
def generatedAxisGlobalOddFourthOutgoingTensor (k : Fin 4) : GeneratedAxisGlobalRationalTensor :=
  fun a i => (generatedAxisGlobalOddFourthOutgoingPacket k).2.2 (golayLabelCoefficients a) i

/-- Physical labels retain the entire actual outgoing tensor and its square-root normalization. -/
theorem generatedAxisGlobalOddFourthOutgoingTensor_actual (k : Fin 4) :
    (griessConwayEncode ((generatedAxisGlobalOddFourthComparisonAction k).val generatedOddAxis)).2.2 =
      generatedAxisGlobalRationalTensorReal (generatedAxisGlobalOddFourthOutgoingTensor k) := by
  rw [generatedAxisGlobalOddFourthOutgoingPacket_actual]
  funext t i
  simp only [generatedAxisGlobalRationalPacketReal, generatedAxisGlobalRationalTensorReal,
    generatedAxisGlobalOddFourthOutgoingTensor, generatedAxisGlobalSpinLabel_decode]

/-- Every framed physical matrix coefficient from the complete original spatial word. -/
def generatedAxisGlobalOddFourthFramedMatrix (k : Fin 4) : Matrix (Fin 24) (Fin 24) ℚ :=
  generatedAxisGlobalRationalSpatialMatrixWord (generatedAxisGlobalOddFourthComparisonLetters k)
    (generatedAxisGlobalOddFourthOutgoingPacket k).1

/-- The entire true preferred short operator; selected finite coordinates are certified separately. -/
def generatedAxisGlobalOddFourthFramedShort (k : Fin 4) : GriessShortIndex → ℚ :=
  generatedAxisGlobalRationalShortOperator (generatedAxisGlobalOddFourthComparisonFiber k)
    (generatedAxisGlobalOddFourthOutgoingPacket k).2.1

/-- The entire actual frame uses compact certified original spin plans. -/
def generatedAxisGlobalOddFourthFramedTensor (k : Fin 4) : GeneratedAxisGlobalRationalTensor :=
  generatedAxisGlobalOddFourthCompactFrameTensor k (generatedAxisGlobalOddFourthOutgoingTensor k)

/-- The complete framed packet uses honest full matrix, preferred short and tensor operators. -/
def generatedAxisGlobalOddFourthFramedPacket (k : Fin 4) : GeneratedAxisGlobalRationalPacket :=
  (generatedAxisGlobalOddFourthFramedMatrix k,
    (generatedAxisGlobalOddFourthFramedShort k,
      fun t i => generatedAxisGlobalOddFourthFramedTensor k (generatedAxisGlobalSpinLabel t) i))

/-- Every coefficient of the four genuine full framed vectors is bound without recognition assumptions. -/
theorem generatedAxisGlobalOddFourthFramedPacket_actual (k : Fin 4) :
    griessConwayEncode (rhoLocal (generatedAxisGlobalOddFourthComparisonLocal k)
      ((generatedAxisGlobalOddFourthComparisonAction k).val generatedOddAxis)) =
      generatedAxisGlobalRationalPacketReal (generatedAxisGlobalOddFourthFramedPacket k) := by
  apply Prod.ext
  · apply generatedAxisGlobalRationalLocalMatrixWord_actual
    exact congrArg Prod.fst (generatedAxisGlobalOddFourthOutgoingPacket_actual k)
  · change (griessConwayEncode (localGriessRepresentation
      (generatedAxisGlobalOddFourthComparisonFiber k)
      ((generatedAxisGlobalOddFourthComparisonAction k).val generatedOddAxis))).2 = _
    rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
    apply Prod.ext
    · change localShortOperator (generatedAxisGlobalOddFourthComparisonFiber k)
        (griessConwayEncode ((generatedAxisGlobalOddFourthComparisonAction k).val generatedOddAxis)).2.1 = _
      rw [generatedAxisGlobalOddFourthOutgoingPacket_actual]
      exact generatedAxisGlobalRationalShortOperator_actual _ _
    · rw [generatedAxisGlobalOddFourthOutgoingTensor_actual]
      exact generatedAxisGlobalOddFourthCompactFrameTensor_unconditional _ _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
