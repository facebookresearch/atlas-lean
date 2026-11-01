/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortAxisRationalPacket
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalShortOperator
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsCanonicalFourthMiddleMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsCanonicalFourthMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsCanonicalFourthTensorInteger

/-! Complete rational coordinates of the genuine original Fourth axis, with every original preferred permutation and central phase retained. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Original forward triality of the genuine code-sixteen signed-short axis. -/
def generatedAxisGlobalCanonicalFourthInitialRationalPacket : GeneratedAxisGlobalRationalPacket :=
  generatedAxisGlobalRationalTriality
    (generatedAxisGlobalShortAxisRationalPacket (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0)

/-- All physical entries after the actual original three-letter middle word. -/
def generatedAxisGlobalCanonicalFourthMiddleRationalPacket : GeneratedAxisGlobalRationalPacket :=
  (generatedAxisGlobalCanonicalFourthMiddleMatrixQ,
    (generatedAxisGlobalRationalShortOperator generatedFourthLocalFiber
      generatedAxisGlobalCanonicalFourthInitialRationalPacket.2.1, 0))

/-- The whole canonical matrix, complete preferred short vector, and all actual scaled tensor entries. -/
def generatedAxisGlobalCanonicalFourthRationalPacket : GeneratedAxisGlobalRationalPacket :=
  (generatedAxisGlobalCanonicalFourthMatrixQ,
    ((generatedAxisGlobalRationalTriality generatedAxisGlobalCanonicalFourthMiddleRationalPacket).2.1,
      fun t i => (generatedAxisGlobalCanonicalFourthTensorInteger (generatedAxisGlobalSpinLabel t) i : ℚ)))

/-- Every initial rational coordinate is the genuine first original triality output. -/
theorem generatedAxisGlobalCanonicalFourthInitialRationalPacket_actual :
    griessConwayEncode
      (sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0)) =
    generatedAxisGlobalRationalPacketReal generatedAxisGlobalCanonicalFourthInitialRationalPacket :=
  generatedAxisGlobalRationalTriality_of_actual _ _
    (generatedAxisGlobalShortAxisRationalPacket_actual _ _)

/-- The middle rational packet binds the entire genuine original local source vector. -/
theorem generatedAxisGlobalCanonicalFourthMiddleRationalPacket_actual :
    griessConwayEncode
      (rhoLocal (localFiberIntoH generatedFourthLocalFiber)
        (sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0))) =
    generatedAxisGlobalRationalPacketReal generatedAxisGlobalCanonicalFourthMiddleRationalPacket := by
  apply Prod.ext
  · funext i j
    exact generatedAxisGlobalCanonicalFourthMiddleMatrix_entry i j
  · apply Prod.ext
    · rw [generatedFourth_local_short]
      have hc := congrArg (fun P : ConwayRawSpace => P.2.1)
        generatedAxisGlobalCanonicalFourthInitialRationalPacket_actual
      rw [hc]
      exact generatedAxisGlobalRationalShortOperator_actual _ _
    · rw [generatedFourth_middle_tensor_zero]
      funext t i
      simp [generatedAxisGlobalRationalPacketReal,
        generatedAxisGlobalCanonicalFourthMiddleRationalPacket]

/-- All displayed rational coordinates equal the full genuine original Fourth axis. -/
theorem generatedAxisGlobalCanonicalFourthRationalPacket_actual :
    griessConwayEncode generatedFourthAxis =
      generatedAxisGlobalRationalPacketReal generatedAxisGlobalCanonicalFourthRationalPacket := by
  apply Prod.ext
  · funext i j
    exact (generatedAxisGlobalCanonicalFourthMatrixQ_actual i j).symm
  · apply Prod.ext
    · rw [generatedFourthAxis_local_expression]
      have hc := congrArg (fun P : ConwayRawSpace => P.2.1)
        (generatedAxisGlobalRationalTriality_of_actual _ _
          generatedAxisGlobalCanonicalFourthMiddleRationalPacket_actual)
      exact hc
    · rw [generatedAxisGlobalCanonicalFourthTensorInteger_eq]
      funext t i
      simp only [generatedAxisGlobalRationalPacketReal,
        generatedAxisGlobalCanonicalFourthRationalPacket, Rat.cast_intCast]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
