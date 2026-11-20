/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexFourByTwoTwoCycleHall
import Code.FrontierD.SixVertexTransitionRetieExact









namespace StatMech.FrontierD

namespace FourByTwoAlignedRetieLoopLoss

def omega : SixVertexArrows sixVertexFourByTwoTorus :=
  sixVertexFourByTwoArrowsOfMasks 0x0f 0x00

def eta : SixVertexArrows sixVertexFourByTwoTorus :=
  sixVertexFourByTwoArrowsOfMasks 0x0f 0x33

def lowerPairing : FKMedialLoopPairing sixVertexFourByTwoTorus :=
  fun v => decide (v.2.val = 0)

def upperPairing : FKMedialLoopPairing sixVertexFourByTwoTorus :=
  fun v => decide (2 <= v.1.val) ^^ decide (v.2.val = 1)

def source : Bool -> FKMedialLoopPairing sixVertexFourByTwoTorus
  | false => lowerPairing
  | true => upperPairing

def first : sixVertexFourByTwoTorus.Vertex :=
  sixVertexFourByTwoVertex 0 0

def second : sixVertexFourByTwoTorus.Vertex :=
  sixVertexFourByTwoVertex 1 1

def retie (pairing : FKMedialLoopPairing sixVertexFourByTwoTorus) :
    FKMedialLoopPairing sixVertexFourByTwoTorus :=
  fkMedialTogglePairingAt
    (fkMedialTogglePairingAt pairing first) second

local instance (arrows : SixVertexArrows sixVertexFourByTwoTorus) :
    Decidable arrows.IceRule :=
  inferInstanceAs (Decidable (forall v, arrows.incomingCount v = 2))

local instance (first second : SixVertexArrows sixVertexFourByTwoTorus) :
    Decidable (SixVertexLocallyDegreeTwo first second) := by
  unfold SixVertexLocallyDegreeTwo
  infer_instance

local instance (pairing : Bool)
    (arrows : SixVertexArrows sixVertexFourByTwoTorus)
    (v : sixVertexFourByTwoTorus.Vertex) :
    Decidable (fkLoopPairingCompatible pairing arrows v) := by
  unfold fkLoopPairingCompatible
  infer_instance

theorem omega_ice : omega.IceRule := by
  decide

theorem eta_ice : eta.IceRule := by
  decide

theorem locallyDegreeTwo : SixVertexLocallyDegreeTwo omega eta := by
  decide


theorem source_compatible (layer : Bool)
    (v : sixVertexFourByTwoTorus.Vertex) :
    fkLoopPairingCompatible (source layer v)
      (if layer then eta else omega) v := by
  decide +revert



theorem source_aligned_exit
    (v : sixVertexFourByTwoTorus.Vertex) (d : Fin 4)
    (hdisagree : sixVertexLocalIncomingPattern omega v d !=
      sixVertexLocalIncomingPattern eta v d)
    (hincoming : sixVertexLocalIncomingPattern omega v d = true) :
    sixVertexLocalIncomingPattern omega v
          (localMate (source true v) (localMate (source false v) d)) !=
      sixVertexLocalIncomingPattern eta v
          (localMate (source true v) (localMate (source false v) d)) := by
  decide +revert

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem lower_source_cycleCount :
    StatMech.FrontierA.permCycleCount
      (fkMedialBlackBoundaryPerm lowerPairing) = 4 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem upper_source_cycleCount :
    StatMech.FrontierA.permCycleCount
      (fkMedialBlackBoundaryPerm upperPairing) = 4 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem lower_target_cycleCount :
    StatMech.FrontierA.permCycleCount
      (fkMedialBlackBoundaryPerm (retie lowerPairing)) = 2 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem upper_target_cycleCount :
    StatMech.FrontierA.permCycleCount
      (fkMedialBlackBoundaryPerm (retie upperPairing)) = 2 := by
  decide

theorem lower_source_loopCount :
    fkMedialLoopCount sixVertexFourByTwoTorus lowerPairing = 4 := by
  rw [<- permCycleCount_fkMedialBlackBoundaryPerm]
  exact lower_source_cycleCount

theorem upper_source_loopCount :
    fkMedialLoopCount sixVertexFourByTwoTorus upperPairing = 4 := by
  rw [<- permCycleCount_fkMedialBlackBoundaryPerm]
  exact upper_source_cycleCount

theorem lower_target_loopCount :
    fkMedialLoopCount sixVertexFourByTwoTorus (retie lowerPairing) = 2 := by
  rw [<- permCycleCount_fkMedialBlackBoundaryPerm]
  exact lower_target_cycleCount

theorem upper_target_loopCount :
    fkMedialLoopCount sixVertexFourByTwoTorus (retie upperPairing) = 2 := by
  rw [<- permCycleCount_fkMedialBlackBoundaryPerm]
  exact upper_target_cycleCount


theorem totalLoopCount_loss :
    fkMedialLoopCount sixVertexFourByTwoTorus (retie (source false)) +
        fkMedialLoopCount sixVertexFourByTwoTorus (retie (source true)) + 4 =
      fkMedialLoopCount sixVertexFourByTwoTorus (source false) +
        fkMedialLoopCount sixVertexFourByTwoTorus (source true) := by
  rw [show source false = lowerPairing by rfl,
    show source true = upperPairing by rfl,
    lower_source_loopCount, upper_source_loopCount,
    lower_target_loopCount, upper_target_loopCount]



theorem not_layeredTwoCutBalanced :
    Not (FKMedialLayeredTwoCutBalanced source first second) := by
  intro hbalanced
  have hcount :=
    (fkMedialLayeredTwoCutBalanced_iff_loopCount_eq
      source first second).mp hbalanced
  change
    fkMedialLoopCount sixVertexFourByTwoTorus (retie (source false)) +
        fkMedialLoopCount sixVertexFourByTwoTorus (retie (source true)) =
      fkMedialLoopCount sixVertexFourByTwoTorus (source false) +
        fkMedialLoopCount sixVertexFourByTwoTorus (source true) at hcount
  have hloss := totalLoopCount_loss
  omega

end FourByTwoAlignedRetieLoopLoss

end StatMech.FrontierD
