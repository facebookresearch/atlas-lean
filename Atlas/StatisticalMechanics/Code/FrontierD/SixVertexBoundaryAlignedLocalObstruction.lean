/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexAlignedFirstReturn












namespace StatMech.FrontierD



def boundaryAlignedTransportedLocalColor
    (p q : SixVertexLocalIncomingPattern)
    (pairingP pairingQ vertexParity : Bool) (entrance : Fin 4)
    (select0 select1 targetPairingP targetPairingQ layer : Bool)
    (slot : Fin 4) : Bool :=
  let baseP := strandSlot pairingP entrance
  let baseQ := boundaryAlignedSlotQRaw vertexParity
    pairingP pairingQ entrance
  let targetPairing := if layer then targetPairingQ else targetPairingP
  let branch := strandSlot targetPairing slot !=
    (if layer then baseQ else baseP)
  let selected := if branch then select1 else select0
  let sourceLayer := layer != selected
  let sourcePattern := if sourceLayer then q else p
  let sourceBase := if sourceLayer then baseQ else baseP
  let sourceSlot := if selected then
      if branch then !sourceBase else sourceBase
    else strandSlot targetPairing slot
  vertexParity ^^ horizontalSlot sourcePattern sourceSlot



def boundaryAlignedTransportedLocalPattern
    (p q : SixVertexLocalIncomingPattern)
    (pairingP pairingQ vertexParity : Bool) (entrance : Fin 4)
    (select0 select1 targetPairingP targetPairingQ layer : Bool) :
    SixVertexLocalIncomingPattern :=
  fun side => (vertexParity ^^ sideVertical side) ^^
    boundaryAlignedTransportedLocalColor p q pairingP pairingQ vertexParity
      entrance select0 select1 targetPairingP targetPairingQ layer side

def boundaryAlignedObstructionP : SixVertexLocalIncomingPattern :=
  ![false, true, false, true]

def boundaryAlignedObstructionQ : SixVertexLocalIncomingPattern :=
  ![false, true, true, false]

theorem boundaryAlignedObstructionP_ice :
    boundaryAlignedObstructionP.Ice := by decide

theorem boundaryAlignedObstructionQ_ice :
    boundaryAlignedObstructionQ.Ice := by decide

theorem boundaryAlignedObstruction_degree_two :
    (sixVertexLocalDisagreementSides
      boundaryAlignedObstructionP boundaryAlignedObstructionQ).card = 2 := by
  decide

theorem boundaryAlignedObstruction_compatible :
    compatible false boundaryAlignedObstructionP /\
      compatible true boundaryAlignedObstructionQ := by
  unfold compatible boundaryAlignedObstructionP
    boundaryAlignedObstructionQ
  decide


theorem boundaryAlignedObstruction_target_patterns
    (targetPairingP targetPairingQ : Bool) :
    boundaryAlignedTransportedLocalPattern
        boundaryAlignedObstructionP boundaryAlignedObstructionQ
        false true false 2 false true
        targetPairingP targetPairingQ false = ![true, true, false, false] /\
      boundaryAlignedTransportedLocalPattern
        boundaryAlignedObstructionP boundaryAlignedObstructionQ
        false true false 2 false true
        targetPairingP targetPairingQ true = ![false, false, true, true] := by
  cases targetPairingP <;> cases targetPairingQ <;>
    decide

theorem boundaryAlignedObstruction_target_ice
    (targetPairingP targetPairingQ layer : Bool) :
    (boundaryAlignedTransportedLocalPattern
      boundaryAlignedObstructionP boundaryAlignedObstructionQ
      false true false 2 false true
      targetPairingP targetPairingQ layer).Ice := by
  cases targetPairingP <;> cases targetPairingQ <;> cases layer <;>
    decide



theorem boundaryAlignedTransport_no_exact_localC
    (targetPairingP targetPairingQ : Bool) :
    localCIndicator
          (boundaryAlignedTransportedLocalPattern
            boundaryAlignedObstructionP boundaryAlignedObstructionQ
            false true false 2 false true
            targetPairingP targetPairingQ false) +
        localCIndicator
          (boundaryAlignedTransportedLocalPattern
            boundaryAlignedObstructionP boundaryAlignedObstructionQ
            false true false 2 false true
            targetPairingP targetPairingQ true) ≠
      localCIndicator boundaryAlignedObstructionP +
        localCIndicator boundaryAlignedObstructionQ := by
  cases targetPairingP <;> cases targetPairingQ <;>
    decide

end StatMech.FrontierD
