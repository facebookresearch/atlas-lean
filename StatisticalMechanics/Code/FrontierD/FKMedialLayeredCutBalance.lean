/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexMedialCutAlignment



namespace StatMech.FrontierD

noncomputable section




def FKMedialLayeredTwoCutBalance
    {T : EvenTorus} (source : Bool -> FKMedialLoopPairing T)
    (first second : T.Vertex) : Prop :=
  (FKMedialCutSplits (source false) first <->
      Not (FKMedialCutSplits (source true) first)) /\
    (FKMedialCutSplits
        (fkMedialTogglePairingAt (source false) first) second <->
      Not (FKMedialCutSplits
        (fkMedialTogglePairingAt (source true) first) second))



theorem fkMedialLoopCount_twoLayer_twoToggle_eq_of_balance
    {T : EvenTorus} (source : Bool -> FKMedialLoopPairing T)
    (first second : T.Vertex)
    (hbalance : FKMedialLayeredTwoCutBalance source first second) :
    fkMedialLoopCount T
          (fkMedialTogglePairingAt
            (fkMedialTogglePairingAt (source false) first) second) +
        fkMedialLoopCount T
          (fkMedialTogglePairingAt
            (fkMedialTogglePairingAt (source true) first) second) =
      fkMedialLoopCount T (source false) +
        fkMedialLoopCount T (source true) := by
  calc
    _ = fkMedialLoopCount T
          (fkMedialTogglePairingAt (source false) first) +
        fkMedialLoopCount T
          (fkMedialTogglePairingAt (source true) first) :=
      fkMedialLoopCount_toggle_add_toggle_eq_of_opposite
        (fkMedialTogglePairingAt (source false) first)
        (fkMedialTogglePairingAt (source true) first) second hbalance.2
    _ = _ := fkMedialLoopCount_toggle_add_toggle_eq_of_opposite
      (source false) (source true) first hbalance.1


theorem fkMedialLayeredTwoCutBalance_of_alternating
    {T : EvenTorus} (source : Bool -> FKMedialLoopPairing T)
    (first second : T.Vertex)
    (hfirst : FKMedialCutSplits (source false) first <->
      Not (FKMedialCutSplits (source true) first))
    (halternating : forall layer,
      FKMedialAlternatingTwoCut (source layer) first second) :
    FKMedialLayeredTwoCutBalance source first second := by
  constructor
  · exact hfirst
  · have hfalse := halternating false
    have htrue := halternating true
    unfold FKMedialAlternatingTwoCut at hfalse htrue
    tauto

end

end StatMech.FrontierD
