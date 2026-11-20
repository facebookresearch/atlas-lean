/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.DecorationWalkSign
import Code.Onsager.DecorationTurnTransfer








namespace StatMech.Onsager

open BigOperators



theorem ons_decCycleFirstReturn_weight_eq_neg_spinCharacter
    {L : ℕ} [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hsnd : q.snd = ons_dartRev L d)
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (a b : Fin 2) :
    ons_edgeWeight
        (ons_KWmatWeightedPhase L weight ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b))
        (ons_decCycleFirstReturn q) =
      -(ons_spinCharacter a b
          (ons_evenHomology L (ons_walkOriginalEdges q)) : ℂ) *
        ∏ edge ∈ ons_walkOriginalEdges q, weight edge := by
  exact ons_decCycleFirstReturn_weight_eq_spinCharacter q hq hsnd
    weight a b
    (ons_decCycle_turnProduct_eq_neg_spinCharacter L q hq hsnd)


theorem ons_firstReturnWeight_decCycle_eq_neg_spinCharacter
    {L : ℕ} [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hsnd : q.snd = ons_dartRev L d)
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (a b : Fin 2) :
    ons_firstReturnWeight
        (ons_KWmatWeightedPhase L weight ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b))
        d (ons_dartRev L d) (ons_decCycleFirstReturn q) =
      -(ons_spinCharacter a b
          (ons_evenHomology L (ons_walkOriginalEdges q)) : ℂ) *
        ∏ edge ∈ ons_walkOriginalEdges q, weight edge := by
  rw [ons_firstReturnWeight_decCycle q hq hsnd]
  exact ons_decCycleFirstReturn_weight_eq_neg_spinCharacter
    q hq hsnd weight a b

end StatMech.Onsager
