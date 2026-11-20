/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKMedialToggleMerge










open SimpleGraph

namespace StatMech.FrontierD

noncomputable section


def FKMedialCutSplits
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (v : T.Vertex) : Prop :=
  (fkMedialLoopGraph T pairing).Reachable
  (fkMedialWestDart v) (fkMedialEastDart v)


theorem fkMedialCutSplits_iff_blackDartSwap_sameCycle
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (d : FKMedialBlackDart T) :
    FKMedialCutSplits pairing d.1.1 <->
      (fkMedialBlackBoundaryPerm pairing).SameCycle d
        (fkMedialBlackDartSwap d.1.1 d) := by
  obtain ⟨v, hd | hd⟩ : exists v : T.Vertex,
      d = fkMedialBlackDart0 v \/ d = fkMedialBlackDart1 v :=
    ⟨d.1.1, fkMedialBlackDart_eq_zero_or_one d⟩
  · subst d
    have hbase :
        (fkMedialBlackBoundaryPerm pairing).SameCycle
            (fkMedialBlackDart0 v) (fkMedialBlackDart1 v) <->
          FKMedialCutSplits pairing v :=
      (fkMedial_blackBoundary_sameCycle_iff_reachable pairing _ _).trans
        (fkMedialBlackDarts_reachable_iff_west_east pairing v)
    change FKMedialCutSplits pairing v <->
      (fkMedialBlackBoundaryPerm pairing).SameCycle
        (fkMedialBlackDart0 v) (fkMedialBlackDartSwap v
          (fkMedialBlackDart0 v))
    simpa [fkMedialBlackDartSwap, fkMedialBlackDart0_ne_dart1]
      using hbase.symm
  · subst d
    have hbase :
        (fkMedialBlackBoundaryPerm pairing).SameCycle
            (fkMedialBlackDart0 v) (fkMedialBlackDart1 v) <->
          FKMedialCutSplits pairing v :=
      (fkMedial_blackBoundary_sameCycle_iff_reachable pairing _ _).trans
        (fkMedialBlackDarts_reachable_iff_west_east pairing v)
    change FKMedialCutSplits pairing v <->
      (fkMedialBlackBoundaryPerm pairing).SameCycle
        (fkMedialBlackDart1 v) (fkMedialBlackDartSwap v
          (fkMedialBlackDart1 v))
    rw [Equiv.Perm.sameCycle_comm]
    simpa [fkMedialBlackDartSwap, fkMedialBlackDart0_ne_dart1]
      using hbase.symm


theorem fkMedialCutSplits_toggle_iff_not
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (v : T.Vertex) :
    FKMedialCutSplits (fkMedialTogglePairingAt pairing v) v ↔
      ¬FKMedialCutSplits pairing v := by
  constructor
  · intro hnew hold
    have hforward :=
      fkMedialLoopCount_toggle_of_reachable T pairing v hold
    have hbackward := fkMedialLoopCount_toggle_of_reachable T
      (fkMedialTogglePairingAt pairing v) v hnew
    rw [fkMedialTogglePairingAt_toggle] at hbackward
    omega
  · intro hold
    exact fkMedialLoopGraph_toggle_reachable_of_not_reachable
      pairing v hold



def FKMedialAlternatingTwoCut
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (first second : T.Vertex) : Prop :=
  FKMedialCutSplits pairing first ↔
    ¬FKMedialCutSplits (fkMedialTogglePairingAt pairing first) second


theorem fkMedialAlternatingTwoCut_self
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (v : T.Vertex) :
    FKMedialAlternatingTwoCut pairing v v := by
  rw [FKMedialAlternatingTwoCut, fkMedialCutSplits_toggle_iff_not]
  tauto



theorem fkMedialLoopCount_twoToggle_eq_of_alternating
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (first second : T.Vertex)
    (halternating : FKMedialAlternatingTwoCut pairing first second) :
    fkMedialLoopCount T
        (fkMedialTogglePairingAt
          (fkMedialTogglePairingAt pairing first) second) =
      fkMedialLoopCount T pairing := by
  classical
  by_cases hfirst : FKMedialCutSplits pairing first
  · have hsecond : ¬FKMedialCutSplits
        (fkMedialTogglePairingAt pairing first) second :=
      halternating.mp hfirst
    have hfirstCount := fkMedialLoopCount_toggle_of_reachable
      T pairing first hfirst
    have hsecondCount := fkMedialLoopCount_toggle_of_not_reachable T
      (fkMedialTogglePairingAt pairing first) second hsecond
    omega
  · have hsecond : FKMedialCutSplits
        (fkMedialTogglePairingAt pairing first) second := by
      by_contra hnot
      exact hfirst (halternating.mpr hnot)
    have hfirstCount := fkMedialLoopCount_toggle_of_not_reachable
      T pairing first hfirst
    have hsecondCount := fkMedialLoopCount_toggle_of_reachable T
      (fkMedialTogglePairingAt pairing first) second hsecond
    omega



theorem fkMedialLoopCount_toggle_add_toggle_eq_of_opposite
    {T : EvenTorus} (first second : FKMedialLoopPairing T)
    (v : T.Vertex)
    (hopposite : FKMedialCutSplits first v ↔
      ¬FKMedialCutSplits second v) :
    fkMedialLoopCount T (fkMedialTogglePairingAt first v) +
        fkMedialLoopCount T (fkMedialTogglePairingAt second v) =
      fkMedialLoopCount T first + fkMedialLoopCount T second := by
  classical
  by_cases hfirst : FKMedialCutSplits first v
  · have hsecond : ¬FKMedialCutSplits second v :=
      hopposite.mp hfirst
    have hfirstCount := fkMedialLoopCount_toggle_of_reachable
      T first v hfirst
    have hsecondCount := fkMedialLoopCount_toggle_of_not_reachable
      T second v hsecond
    omega
  · have hsecond : FKMedialCutSplits second v := by
      by_contra hnot
      exact hfirst (hopposite.mpr hnot)
    have hfirstCount := fkMedialLoopCount_toggle_of_not_reachable
      T first v hfirst
    have hsecondCount := fkMedialLoopCount_toggle_of_reachable
      T second v hsecond
    omega



theorem fkMedialAlternatingTwoCut_of_loopCount_twoToggle_eq
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (first second : T.Vertex)
    (hcount : fkMedialLoopCount T
        (fkMedialTogglePairingAt
          (fkMedialTogglePairingAt pairing first) second) =
      fkMedialLoopCount T pairing) :
    FKMedialAlternatingTwoCut pairing first second := by
  classical
  by_cases hfirst : FKMedialCutSplits pairing first
  · constructor
    · intro _ hsecond
      have hfirstCount := fkMedialLoopCount_toggle_of_reachable
        T pairing first hfirst
      have hsecondCount := fkMedialLoopCount_toggle_of_reachable T
        (fkMedialTogglePairingAt pairing first) second hsecond
      omega
    · intro _
      exact hfirst
  · constructor
    · intro h
      exact False.elim (hfirst h)
    · intro hsecond
      have hfirstCount := fkMedialLoopCount_toggle_of_not_reachable
        T pairing first hfirst
      have hsecondCount := fkMedialLoopCount_toggle_of_not_reachable T
        (fkMedialTogglePairingAt pairing first) second hsecond
      omega




theorem fkMedialBlackBoundary_successors_alternate
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (v : T.Vertex) :
    let source := fkMedialBlackBoundaryPerm pairing
    let target := fkMedialBlackBoundaryPerm
      (fkMedialTogglePairingAt pairing v)
    source.SameCycle (fkMedialBlackDart0 v) (fkMedialBlackDart1 v) ↔
      ¬target.SameCycle
        (source (fkMedialBlackDart0 v))
        (source (fkMedialBlackDart1 v)) := by
  dsimp only
  let source := fkMedialBlackBoundaryPerm pairing
  let target := fkMedialBlackBoundaryPerm
    (fkMedialTogglePairingAt pairing v)
  let a := fkMedialBlackDart0 v
  let b := fkMedialBlackDart1 v
  have htarget : target = source * Equiv.swap a b := by
    simpa [source, target, a, b, fkMedialBlackDartSwap] using
      fkMedialBlackBoundaryPerm_toggle pairing v
  have htargetA : target a = source b := by
    rw [htarget]
    simp [a, b]
  have htargetB : target b = source a := by
    rw [htarget]
    simp [a, b]
  have hcycleImage :
      target.SameCycle (source a) (source b) ↔
        target.SameCycle a b := by
    rw [← htargetB, ← htargetA]
    constructor
    · intro h
      have hb : target.SameCycle b (target b) :=
        Equiv.Perm.SameCycle.rfl.apply_right
      have ha : target.SameCycle a (target a) :=
        Equiv.Perm.SameCycle.rfl.apply_right
      exact (hb.trans (h.trans ha.symm)).symm
    · intro h
      exact h.symm.apply_left.apply_right
  rw [hcycleImage]
  have hsource : source.SameCycle a b ↔
      FKMedialCutSplits pairing v :=
    (fkMedial_blackBoundary_sameCycle_iff_reachable pairing a b).trans
      (fkMedialBlackDarts_reachable_iff_west_east pairing v)
  have htargetCut : target.SameCycle a b ↔
      FKMedialCutSplits (fkMedialTogglePairingAt pairing v) v :=
    (fkMedial_blackBoundary_sameCycle_iff_reachable
      (fkMedialTogglePairingAt pairing v) a b).trans
        (fkMedialBlackDarts_reachable_iff_west_east
          (fkMedialTogglePairingAt pairing v) v)
  rw [hsource, htargetCut, fkMedialCutSplits_toggle_iff_not]
  tauto

end

end StatMech.FrontierD
