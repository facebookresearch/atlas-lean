/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKMedialBoundaryToggleParity
import Code.FrontierA.PermSameCycleSwap

open SimpleGraph Equiv

namespace StatMech.FrontierD

variable {T : EvenTorus}



theorem fkMedialBlackDarts_reachable_iff_west_east
    (pairing : FKMedialLoopPairing T) (v : T.Vertex) :
    (fkMedialLoopGraph T pairing).Reachable
        (fkMedialBlackDart0 v).1 (fkMedialBlackDart1 v).1 <->
      (fkMedialLoopGraph T pairing).Reachable
        (fkMedialWestDart v) (fkMedialEastDart v) := by
  let G := fkMedialLoopGraph T pairing
  have hlocal (d : FKMedialDart T) :
      G.Reachable d (fkMedialLocalMate pairing d) := by
    apply Adj.reachable
    rw [fkMedialLoopGraph_adj_iff]
    exact Or.inl rfl
  by_cases hp : fkMedialVertexParity v <;> cases hpair : pairing v
  · have hsE := hlocal (v, .south)
    have hnW := hlocal (v, .north)
    simp only [fkMedialLocalMate, hpair] at hsE hnW
    simp [fkMedialBlackDart0, fkMedialBlackDart1, hp,
      fkMedialWestDart, fkMedialEastDart]
    constructor
    · intro h
      exact hnW.symm.trans (h.symm.trans hsE)
    · intro h
      exact hsE.trans (h.symm.trans hnW.symm)
  · have hsW := hlocal (v, .south)
    have hnE := hlocal (v, .north)
    simp only [fkMedialLocalMate, hpair] at hsW hnE
    simp [fkMedialBlackDart0, fkMedialBlackDart1, hp,
      fkMedialWestDart, fkMedialEastDart]
    constructor
    · intro h
      exact hsW.symm.trans (h.trans hnE)
    · intro h
      exact hsW.trans (h.trans hnE.symm)
  · simp [fkMedialBlackDart0, fkMedialBlackDart1, hp,
      fkMedialWestDart, fkMedialEastDart]
  · simp [fkMedialBlackDart0, fkMedialBlackDart1, hp,
      fkMedialWestDart, fkMedialEastDart]



theorem fkMedialLoopCount_toggle_of_reachable
    (T : EvenTorus) (pairing : FKMedialLoopPairing T) (v : T.Vertex)
    (hconn : (fkMedialLoopGraph T pairing).Reachable
      (fkMedialWestDart v) (fkMedialEastDart v)) :
    fkMedialLoopCount T pairing + 1 =
      fkMedialLoopCount T (fkMedialTogglePairingAt pairing v) := by
  let sigma := fkMedialBlackBoundaryPerm pairing
  have hab : sigma.SameCycle
      (fkMedialBlackDart0 v) (fkMedialBlackDart1 v) := by
    apply (fkMedial_blackBoundary_sameCycle_iff_reachable pairing _ _).2
    exact (fkMedialBlackDarts_reachable_iff_west_east pairing v).2 hconn
  have hnewCycle :
      ¬(fkMedialBlackBoundaryPerm (fkMedialTogglePairingAt pairing v)).SameCycle
        (fkMedialBlackDart0 v) (fkMedialBlackDart1 v) := by
    rw [fkMedialBlackBoundaryPerm_toggle]
    exact StatMech.FrontierA.not_sameCycle_mul_swap_of_sameCycle sigma
      (fkMedialBlackDart0_ne_dart1 v) hab
  have hdisc :
      ¬(fkMedialLoopGraph T (fkMedialTogglePairingAt pairing v)).Reachable
        (fkMedialWestDart v) (fkMedialEastDart v) := by
    intro hreach
    apply hnewCycle
    apply (fkMedial_blackBoundary_sameCycle_iff_reachable
      (fkMedialTogglePairingAt pairing v) _ _).2
    exact (fkMedialBlackDarts_reachable_iff_west_east
      (fkMedialTogglePairingAt pairing v) v).2 hreach
  have hcount := fkMedialLoopCount_toggle_of_not_reachable T
    (fkMedialTogglePairingAt pairing v) v hdisc
  rwa [fkMedialTogglePairingAt_toggle] at hcount

end StatMech.FrontierD
