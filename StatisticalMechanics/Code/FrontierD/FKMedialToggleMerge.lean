/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKMedialToggleExact
import Code.FrontierD.PermSameCycleSplit









open Equiv SimpleGraph

namespace StatMech.FrontierD

open StatMech.FrontierA

noncomputable section

variable {T : EvenTorus}



theorem fkMedialLoopGraph_toggle_reachable_of_not_reachable
    (pairing : FKMedialLoopPairing T) (v : T.Vertex)
    (hold : ¬ (fkMedialLoopGraph T pairing).Reachable
      (fkMedialWestDart v) (fkMedialEastDart v)) :
    (fkMedialLoopGraph T (fkMedialTogglePairingAt pairing v)).Reachable
      (fkMedialWestDart v) (fkMedialEastDart v) := by
  by_contra hnew
  have hforward := fkMedialLoopCount_toggle_of_not_reachable
    T pairing v hold
  have hbackward := fkMedialLoopCount_toggle_of_not_reachable
    T (fkMedialTogglePairingAt pairing v) v hnew
  rw [fkMedialTogglePairingAt_toggle] at hbackward
  omega



theorem fkMedialBlackBoundaryPerm_toggle_merge_partition
    (pairing : FKMedialLoopPairing T) (v : T.Vertex)
    (hold : ¬ (fkMedialLoopGraph T pairing).Reachable
      (fkMedialWestDart v) (fkMedialEastDart v))
    (x : FKMedialBlackDart T) :
    (fkMedialBlackBoundaryPerm
        (fkMedialTogglePairingAt pairing v)).SameCycle
          (fkMedialBlackDart0 v) x ↔
      (fkMedialBlackBoundaryPerm pairing).SameCycle
          (fkMedialBlackDart0 v) x ∨
        (fkMedialBlackBoundaryPerm pairing).SameCycle
          (fkMedialBlackDart1 v) x := by
  let sigma := fkMedialBlackBoundaryPerm
    (fkMedialTogglePairingAt pairing v)
  let a := fkMedialBlackDart0 v
  let b := fkMedialBlackDart1 v
  have hnewReach :=
    fkMedialLoopGraph_toggle_reachable_of_not_reachable pairing v hold
  have hab : sigma.SameCycle a b := by
    apply (fkMedial_blackBoundary_sameCycle_iff_reachable
      (fkMedialTogglePairingAt pairing v) _ _).2
    exact (fkMedialBlackDarts_reachable_iff_west_east
      (fkMedialTogglePairingAt pairing v) v).2 hnewReach
  have hperm : sigma * Equiv.swap a b =
      fkMedialBlackBoundaryPerm pairing := by
    symm
    simpa only [sigma, a, b, fkMedialBlackDartSwap,
      fkMedialTogglePairingAt_toggle] using
        (fkMedialBlackBoundaryPerm_toggle
          (fkMedialTogglePairingAt pairing v) v)
  have hcount : permCycleCount (sigma * Equiv.swap a b) =
      permCycleCount sigma + 1 := by
    rw [hperm, permCycleCount_fkMedialBlackBoundaryPerm,
      permCycleCount_fkMedialBlackBoundaryPerm]
    exact (fkMedialLoopCount_toggle_of_not_reachable T pairing v hold).symm
  have hpartition := sameCycle_mul_swap_partition_of_count
    sigma (fkMedialBlackDart0_ne_dart1 v) hab hcount x
  rw [hperm] at hpartition
  exact hpartition



theorem fkMedialBlackBoundaryPerm_toggle_sameCycle_iff_of_away
    (pairing : FKMedialLoopPairing T) (v : T.Vertex)
    (hold : ¬ (fkMedialLoopGraph T pairing).Reachable
      (fkMedialWestDart v) (fkMedialEastDart v))
    {x y : FKMedialBlackDart T}
    (hx : ¬ (fkMedialBlackBoundaryPerm pairing).SameCycle
      (fkMedialBlackDart0 v) x)
    (hx' : ¬ (fkMedialBlackBoundaryPerm pairing).SameCycle
      (fkMedialBlackDart1 v) x) :
    (fkMedialBlackBoundaryPerm
        (fkMedialTogglePairingAt pairing v)).SameCycle x y ↔
      (fkMedialBlackBoundaryPerm pairing).SameCycle x y := by
  let sigma := fkMedialBlackBoundaryPerm
    (fkMedialTogglePairingAt pairing v)
  let a := fkMedialBlackDart0 v
  let b := fkMedialBlackDart1 v
  have hnewReach :=
    fkMedialLoopGraph_toggle_reachable_of_not_reachable pairing v hold
  have hab : sigma.SameCycle a b := by
    apply (fkMedial_blackBoundary_sameCycle_iff_reachable
      (fkMedialTogglePairingAt pairing v) _ _).2
    exact (fkMedialBlackDarts_reachable_iff_west_east
      (fkMedialTogglePairingAt pairing v) v).2 hnewReach
  have hperm : sigma * Equiv.swap a b =
      fkMedialBlackBoundaryPerm pairing := by
    symm
    simpa only [sigma, a, b, fkMedialBlackDartSwap,
      fkMedialTogglePairingAt_toggle] using
        (fkMedialBlackBoundaryPerm_toggle
          (fkMedialTogglePairingAt pairing v) v)
  have hcount : permCycleCount (sigma * Equiv.swap a b) =
      permCycleCount sigma + 1 := by
    rw [hperm, permCycleCount_fkMedialBlackBoundaryPerm,
      permCycleCount_fkMedialBlackBoundaryPerm]
    exact (fkMedialLoopCount_toggle_of_not_reachable T pairing v hold).symm
  have haway : ¬ sigma.SameCycle a x := by
    rw [fkMedialBlackBoundaryPerm_toggle_merge_partition pairing v hold x]
    exact not_or_intro hx hx'
  have hiff := sameCycle_mul_swap_iff_of_not_sameCycle
    sigma (fkMedialBlackDart0_ne_dart1 v) hab hcount
      (x := x) (y := y) haway
  rw [hperm] at hiff
  simpa only [sigma] using hiff.symm



theorem fkMedialBlackBoundaryPerm_toggle_sameCycle_mono_of_not_reachable
    (pairing : FKMedialLoopPairing T) (v : T.Vertex)
    (hold : ¬ (fkMedialLoopGraph T pairing).Reachable
      (fkMedialWestDart v) (fkMedialEastDart v))
    {x y : FKMedialBlackDart T}
    (hxy : (fkMedialBlackBoundaryPerm pairing).SameCycle x y) :
    (fkMedialBlackBoundaryPerm
      (fkMedialTogglePairingAt pairing v)).SameCycle x y := by
  by_cases hax : (fkMedialBlackBoundaryPerm pairing).SameCycle
      (fkMedialBlackDart0 v) x
  · have hay := hax.trans hxy
    have hnewX :=
      (fkMedialBlackBoundaryPerm_toggle_merge_partition
        pairing v hold x).2 (Or.inl hax)
    have hnewY :=
      (fkMedialBlackBoundaryPerm_toggle_merge_partition
        pairing v hold y).2 (Or.inl hay)
    exact hnewX.symm.trans hnewY
  · by_cases hbx : (fkMedialBlackBoundaryPerm pairing).SameCycle
        (fkMedialBlackDart1 v) x
    · have hby := hbx.trans hxy
      have hnewX :=
        (fkMedialBlackBoundaryPerm_toggle_merge_partition
          pairing v hold x).2 (Or.inr hbx)
      have hnewY :=
        (fkMedialBlackBoundaryPerm_toggle_merge_partition
          pairing v hold y).2 (Or.inr hby)
      exact hnewX.symm.trans hnewY
    · exact
        (fkMedialBlackBoundaryPerm_toggle_sameCycle_iff_of_away
          pairing v hold hax hbx).2 hxy



noncomputable def fkMedialBlackRepresentative
    (T : EvenTorus) (d : FKMedialDart T) : FKMedialBlackDart T := by
  classical
  by_cases hd : fkMedialCheckerColor d = false
  · exact ⟨d, hd⟩
  · refine ⟨fkMedialBondMate T d, ?_⟩
    have hne := fkMedialCheckerColor_bondMate_ne T d
    generalize hc : fkMedialCheckerColor d = c at hd hne
    generalize hb : fkMedialCheckerColor (fkMedialBondMate T d) = b at hne ⊢
    cases c <;> cases b <;> simp_all



theorem fkMedial_reachable_blackRepresentative
    (pairing : FKMedialLoopPairing T) (d : FKMedialDart T) :
    (fkMedialLoopGraph T pairing).Reachable d
      (fkMedialBlackRepresentative T d).1 := by
  classical
  unfold fkMedialBlackRepresentative
  split
  · exact SimpleGraph.Reachable.refl _
  · apply SimpleGraph.Adj.reachable
    rw [fkMedialLoopGraph_adj_iff]
    exact Or.inr rfl



theorem fkMedialLoopGraph_toggle_reachable_mono_of_not_reachable
    (pairing : FKMedialLoopPairing T) (v : T.Vertex)
    (hold : ¬ (fkMedialLoopGraph T pairing).Reachable
      (fkMedialWestDart v) (fkMedialEastDart v))
    {d e : FKMedialDart T}
    (hde : (fkMedialLoopGraph T pairing).Reachable d e) :
    (fkMedialLoopGraph T
      (fkMedialTogglePairingAt pairing v)).Reachable d e := by
  let bd := fkMedialBlackRepresentative T d
  let be := fkMedialBlackRepresentative T e
  have hbOld : (fkMedialLoopGraph T pairing).Reachable bd.1 be.1 :=
    (fkMedial_reachable_blackRepresentative pairing d).symm.trans
      (hde.trans (fkMedial_reachable_blackRepresentative pairing e))
  have hcycleOld : (fkMedialBlackBoundaryPerm pairing).SameCycle bd be :=
    (fkMedial_blackBoundary_sameCycle_iff_reachable pairing bd be).2 hbOld
  have hcycleNew :=
    fkMedialBlackBoundaryPerm_toggle_sameCycle_mono_of_not_reachable
      pairing v hold hcycleOld
  have hbNew : (fkMedialLoopGraph T
      (fkMedialTogglePairingAt pairing v)).Reachable bd.1 be.1 :=
    (fkMedial_blackBoundary_sameCycle_iff_reachable
      (fkMedialTogglePairingAt pairing v) bd be).1 hcycleNew
  exact
    (fkMedial_reachable_blackRepresentative
      (fkMedialTogglePairingAt pairing v) d).trans
        (hbNew.trans
          (fkMedial_reachable_blackRepresentative
            (fkMedialTogglePairingAt pairing v) e).symm)

end

end StatMech.FrontierD
