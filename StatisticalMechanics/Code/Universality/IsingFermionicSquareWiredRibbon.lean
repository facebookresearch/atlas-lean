/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicSquareWiredCompletion
import Code.FrontierA.PermCycleQuotientCount
import Code.FrontierA.FKTutte










open Equiv SimpleGraph

namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareWiredDartSideColor : FKIsingMedialSide → Bool
  | .west | .east => false
  | .south | .north => true

def fkIsingSquareWiredTurnColor : FKIsingSquareCornerTurn → Bool
  | .counterclockwise => false
  | .clockwise => true


def fkIsingSquareWiredCarrierColor (n : Nat) :
    FKIsingSquareWiredCarrier n → Bool
  | .dart d => fkIsingSquareWiredDartSideColor d.2
  | .bond d => !fkIsingSquareWiredTurnColor
      (fkIsingSquareSideCorner d.2).2
  | .source => true
  | .terminal => false

theorem fkIsingSquareWiredDartColor_localMate_ne
    (n : Nat)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredDartSideColor
        (FKIsingMedialDart.localMate omega d).2 ≠
      fkIsingSquareWiredDartSideColor d.2 := by
  rcases d with ⟨e, side⟩
  cases h : omega e.1 <;> cases side <;>
    simp [FKIsingMedialDart.localMate,
      fkIsingSquareWiredDartSideColor, h]

private theorem fkIsingSquareWiredBoundaryDart_turn
    (n : Nat) (hn : 0 < n) (i : FKIsingSquareWiredBoundaryDartIndex n) :
    (fkIsingSquareSideCorner
      (fkIsingSquareWiredBoundaryDart n hn i).2).2 =
      match i with
      | .bottom | .north _ => .clockwise
      | .west _ | .top => .counterclockwise := by
  cases i <;> simp [fkIsingSquareWiredBoundaryDart,
    fkIsingSquareDirectionDart_turn]

private theorem fkIsingSquareWiredBondMate_turn_ne_of_boundary
    (n : Nat) (hn : 0 < n) (i : FKIsingSquareWiredBoundaryDartIndex n) :
    (fkIsingSquareSideCorner
      (fkIsingSquareWiredBondMate n hn
        (fkIsingSquareWiredBoundaryDart n hn i)).2).2 ≠
      (fkIsingSquareSideCorner
        (fkIsingSquareWiredBoundaryDart n hn i).2).2 := by
  cases i with
  | bottom => simp [fkIsingSquareWiredBoundaryDart_turn]
  | top => simp [fkIsingSquareWiredBoundaryDart_turn]
  | west k => simp [fkIsingSquareWiredBoundaryDart_turn]
  | north k => simp [fkIsingSquareWiredBoundaryDart_turn]

theorem fkIsingSquareWiredBondMate_turn_ne
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (fkIsingSquareSideCorner (fkIsingSquareWiredBondMate n hn d).2).2 ≠
      (fkIsingSquareSideCorner d.2).2 := by
  let emb := fkIsingSquareWiredBoundaryEmbedding n hn
  let S := fkIsingSquareWiredShiftDartEquiv n hn
  by_cases hd : d ∈ Set.range emb
  · obtain ⟨i, rfl⟩ := hd
    exact fkIsingSquareWiredBondMate_turn_ne_of_boundary n hn i
  · have hSd : S.symm d = d := by
      have hforward : S d = d := by
        exact Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ hd
      apply S.injective
      rw [S.apply_symm_apply, hforward]
    have hBd : fkIsingSquareBondMate n hn d ∉ Set.range emb := by
      intro hmem
      obtain ⟨i, hi⟩ := hmem
      have hback := congrArg (fkIsingSquareBondMate n hn) hi
      rw [fkIsingSquareBondMate_involutive] at hback
      apply hd
      cases i with
      | bottom =>
          refine ⟨.west ⟨0, by omega⟩, ?_⟩
          exact (fkIsingSquareBondMate_wired_bottom n hn).symm.trans hback
      | west k =>
          by_cases hk : k.val = 0
          · have hkfin : k = ⟨0, by omega⟩ := Fin.ext hk
            refine ⟨.bottom, ?_⟩
            rw [hkfin] at hback
            exact (fkIsingSquareBondMate_wired_west_zero n hn).symm.trans hback
          · refine ⟨.north ⟨k.val - 1, by omega⟩, ?_⟩
            exact (fkIsingSquareBondMate_wired_west_succ n hn k hk).symm.trans hback
      | north k =>
          by_cases hk : k.val + 1 < 2 * n
          · refine ⟨.west ⟨k.val + 1, hk⟩, ?_⟩
            exact (fkIsingSquareBondMate_wired_north_not_last n hn k hk).symm.trans hback
          · refine ⟨.top, ?_⟩
            exact (fkIsingSquareBondMate_wired_north_last n hn k hk).symm.trans hback
      | top =>
          refine ⟨.north ⟨2 * n - 1, by omega⟩, ?_⟩
          exact (fkIsingSquareBondMate_wired_top n hn).symm.trans hback
    have hSB : S (fkIsingSquareBondMate n hn d) =
        fkIsingSquareBondMate n hn d := by
      exact Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ hBd
    have hwire : fkIsingSquareWiredBondMate n hn d =
        fkIsingSquareBondMate n hn d := by
      simp only [fkIsingSquareWiredBondMate,
        fkIsingSquareWiredBondMateEquiv, Equiv.Perm.mul_apply]
      rw [hSd]
      change S (fkIsingSquareBondMate n hn d) = _
      exact hSB
    rw [hwire]
    exact fkIsingSquareBondMate_cornerTurn_ne n hn d

theorem fkIsingSquareWiredBondColor_bondMate_ne
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (!fkIsingSquareWiredTurnColor
        (fkIsingSquareSideCorner
          (fkIsingSquareWiredBondMate n hn d).2).2) ≠
      !fkIsingSquareWiredTurnColor (fkIsingSquareSideCorner d.2).2 := by
  have hturn := fkIsingSquareWiredBondMate_turn_ne n hn d
  generalize ha : (fkIsingSquareSideCorner
    (fkIsingSquareWiredBondMate n hn d).2).2 = a at hturn ⊢
  generalize hb : (fkIsingSquareSideCorner d.2).2 = b at hturn ⊢
  cases a <;> cases b <;>
    simp_all [fkIsingSquareWiredTurnColor]



def fkIsingSquareWiredCompletedIncidenceEquiv (n : Nat) :
    Equiv.Perm (FKIsingSquareWiredCarrier n) where
  toFun
    | .dart d => .bond d
    | .bond d => .dart d
    | .source => .terminal
    | .terminal => .source
  invFun
    | .dart d => .bond d
    | .bond d => .dart d
    | .source => .terminal
    | .terminal => .source
  left_inv := by intro x; cases x <;> rfl
  right_inv := by intro x; cases x <;> rfl


def fkIsingSquareWiredTransitionEquiv
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    Equiv.Perm (FKIsingSquareWiredCarrier n) where
  toFun := fkIsingSquareWiredTransitionMate n hn omega
  invFun := fkIsingSquareWiredTransitionMate n hn omega
  left_inv := fkIsingSquareWiredTransitionMate_involutive n hn omega
  right_inv := fkIsingSquareWiredTransitionMate_involutive n hn omega

theorem fkIsingSquareWiredCarrierColor_completedIncidence_ne
    (n : Nat) (x : FKIsingSquareWiredCarrier n) :
    fkIsingSquareWiredCarrierColor n
        (fkIsingSquareWiredCompletedIncidenceEquiv n x) ≠
      fkIsingSquareWiredCarrierColor n x := by
  cases x with
  | source => simp [fkIsingSquareWiredCompletedIncidenceEquiv,
      fkIsingSquareWiredCarrierColor]
  | terminal => simp [fkIsingSquareWiredCompletedIncidenceEquiv,
      fkIsingSquareWiredCarrierColor]
  | dart d =>
      rcases d with ⟨e, side⟩
      cases side <;> simp [fkIsingSquareWiredCompletedIncidenceEquiv,
        fkIsingSquareWiredCarrierColor, fkIsingSquareWiredDartSideColor,
        fkIsingSquareWiredTurnColor, fkIsingSquareSideCorner]
  | bond d =>
      rcases d with ⟨e, side⟩
      cases side <;> simp [fkIsingSquareWiredCompletedIncidenceEquiv,
        fkIsingSquareWiredCarrierColor, fkIsingSquareWiredDartSideColor,
        fkIsingSquareWiredTurnColor, fkIsingSquareSideCorner]

theorem fkIsingSquareWiredCarrierColor_transition_ne
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x : FKIsingSquareWiredCarrier n) :
    fkIsingSquareWiredCarrierColor n
        (fkIsingSquareWiredTransitionEquiv n hn omega x) ≠
      fkIsingSquareWiredCarrierColor n x := by
  cases x with
  | source =>
      simp [fkIsingSquareWiredTransitionEquiv,
        fkIsingSquareWiredTransitionMate, fkIsingSquareWiredCarrierColor,
        fkIsingSquareWiredSourceDart, fkIsingSquareWiredBoundaryDart,
        fkIsingSquareWiredTurnColor]
  | terminal =>
      have hne := (fkIsingSquareWiredSourceDart_ne_terminalDart n hn).symm
      change fkIsingSquareWiredCarrierColor n
          (fkIsingSquareWiredTransitionMate n hn omega .terminal) ≠
        fkIsingSquareWiredCarrierColor n .terminal
      simp only [fkIsingSquareWiredTransitionMate, hne, ↓reduceIte]
      simp [fkIsingSquareWiredCarrierColor,
        fkIsingSquareWiredTerminalDart, fkIsingSquareWiredBoundaryDart,
        fkIsingSquareWiredTurnColor]
  | dart d =>
      simpa [fkIsingSquareWiredTransitionEquiv,
        fkIsingSquareWiredTransitionMate, fkIsingSquareWiredCarrierColor] using
        fkIsingSquareWiredDartColor_localMate_ne n omega d
  | bond d =>
      by_cases ha : d = fkIsingSquareWiredSourceDart n hn
      · subst d
        simp [fkIsingSquareWiredTransitionEquiv,
          fkIsingSquareWiredTransitionMate, fkIsingSquareWiredCarrierColor,
          fkIsingSquareWiredSourceDart, fkIsingSquareWiredBoundaryDart,
          fkIsingSquareWiredTurnColor]
      by_cases hb : d = fkIsingSquareWiredTerminalDart n hn
      · subst d
        have hne := (fkIsingSquareWiredSourceDart_ne_terminalDart n hn).symm
        change fkIsingSquareWiredCarrierColor n
            (fkIsingSquareWiredTransitionMate n hn omega
              (.bond (fkIsingSquareWiredTerminalDart n hn))) ≠
          fkIsingSquareWiredCarrierColor n
            (.bond (fkIsingSquareWiredTerminalDart n hn))
        simp only [fkIsingSquareWiredTransitionMate, hne, ↓reduceIte]
        simp [fkIsingSquareWiredCarrierColor,
          fkIsingSquareWiredTerminalDart, fkIsingSquareWiredBoundaryDart,
          fkIsingSquareWiredTurnColor]
      · simpa [fkIsingSquareWiredTransitionEquiv,
          fkIsingSquareWiredTransitionMate, fkIsingSquareWiredCarrierColor,
          ha, hb] using fkIsingSquareWiredBondColor_bondMate_ne n hn d


def fkIsingSquareWiredBoundaryStep
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    Equiv.Perm (FKIsingSquareWiredCarrier n) :=
  (fkIsingSquareWiredTransitionEquiv n hn omega).trans
    (fkIsingSquareWiredCompletedIncidenceEquiv n)

theorem fkIsingSquareWiredCarrierColor_boundaryStep
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x : FKIsingSquareWiredCarrier n) :
    fkIsingSquareWiredCarrierColor n
        (fkIsingSquareWiredBoundaryStep n hn omega x) =
      fkIsingSquareWiredCarrierColor n x := by
  have hT := fkIsingSquareWiredCarrierColor_transition_ne n hn omega x
  have hI := fkIsingSquareWiredCarrierColor_completedIncidence_ne n
    (fkIsingSquareWiredTransitionEquiv n hn omega x)
  simp only [fkIsingSquareWiredBoundaryStep, Equiv.trans_apply] at hI ⊢
  generalize hx : fkIsingSquareWiredCarrierColor n x = a at hT ⊢
  generalize ht : fkIsingSquareWiredCarrierColor n
    (fkIsingSquareWiredTransitionEquiv n hn omega x) = b at hT hI
  generalize hi : fkIsingSquareWiredCarrierColor n
    (fkIsingSquareWiredCompletedIncidenceEquiv n
      (fkIsingSquareWiredTransitionEquiv n hn omega x)) = c at hI ⊢
  cases a <;> cases b <;> cases c <;> simp_all



abbrev FKIsingSquareWiredBlackCarrier (n : Nat) :=
  {x : FKIsingSquareWiredCarrier n //
    fkIsingSquareWiredCarrierColor n x = false}

def fkIsingSquareWiredBlackBoundaryPerm
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    Equiv.Perm (FKIsingSquareWiredBlackCarrier n) :=
  (fkIsingSquareWiredBoundaryStep n hn omega).subtypePerm fun x => by
    rw [fkIsingSquareWiredCarrierColor_boundaryStep]

set_option maxHeartbeats 1000000 in
theorem fkIsingSquareWiredCompletedLoopGraph_adj_iff
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x y : FKIsingSquareWiredCarrier n) :
    (fkIsingSquareWiredCompletedLoopGraph n hn omega).Adj x y ↔
      y = fkIsingSquareWiredTransitionEquiv n hn omega x ∨
      y = fkIsingSquareWiredCompletedIncidenceEquiv n x := by
  cases x <;> cases y <;>
    simp [fkIsingSquareWiredCompletedLoopGraph,
      fkIsingSquareWiredLoopGraph, fkIsingSquareWiredTransitionEquiv,
      fkIsingSquareWiredCompletedIncidenceEquiv, SimpleGraph.edge_adj,
      fkIsingSquareWiredTransitionMate, fkIsingSquareWiredIncidenceMate,
      or_comm]

theorem fkIsingSquareWiredCompletedLoopGraph_adj_color_ne
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareWiredCarrier n}
    (hxy : (fkIsingSquareWiredCompletedLoopGraph n hn omega).Adj x y) :
    fkIsingSquareWiredCarrierColor n x ≠
      fkIsingSquareWiredCarrierColor n y := by
  rw [fkIsingSquareWiredCompletedLoopGraph_adj_iff] at hxy
  rcases hxy with rfl | rfl
  · exact (fkIsingSquareWiredCarrierColor_transition_ne n hn omega x).symm
  · exact (fkIsingSquareWiredCarrierColor_completedIncidence_ne n x).symm

theorem fkIsingSquareWiredBoundaryStep_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x : FKIsingSquareWiredCarrier n) :
    (fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable x
      (fkIsingSquareWiredBoundaryStep n hn omega x) := by
  let T := fkIsingSquareWiredTransitionEquiv n hn omega
  let I := fkIsingSquareWiredCompletedIncidenceEquiv n
  have hT : (fkIsingSquareWiredCompletedLoopGraph n hn omega).Adj x (T x) := by
    rw [fkIsingSquareWiredCompletedLoopGraph_adj_iff]
    exact Or.inl rfl
  have hI : (fkIsingSquareWiredCompletedLoopGraph n hn omega).Adj
      (T x) (I (T x)) := by
    rw [fkIsingSquareWiredCompletedLoopGraph_adj_iff]
    exact Or.inr rfl
  exact hT.reachable.trans (by
    simpa only [T, I, fkIsingSquareWiredBoundaryStep, Equiv.trans_apply] using
      hI.reachable)

theorem fkIsingSquareWired_reachable_of_blackBoundary_sameCycle
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x y : FKIsingSquareWiredBlackCarrier n)
    (hxy : (fkIsingSquareWiredBlackBoundaryPerm n hn omega).SameCycle x y) :
    (fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable x.1 y.1 := by
  obtain ⟨k, hk⟩ := hxy.exists_nat_pow_eq
  have hpow : ∀ k : Nat,
      (fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable x.1
        (((fkIsingSquareWiredBlackBoundaryPerm n hn omega) ^ k) x).1 := by
    intro k
    induction k with
    | zero => exact Reachable.refl _
    | succ k ih =>
        rw [pow_succ']
        change (fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable x.1
          (fkIsingSquareWiredBlackBoundaryPerm n hn omega
            (((fkIsingSquareWiredBlackBoundaryPerm n hn omega) ^ k) x)).1
        exact ih.trans (fkIsingSquareWiredBoundaryStep_reachable n hn omega _)
  simpa only [hk] using hpow k

set_option maxHeartbeats 800000 in
theorem fkIsingSquareWired_blackBoundary_sameCycle_of_walk
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareWiredCarrier n}
    (p : (fkIsingSquareWiredCompletedLoopGraph n hn omega).Walk x y)
    (hx : fkIsingSquareWiredCarrierColor n x = false)
    (hy : fkIsingSquareWiredCarrierColor n y = false) :
    (fkIsingSquareWiredBlackBoundaryPerm n hn omega).SameCycle
      ⟨x, hx⟩ ⟨y, hy⟩ := by
  let T := fkIsingSquareWiredTransitionEquiv n hn omega
  let I := fkIsingSquareWiredCompletedIncidenceEquiv n
  induction m : p.length using Nat.strong_induction_on generalizing x y with
  | _ m ih =>
      subst m
      cases p with
      | nil => exact ⟨0, rfl⟩
      | @cons _ v _ hxv p' =>
        cases p' with
        | nil =>
            exact False.elim
              ((fkIsingSquareWiredCompletedLoopGraph_adj_color_ne
                n hn omega hxv) (hx.trans hy.symm))
        | @cons _ w _ hvw rest =>
            have hcv := fkIsingSquareWiredCompletedLoopGraph_adj_color_ne
              n hn omega hxv
            have hvw' := fkIsingSquareWiredCompletedLoopGraph_adj_color_ne
              n hn omega hvw
            have hw : fkIsingSquareWiredCarrierColor n w = false := by
              generalize hcV : fkIsingSquareWiredCarrierColor n v = cv at hcv hvw'
              generalize hcW : fkIsingSquareWiredCarrierColor n w = cw at hvw' ⊢
              cases cv <;> cases cw <;> simp_all
            have htail :
                (fkIsingSquareWiredBlackBoundaryPerm n hn omega).SameCycle
                  ⟨w, hw⟩ ⟨y, hy⟩ :=
              ih rest.length (by simp only [Walk.length_cons]; omega)
                rest hw hy rfl
            have htwo :
                (fkIsingSquareWiredBlackBoundaryPerm n hn omega).SameCycle
                  ⟨x, hx⟩ ⟨w, hw⟩ := by
              rw [fkIsingSquareWiredCompletedLoopGraph_adj_iff] at hxv hvw
              rcases hxv with hxv | hxv <;> rcases hvw with hvw | hvw
              · have hxw : x = w := by
                  rw [hvw, hxv]
                  exact (T.symm_apply_apply x).symm
                exact (Subtype.ext hxw).sameCycle _
              · have hstep :
                    (fkIsingSquareWiredBlackBoundaryPerm n hn omega
                      ⟨x, hx⟩).1 = w := by
                  simp only [fkIsingSquareWiredBlackBoundaryPerm,
                    fkIsingSquareWiredBoundaryStep, Equiv.Perm.subtypePerm_apply,
                    Equiv.trans_apply]
                  rw [hvw, hxv]
                refine ⟨1, ?_⟩
                apply Subtype.ext
                simpa only [zpow_one] using hstep
              · have hstep :
                    (fkIsingSquareWiredBlackBoundaryPerm n hn omega
                      ⟨w, hw⟩).1 = x := by
                  simp only [fkIsingSquareWiredBlackBoundaryPerm,
                    fkIsingSquareWiredBoundaryStep, Equiv.Perm.subtypePerm_apply,
                    Equiv.trans_apply]
                  rw [hvw]
                  have hT : T (T v) = v := T.symm_apply_apply v
                  rw [hT, hxv]
                  exact I.symm_apply_apply x
                apply Equiv.Perm.SameCycle.symm
                refine ⟨1, ?_⟩
                apply Subtype.ext
                simpa only [zpow_one] using hstep
              · have hxw : x = w := by
                  rw [hvw, hxv]
                  exact (I.symm_apply_apply x).symm
                exact (Subtype.ext hxw).sameCycle _
            exact htwo.trans htail

theorem fkIsingSquareWired_blackBoundary_sameCycle_iff_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x y : FKIsingSquareWiredBlackCarrier n) :
    (fkIsingSquareWiredBlackBoundaryPerm n hn omega).SameCycle x y ↔
      (fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable x.1 y.1 := by
  constructor
  · exact fkIsingSquareWired_reachable_of_blackBoundary_sameCycle
      n hn omega x y
  · rintro ⟨p⟩
    exact fkIsingSquareWired_blackBoundary_sameCycle_of_walk
      n hn omega p x.2 y.2

noncomputable def fkIsingSquareWiredBlackBoundaryCycleToComponent
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    StatMech.FrontierA.PermCycleClass
        (fkIsingSquareWiredBlackBoundaryPerm n hn omega) →
      (fkIsingSquareWiredCompletedLoopGraph n hn omega).ConnectedComponent := by
  classical
  exact Quot.lift
    (fun x : FKIsingSquareWiredBlackCarrier n =>
      (fkIsingSquareWiredCompletedLoopGraph n hn omega).connectedComponentMk x.1)
    (fun x y hxy => SimpleGraph.ConnectedComponent.sound
      ((fkIsingSquareWired_blackBoundary_sameCycle_iff_reachable
        n hn omega x y).1 hxy))

theorem fkIsingSquareWiredBlackBoundaryCycleToComponent_bijective
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    Function.Bijective
      (fkIsingSquareWiredBlackBoundaryCycleToComponent n hn omega) := by
  classical
  constructor
  · intro A B hAB
    induction A using Quot.ind with
    | _ x =>
      induction B using Quot.ind with
      | _ y =>
        apply Quot.sound
        apply (fkIsingSquareWired_blackBoundary_sameCycle_iff_reachable
          n hn omega x y).2
        apply SimpleGraph.ConnectedComponent.exact
        exact hAB
  · intro C
    induction C using SimpleGraph.ConnectedComponent.ind with
    | _ x =>
      by_cases hx : fkIsingSquareWiredCarrierColor n x = false
      · exact ⟨Quot.mk _ (⟨x, hx⟩ : FKIsingSquareWiredBlackCarrier n), rfl⟩
      · have hblack : fkIsingSquareWiredCarrierColor n
            (fkIsingSquareWiredTransitionEquiv n hn omega x) = false := by
          have hne := fkIsingSquareWiredCarrierColor_transition_ne n hn omega x
          generalize hc : fkIsingSquareWiredCarrierColor n x = c at hx hne
          generalize ht : fkIsingSquareWiredCarrierColor n
            (fkIsingSquareWiredTransitionEquiv n hn omega x) = t at hne ⊢
          cases c <;> cases t <;> simp_all
        let b : FKIsingSquareWiredBlackCarrier n :=
          ⟨fkIsingSquareWiredTransitionEquiv n hn omega x, hblack⟩
        refine ⟨Quot.mk _ b, ?_⟩
        apply SimpleGraph.ConnectedComponent.sound
        apply Adj.reachable
        rw [fkIsingSquareWiredCompletedLoopGraph_adj_iff]
        apply Or.inl
        change x = fkIsingSquareWiredTransitionMate n hn omega
          (fkIsingSquareWiredTransitionMate n hn omega x)
        exact (fkIsingSquareWiredTransitionMate_involutive n hn omega x).symm



theorem permCycleCount_fkIsingSquareWiredBlackBoundaryPerm
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    StatMech.FrontierA.permCycleCount
        (fkIsingSquareWiredBlackBoundaryPerm n hn omega) =
      Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn omega).ConnectedComponent := by
  classical
  rw [← StatMech.FrontierA.natCard_permCycleClass]
  exact Nat.card_congr (Equiv.ofBijective
    (fkIsingSquareWiredBlackBoundaryCycleToComponent n hn omega)
    (fkIsingSquareWiredBlackBoundaryCycleToComponent_bijective n hn omega))

def fkIsingSquareWiredBlackWest (n : Nat)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    FKIsingSquareWiredBlackCarrier n :=
  ⟨.dart (e, .west), rfl⟩

def fkIsingSquareWiredBlackEast (n : Nat)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    FKIsingSquareWiredBlackCarrier n :=
  ⟨.dart (e, .east), rfl⟩

theorem fkIsingSquareWiredBlackWest_ne_east
    (n : Nat) (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredBlackWest n e ≠ fkIsingSquareWiredBlackEast n e := by
  intro h
  have hval := congrArg Subtype.val h
  simp [fkIsingSquareWiredBlackWest, fkIsingSquareWiredBlackEast] at hval

def fkIsingSquareWiredBlackLocalSwap (n : Nat)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    Equiv.Perm (FKIsingSquareWiredBlackCarrier n) :=
  Equiv.swap (fkIsingSquareWiredBlackWest n e)
    (fkIsingSquareWiredBlackEast n e)

theorem fkIsingSquareWiredBlackLocalSwap_isSwap
    (n : Nat) (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    (fkIsingSquareWiredBlackLocalSwap n e).IsSwap := by
  exact ⟨_, _, fkIsingSquareWiredBlackWest_ne_east n e, rfl⟩

theorem fkIsingSquareWiredBlackLocalSwap_apply_of_edge_ne
    (n : Nat) {e f : FKIsingMedialVertex (fkSquareBoxPlanar n)}
    (hef : e ≠ f) (x : FKIsingSquareWiredBlackCarrier n)
    (hx : x.1 = .dart (f, .west) ∨ x.1 = .dart (f, .east)) :
    fkIsingSquareWiredBlackLocalSwap n e x = x := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    have hval := congrArg Subtype.val h
    rcases hx with hx | hx <;> simp [fkIsingSquareWiredBlackWest, hx] at hval
    all_goals exact hef hval.symm
  · intro h
    have hval := congrArg Subtype.val h
    rcases hx with hx | hx <;> simp [fkIsingSquareWiredBlackEast, hx] at hval
    all_goals exact hef hval.symm

theorem fkIsingSquareWiredBlackLocalSwap_commute
    (n : Nat) {e f : FKIsingMedialVertex (fkSquareBoxPlanar n)}
    (hef : e ≠ f) :
    Commute (fkIsingSquareWiredBlackLocalSwap n e)
      (fkIsingSquareWiredBlackLocalSwap n f) := by
  have hww : fkIsingSquareWiredBlackWest n e ≠
      fkIsingSquareWiredBlackWest n f := by
    intro h
    apply hef
    simpa [fkIsingSquareWiredBlackWest] using congrArg Subtype.val h
  have hwe : fkIsingSquareWiredBlackWest n e ≠
      fkIsingSquareWiredBlackEast n f := by
    intro h
    simpa [fkIsingSquareWiredBlackWest,
      fkIsingSquareWiredBlackEast] using congrArg Subtype.val h
  have hew : fkIsingSquareWiredBlackEast n e ≠
      fkIsingSquareWiredBlackWest n f := by
    intro h
    simpa [fkIsingSquareWiredBlackWest,
      fkIsingSquareWiredBlackEast] using congrArg Subtype.val h
  have hee : fkIsingSquareWiredBlackEast n e ≠
      fkIsingSquareWiredBlackEast n f := by
    intro h
    apply hef
    simpa [fkIsingSquareWiredBlackEast] using congrArg Subtype.val h
  have hnodup : [fkIsingSquareWiredBlackWest n e,
      fkIsingSquareWiredBlackEast n e,
      fkIsingSquareWiredBlackWest n f,
      fkIsingSquareWiredBlackEast n f].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or]
    exact ⟨⟨fkIsingSquareWiredBlackWest_ne_east n e,
      hww, hwe⟩, ⟨⟨hew, hee⟩,
        fkIsingSquareWiredBlackWest_ne_east n f,
        by simp, List.nodup_nil⟩⟩
  exact (Equiv.Perm.disjoint_swap_swap hnodup).commute

private theorem fkIsingSquareWiredTransitionMate_setOpen_black
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (x : FKIsingSquareWiredBlackCarrier n) :
    fkIsingSquareWiredTransitionMate n hn (setOpen e.1 omega) x.1 =
      fkIsingSquareWiredTransitionMate n hn (setClosed e.1 omega)
        (fkIsingSquareWiredBlackLocalSwap n e x).1 := by
  rcases x with ⟨x, hx⟩
  cases x with
  | source =>
      have hswap : fkIsingSquareWiredBlackLocalSwap n e
          ⟨.source, hx⟩ = ⟨.source, hx⟩ := by
        apply Equiv.swap_apply_of_ne_of_ne
        · intro h
          simpa [fkIsingSquareWiredBlackWest] using congrArg Subtype.val h
        · intro h
          simpa [fkIsingSquareWiredBlackEast] using congrArg Subtype.val h
      rw [hswap]
      simp [fkIsingSquareWiredTransitionMate]
  | terminal =>
      have hswap : fkIsingSquareWiredBlackLocalSwap n e
          ⟨.terminal, hx⟩ = ⟨.terminal, hx⟩ := by
        apply Equiv.swap_apply_of_ne_of_ne
        · intro h
          simpa [fkIsingSquareWiredBlackWest] using congrArg Subtype.val h
        · intro h
          simpa [fkIsingSquareWiredBlackEast] using congrArg Subtype.val h
      rw [hswap]
      simp [fkIsingSquareWiredTransitionMate]
  | bond d =>
      have hswap : fkIsingSquareWiredBlackLocalSwap n e
          ⟨.bond d, hx⟩ = ⟨.bond d, hx⟩ := by
        apply Equiv.swap_apply_of_ne_of_ne
        · intro h
          simpa [fkIsingSquareWiredBlackWest] using congrArg Subtype.val h
        · intro h
          simpa [fkIsingSquareWiredBlackEast] using congrArg Subtype.val h
      rw [hswap]
      simp [fkIsingSquareWiredTransitionMate]
  | dart d =>
      rcases d with ⟨f, side⟩
      have hside : side = .west ∨ side = .east := by
        cases side <;> simp_all [fkIsingSquareWiredCarrierColor,
          fkIsingSquareWiredDartSideColor]
      rcases hside with rfl | rfl <;> by_cases hfe : f = e
      · subst f
        simp [fkIsingSquareWiredBlackLocalSwap,
          fkIsingSquareWiredBlackWest, fkIsingSquareWiredBlackEast,
          fkIsingSquareWiredTransitionMate, FKIsingMedialDart.localMate]
      · have hswap := fkIsingSquareWiredBlackLocalSwap_apply_of_edge_ne
          n (Ne.symm hfe) ⟨.dart (f, .west), hx⟩ (Or.inl rfl)
        rw [hswap]
        have hne : f.1 ≠ e.1 := fun h => hfe (Subtype.ext h)
        simp [fkIsingSquareWiredTransitionMate, FKIsingMedialDart.localMate,
          setOpen, setClosed, hne]
      · subst f
        simp [fkIsingSquareWiredBlackLocalSwap,
          fkIsingSquareWiredBlackWest, fkIsingSquareWiredBlackEast,
          fkIsingSquareWiredTransitionMate, FKIsingMedialDart.localMate]
      · have hswap := fkIsingSquareWiredBlackLocalSwap_apply_of_edge_ne
          n (Ne.symm hfe) ⟨.dart (f, .east), hx⟩ (Or.inr rfl)
        rw [hswap]
        have hne : f.1 ≠ e.1 := fun h => hfe (Subtype.ext h)
        simp [fkIsingSquareWiredTransitionMate, FKIsingMedialDart.localMate,
          setOpen, setClosed, hne]

set_option maxHeartbeats 1000000 in
theorem fkIsingSquareWiredBlackBoundaryPerm_setOpen
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredBlackBoundaryPerm n hn (setOpen e.1 omega) =
      fkIsingSquareWiredBlackBoundaryPerm n hn (setClosed e.1 omega) *
        fkIsingSquareWiredBlackLocalSwap n e := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  simp only [fkIsingSquareWiredBlackBoundaryPerm,
    Equiv.Perm.subtypePerm_apply, Equiv.Perm.mul_apply,
    fkIsingSquareWiredBoundaryStep, Equiv.trans_apply]
  exact congrArg (fkIsingSquareWiredCompletedIncidenceEquiv n)
    (fkIsingSquareWiredTransitionMate_setOpen_black n hn omega e x)



def fkIsingSquareWiredConfigurationOfEdges (n : Nat)
    (F : Finset (FKIsingMedialVertex (fkSquareBoxPlanar n))) :
    ConfigSpace (Sym2 (fkSquareBoxPlanar n).V) :=
  FK.edgeSetConfig (F.image Subtype.val)

@[simp] theorem fkIsingSquareWiredConfigurationOfEdges_apply
    (n : Nat) (F : Finset (FKIsingMedialVertex (fkSquareBoxPlanar n)))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredConfigurationOfEdges n F e.1 = true ↔ e ∈ F := by
  simp [fkIsingSquareWiredConfigurationOfEdges]

theorem fkIsingSquareWiredConfigurationOfEdges_insert
    (n : Nat) (F : Finset (FKIsingMedialVertex (fkSquareBoxPlanar n)))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) (he : e ∉ F) :
    fkIsingSquareWiredConfigurationOfEdges n (insert e F) =
      setOpen e.1 (fkIsingSquareWiredConfigurationOfEdges n F) := by
  funext f
  by_cases hfe : f = e.1
  · subst f
    simp [fkIsingSquareWiredConfigurationOfEdges]
  · simp [fkIsingSquareWiredConfigurationOfEdges, setOpen, hfe]
    unfold FK.edgeSetConfig
    simp [hfe]

theorem fkIsingSquareWiredConfigurationOfEdges_closed
    (n : Nat) (F : Finset (FKIsingMedialVertex (fkSquareBoxPlanar n)))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) (he : e ∉ F) :
    setClosed e.1 (fkIsingSquareWiredConfigurationOfEdges n F) =
      fkIsingSquareWiredConfigurationOfEdges n F := by
  funext f
  by_cases hfe : f = e.1
  · subst f
    have hnot : e.1 ∉ F.image Subtype.val := by simpa using he
    simp [fkIsingSquareWiredConfigurationOfEdges, hnot]
    unfold FK.edgeSetConfig
    simp [hnot]
  · simp [setClosed, hfe]



noncomputable def fkIsingSquareWiredRibbonSystem (n : Nat) (hn : 0 < n) :
    StatMech.FrontierA.RibbonPermutationSystem
      (FKIsingMedialVertex (fkSquareBoxPlanar n))
      (FKIsingSquareWiredBlackCarrier n) where
  rotation := fkIsingSquareWiredBlackBoundaryPerm n hn
    (fkIsingSquareWiredConfigurationOfEdges n ∅)
  edgeFlip := fkIsingSquareWiredBlackLocalSwap n
  edgeFlip_isSwap := fkIsingSquareWiredBlackLocalSwap_isSwap n
  edgeFlip_commute := fun e f hef =>
    fkIsingSquareWiredBlackLocalSwap_commute n hef

private theorem fkIsingSquareWiredRibbonBoundaryPerm_insert_right
    (n : Nat) (hn : 0 < n)
    (F : Finset (FKIsingMedialVertex (fkSquareBoxPlanar n)))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) (he : e ∉ F) :
    (fkIsingSquareWiredRibbonSystem n hn).boundaryPerm (insert e F) =
      (fkIsingSquareWiredRibbonSystem n hn).boundaryPerm F *
        fkIsingSquareWiredBlackLocalSwap n e := by
  let R := fkIsingSquareWiredRibbonSystem n hn
  change R.boundaryPerm (insert e F) =
    R.boundaryPerm F * R.edgeFlip e
  have hcomm : Commute (R.edgeFlip e) (R.partialEdgeFlip F) := by
    unfold StatMech.FrontierA.RibbonPermutationSystem.partialEdgeFlip
    apply Finset.noncommProd_commute
    intro f hf
    exact R.edgeFlip_commute e f fun h => he (h ▸ hf)
  rw [StatMech.FrontierA.RibbonPermutationSystem.boundaryPerm,
    R.partialEdgeFlip_insert F e (by simpa using he),
    StatMech.FrontierA.RibbonPermutationSystem.boundaryPerm]
  rw [hcomm.eq]
  simp only [mul_assoc]

theorem fkIsingSquareWiredRibbonSystem_boundaryPerm
    (n : Nat) (hn : 0 < n)
    (F : Finset (FKIsingMedialVertex (fkSquareBoxPlanar n))) :
    (fkIsingSquareWiredRibbonSystem n hn).boundaryPerm F =
      fkIsingSquareWiredBlackBoundaryPerm n hn
        (fkIsingSquareWiredConfigurationOfEdges n F) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      rw [StatMech.FrontierA.RibbonPermutationSystem.boundaryPerm_empty]
      rfl
  | @insert e F he ih =>
      calc
        (fkIsingSquareWiredRibbonSystem n hn).boundaryPerm (insert e F) =
            (fkIsingSquareWiredRibbonSystem n hn).boundaryPerm F *
              fkIsingSquareWiredBlackLocalSwap n e :=
          fkIsingSquareWiredRibbonBoundaryPerm_insert_right n hn F e he
        _ = fkIsingSquareWiredBlackBoundaryPerm n hn
              (fkIsingSquareWiredConfigurationOfEdges n F) *
                fkIsingSquareWiredBlackLocalSwap n e := by rw [ih]
        _ = fkIsingSquareWiredBlackBoundaryPerm n hn
              (setClosed e.1 (fkIsingSquareWiredConfigurationOfEdges n F)) *
                fkIsingSquareWiredBlackLocalSwap n e := by
          rw [fkIsingSquareWiredConfigurationOfEdges_closed n F e he]
        _ = fkIsingSquareWiredBlackBoundaryPerm n hn
              (setOpen e.1 (fkIsingSquareWiredConfigurationOfEdges n F)) :=
          (fkIsingSquareWiredBlackBoundaryPerm_setOpen n hn _ e).symm
        _ = fkIsingSquareWiredBlackBoundaryPerm n hn
              (fkIsingSquareWiredConfigurationOfEdges n (insert e F)) := by
          rw [fkIsingSquareWiredConfigurationOfEdges_insert n F e he]

theorem fkIsingSquareWiredRibbonSystem_boundaryComponents
    (n : Nat) (hn : 0 < n)
    (F : Finset (FKIsingMedialVertex (fkSquareBoxPlanar n))) :
    (fkIsingSquareWiredRibbonSystem n hn).boundaryComponents F =
      Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn
        (fkIsingSquareWiredConfigurationOfEdges n F)).ConnectedComponent := by
  unfold StatMech.FrontierA.RibbonPermutationSystem.boundaryComponents
  rw [fkIsingSquareWiredRibbonSystem_boundaryPerm,
    permCycleCount_fkIsingSquareWiredBlackBoundaryPerm]

end

end StatMech.Universality
