/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicSquareWiredCompletion









open Finset SimpleGraph

namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section


theorem fkIsingSquareWiredBondMate_cornerTurn_ne
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (fkIsingSquareSideCorner (fkIsingSquareWiredBondMate n hn d).2).2 ≠
      (fkIsingSquareSideCorner d.2).2 := by
  classical
  let f := fkIsingSquareWiredBoundaryEmbedding n hn
  let sigma := fkIsingSquareWiredShiftDartEquiv n hn
  by_cases hd : ∃ i, d = fkIsingSquareWiredBoundaryDart n hn i
  · obtain ⟨i, rfl⟩ := hd
    cases i with
    | bottom =>
        rw [fkIsingSquareWiredBondMate_bottom]
        simp [fkIsingSquareWiredBoundaryDart]
    | west k =>
        rw [fkIsingSquareWiredBondMate_west]
        simp [fkIsingSquareWiredBoundaryDart]
    | north k =>
        rw [fkIsingSquareWiredBondMate_north]
        simp [fkIsingSquareWiredBoundaryDart]
    | top =>
        rw [fkIsingSquareWiredBondMate_top]
        simp [fkIsingSquareWiredBoundaryDart]
  · have hdRange : d ∉ Set.range f := by
      rintro ⟨i, hi⟩
      exact hd ⟨i, hi.symm⟩
    have hsigma : sigma d = d := by
      exact Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ f hdRange
    have hsigmaInv : sigma.symm d = d := by
      apply sigma.injective
      simpa [hsigma]
    have hBd : fkIsingSquareBondMate n hn d ∉ Set.range f := by
      intro hmem
      obtain ⟨i, hi⟩ := hmem
      have hB : fkIsingSquareBondMate n hn (f i) = d := by
        calc
          fkIsingSquareBondMate n hn (f i) =
              fkIsingSquareBondMate n hn (fkIsingSquareBondMate n hn d) :=
            congrArg (fkIsingSquareBondMate n hn) hi
          _ = d := fkIsingSquareBondMate_involutive n hn d
      apply hd
      cases i with
      | bottom =>
          refine ⟨.west ⟨0, by omega⟩, ?_⟩
          change fkIsingSquareBondMate n hn
            (fkIsingSquareWiredBoundaryDart n hn .bottom) = d at hB
          rw [fkIsingSquareBondMate_wired_bottom] at hB
          exact hB.symm
      | west k =>
          by_cases hk : k.val = 0
          · have hk0 : k = ⟨0, by omega⟩ := Fin.ext hk
            refine ⟨.bottom, ?_⟩
            change fkIsingSquareBondMate n hn
              (fkIsingSquareWiredBoundaryDart n hn (.west k)) = d at hB
            rw [hk0] at hB
            rw [fkIsingSquareBondMate_wired_west_zero] at hB
            exact hB.symm
          · refine ⟨.north ⟨k.val - 1, by omega⟩, ?_⟩
            change fkIsingSquareBondMate n hn
              (fkIsingSquareWiredBoundaryDart n hn (.west k)) = d at hB
            rw [fkIsingSquareBondMate_wired_west_succ n hn k hk] at hB
            exact hB.symm
      | north k =>
          by_cases hk : k.val + 1 < 2 * n
          · refine ⟨.west ⟨k.val + 1, hk⟩, ?_⟩
            change fkIsingSquareBondMate n hn
              (fkIsingSquareWiredBoundaryDart n hn (.north k)) = d at hB
            rw [fkIsingSquareBondMate_wired_north_not_last n hn k hk] at hB
            exact hB.symm
          · refine ⟨.top, ?_⟩
            change fkIsingSquareBondMate n hn
              (fkIsingSquareWiredBoundaryDart n hn (.north k)) = d at hB
            rw [fkIsingSquareBondMate_wired_north_last n hn k hk] at hB
            exact hB.symm
      | top =>
          refine ⟨.north ⟨2 * n - 1, by omega⟩, ?_⟩
          change fkIsingSquareBondMate n hn
            (fkIsingSquareWiredBoundaryDart n hn .top) = d at hB
          rw [fkIsingSquareBondMate_wired_top] at hB
          exact hB.symm
    have hsigmaB : sigma (fkIsingSquareBondMate n hn d) =
        fkIsingSquareBondMate n hn d := by
      exact Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ f hBd
    change (fkIsingSquareSideCorner
      (sigma (fkIsingSquareBondMate n hn (sigma.symm d))).2).2 ≠ _
    rw [hsigmaInv, hsigmaB]
    exact fkIsingSquareBondMate_cornerTurn_ne n hn d


def fkIsingSquareWiredCarrierPhase (n : Nat) :
    FKIsingSquareWiredCarrier n → Fin 4
  | .source => 0
  | .terminal => 1
  | .dart d =>
      if (fkIsingSquareSideCorner d.2).2 = .clockwise then 2 else 3
  | .bond d =>
      if (fkIsingSquareSideCorner d.2).2 = .clockwise then 1 else 0

theorem fkIsingSquareWiredLoopGraph_adj_phase_succ
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareWiredCarrier n}
    (hxy : (fkIsingSquareWiredLoopGraph n hn omega).Adj x y) :
    fkIsingSquareWiredCarrierPhase n y =
      fkIsingSquareWiredCarrierPhase n x + 1 ∨
    fkIsingSquareWiredCarrierPhase n x =
      fkIsingSquareWiredCarrierPhase n y + 1 := by
  rcases hxy with hinc | htrans
  · rcases hinc with ⟨hxs, hxt, rfl⟩
    cases x with
    | source => exact False.elim (hxs rfl)
    | terminal => exact False.elim (hxt rfl)
    | dart d =>
        cases hcorner : (fkIsingSquareSideCorner d.2).2 <;>
          simp [fkIsingSquareWiredCarrierPhase,
            fkIsingSquareWiredIncidenceMate, hcorner]
    | bond d =>
        cases hcorner : (fkIsingSquareSideCorner d.2).2 <;>
          simp [fkIsingSquareWiredCarrierPhase,
            fkIsingSquareWiredIncidenceMate, hcorner]
  · subst y
    cases x with
    | source =>
        simp [fkIsingSquareWiredCarrierPhase,
          fkIsingSquareWiredTransitionMate,
          fkIsingSquareWiredSourceDart,
          fkIsingSquareWiredBoundaryDart]
    | terminal =>
        simp [fkIsingSquareWiredCarrierPhase,
          fkIsingSquareWiredTransitionMate,
          fkIsingSquareWiredTerminalDart,
          fkIsingSquareWiredBoundaryDart]
    | dart d =>
        have hne := fkIsingSquare_localMate_cornerTurn_ne n omega d
        cases hd : (fkIsingSquareSideCorner d.2).2 <;>
          cases hm : (fkIsingSquareSideCorner
            (FKIsingMedialDart.localMate omega d).2).2 <;>
          simp_all [fkIsingSquareWiredCarrierPhase,
            fkIsingSquareWiredTransitionMate]
    | bond d =>
        by_cases hs : d = fkIsingSquareWiredSourceDart n hn
        · subst d
          simp [fkIsingSquareWiredCarrierPhase, fkIsingSquareWiredTransitionMate,
            fkIsingSquareWiredSourceDart,
            fkIsingSquareWiredBoundaryDart]
        by_cases ht : d = fkIsingSquareWiredTerminalDart n hn
        · subst d
          left
          simp only [fkIsingSquareWiredTransitionMate]
          rw [if_neg hs]
          simp only [if_true]
          simp [fkIsingSquareWiredCarrierPhase,
            fkIsingSquareWiredTerminalDart,
            fkIsingSquareWiredBoundaryDart]
        · have hne := fkIsingSquareWiredBondMate_cornerTurn_ne n hn d
          cases hd : (fkIsingSquareSideCorner d.2).2 <;>
            cases hm : (fkIsingSquareSideCorner
              (fkIsingSquareWiredBondMate n hn d).2).2 <;>
            simp_all [fkIsingSquareWiredCarrierPhase,
              fkIsingSquareWiredTransitionMate, hs, ht]


def fkIsingSquareWiredIncidenceGraph (n : Nat) :
    SimpleGraph (FKIsingSquareWiredCarrier n) where
  Adj x y := x ≠ .source ∧ x ≠ .terminal ∧
    y = fkIsingSquareWiredIncidenceMate n x
  symm := by
    rintro x _ ⟨hxs, hxt, rfl⟩
    cases x with
    | source => exact False.elim (hxs rfl)
    | terminal => exact False.elim (hxt rfl)
    | dart d => simp [fkIsingSquareWiredIncidenceMate]
    | bond d => simp [fkIsingSquareWiredIncidenceMate]
  loopless := ⟨by
    rintro x ⟨hxs, hxt, hx⟩
    cases x with
    | source => exact hxs rfl
    | terminal => exact hxt rfl
    | dart d => simp [fkIsingSquareWiredIncidenceMate] at hx
    | bond d => simp [fkIsingSquareWiredIncidenceMate] at hx⟩

theorem fkIsingSquareWiredLoopGraph_isAlternating_incidence
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (fkIsingSquareWiredLoopGraph n hn omega).IsAlternating
      (fkIsingSquareWiredIncidenceGraph n) := by
  intro v w w' hne hvw hvw'
  rcases hvw with hi | ht <;> rcases hvw' with hi' | ht'
  · exact False.elim (hne (hi.2.2.trans hi'.2.2.symm))
  · simp only [fkIsingSquareWiredIncidenceGraph]
    constructor
    · intro _ hi''
      exact fkIsingSquareWiredIncidenceMate_ne_transitionMate n hn omega v
        hi''.1 hi''.2.1 (hi''.2.2.symm.trans ht')
    · intro _
      exact hi
  · simp only [fkIsingSquareWiredIncidenceGraph]
    constructor
    · intro hi''
      exfalso
      exact (fkIsingSquareWiredIncidenceMate_ne_transitionMate n hn omega v
        hi''.1 hi''.2.1) (hi''.2.2.symm.trans ht)
    · intro hnot
      exact False.elim (hnot hi')
  · exact False.elim (hne (ht.trans ht'.symm))


def fkIsingSquareWiredCarrierOddClass (n : Nat) :
    FKIsingSquareWiredCarrier n → Prop
  | .source => False
  | .terminal => True
  | .dart d =>
      (fkIsingSquareSideCorner d.2).2 = .counterclockwise
  | .bond d =>
      (fkIsingSquareSideCorner d.2).2 = .clockwise

theorem fkIsingSquareWiredLoopGraph_adj_oddClass
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareWiredCarrier n}
    (hxy : (fkIsingSquareWiredLoopGraph n hn omega).Adj x y) :
    fkIsingSquareWiredCarrierOddClass n x ↔
      ¬ fkIsingSquareWiredCarrierOddClass n y := by
  rcases hxy with hinc | htrans
  · rcases hinc with ⟨hxs, hxt, rfl⟩
    cases x with
    | source => exact False.elim (hxs rfl)
    | terminal => exact False.elim (hxt rfl)
    | dart d =>
        cases hcorner : (fkIsingSquareSideCorner d.2).2 <;>
          simp [fkIsingSquareWiredCarrierOddClass,
            fkIsingSquareWiredIncidenceMate, hcorner]
    | bond d =>
        cases hcorner : (fkIsingSquareSideCorner d.2).2 <;>
          simp [fkIsingSquareWiredCarrierOddClass,
            fkIsingSquareWiredIncidenceMate, hcorner]
  · subst y
    cases x with
    | source =>
        simp [fkIsingSquareWiredCarrierOddClass,
          fkIsingSquareWiredTransitionMate,
          fkIsingSquareWiredSourceDart,
          fkIsingSquareWiredBoundaryDart]
    | terminal =>
        simp [fkIsingSquareWiredCarrierOddClass,
          fkIsingSquareWiredTransitionMate,
          fkIsingSquareWiredTerminalDart,
          fkIsingSquareWiredBoundaryDart]
    | dart d =>
        have hne := fkIsingSquare_localMate_cornerTurn_ne n omega d
        cases hd : (fkIsingSquareSideCorner d.2).2 <;>
          cases hm : (fkIsingSquareSideCorner
            (FKIsingMedialDart.localMate omega d).2).2 <;>
          simp_all [fkIsingSquareWiredCarrierOddClass,
            fkIsingSquareWiredTransitionMate]
    | bond d =>
        by_cases hs : d = fkIsingSquareWiredSourceDart n hn
        · subst d
          simp [fkIsingSquareWiredCarrierOddClass,
            fkIsingSquareWiredTransitionMate,
            fkIsingSquareWiredSourceDart,
            fkIsingSquareWiredBoundaryDart]
        by_cases ht : d = fkIsingSquareWiredTerminalDart n hn
        · subst d
          simp only [fkIsingSquareWiredTransitionMate]
          rw [if_neg hs]
          simp [fkIsingSquareWiredCarrierOddClass,
            fkIsingSquareWiredTerminalDart,
            fkIsingSquareWiredBoundaryDart]
        · have hne := fkIsingSquareWiredBondMate_cornerTurn_ne n hn d
          cases hd : (fkIsingSquareSideCorner d.2).2 <;>
            cases hm : (fkIsingSquareSideCorner
              (fkIsingSquareWiredBondMate n hn d).2).2 <;>
            simp_all [fkIsingSquareWiredCarrierOddClass,
              fkIsingSquareWiredTransitionMate, hs, ht]

theorem fkIsingSquareWiredExplorationPath_oddClass
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (i : Nat)
    (hi : i ≤ (fkIsingSquareWiredExplorationPath n hn omega :
      (fkIsingSquareWiredLoopGraph n hn omega).Walk .source .terminal).length) :
    fkIsingSquareWiredCarrierOddClass n
        ((fkIsingSquareWiredExplorationPath n hn omega :
          (fkIsingSquareWiredLoopGraph n hn omega).Walk
            .source .terminal).getVert i) ↔
      Odd i := by
  let p : (fkIsingSquareWiredLoopGraph n hn omega).Walk
      (.source : FKIsingSquareWiredCarrier n) .terminal :=
    fkIsingSquareWiredExplorationPath n hn omega
  change fkIsingSquareWiredCarrierOddClass n (p.getVert i) ↔ Odd i
  induction i with
  | zero => simp [p, fkIsingSquareWiredCarrierOddClass]
  | succ i ih =>
      have hi0 : i < p.length := by simpa [p] using hi
      have hadj := p.adj_getVert_succ hi0
      have hflip := fkIsingSquareWiredLoopGraph_adj_oddClass
        n hn omega hadj
      have ih' := ih (by simpa [p] using Nat.le_of_lt hi0)
      have hrev : fkIsingSquareWiredCarrierOddClass n (p.getVert (i + 1)) ↔
          ¬ fkIsingSquareWiredCarrierOddClass n (p.getVert i) := by
        tauto
      rw [hrev, ih', Nat.odd_add_one]



theorem fkIsingSquareWired_localMate_infix_of_counterclockwise
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (side : FKIsingMedialSide)
    (hccw : (fkIsingSquareSideCorner side).2 = .counterclockwise)
    (h : fkIsingSquareWiredPathUsesLocalSide n hn omega e side) :
    [(.dart (FKIsingMedialDart.localMate omega (e, side)) :
        FKIsingSquareWiredCarrier n), .dart (e, side)] <:+:
      fkIsingSquareWiredExplorationOrder n hn omega := by
  let H := fkIsingSquareWiredLoopGraph n hn omega
  let M := fkIsingSquareWiredIncidenceGraph n
  let p : H.Walk (.source : FKIsingSquareWiredCarrier n) .terminal :=
    fkIsingSquareWiredExplorationPath n hn omega
  let x : FKIsingSquareWiredCarrier n := .dart (e, side)
  let y : FKIsingSquareWiredCarrier n :=
    .dart (FKIsingMedialDart.localMate omega (e, side))
  rcases fkIsingSquareWired_localMate_infix_explorationOrder
      n hn omega e side h with hforward | hbackward
  · exfalso
    have hx : x ∈ p.support := hforward.mem (by simp [x])
    have hy : y ∈ p.support := hforward.mem (by simp [y])
    have hidx := idxOf_succ_of_pair_infix_nodup
      (fkIsingSquareWiredExplorationOrder_nodup n hn omega) hforward
    change p.support.idxOf y = p.support.idxOf x + 1 at hidx
    have hilt : p.support.idxOf x < p.length := by
      have hylt : p.support.idxOf y < p.support.length :=
        List.idxOf_lt_length_iff.mpr hy
      rw [p.length_support, hidx] at hylt
      omega
    have hgetx : p.getVert (p.support.idxOf x) = x :=
      p.getVert_support_idxOf hx
    have hgety : p.getVert (p.support.idxOf x + 1) = y := by
      have hy' := p.getVert_support_idxOf hy
      rw [hidx] at hy'
      exact hy'
    have hfirst : ¬ M.Adj (p.getVert 0) (p.getVert 1) := by
      intro hinc
      rcases hinc with ⟨hsource, _, _⟩
      simpa [p] using hsource
    have hincIff :=
      isAlternating_path_edge_iff_odd
        (fkIsingSquareWiredLoopGraph_isAlternating_incidence n hn omega)
        p (fkIsingSquareWiredExplorationPath n hn omega).isPath hfirst
        (p.support.idxOf x) hilt
    have hnotinc : ¬ M.Adj
        (p.getVert (p.support.idxOf x))
        (p.getVert (p.support.idxOf x + 1)) := by
      rw [hgetx, hgety]
      dsimp only [M, x, y]
      simp only [fkIsingSquareWiredIncidenceGraph]
      simp [fkIsingSquareWiredIncidenceMate]
    have hnotodd : ¬ Odd (p.support.idxOf x) := fun hodd =>
      hnotinc (hincIff.mpr hodd)
    have hclass : fkIsingSquareWiredCarrierOddClass n x ↔
        Odd (p.support.idxOf x) := by
      have hpath := fkIsingSquareWiredExplorationPath_oddClass n hn omega
        (p.support.idxOf x) (Nat.le_of_lt hilt)
      change fkIsingSquareWiredCarrierOddClass n
        (p.getVert (p.support.idxOf x)) ↔ Odd (p.support.idxOf x) at hpath
      rw [hgetx] at hpath
      exact hpath
    have hxclass : fkIsingSquareWiredCarrierOddClass n x := by
      simpa [x, fkIsingSquareWiredCarrierOddClass] using hccw
    exact hnotodd (hclass.mp hxclass)
  · exact hbackward

theorem fkIsingSquareWired_closed_south_west_oriented_infix
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west) :
    [(.dart (e, .south) : FKIsingSquareWiredCarrier n), .dart (e, .west)] <:+:
      fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega) := by
  simpa [FKIsingMedialDart.localMate, setClosed_self] using
    fkIsingSquareWired_localMate_infix_of_counterclockwise n hn
      (setClosed e.1 omega) e .west rfl h

theorem fkIsingSquareWired_closed_north_east_oriented_infix
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    [(.dart (e, .north) : FKIsingSquareWiredCarrier n), .dart (e, .east)] <:+:
      fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega) := by
  simpa [FKIsingMedialDart.localMate, setClosed_self,
    fkIsingSquareSideCorner] using
    fkIsingSquareWired_localMate_infix_of_counterclockwise n hn
      (setClosed e.1 omega) e .east rfl h

theorem fkIsingSquareWired_open_north_west_oriented_infix
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquareWiredPathUsesLocalSide n hn
      (setOpen e.1 omega) e .west) :
    [(.dart (e, .north) : FKIsingSquareWiredCarrier n), .dart (e, .west)] <:+:
      fkIsingSquareWiredExplorationOrder n hn (setOpen e.1 omega) := by
  simpa [FKIsingMedialDart.localMate, setOpen_self] using
    fkIsingSquareWired_localMate_infix_of_counterclockwise n hn
      (setOpen e.1 omega) e .west rfl h

theorem fkIsingSquareWired_open_south_east_oriented_infix
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquareWiredPathUsesLocalSide n hn
      (setOpen e.1 omega) e .east) :
    [(.dart (e, .south) : FKIsingSquareWiredCarrier n), .dart (e, .east)] <:+:
      fkIsingSquareWiredExplorationOrder n hn (setOpen e.1 omega) := by
  simpa [FKIsingMedialDart.localMate, setOpen_self,
    fkIsingSquareSideCorner] using
    fkIsingSquareWired_localMate_infix_of_counterclockwise n hn
      (setOpen e.1 omega) e .east rfl h


theorem fkIsingSquareWired_double_visit_closed_order
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    (fkIsingSquareWiredExplorationOrder n hn
        (setClosed e.1 omega)).idxOf (.dart (e, .west)) <
      (fkIsingSquareWiredExplorationOrder n hn
        (setClosed e.1 omega)).idxOf (.dart (e, .north)) ∨
    (fkIsingSquareWiredExplorationOrder n hn
        (setClosed e.1 omega)).idxOf (.dart (e, .east)) <
      (fkIsingSquareWiredExplorationOrder n hn
        (setClosed e.1 omega)).idxOf (.dart (e, .south)) := by
  let p := fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)
  have hSW := fkIsingSquareWired_closed_south_west_oriented_infix
    n hn omega e hwest
  have hNE := fkIsingSquareWired_closed_north_east_oriented_infix
    n hn omega e heast
  have hiSW := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareWiredExplorationOrder_nodup n hn
      (setClosed e.1 omega)) hSW
  have hiNE := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareWiredExplorationOrder_nodup n hn
      (setClosed e.1 omega)) hNE
  have hS : (.dart (e, .south) : FKIsingSquareWiredCarrier n) ∈ p :=
    hSW.mem (by simp)
  have hW : (.dart (e, .west) : FKIsingSquareWiredCarrier n) ∈ p :=
    hSW.mem (by simp)
  have hN : (.dart (e, .north) : FKIsingSquareWiredCarrier n) ∈ p :=
    hNE.mem (by simp)
  have hE : (.dart (e, .east) : FKIsingSquareWiredCarrier n) ∈ p :=
    hNE.mem (by simp)
  have hSN : p.idxOf (.dart (e, .south)) ≠
      p.idxOf (.dart (e, .north)) := by
    intro hi
    have heq := (List.idxOf_inj hS).mp hi
    simp at heq
  have hWN : p.idxOf (.dart (e, .west)) ≠
      p.idxOf (.dart (e, .north)) := by
    intro hi
    have heq := (List.idxOf_inj hW).mp hi
    simp at heq
  have hES : p.idxOf (.dart (e, .east)) ≠
      p.idxOf (.dart (e, .south)) := by
    intro hi
    have heq := (List.idxOf_inj hE).mp hi
    simp at heq
  change p.idxOf (.dart (e, .west)) < p.idxOf (.dart (e, .north)) ∨
    p.idxOf (.dart (e, .east)) < p.idxOf (.dart (e, .south))
  change p.idxOf (.dart (e, .west)) =
    p.idxOf (.dart (e, .south)) + 1 at hiSW
  change p.idxOf (.dart (e, .east)) =
    p.idxOf (.dart (e, .north)) + 1 at hiNE
  omega

private def fkIsingSquareWiredPathSpliceCast
    {V : Type*} {G H : SimpleGraph V} (h : G = H)
    {u v : V} (p : G.Walk u v) : H.Walk u v := h ▸ p

@[simp] private theorem fkIsingSquareWiredPathSpliceCast_support
    {V : Type*} {G H : SimpleGraph V} (h : G = H)
    {u v : V} (p : G.Walk u v) :
    (fkIsingSquareWiredPathSpliceCast h p).support = p.support := by
  subst H
  rfl

private theorem medialTwoEdgeSwitch_reverse_both_pairs
    {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (a b c d : V) :
    medialTwoEdgeSwitch G b a d c = medialTwoEdgeSwitch G a b c d := by
  ext u v
  simp [medialTwoEdgeSwitch, SimpleGraph.deleteEdges_adj,
    SimpleGraph.sup_adj, SimpleGraph.edge_adj, or_comm, or_left_comm,
    or_assoc]

@[simp] private theorem fkIsingSquareWiredPathSpliceCast_isPath
    {V : Type*} {G H : SimpleGraph V} (h : G = H)
    {u v : V} (p : G.Walk u v) :
    (fkIsingSquareWiredPathSpliceCast h p).IsPath ↔ p.IsPath := by
  subst H
  rfl



theorem fkIsingSquareWired_double_visit_open_splice_support
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    ((fkIsingSquareWiredExplorationOrder n hn (setOpen e.1 omega) =
        (fkIsingSquareWiredExplorationOrder n hn
          (setClosed e.1 omega)).take
            ((fkIsingSquareWiredExplorationOrder n hn
              (setClosed e.1 omega)).idxOf (.dart (e, .south)) + 1) ++
          (fkIsingSquareWiredExplorationOrder n hn
            (setClosed e.1 omega)).drop
              ((fkIsingSquareWiredExplorationOrder n hn
                (setClosed e.1 omega)).idxOf (.dart (e, .east)))) ∧
      (fkIsingSquareWiredExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .west)) <
        (fkIsingSquareWiredExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .north))) ∨
    ((fkIsingSquareWiredExplorationOrder n hn (setOpen e.1 omega) =
        (fkIsingSquareWiredExplorationOrder n hn
          (setClosed e.1 omega)).take
            ((fkIsingSquareWiredExplorationOrder n hn
              (setClosed e.1 omega)).idxOf (.dart (e, .north)) + 1) ++
          (fkIsingSquareWiredExplorationOrder n hn
            (setClosed e.1 omega)).drop
              ((fkIsingSquareWiredExplorationOrder n hn
                (setClosed e.1 omega)).idxOf (.dart (e, .west)))) ∧
      (fkIsingSquareWiredExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .east)) <
        (fkIsingSquareWiredExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .south))) := by
  classical
  let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
  let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
  let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
  let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
  let G := fkIsingSquareWiredLoopGraph n hn (setClosed e.1 omega)
  let p : G.Walk (.source : FKIsingSquareWiredCarrier n) .terminal :=
    fkIsingSquareWiredExplorationPath n hn (setClosed e.1 omega)
  have hp : p.IsPath :=
    (fkIsingSquareWiredExplorationPath n hn
      (setClosed e.1 omega)).isPath
  have hSW := fkIsingSquareWired_closed_south_west_oriented_infix
    n hn omega e hwest
  have hNE := fkIsingSquareWired_closed_north_east_oriented_infix
    n hn omega e heast
  have hS : S ∈ p.support := by simpa [S, p] using hSW.mem (by simp)
  have hW : W ∈ p.support := by simpa [W, p] using hSW.mem (by simp)
  have hN : N ∈ p.support := by simpa [N, p] using hNE.mem (by simp)
  have hE : E ∈ p.support := by simpa [E, p] using hNE.mem (by simp)
  have hiSW := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareWiredExplorationOrder_nodup n hn
      (setClosed e.1 omega)) hSW
  have hiNE := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareWiredExplorationOrder_nodup n hn
      (setClosed e.1 omega)) hNE
  change p.support.idxOf W = p.support.idxOf S + 1 at hiSW
  change p.support.idxOf E = p.support.idxOf N + 1 at hiNE
  have horder := fkIsingSquareWired_double_visit_closed_order
    n hn omega e hwest heast
  change p.support.idxOf W < p.support.idxOf N ∨
    p.support.idxOf E < p.support.idxOf S at horder
  have hopenBase : fkIsingSquareWiredLoopGraph n hn (setOpen e.1 omega) =
      medialTwoEdgeSwitch G W S E N := by
    simpa [G, W, S, E, N] using
      fkIsingSquareWiredLoopGraph_setOpen_eq_twoEdgeSwitch n hn omega e
  rcases horder with hWN | hES
  · have hswitch : medialTwoEdgeSwitch G S W N E =
        medialTwoEdgeSwitch G W S E N :=
      medialTwoEdgeSwitch_reverse_both_pairs G W S E N
    have hopen : fkIsingSquareWiredLoopGraph n hn (setOpen e.1 omega) =
        medialTwoEdgeSwitch G S W N E := hopenBase.trans hswitch.symm
    obtain ⟨q, hq, hqSupport⟩ :=
      walkSplice_of_order G p hp hS hW hN hE
        (by omega) hWN (by omega)
    let qOpen : (fkIsingSquareWiredLoopGraph n hn
        (setOpen e.1 omega)).Walk
        (.source : FKIsingSquareWiredCarrier n) .terminal :=
      fkIsingSquareWiredPathSpliceCast hopen.symm q
    have hqOpen : qOpen.IsPath := by
      simpa only [qOpen, fkIsingSquareWiredPathSpliceCast_isPath] using hq
    have hcanonical : qOpen =
        (fkIsingSquareWiredExplorationPath n hn (setOpen e.1 omega) :
          (fkIsingSquareWiredLoopGraph n hn
            (setOpen e.1 omega)).Walk .source .terminal) :=
      fkIsingSquareWired_sourceTerminalPath_unique n hn
        (setOpen e.1 omega) qOpen _ hqOpen
          (fkIsingSquareWiredExplorationPath n hn
            (setOpen e.1 omega)).isPath
    left
    refine ⟨?_, by simpa only [p, W, N] using hWN⟩
    change (fkIsingSquareWiredExplorationPath n hn (setOpen e.1 omega) :
      (fkIsingSquareWiredLoopGraph n hn
        (setOpen e.1 omega)).Walk .source .terminal).support = _
    rw [← hcanonical]
    simpa only [qOpen, fkIsingSquareWiredPathSpliceCast_support,
      p, S, E] using hqSupport
  · have hswitch : medialTwoEdgeSwitch G N E S W =
        medialTwoEdgeSwitch G W S E N := by
      calc
        medialTwoEdgeSwitch G N E S W =
            medialTwoEdgeSwitch G E N W S :=
          medialTwoEdgeSwitch_reverse_both_pairs G E N W S
        _ = medialTwoEdgeSwitch G W S E N :=
          medialTwoEdgeSwitch_swap_pairs G W S E N
    have hopen : fkIsingSquareWiredLoopGraph n hn (setOpen e.1 omega) =
        medialTwoEdgeSwitch G N E S W := hopenBase.trans hswitch.symm
    obtain ⟨q, hq, hqSupport⟩ :=
      walkSplice_of_order G p hp hN hE hS hW
        (by omega) hES (by omega)
    let qOpen : (fkIsingSquareWiredLoopGraph n hn
        (setOpen e.1 omega)).Walk
        (.source : FKIsingSquareWiredCarrier n) .terminal :=
      fkIsingSquareWiredPathSpliceCast hopen.symm q
    have hqOpen : qOpen.IsPath := by
      simpa only [qOpen, fkIsingSquareWiredPathSpliceCast_isPath] using hq
    have hcanonical : qOpen =
        (fkIsingSquareWiredExplorationPath n hn (setOpen e.1 omega) :
          (fkIsingSquareWiredLoopGraph n hn
            (setOpen e.1 omega)).Walk .source .terminal) :=
      fkIsingSquareWired_sourceTerminalPath_unique n hn
        (setOpen e.1 omega) qOpen _ hqOpen
          (fkIsingSquareWiredExplorationPath n hn
            (setOpen e.1 omega)).isPath
    right
    refine ⟨?_, by simpa only [p, E, S] using hES⟩
    change (fkIsingSquareWiredExplorationPath n hn (setOpen e.1 omega) :
      (fkIsingSquareWiredLoopGraph n hn
        (setOpen e.1 omega)).Walk .source .terminal).support = _
    rw [← hcanonical]
    simpa only [qOpen, fkIsingSquareWiredPathSpliceCast_support,
      p, N, W] using hqSupport



theorem fkIsingSquareWiredLiftedWinding_eq_neg_suffix_sum
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareWiredCarrier n)
    (hz : z ∈ fkIsingSquareWiredExplorationOrder n hn omega) :
    fkIsingSquareWiredLiftedWinding n hn omega z =
      (-(((fkIsingSquareWiredExplorationTurnSteps n hn omega).drop
        ((fkIsingSquareWiredExplorationOrder n hn omega).idxOf z)).sum) :
          Real) * (Real.pi / 4) := by
  let p := fkIsingSquareWiredExplorationOrder n hn omega
  let t := fkIsingSquareWiredExplorationTurnSteps n hn omega
  let w : (fkIsingSquareWiredLoopGraph n hn omega).Walk
      (.source : FKIsingSquareWiredCarrier n) .terminal :=
    fkIsingSquareWiredExplorationPath n hn omega
  have hp : p = w.support := rfl
  have hpne : p ≠ [] := by
    rw [hp]
    exact w.support_ne_nil
  have hplen : 0 < p.length := List.length_pos_of_ne_nil hpne
  let lastIndex : Fin p.length := ⟨p.length - 1, by omega⟩
  have hlast : p.get lastIndex =
      (.terminal : FKIsingSquareWiredCarrier n) := by
    have hwlast := w.getLast_support
    rw [List.getLast_eq_getElem w.support_ne_nil] at hwlast
    simpa only [lastIndex, hp] using hwlast
  have hnodup : p.Nodup := by
    simpa only [p] using fkIsingSquareWiredExplorationOrder_nodup n hn omega
  have hterminalIdx : p.idxOf
      (.terminal : FKIsingSquareWiredCarrier n) = p.length - 1 := by
    have hidx := List.get_idxOf hnodup lastIndex
    rw [hlast] at hidx
    exact hidx
  have hterminal : (.terminal : FKIsingSquareWiredCarrier n) ∈ p := by
    rw [← hlast]
    exact List.get_mem p lastIndex
  have htlen : t.length = p.length - 1 := by
    simp [t, p, fkIsingSquareWiredExplorationTurnSteps]
  have htakeTerminal : t.take (p.length - 1) = t := by
    rw [← htlen, List.take_length]
  have hsum := List.sum_take_add_sum_drop t (p.idxOf z)
  have hcount :
      fkIsingSquareWiredRawTurnCount n hn omega z -
          fkIsingSquareWiredRawTurnCount n hn omega .terminal =
        -(t.drop (p.idxOf z)).sum := by
    simp only [fkIsingSquareWiredRawTurnCount, p, t]
    rw [if_pos hz, if_pos hterminal, hterminalIdx, htakeTerminal]
    rw [← hsum]
    abel
  simp only [fkIsingSquareWiredLiftedWinding,
    fkIsingSquareWiredPhysicalTurnCount]
  rw [hcount]
  push_cast
  ring



theorem fkIsingSquareWiredTransitionTurn_open_eq_closed_of_nonlocal
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (x y : FKIsingSquareWiredCarrier n)
    (hnonlocal : ∀ side,
      x = .dart (e, side) → ∀ side', y ≠ .dart (e, side')) :
    fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega) x y =
      fkIsingSquareWiredTransitionTurn n hn (setClosed e.1 omega) x y := by
  cases x with
  | source => cases y <;> rfl
  | terminal => cases y <;> rfl
  | bond d => cases y <;> rfl
  | dart d =>
      cases y with
      | source => rfl
      | terminal => rfl
      | bond f => rfl
      | dart f =>
          rcases d with ⟨d, side⟩
          rcases f with ⟨f, side'⟩
          by_cases hd : d = e
          · subst d
            have hf : f ≠ e := by
              intro hfe
              subst f
              exact hnonlocal side rfl side' rfl
            have hopen : (f, side') ≠
                FKIsingMedialDart.localMate (setOpen e.1 omega)
                  (e, side) := by
              intro heq
              have hfirst := congrArg Prod.fst heq
              exact hf (by
                cases side <;>
                  simpa [FKIsingMedialDart.localMate] using hfirst)
            have hclosed : (f, side') ≠
                FKIsingMedialDart.localMate (setClosed e.1 omega)
                  (e, side) := by
              intro heq
              have hfirst := congrArg Prod.fst heq
              exact hf (by
                cases side <;>
                  simpa [FKIsingMedialDart.localMate] using hfirst)
            simp [fkIsingSquareWiredTransitionTurn, hopen, hclosed]
          · have hedge : d.1 ≠ e.1 := by
              intro hedge
              exact hd (Subtype.ext hedge)
            have hmate :
                FKIsingMedialDart.localMate (setOpen e.1 omega) (d, side) =
                  FKIsingMedialDart.localMate (setClosed e.1 omega)
                    (d, side) := by
              simp [FKIsingMedialDart.localMate,
                setOpen_of_ne hedge, setClosed_of_ne hedge]
            simp only [fkIsingSquareWiredTransitionTurn, hmate]

private theorem wiredZipWith_eq_of_mem
    {A B C : Type*} (f g : A → B → C) (l : List A) (r : List B)
    (h : ∀ a ∈ l, ∀ b ∈ r, f a b = g a b) :
    List.zipWith f l r = List.zipWith g l r := by
  induction l generalizing r with
  | nil => rfl
  | cons a l ih =>
      cases r with
      | nil => rfl
      | cons b r =>
          simp only [List.zipWith_cons_cons]
          rw [h a (by simp) b (by simp)]
          apply congrArg (List.cons (g a b))
          exact ih r (by
            intro x hx y hy
            exact h x (by simp [hx]) y (by simp [hy]))

private theorem fkIsingSquareWired_terminalSide_winding_eq_of_splice
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (d : FKIsingSquareWiredCarrier n) (prefixLength : Nat)
    (hdClosed : d ∈ fkIsingSquareWiredExplorationOrder n hn
      (setClosed e.1 omega))
    (hdOpen : d ∈ fkIsingSquareWiredExplorationOrder n hn
      (setOpen e.1 omega))
    (hprefix : prefixLength ≤
      (fkIsingSquareWiredExplorationOrder n hn
        (setClosed e.1 omega)).length)
    (hdPrefix : d ∉
      (fkIsingSquareWiredExplorationOrder n hn
        (setClosed e.1 omega)).take prefixLength)
    (hcentral : ∀ side,
      (.dart (e, side) : FKIsingSquareWiredCarrier n) ∈
        (fkIsingSquareWiredExplorationOrder n hn
          (setClosed e.1 omega)).take
            ((fkIsingSquareWiredExplorationOrder n hn
              (setClosed e.1 omega)).idxOf d + 1))
    (hsplice : fkIsingSquareWiredExplorationOrder n hn
        (setOpen e.1 omega) =
      (fkIsingSquareWiredExplorationOrder n hn
        (setClosed e.1 omega)).take prefixLength ++
      (fkIsingSquareWiredExplorationOrder n hn
        (setClosed e.1 omega)).drop
          ((fkIsingSquareWiredExplorationOrder n hn
            (setClosed e.1 omega)).idxOf d)) :
    fkIsingSquareWiredLiftedWinding n hn (setOpen e.1 omega) d =
      fkIsingSquareWiredLiftedWinding n hn (setClosed e.1 omega) d := by
  let pClosed := fkIsingSquareWiredExplorationOrder n hn
    (setClosed e.1 omega)
  let pOpen := fkIsingSquareWiredExplorationOrder n hn
    (setOpen e.1 omega)
  let tClosed := fkIsingSquareWiredExplorationTurnSteps n hn
    (setClosed e.1 omega)
  let tOpen := fkIsingSquareWiredExplorationTurnSteps n hn
    (setOpen e.1 omega)
  have hprefix' : prefixLength ≤ pClosed.length := by
    simpa only [pClosed] using hprefix
  have hdPrefix' : d ∉ pClosed.take prefixLength := by
    simpa only [pClosed] using hdPrefix
  have hcentral' (side : FKIsingMedialSide) :
      (.dart (e, side) : FKIsingSquareWiredCarrier n) ∈
        pClosed.take (pClosed.idxOf d + 1) := by
    simpa only [pClosed] using hcentral side
  have hsplice' : pOpen =
      pClosed.take prefixLength ++ pClosed.drop (pClosed.idxOf d) := by
    simpa only [pOpen, pClosed] using hsplice
  have hdlt : pClosed.idxOf d < pClosed.length :=
    List.idxOf_lt_length_iff.mpr hdClosed
  have hsuffix : pClosed.drop (pClosed.idxOf d) =
      d :: pClosed.drop (pClosed.idxOf d + 1) := by
    rw [List.drop_eq_getElem_cons hdlt, List.getElem_idxOf hdlt]
  have hprefixLength : (pClosed.take prefixLength).length = prefixLength := by
    simp only [List.length_take]
    omega
  have hidxOpen : pOpen.idxOf d = prefixLength := by
    rw [hsplice', List.idxOf_append, if_neg hdPrefix', hsuffix,
      List.idxOf_cons_self, hprefixLength]
    omega
  have hopenDrop : pOpen.drop prefixLength =
      pClosed.drop (pClosed.idxOf d) := by
    rw [hsplice']
    simpa only [hprefixLength] using
      (List.drop_left (l₁ := pClosed.take prefixLength)
        (l₂ := pClosed.drop (pClosed.idxOf d)))
  have hopenDropSucc : pOpen.drop (prefixLength + 1) =
      pClosed.drop (pClosed.idxOf d + 1) := by
    rw [← List.tail_drop, hopenDrop, List.tail_drop]
  have hclosedNodup : pClosed.Nodup := by
    simpa only [pClosed] using
      fkIsingSquareWiredExplorationOrder_nodup n hn
        (setClosed e.1 omega)
  have hsplit :
      (pClosed.take (pClosed.idxOf d + 1) ++
        pClosed.drop (pClosed.idxOf d + 1)).Nodup := by
    simpa only [List.take_append_drop] using hclosedNodup
  have hdisjoint : List.Disjoint
      (pClosed.take (pClosed.idxOf d + 1))
      (pClosed.drop (pClosed.idxOf d + 1)) := hsplit.disjoint
  have hcentralDrop (side : FKIsingMedialSide) :
      (.dart (e, side) : FKIsingSquareWiredCarrier n) ∉
        pClosed.drop (pClosed.idxOf d + 1) :=
    fun h => hdisjoint (hcentral' side) h
  have hzip :
      List.zipWith
          (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega))
          (pClosed.drop (pClosed.idxOf d))
          (pClosed.drop (pClosed.idxOf d + 1)) =
        List.zipWith
          (fkIsingSquareWiredTransitionTurn n hn (setClosed e.1 omega))
          (pClosed.drop (pClosed.idxOf d))
          (pClosed.drop (pClosed.idxOf d + 1)) := by
    apply wiredZipWith_eq_of_mem
    intro x hx y hy
    apply fkIsingSquareWiredTransitionTurn_open_eq_closed_of_nonlocal
    intro side _ side' hycentral
    apply hcentralDrop side'
    rw [← hycentral]
    exact hy
  have hsteps : tOpen.drop (pOpen.idxOf d) =
      tClosed.drop (pClosed.idxOf d) := by
    simp only [tOpen, tClosed, fkIsingSquareWiredExplorationTurnSteps,
      List.drop_zipWith, List.drop_tail]
    rw [hidxOpen, hopenDrop, hopenDropSucc]
    exact hzip
  rw [fkIsingSquareWiredLiftedWinding_eq_neg_suffix_sum n hn
      (setOpen e.1 omega) d hdOpen,
    fkIsingSquareWiredLiftedWinding_eq_neg_suffix_sum n hn
      (setClosed e.1 omega) d hdClosed]
  rw [hsteps]



theorem fkIsingSquareWired_double_visit_terminal_side_winding
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    (((fkIsingSquareWiredExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .west)) <
        (fkIsingSquareWiredExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .north))) ∧
      fkIsingSquareWiredLiftedWinding n hn (setOpen e.1 omega)
          (.dart (e, .east)) =
        fkIsingSquareWiredLiftedWinding n hn (setClosed e.1 omega)
          (.dart (e, .east))) ∨
    (((fkIsingSquareWiredExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .east)) <
        (fkIsingSquareWiredExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .south))) ∧
      fkIsingSquareWiredLiftedWinding n hn (setOpen e.1 omega)
          (.dart (e, .west)) =
        fkIsingSquareWiredLiftedWinding n hn (setClosed e.1 omega)
          (.dart (e, .west))) := by
  classical
  let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
  let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
  let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
  let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
  let pClosed := fkIsingSquareWiredExplorationOrder n hn
    (setClosed e.1 omega)
  let pOpen := fkIsingSquareWiredExplorationOrder n hn
    (setOpen e.1 omega)
  have hSW := fkIsingSquareWired_closed_south_west_oriented_infix
    n hn omega e hwest
  have hNE := fkIsingSquareWired_closed_north_east_oriented_infix
    n hn omega e heast
  have hS : S ∈ pClosed := by simpa [S, pClosed] using hSW.mem (by simp)
  have hW : W ∈ pClosed := by simpa [W, pClosed] using hSW.mem (by simp)
  have hN : N ∈ pClosed := by simpa [N, pClosed] using hNE.mem (by simp)
  have hE : E ∈ pClosed := by simpa [E, pClosed] using hNE.mem (by simp)
  have hiSW := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareWiredExplorationOrder_nodup n hn
      (setClosed e.1 omega)) hSW
  have hiNE := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareWiredExplorationOrder_nodup n hn
      (setClosed e.1 omega)) hNE
  change pClosed.idxOf W = pClosed.idxOf S + 1 at hiSW
  change pClosed.idxOf E = pClosed.idxOf N + 1 at hiNE
  rcases fkIsingSquareWired_double_visit_open_splice_support
      n hn omega e hwest heast with
    ⟨hsplice, hWN⟩ | ⟨hsplice, hES⟩
  · left
    refine ⟨hWN, ?_⟩
    have hsplice' : pOpen =
        pClosed.take (pClosed.idxOf S + 1) ++
          pClosed.drop (pClosed.idxOf E) := by
      simpa only [pOpen, pClosed, S, E] using hsplice
    have hWN' : pClosed.idxOf W < pClosed.idxOf N := by
      simpa only [pClosed, W, N] using hWN
    have hprefix : pClosed.idxOf S + 1 ≤ pClosed.length := by
      have := List.idxOf_lt_length_iff.mpr hS
      omega
    have hEPrefix : E ∉ pClosed.take (pClosed.idxOf S + 1) := by
      rw [List.mem_take_iff_idxOf_lt hE]
      omega
    have hcentral (side : FKIsingMedialSide) :
        (.dart (e, side) : FKIsingSquareWiredCarrier n) ∈
          pClosed.take (pClosed.idxOf E + 1) := by
      cases side
      · exact (List.mem_take_iff_idxOf_lt hW).2 (by omega)
      · exact (List.mem_take_iff_idxOf_lt hE).2 (by omega)
      · exact (List.mem_take_iff_idxOf_lt hS).2 (by omega)
      · exact (List.mem_take_iff_idxOf_lt hN).2 (by omega)
    have hEOpen : E ∈ pOpen := by
      rw [hsplice', List.mem_append]
      right
      rw [List.drop_eq_getElem_cons
        (List.idxOf_lt_length_iff.mpr hE),
        List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hE)]
      simp
    have hwind := fkIsingSquareWired_terminalSide_winding_eq_of_splice
      n hn omega e E (pClosed.idxOf S + 1) hE hEOpen
        hprefix hEPrefix hcentral hsplice
    simpa only [E] using hwind
  · right
    refine ⟨hES, ?_⟩
    have hsplice' : pOpen =
        pClosed.take (pClosed.idxOf N + 1) ++
          pClosed.drop (pClosed.idxOf W) := by
      simpa only [pOpen, pClosed, N, W] using hsplice
    have hES' : pClosed.idxOf E < pClosed.idxOf S := by
      simpa only [pClosed, E, S] using hES
    have hprefix : pClosed.idxOf N + 1 ≤ pClosed.length := by
      have := List.idxOf_lt_length_iff.mpr hN
      omega
    have hWPrefix : W ∉ pClosed.take (pClosed.idxOf N + 1) := by
      rw [List.mem_take_iff_idxOf_lt hW]
      omega
    have hcentral (side : FKIsingMedialSide) :
        (.dart (e, side) : FKIsingSquareWiredCarrier n) ∈
          pClosed.take (pClosed.idxOf W + 1) := by
      cases side
      · exact (List.mem_take_iff_idxOf_lt hW).2 (by omega)
      · exact (List.mem_take_iff_idxOf_lt hE).2 (by omega)
      · exact (List.mem_take_iff_idxOf_lt hS).2 (by omega)
      · exact (List.mem_take_iff_idxOf_lt hN).2 (by omega)
    have hWOpen : W ∈ pOpen := by
      rw [hsplice', List.mem_append]
      right
      rw [List.drop_eq_getElem_cons
        (List.idxOf_lt_length_iff.mpr hW),
        List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hW)]
      simp
    have hwind := fkIsingSquareWired_terminalSide_winding_eq_of_splice
      n hn omega e W (pClosed.idxOf N + 1) hW hWOpen
        hprefix hWPrefix hcentral hsplice
    simpa only [W] using hwind


theorem fkIsingSquareWired_double_visit_terminal_side_phase
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    (((fkIsingSquareWiredExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .west)) <
        (fkIsingSquareWiredExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .north))) ∧
      (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
          (setOpen e.1 omega) (.dart (e, .east)) =
        (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .east))) ∨
    (((fkIsingSquareWiredExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .east)) <
        (fkIsingSquareWiredExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .south))) ∧
      (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
          (setOpen e.1 omega) (.dart (e, .west)) =
        (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .west))) := by
  rcases fkIsingSquareWired_double_visit_terminal_side_winding
      n hn omega e hwest heast with ⟨horder, hwind⟩ | ⟨horder, hwind⟩
  · left
    refine ⟨horder, ?_⟩
    unfold FKIsingDobrushinDomain.windingPhase
    simpa only [fkIsingSquareWiredDobrushinDomain, hwind]
  · right
    refine ⟨horder, ?_⟩
    unfold FKIsingDobrushinDomain.windingPhase
    simpa only [fkIsingSquareWiredDobrushinDomain, hwind]

end

end StatMech.Universality
