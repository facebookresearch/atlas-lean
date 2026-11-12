/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicSquareBox










open Finset SimpleGraph

namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

private def squareWalkCast {V : Type*} {G H : SimpleGraph V}
    (h : G = H) {u v : V} (p : G.Walk u v) : H.Walk u v :=
  h ▸ p

@[simp] private theorem squareWalkCast_support
    {V : Type*} {G H : SimpleGraph V} (h : G = H)
    {u v : V} (p : G.Walk u v) :
    (squareWalkCast h p).support = p.support := by
  subst H
  rfl

@[simp] private theorem squareWalkCast_isPath
    {V : Type*} {G H : SimpleGraph V} (h : G = H)
    {u v : V} (p : G.Walk u v) :
    (squareWalkCast h p).IsPath ↔ p.IsPath := by
  subst H
  rfl



theorem fkIsingSquare_sourceTerminalPath_unique
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (p q : (fkIsingSquareLoopGraph n hn omega).Walk
      (.source : FKIsingSquareMedialCarrier n) .terminal)
    (hp : p.IsPath) (hq : q.IsPath) : p = q := by
  let H := fkIsingSquareLoopGraph n hn omega
  let G := fkIsingSquareCompletedLoopGraph n hn omega
  have hle : H ≤ G := le_sup_left
  have hmem (z : FKIsingSquareMedialCarrier n) :
      z ∈ p.support ↔ z ∈ q.support := by
    rw [fkIsingSquarePath_mem_support_iff_reachable n hn omega p hp,
      fkIsingSquarePath_mem_support_iff_reachable n hn omega q hq]
  have hfin : p.support.toFinset = q.support.toFinset := by
    ext z
    simpa only [List.mem_toFinset] using hmem z
  have hsupportLen : p.support.length = q.support.length := by
    rw [← List.toFinset_card_of_nodup hp.support_nodup,
      ← List.toFinset_card_of_nodup hq.support_nodup, hfin]
  have hlen : p.length = q.length := by
    have hpLengthSupport := p.length_support
    have hqLengthSupport := q.length_support
    omega
  have hcycles : G.IsCycles := by
    intro v _
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card,
      SimpleGraph.card_neighborSet_eq_degree]
    cases v with
    | source => exact fkIsingSquareCompletedLoopGraph_source_degree n hn omega
    | terminal => exact fkIsingSquareCompletedLoopGraph_terminal_degree n hn omega
    | dart d => exact fkIsingSquareCompletedLoopGraph_dart_degree n hn omega d
  have hget : ∀ i, i ≤ p.length → p.getVert i = q.getVert i := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      intro hi
      by_cases hi0 : i = 0
      · subst i
        simp
      by_cases hi1 : i = 1
      · subst i
        have hpLen : 0 < p.length := by
          by_contra hzero
          have hz : p.length = 0 := Nat.eq_zero_of_not_pos hzero
          exact fkIsingSquare_source_ne_terminal n
            (Walk.eq_of_length_eq_zero hz)
        have hqLen : 0 < q.length := by simpa [hlen] using hpLen
        have hpAdj := p.adj_getVert_succ hpLen
        have hqAdj := q.adj_getVert_succ hqLen
        simp only [Walk.getVert_zero, zero_add] at hpAdj hqAdj
        rw [fkIsingSquareLoopGraph_adj_source_iff] at hpAdj hqAdj
        exact hpAdj.trans hqAdj.symm
      have hi2 : 2 ≤ i := by omega
      have him1 : i - 1 < i := by omega
      have him2 : i - 2 < i := by omega
      have hprev := ih (i - 2) him2 (by omega)
      have hcurr := ih (i - 1) him1 (by omega)
      have hpPrevAdj : G.Adj (p.getVert (i - 1)) (p.getVert (i - 2)) := by
        have h := p.adj_getVert_succ (show i - 2 < p.length by omega)
        have heq : i - 2 + 1 = i - 1 := by omega
        rw [heq] at h
        exact (hle h).symm
      obtain ⟨z, _hz, huniq⟩ := hcycles.existsUnique_ne_adj hpPrevAdj
      have hpNext : p.getVert (i - 2) ≠ p.getVert i ∧
          G.Adj (p.getVert (i - 1)) (p.getVert i) := by
        constructor
        · intro heq
          have hinj := hp.getVert_injOn (show i - 2 ≤ p.length by omega)
            hi heq
          omega
        · have h := p.adj_getVert_succ (show i - 1 < p.length by omega)
          have heq : i - 1 + 1 = i := by omega
          rw [heq] at h
          exact hle h
      have hqNext : q.getVert (i - 2) ≠ q.getVert i ∧
          G.Adj (q.getVert (i - 1)) (q.getVert i) := by
        constructor
        · intro heq
          have hinj := hq.getVert_injOn
            (show i - 2 ≤ q.length by omega)
            (show i ≤ q.length by omega) heq
          omega
        · have h := q.adj_getVert_succ (show i - 1 < q.length by omega)
          have heq : i - 1 + 1 = i := by omega
          rw [heq] at h
          exact hle h
      have hpz : p.getVert i = z := huniq _ hpNext
      have hqz : q.getVert i = z := by
        apply huniq
        simpa only [hprev, hcurr] using hqNext
      exact hpz.trans hqz.symm
  apply Walk.ext_support
  apply List.ext_getElem hsupportLen
  intro i hip hiq
  have hpLengthSupport := p.length_support
  have hqLengthSupport := q.length_support
  have hipLength : i ≤ p.length := by omega
  have hiqLength : i ≤ q.length := by omega
  rw [← p.getVert_eq_support_getElem hipLength,
    ← q.getVert_eq_support_getElem hiqLength]
  exact hget i hipLength




theorem fkIsingSquare_double_visit_open_splice_support
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    ((fkIsingSquareExplorationOrder n hn (setOpen e.1 omega) =
        (fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)).take
            ((fkIsingSquareExplorationOrder n hn
              (setClosed e.1 omega)).idxOf (.dart (e, .west)) + 1) ++
          (fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)).drop
            ((fkIsingSquareExplorationOrder n hn
              (setClosed e.1 omega)).idxOf (.dart (e, .north)))) ∧
      (fkIsingSquareExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .south)) <
        (fkIsingSquareExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .east))) ∨
    ((fkIsingSquareExplorationOrder n hn (setOpen e.1 omega) =
        (fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)).take
            ((fkIsingSquareExplorationOrder n hn
              (setClosed e.1 omega)).idxOf (.dart (e, .east)) + 1) ++
          (fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)).drop
            ((fkIsingSquareExplorationOrder n hn
              (setClosed e.1 omega)).idxOf (.dart (e, .south)))) ∧
      (fkIsingSquareExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .north)) <
        (fkIsingSquareExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .west))) := by
  classical
  let W : FKIsingSquareMedialCarrier n := .dart (e, .west)
  let N : FKIsingSquareMedialCarrier n := .dart (e, .north)
  let E : FKIsingSquareMedialCarrier n := .dart (e, .east)
  let S : FKIsingSquareMedialCarrier n := .dart (e, .south)
  let G := fkIsingSquareLoopGraph n hn (setClosed e.1 omega)
  let p : G.Walk (.source : FKIsingSquareMedialCarrier n) .terminal :=
    fkIsingSquareExplorationPath n hn (setClosed e.1 omega)
  have hp : p.IsPath :=
    (fkIsingSquareExplorationPath n hn (setClosed e.1 omega)).isPath
  have hWS := fkIsingSquare_closed_west_south_oriented_infix
    n hn omega e hwest
  have hEN := fkIsingSquare_closed_east_north_oriented_infix
    n hn omega e heast
  have hW : W ∈ p.support := by
    simpa [W, p, fkIsingSquarePathUsesLocalSide,
      fkIsingSquareExplorationOrder] using hwest
  have hS : S ∈ p.support := by
    simpa [S, p, fkIsingSquareExplorationOrder] using
      hWS.mem (by simp)
  have hE : E ∈ p.support := by
    simpa [E, p, fkIsingSquarePathUsesLocalSide,
      fkIsingSquareExplorationOrder] using heast
  have hN : N ∈ p.support := by
    simpa [N, p, fkIsingSquareExplorationOrder] using
      hEN.mem (by simp)
  have hiWS := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareExplorationOrder_nodup n hn (setClosed e.1 omega)) hWS
  have hiEN := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareExplorationOrder_nodup n hn (setClosed e.1 omega)) hEN
  change p.support.idxOf S = p.support.idxOf W + 1 at hiWS
  change p.support.idxOf N = p.support.idxOf E + 1 at hiEN
  have horder := fkIsingSquare_double_visit_closed_order
    n hn omega e hwest heast
  change p.support.idxOf S < p.support.idxOf E ∨
    p.support.idxOf N < p.support.idxOf W at horder
  have hopen : fkIsingSquareLoopGraph n hn (setOpen e.1 omega) =
      medialTwoEdgeSwitch G W S E N := by
    simpa [G, W, N, E, S] using
      fkIsingSquareLoopGraph_setOpen_eq_twoEdgeSwitch n hn omega e
  rcases horder with hSE | hNW
  · obtain ⟨q, hq, hqSupport⟩ :=
      walkSplice_of_order G p hp hW hS hE hN
        (by omega) hSE (by omega)
    let qOpen : (fkIsingSquareLoopGraph n hn (setOpen e.1 omega)).Walk
        (.source : FKIsingSquareMedialCarrier n) .terminal :=
      squareWalkCast hopen.symm q
    have hqOpen : qOpen.IsPath := by
      simpa only [qOpen, squareWalkCast_isPath] using hq
    have hcanonical : qOpen =
        (fkIsingSquareExplorationPath n hn (setOpen e.1 omega) :
          (fkIsingSquareLoopGraph n hn (setOpen e.1 omega)).Walk
            .source .terminal) :=
      fkIsingSquare_sourceTerminalPath_unique n hn
        (setOpen e.1 omega) qOpen _ hqOpen
          (fkIsingSquareExplorationPath n hn (setOpen e.1 omega)).isPath
    left
    refine ⟨?_, ?_⟩
    · change (fkIsingSquareExplorationPath n hn (setOpen e.1 omega) :
        (fkIsingSquareLoopGraph n hn (setOpen e.1 omega)).Walk
          .source .terminal).support = _
      rw [← hcanonical]
      simpa only [qOpen, squareWalkCast_support, p, W, N] using hqSupport
    · simpa only [p, S, E, fkIsingSquareExplorationOrder] using hSE
  · have hpair : medialTwoEdgeSwitch G E N W S =
        medialTwoEdgeSwitch G W S E N :=
      medialTwoEdgeSwitch_swap_pairs G W S E N
    have hopen' : fkIsingSquareLoopGraph n hn (setOpen e.1 omega) =
        medialTwoEdgeSwitch G E N W S := hopen.trans hpair.symm
    obtain ⟨q, hq, hqSupport⟩ :=
      walkSplice_of_order G p hp hE hN hW hS
        (by omega) hNW (by omega)
    let qOpen : (fkIsingSquareLoopGraph n hn (setOpen e.1 omega)).Walk
        (.source : FKIsingSquareMedialCarrier n) .terminal :=
      squareWalkCast hopen'.symm q
    have hqOpen : qOpen.IsPath := by
      simpa only [qOpen, squareWalkCast_isPath] using hq
    have hcanonical : qOpen =
        (fkIsingSquareExplorationPath n hn (setOpen e.1 omega) :
          (fkIsingSquareLoopGraph n hn (setOpen e.1 omega)).Walk
            .source .terminal) :=
      fkIsingSquare_sourceTerminalPath_unique n hn
        (setOpen e.1 omega) qOpen _ hqOpen
          (fkIsingSquareExplorationPath n hn (setOpen e.1 omega)).isPath
    right
    refine ⟨?_, ?_⟩
    · change (fkIsingSquareExplorationPath n hn (setOpen e.1 omega) :
        (fkIsingSquareLoopGraph n hn (setOpen e.1 omega)).Walk
          .source .terminal).support = _
      rw [← hcanonical]
      simpa only [qOpen, squareWalkCast_support, p, E, S] using hqSupport
    · simpa only [p, N, W, fkIsingSquareExplorationOrder] using hNW



theorem fkIsingSquareLiftedWinding_eq_neg_suffix_sum
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareMedialCarrier n)
    (hz : z ∈ fkIsingSquareExplorationOrder n hn omega) :
    fkIsingSquareLiftedWinding n hn omega z =
      (-(((fkIsingSquareExplorationTurnSteps n hn omega).drop
        ((fkIsingSquareExplorationOrder n hn omega).idxOf z)).sum) : Real) *
          (Real.pi / 4) := by
  let p := fkIsingSquareExplorationOrder n hn omega
  let t := fkIsingSquareExplorationTurnSteps n hn omega
  let w : (fkIsingSquareLoopGraph n hn omega).Walk
      (.source : FKIsingSquareMedialCarrier n) .terminal :=
    fkIsingSquareExplorationPath n hn omega
  have hp : p = w.support := rfl
  have hpne : p ≠ [] := by
    rw [hp]
    exact w.support_ne_nil
  have hplen : 0 < p.length := List.length_pos_of_ne_nil hpne
  let lastIndex : Fin p.length := ⟨p.length - 1, by omega⟩
  have hlast : p.get lastIndex =
      (.terminal : FKIsingSquareMedialCarrier n) := by
    have hwlast := w.getLast_support
    rw [List.getLast_eq_getElem w.support_ne_nil] at hwlast
    simpa only [lastIndex, hp] using hwlast
  have hnodup : p.Nodup := by
    simpa only [p] using fkIsingSquareExplorationOrder_nodup n hn omega
  have hterminalIdx : p.idxOf
      (.terminal : FKIsingSquareMedialCarrier n) = p.length - 1 := by
    have hidx := List.get_idxOf hnodup lastIndex
    rw [hlast] at hidx
    exact hidx
  have hterminal : (.terminal : FKIsingSquareMedialCarrier n) ∈ p := by
    rw [← hlast]
    exact List.get_mem p lastIndex
  have htlen : t.length = p.length - 1 := by
    simp [t, p, fkIsingSquareExplorationTurnSteps]
  have htakeTerminal : t.take (p.length - 1) = t := by
    rw [← htlen, List.take_length]
  have hsum := List.sum_take_add_sum_drop t (p.idxOf z)
  have hcount :
      fkIsingSquareLiftedTurnCount n hn omega z -
          fkIsingSquareLiftedTurnCount n hn omega .terminal =
        -(t.drop (p.idxOf z)).sum := by
    simp only [fkIsingSquareLiftedTurnCount, p, t]
    rw [if_pos hz, if_pos hterminal, hterminalIdx, htakeTerminal]
    rw [← hsum]
    abel
  simp only [fkIsingSquareLiftedWinding,
    fkIsingSquarePhysicalTurnCount, fkIsingSquareObservationFrameTurn]
  simp only [add_zero]
  rw [hcount]
  push_cast
  ring



theorem fkIsingSquareExplorationTransitionTurn_open_eq_closed_of_nonlocal
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (x y : FKIsingSquareMedialCarrier n)
    (hnonlocal : ∀ side,
      x = .dart (e, side) → ∀ side', y ≠ .dart (e, side')) :
    fkIsingSquareExplorationTransitionTurn n hn (setOpen e.1 omega) x y =
      fkIsingSquareExplorationTransitionTurn n hn (setClosed e.1 omega) x y := by
  cases x with
  | source => cases y <;> rfl
  | terminal => cases y <;> rfl
  | dart d =>
      cases y with
      | source => rfl
      | terminal => rfl
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
                FKIsingMedialDart.localMate (setOpen e.1 omega) (e, side) := by
              intro heq
              have hfirst := congrArg Prod.fst heq
              exact hf (by
                cases side <;>
                  simpa [FKIsingMedialDart.localMate] using hfirst)
            have hclosed : (f, side') ≠
                FKIsingMedialDart.localMate (setClosed e.1 omega) (e, side) := by
              intro heq
              have hfirst := congrArg Prod.fst heq
              exact hf (by
                cases side <;>
                  simpa [FKIsingMedialDart.localMate] using hfirst)
            simp [fkIsingSquareExplorationTransitionTurn, hopen, hclosed]
          · have hedge : d.1 ≠ e.1 := by
              intro hedge
              exact hd (Subtype.ext hedge)
            have hmate :
                FKIsingMedialDart.localMate (setOpen e.1 omega) (d, side) =
                  FKIsingMedialDart.localMate (setClosed e.1 omega) (d, side) := by
              simp [FKIsingMedialDart.localMate,
                setOpen_of_ne hedge, setClosed_of_ne hedge]
            simp only [fkIsingSquareExplorationTransitionTurn, hmate]

private theorem zipWith_eq_of_mem
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

private theorem fkIsingSquare_terminalSide_winding_eq_of_splice
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (d : FKIsingSquareMedialCarrier n) (prefixLength : Nat)
    (hdClosed : d ∈ fkIsingSquareExplorationOrder n hn
      (setClosed e.1 omega))
    (hdOpen : d ∈ fkIsingSquareExplorationOrder n hn
      (setOpen e.1 omega))
    (hprefix : prefixLength ≤
      (fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)).length)
    (hdPrefix : d ∉
      (fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)).take
        prefixLength)
    (hcentral : ∀ side,
      (.dart (e, side) : FKIsingSquareMedialCarrier n) ∈
        (fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)).take
          ((fkIsingSquareExplorationOrder n hn
            (setClosed e.1 omega)).idxOf d + 1))
    (hsplice : fkIsingSquareExplorationOrder n hn (setOpen e.1 omega) =
      (fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)).take
          prefixLength ++
        (fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)).drop
          ((fkIsingSquareExplorationOrder n hn
            (setClosed e.1 omega)).idxOf d)) :
    fkIsingSquareLiftedWinding n hn (setOpen e.1 omega) d =
      fkIsingSquareLiftedWinding n hn (setClosed e.1 omega) d := by
  let pClosed := fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)
  let pOpen := fkIsingSquareExplorationOrder n hn (setOpen e.1 omega)
  let tClosed := fkIsingSquareExplorationTurnSteps n hn (setClosed e.1 omega)
  let tOpen := fkIsingSquareExplorationTurnSteps n hn (setOpen e.1 omega)
  have hprefix' : prefixLength ≤ pClosed.length := by
    simpa only [pClosed] using hprefix
  have hdPrefix' : d ∉ pClosed.take prefixLength := by
    simpa only [pClosed] using hdPrefix
  have hcentral' (side : FKIsingMedialSide) :
      (.dart (e, side) : FKIsingSquareMedialCarrier n) ∈
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
      fkIsingSquareExplorationOrder_nodup n hn (setClosed e.1 omega)
  have hsplit :
      (pClosed.take (pClosed.idxOf d + 1) ++
        pClosed.drop (pClosed.idxOf d + 1)).Nodup := by
    simpa only [List.take_append_drop] using hclosedNodup
  have hdisjoint : List.Disjoint
      (pClosed.take (pClosed.idxOf d + 1))
      (pClosed.drop (pClosed.idxOf d + 1)) := hsplit.disjoint
  have hcentralDrop (side : FKIsingMedialSide) :
      (.dart (e, side) : FKIsingSquareMedialCarrier n) ∉
        pClosed.drop (pClosed.idxOf d + 1) :=
    fun h => hdisjoint (hcentral' side) h
  have hzip :
      List.zipWith
          (fkIsingSquareExplorationTransitionTurn n hn (setOpen e.1 omega))
          (pClosed.drop (pClosed.idxOf d))
          (pClosed.drop (pClosed.idxOf d + 1)) =
        List.zipWith
          (fkIsingSquareExplorationTransitionTurn n hn (setClosed e.1 omega))
          (pClosed.drop (pClosed.idxOf d))
          (pClosed.drop (pClosed.idxOf d + 1)) := by
    apply zipWith_eq_of_mem
    intro x hx y hy
    apply fkIsingSquareExplorationTransitionTurn_open_eq_closed_of_nonlocal
    intro side _ side' hycentral
    apply hcentralDrop side'
    rw [← hycentral]
    exact hy
  have hsteps : tOpen.drop (pOpen.idxOf d) =
      tClosed.drop (pClosed.idxOf d) := by
    simp only [tOpen, tClosed, fkIsingSquareExplorationTurnSteps,
      List.drop_zipWith, List.drop_tail]
    rw [hidxOpen, hopenDrop, hopenDropSucc]
    exact hzip
  rw [fkIsingSquareLiftedWinding_eq_neg_suffix_sum n hn
      (setOpen e.1 omega) d hdOpen,
    fkIsingSquareLiftedWinding_eq_neg_suffix_sum n hn
      (setClosed e.1 omega) d hdClosed]
  rw [hsteps]




theorem fkIsingSquare_double_visit_terminal_side_winding
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    (((fkIsingSquareExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .south)) <
        (fkIsingSquareExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .east))) ∧
      fkIsingSquareLiftedWinding n hn (setOpen e.1 omega)
          (.dart (e, .north)) =
        fkIsingSquareLiftedWinding n hn (setClosed e.1 omega)
          (.dart (e, .north))) ∨
    (((fkIsingSquareExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .north)) <
        (fkIsingSquareExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .west))) ∧
      fkIsingSquareLiftedWinding n hn (setOpen e.1 omega)
          (.dart (e, .south)) =
        fkIsingSquareLiftedWinding n hn (setClosed e.1 omega)
          (.dart (e, .south))) := by
  classical
  let W : FKIsingSquareMedialCarrier n := .dart (e, .west)
  let N : FKIsingSquareMedialCarrier n := .dart (e, .north)
  let E : FKIsingSquareMedialCarrier n := .dart (e, .east)
  let S : FKIsingSquareMedialCarrier n := .dart (e, .south)
  let pClosed := fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)
  let pOpen := fkIsingSquareExplorationOrder n hn (setOpen e.1 omega)
  have hWS := fkIsingSquare_closed_west_south_oriented_infix
    n hn omega e hwest
  have hEN := fkIsingSquare_closed_east_north_oriented_infix
    n hn omega e heast
  have hW : W ∈ pClosed := by
    simpa [W, pClosed, fkIsingSquarePathUsesLocalSide] using hwest
  have hS : S ∈ pClosed := by
    simpa [S, pClosed] using hWS.mem (by simp)
  have hE : E ∈ pClosed := by
    simpa [E, pClosed, fkIsingSquarePathUsesLocalSide] using heast
  have hN : N ∈ pClosed := by
    simpa [N, pClosed] using hEN.mem (by simp)
  have hiWS := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareExplorationOrder_nodup n hn (setClosed e.1 omega)) hWS
  have hiEN := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareExplorationOrder_nodup n hn (setClosed e.1 omega)) hEN
  change pClosed.idxOf S = pClosed.idxOf W + 1 at hiWS
  change pClosed.idxOf N = pClosed.idxOf E + 1 at hiEN
  rcases fkIsingSquare_double_visit_open_splice_support
      n hn omega e hwest heast with
    ⟨hsplice, hSE⟩ | ⟨hsplice, hNW⟩
  · left
    refine ⟨hSE, ?_⟩
    have hsplice' : pOpen =
        pClosed.take (pClosed.idxOf W + 1) ++
          pClosed.drop (pClosed.idxOf N) := by
      simpa only [pOpen, pClosed, W, N] using hsplice
    have hSE' : pClosed.idxOf S < pClosed.idxOf E := by
      simpa only [pClosed, S, E] using hSE
    have hprefix : pClosed.idxOf W + 1 ≤ pClosed.length := by
      have := List.idxOf_lt_length_iff.mpr hW
      omega
    have hNPrefix : N ∉ pClosed.take (pClosed.idxOf W + 1) := by
      rw [List.mem_take_iff_idxOf_lt hN]
      omega
    have hcentral (side : FKIsingMedialSide) :
        (.dart (e, side) : FKIsingSquareMedialCarrier n) ∈
          pClosed.take (pClosed.idxOf N + 1) := by
      cases side
      · exact (List.mem_take_iff_idxOf_lt hW).2 (by omega)
      · exact (List.mem_take_iff_idxOf_lt hE).2 (by omega)
      · exact (List.mem_take_iff_idxOf_lt hS).2 (by omega)
      · exact (List.mem_take_iff_idxOf_lt hN).2 (by omega)
    have hNOpen : N ∈ pOpen := by
      rw [hsplice', List.mem_append]
      right
      rw [List.drop_eq_getElem_cons
        (List.idxOf_lt_length_iff.mpr hN),
        List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hN)]
      simp
    have hwind := fkIsingSquare_terminalSide_winding_eq_of_splice
      n hn omega e N (pClosed.idxOf W + 1) hN hNOpen
        hprefix hNPrefix hcentral hsplice
    simpa only [N] using hwind
  · right
    refine ⟨hNW, ?_⟩
    have hsplice' : pOpen =
        pClosed.take (pClosed.idxOf E + 1) ++
          pClosed.drop (pClosed.idxOf S) := by
      simpa only [pOpen, pClosed, E, S] using hsplice
    have hNW' : pClosed.idxOf N < pClosed.idxOf W := by
      simpa only [pClosed, N, W] using hNW
    have hprefix : pClosed.idxOf E + 1 ≤ pClosed.length := by
      have := List.idxOf_lt_length_iff.mpr hE
      omega
    have hSPrefix : S ∉ pClosed.take (pClosed.idxOf E + 1) := by
      rw [List.mem_take_iff_idxOf_lt hS]
      omega
    have hcentral (side : FKIsingMedialSide) :
        (.dart (e, side) : FKIsingSquareMedialCarrier n) ∈
          pClosed.take (pClosed.idxOf S + 1) := by
      cases side
      · exact (List.mem_take_iff_idxOf_lt hW).2 (by omega)
      · exact (List.mem_take_iff_idxOf_lt hE).2 (by omega)
      · exact (List.mem_take_iff_idxOf_lt hS).2 (by omega)
      · exact (List.mem_take_iff_idxOf_lt hN).2 (by omega)
    have hSOpen : S ∈ pOpen := by
      rw [hsplice', List.mem_append]
      right
      rw [List.drop_eq_getElem_cons
        (List.idxOf_lt_length_iff.mpr hS),
        List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hS)]
      simp
    have hwind := fkIsingSquare_terminalSide_winding_eq_of_splice
      n hn omega e S (pClosed.idxOf E + 1) hS hSOpen
        hprefix hSPrefix hcentral hsplice
    simpa only [S] using hwind

end

end StatMech.Universality
