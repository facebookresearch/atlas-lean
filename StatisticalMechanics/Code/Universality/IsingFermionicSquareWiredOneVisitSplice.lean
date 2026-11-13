/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.MedialPathCycleSplice
import Code.Universality.IsingFermionicSquareWiredPathSplice











open Finset SimpleGraph Set

namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

private def oneVisitWalkCast
    {V : Type*} {G H : SimpleGraph V} (h : G = H)
    {u v : V} (p : G.Walk u v) : H.Walk u v := h ▸ p

@[simp] private theorem oneVisitWalkCast_support
    {V : Type*} {G H : SimpleGraph V} (h : G = H)
    {u v : V} (p : G.Walk u v) :
    (oneVisitWalkCast h p).support = p.support := by
  subst H
  rfl

private theorem medialTwoEdgeSwitch_reverse_both_pairs_oneVisit
    {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (a b c d : V) :
    medialTwoEdgeSwitch G b a d c = medialTwoEdgeSwitch G a b c d := by
  ext u v
  simp [medialTwoEdgeSwitch, SimpleGraph.deleteEdges_adj,
    SimpleGraph.sup_adj, SimpleGraph.edge_adj, or_comm, or_left_comm]

private theorem oneVisitZipWith_eq_of_mem
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



theorem fkIsingSquareWired_winding_eq_of_terminal_suffix
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (d : FKIsingSquareWiredCarrier n)
    (pre : List (FKIsingSquareWiredCarrier n))
    (hdClosed : d ∈ fkIsingSquareWiredExplorationOrder n hn
      (setClosed e.1 omega))
    (hdOpen : d ∈ fkIsingSquareWiredExplorationOrder n hn
      (setOpen e.1 omega))
    (hdPrefix : d ∉ pre)
    (hcentralDrop : ∀ side,
      (.dart (e, side) : FKIsingSquareWiredCarrier n) ∉
        (fkIsingSquareWiredExplorationOrder n hn
          (setClosed e.1 omega)).drop
            ((fkIsingSquareWiredExplorationOrder n hn
              (setClosed e.1 omega)).idxOf d + 1))
    (hsplice : fkIsingSquareWiredExplorationOrder n hn
        (setOpen e.1 omega) =
      pre ++
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
  have hdPrefix' : d ∉ pre := hdPrefix
  have hcentralDrop' (side : FKIsingMedialSide) :
      (.dart (e, side) : FKIsingSquareWiredCarrier n) ∉
        pClosed.drop (pClosed.idxOf d + 1) := by
    simpa only [pClosed] using hcentralDrop side
  have hsplice' : pOpen = pre ++ pClosed.drop (pClosed.idxOf d) := by
    simpa only [pOpen, pClosed] using hsplice
  have hdlt : pClosed.idxOf d < pClosed.length :=
    List.idxOf_lt_length_iff.mpr hdClosed
  have hsuffix : pClosed.drop (pClosed.idxOf d) =
      d :: pClosed.drop (pClosed.idxOf d + 1) := by
    rw [List.drop_eq_getElem_cons hdlt, List.getElem_idxOf hdlt]
  have hidxOpen : pOpen.idxOf d = pre.length := by
    rw [hsplice', List.idxOf_append, if_neg hdPrefix', hsuffix,
      List.idxOf_cons_self]
    omega
  have hopenDrop : pOpen.drop pre.length =
      pClosed.drop (pClosed.idxOf d) := by
    rw [hsplice']
    exact List.drop_left
  have hopenDropSucc : pOpen.drop (pre.length + 1) =
      pClosed.drop (pClosed.idxOf d + 1) := by
    rw [← List.tail_drop, hopenDrop, List.tail_drop]
  have hzip :
      List.zipWith
          (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega))
          (pClosed.drop (pClosed.idxOf d))
          (pClosed.drop (pClosed.idxOf d + 1)) =
        List.zipWith
          (fkIsingSquareWiredTransitionTurn n hn (setClosed e.1 omega))
          (pClosed.drop (pClosed.idxOf d))
          (pClosed.drop (pClosed.idxOf d + 1)) := by
    apply oneVisitZipWith_eq_of_mem
    intro x hx y hy
    apply fkIsingSquareWiredTransitionTurn_open_eq_closed_of_nonlocal
    intro side _ side' hycentral
    apply hcentralDrop' side'
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

@[simp] private theorem oneVisitWalkCast_isPath
    {V : Type*} {G H : SimpleGraph V} (h : G = H)
    {u v : V} (p : G.Walk u v) :
    (oneVisitWalkCast h p).IsPath ↔ p.IsPath := by
  subst H
  rfl


theorem fkIsingSquareWired_one_visit_west_cycleArc
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : ¬ fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    let H := fkIsingSquareWiredLoopGraph n hn (setClosed e.1 omega)
    let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
    let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
    let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
    let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
    ∃ r : (H.deleteEdges {s(S, W), s(N, E)}).Walk E N,
      r.IsPath ∧ List.Disjoint
        (fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega))
        r.support := by
  classical
  let H := fkIsingSquareWiredLoopGraph n hn (setClosed e.1 omega)
  let C := fkIsingSquareWiredCompletedLoopGraph n hn (setClosed e.1 omega)
  let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
  let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
  let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
  let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
  let st : Sym2 (FKIsingSquareWiredCarrier n) := s(.source, .terminal)
  have hcycles : C.IsCycles := by
    intro v _
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card,
      SimpleGraph.card_neighborSet_eq_degree]
    simpa only [C] using
      fkIsingSquareWiredCompletedLoopGraph_degree_eq_two n hn
        (setClosed e.1 omega) v
  have hEN : C.Adj E N := by
    simpa only [C, E, N] using
      fkIsingSquareWiredCompletedLoopGraph_closed_east_north_adj
        n hn omega e
  have hnotSource : ¬ C.Reachable E .source := by
    intro h
    apply heast
    rw [fkIsingSquareWiredPathUsesLocalSide,
      mem_fkIsingSquareWiredExplorationOrder_iff_reachable,
      ← fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff]
    simpa only [C, E] using h.symm
  let rC : (C.deleteEdges {s(E, N)}).Walk E N :=
    (hcycles.reachable_deleteEdges hEN).some.toPath
  have hrC : rC.IsPath :=
    (hcycles.reachable_deleteEdges hEN).some.toPath.isPath
  have hsupportNotSource : (.source : FKIsingSquareWiredCarrier n) ∉ rC.support := by
    intro hs
    apply hnotSource
    exact ((rC.takeUntil .source hs).mapLe
      (SimpleGraph.deleteEdges_le _)).reachable
  have havoid : ∀ f, f ∈ rC.edges →
      f ∉ ({st, s(S, W)} : Set (Sym2 (FKIsingSquareWiredCarrier n))) := by
    intro f hf hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with rfl | rfl
    · exact hsupportNotSource (rC.fst_mem_support_of_mem_edges hf)
    · have hS : S ∈ rC.support := rC.fst_mem_support_of_mem_edges hf
      have hES : C.Reachable E S :=
        ((rC.takeUntil S hS).mapLe (SimpleGraph.deleteEdges_le _)).reachable
      have hSW : C.Adj S W := by
        simpa only [C, S, W] using
          (fkIsingSquareWiredCompletedLoopGraph_closed_west_south_adj
            n hn omega e).symm
      have hsourceW : C.Reachable .source W := by
        rw [fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff]
        rw [← mem_fkIsingSquareWiredExplorationOrder_iff_reachable]
        simpa only [fkIsingSquareWiredPathUsesLocalSide, W] using hwest
      exact hnotSource (hES.trans hSW.reachable |>.trans hsourceW.symm)
  let rDel := rC.toDeleteEdges {st, s(S, W)} havoid
  have hrDel : rDel.IsPath :=
    hrC.toDeleteEdges (C.deleteEdges {s(E, N)}) {st, s(S, W)} havoid
  have hHnotST : st ∉ H.edgeSet := by
    change ¬ H.Adj (.source : FKIsingSquareWiredCarrier n) .terminal
    rw [fkIsingSquareWiredLoopGraph_adj_source_iff]
    simp
  have hsymEN : s(E, N) = s(N, E) := Sym2.eq_swap
  have hgraph :
      (C.deleteEdges {s(E, N)}).deleteEdges {st, s(S, W)} =
        H.deleteEdges {s(S, W), s(N, E)} := by
    ext x y
    simp only [SimpleGraph.deleteEdges_adj, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or, C, H,
      fkIsingSquareWiredCompletedLoopGraph, SimpleGraph.sup_adj,
      SimpleGraph.edge_adj]
    constructor
    · rintro ⟨⟨hxy | hst, hneEN⟩, hneST, hneSW⟩
      · exact ⟨hxy, hneSW, fun h => hneEN (h.trans hsymEN.symm)⟩
      · exact False.elim (hneST (Sym2.eq_iff.mpr hst.1))
    · rintro ⟨hxy, hneSW, hneNE⟩
      exact ⟨⟨Or.inl hxy, fun h => hneNE (h.trans hsymEN)⟩,
        (fun hstEq => hHnotST (by
          rw [← hstEq]
          exact hxy)), hneSW⟩
  let r : (H.deleteEdges {s(S, W), s(N, E)}).Walk E N :=
    oneVisitWalkCast hgraph rDel
  refine ⟨r, ?_, ?_⟩
  · simpa only [r, oneVisitWalkCast_isPath] using hrDel
  · rw [List.disjoint_left]
    intro z hzp hzr
    have hsourceZ : C.Reachable .source z := by
      have hzH : H.Reachable .source z := by
        rw [← mem_fkIsingSquareWiredExplorationOrder_iff_reachable]
        exact hzp
      exact hzH.mono (by
        intro x y hxy
        exact Or.inl hxy)
    have hzrC : z ∈ rC.support := by
      simpa only [r, oneVisitWalkCast_support, rDel,
        Walk.support_transfer] using hzr
    have hEz : C.Reachable E z :=
      ((rC.takeUntil z hzrC).mapLe (SimpleGraph.deleteEdges_le _)).reachable
    exact hnotSource (hEz.trans hsourceZ.symm)


theorem fkIsingSquareWired_one_visit_west_open_splice_support
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : ¬ fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    let H := fkIsingSquareWiredLoopGraph n hn (setClosed e.1 omega)
    let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
    let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
    let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
    let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
    ∃ r : (H.deleteEdges {s(S, W), s(N, E)}).Walk E N,
      r.IsPath ∧
      List.Disjoint
        (fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega))
        r.support ∧
      fkIsingSquareWiredExplorationOrder n hn (setOpen e.1 omega) =
        (fkIsingSquareWiredExplorationOrder n hn
          (setClosed e.1 omega)).take
            ((fkIsingSquareWiredExplorationOrder n hn
              (setClosed e.1 omega)).idxOf S + 1) ++
          r.support ++
          (fkIsingSquareWiredExplorationOrder n hn
            (setClosed e.1 omega)).drop
              ((fkIsingSquareWiredExplorationOrder n hn
                (setClosed e.1 omega)).idxOf W) := by
  classical
  let H := fkIsingSquareWiredLoopGraph n hn (setClosed e.1 omega)
  let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
  let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
  let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
  let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
  let p : H.Walk (.source : FKIsingSquareWiredCarrier n) .terminal :=
    fkIsingSquareWiredExplorationPath n hn (setClosed e.1 omega)
  obtain ⟨r, hr, hdisjoint⟩ :=
    fkIsingSquareWired_one_visit_west_cycleArc
    n hn omega e hwest heast
  have hSW := fkIsingSquareWired_closed_south_west_oriented_infix
    n hn omega e hwest
  have hS : S ∈ p.support := by
    simpa only [S, p] using hSW.mem (by simp)
  have hW : W ∈ p.support := by
    simpa only [W, p] using hSW.mem (by simp)
  have hiSW := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareWiredExplorationOrder_nodup n hn
      (setClosed e.1 omega)) hSW
  have horder : p.support.idxOf S < p.support.idxOf W := by
    change p.support.idxOf W = p.support.idxOf S + 1 at hiSW
    omega
  have hE : E ∈ r.support := by
    simpa only [Walk.getVert_zero] using r.getVert_mem_support 0
  have hN : N ∈ r.support := by
    simpa only [Walk.getVert_length] using r.getVert_mem_support r.length
  obtain ⟨q, hq, hqSupport⟩ :=
    walkCycleArcSplice_of_order H p
      (fkIsingSquareWiredExplorationPath n hn
        (setClosed e.1 omega)).isPath
      hS hW horder r hr hE hN hdisjoint
  have hopenBase : fkIsingSquareWiredLoopGraph n hn (setOpen e.1 omega) =
      medialTwoEdgeSwitch H W S E N := by
    simpa only [H, W, S, E, N] using
      fkIsingSquareWiredLoopGraph_setOpen_eq_twoEdgeSwitch n hn omega e
  have hswitch : medialTwoEdgeSwitch H S W N E =
      medialTwoEdgeSwitch H W S E N :=
    medialTwoEdgeSwitch_reverse_both_pairs_oneVisit H W S E N
  have hopen : fkIsingSquareWiredLoopGraph n hn (setOpen e.1 omega) =
      medialTwoEdgeSwitch H S W N E := hopenBase.trans hswitch.symm
  let qOpen : (fkIsingSquareWiredLoopGraph n hn
      (setOpen e.1 omega)).Walk
      (.source : FKIsingSquareWiredCarrier n) .terminal :=
    oneVisitWalkCast hopen.symm q
  have hqOpen : qOpen.IsPath := by
    simpa only [qOpen, oneVisitWalkCast_isPath] using hq
  have hcanonical : qOpen =
      (fkIsingSquareWiredExplorationPath n hn (setOpen e.1 omega) :
        (fkIsingSquareWiredLoopGraph n hn
          (setOpen e.1 omega)).Walk .source .terminal) :=
    fkIsingSquareWired_sourceTerminalPath_unique n hn
      (setOpen e.1 omega) qOpen _ hqOpen
        (fkIsingSquareWiredExplorationPath n hn
          (setOpen e.1 omega)).isPath
  refine ⟨r, hr, hdisjoint, ?_⟩
  change (fkIsingSquareWiredExplorationPath n hn (setOpen e.1 omega) :
    (fkIsingSquareWiredLoopGraph n hn
      (setOpen e.1 omega)).Walk .source .terminal).support = _
  rw [← hcanonical]
  simpa only [qOpen, oneVisitWalkCast_support, p, S, W] using hqSupport



theorem fkIsingSquareWired_one_visit_west_winding
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : ¬ fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    fkIsingSquareWiredLiftedWinding n hn (setOpen e.1 omega)
        (.dart (e, .west)) =
      fkIsingSquareWiredLiftedWinding n hn (setClosed e.1 omega)
        (.dart (e, .west)) := by
  classical
  let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
  let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
  let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
  let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
  let pClosed := fkIsingSquareWiredExplorationOrder n hn
    (setClosed e.1 omega)
  let pOpen := fkIsingSquareWiredExplorationOrder n hn
    (setOpen e.1 omega)
  obtain ⟨r, hr, hdisjoint, hsplice⟩ :=
    fkIsingSquareWired_one_visit_west_open_splice_support
    n hn omega e hwest heast
  have hSW := fkIsingSquareWired_closed_south_west_oriented_infix
    n hn omega e hwest
  have hS : S ∈ pClosed := by
    simpa only [S, pClosed] using hSW.mem (by simp)
  have hW : W ∈ pClosed := by
    simpa only [W, pClosed] using hSW.mem (by simp)
  have hiSW := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareWiredExplorationOrder_nodup n hn
      (setClosed e.1 omega)) hSW
  change pClosed.idxOf W = pClosed.idxOf S + 1 at hiSW
  have hwestTrace : W ∈
      fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega) := by
    rw [← mem_fkIsingSquareWiredExplorationOrder_iff_trace]
    exact hW
  have heastTrace : E ∉
      fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega) := by
    intro hE
    apply heast
    rw [fkIsingSquareWiredPathUsesLocalSide,
      mem_fkIsingSquareWiredExplorationOrder_iff_trace]
    simpa only [E] using hE
  have hopenAll :=
    fkIsingSquareWired_open_local_mem_of_closed_west_mem_not_east
      n hn omega e (by simpa only [W] using hwestTrace)
        (by simpa only [E] using heastTrace)
  have hWOpen : W ∈ pOpen := by
    rw [mem_fkIsingSquareWiredExplorationOrder_iff_trace]
    simpa only [W] using hopenAll .west
  let pre := pClosed.take (pClosed.idxOf S + 1) ++ r.support
  have hWPre : W ∉ pre := by
    simp only [pre, List.mem_append, not_or]
    constructor
    · rw [List.mem_take_iff_idxOf_lt hW]
      omega
    · exact fun hWr => hdisjoint hW hWr
  have hclosedNodup : pClosed.Nodup := by
    simpa only [pClosed] using
      fkIsingSquareWiredExplorationOrder_nodup n hn
        (setClosed e.1 omega)
  have hsplit : List.Disjoint
      (pClosed.take (pClosed.idxOf W + 1))
      (pClosed.drop (pClosed.idxOf W + 1)) := by
    have h : (pClosed.take (pClosed.idxOf W + 1) ++
        pClosed.drop (pClosed.idxOf W + 1)).Nodup := by
      simpa only [List.take_append_drop] using hclosedNodup
    exact h.disjoint
  have hcentralDrop (side : FKIsingMedialSide) :
      (.dart (e, side) : FKIsingSquareWiredCarrier n) ∉
        pClosed.drop (pClosed.idxOf W + 1) := by
    intro hdrop
    cases side with
    | west =>
        exact hsplit (by
          rw [List.mem_take_iff_idxOf_lt hW]
          omega) (by simpa only [W] using hdrop)
    | south =>
        exact hsplit (by
          rw [List.mem_take_iff_idxOf_lt hS]
          omega) (by simpa only [S] using hdrop)
    | east =>
        apply heast
        exact (List.drop_sublist _ _).subset (by
          simpa only [E] using hdrop)
    | north =>
        have hN : N ∈ pClosed := (List.drop_sublist _ _).subset (by
          simpa only [N] using hdrop)
        have hNTrace : N ∈ fkIsingSquareWiredExplorationTrace n hn
            (setClosed e.1 omega) := by
          rw [← mem_fkIsingSquareWiredExplorationOrder_iff_trace]
          exact hN
        have hETrace :=
          (fkIsingSquareWired_closed_east_mem_iff_north n hn omega e).2
            (by simpa only [N] using hNTrace)
        exact heastTrace (by simpa only [E] using hETrace)
  have hsplice' : pOpen = pre ++ pClosed.drop (pClosed.idxOf W) := by
    simpa only [pOpen, pClosed, pre, S, W, List.append_assoc] using hsplice
  have hwind := fkIsingSquareWired_winding_eq_of_terminal_suffix
    n hn omega e W pre hW hWOpen hWPre hcentralDrop hsplice'
  simpa only [W] using hwind


theorem fkIsingSquareWired_one_visit_west_phase
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : ¬ fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
        (setOpen e.1 omega) (.dart (e, .west)) =
      (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
        (setClosed e.1 omega) (.dart (e, .west)) := by
  have hwind := fkIsingSquareWired_one_visit_west_winding
    n hn omega e hwest heast
  unfold FKIsingDobrushinDomain.windingPhase
  simpa only [fkIsingSquareWiredDobrushinDomain, hwind]


theorem fkIsingSquareWired_one_visit_east_cycleArc
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : ¬ fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    let H := fkIsingSquareWiredLoopGraph n hn (setClosed e.1 omega)
    let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
    let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
    let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
    let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
    ∃ r : (H.deleteEdges {s(N, E), s(S, W)}).Walk W S,
      r.IsPath ∧ List.Disjoint
        (fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega))
        r.support := by
  classical
  let H := fkIsingSquareWiredLoopGraph n hn (setClosed e.1 omega)
  let C := fkIsingSquareWiredCompletedLoopGraph n hn (setClosed e.1 omega)
  let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
  let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
  let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
  let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
  let st : Sym2 (FKIsingSquareWiredCarrier n) := s(.source, .terminal)
  have hcycles : C.IsCycles := by
    intro v _
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card,
      SimpleGraph.card_neighborSet_eq_degree]
    simpa only [C] using
      fkIsingSquareWiredCompletedLoopGraph_degree_eq_two n hn
        (setClosed e.1 omega) v
  have hWS : C.Adj W S := by
    simpa only [C, W, S] using
      fkIsingSquareWiredCompletedLoopGraph_closed_west_south_adj
        n hn omega e
  have hnotSource : ¬ C.Reachable W .source := by
    intro h
    apply hwest
    rw [fkIsingSquareWiredPathUsesLocalSide,
      mem_fkIsingSquareWiredExplorationOrder_iff_reachable,
      ← fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff]
    simpa only [C, W] using h.symm
  let rC : (C.deleteEdges {s(W, S)}).Walk W S :=
    (hcycles.reachable_deleteEdges hWS).some.toPath
  have hrC : rC.IsPath :=
    (hcycles.reachable_deleteEdges hWS).some.toPath.isPath
  have hsupportNotSource : (.source : FKIsingSquareWiredCarrier n) ∉ rC.support := by
    intro hs
    apply hnotSource
    exact ((rC.takeUntil .source hs).mapLe
      (SimpleGraph.deleteEdges_le _)).reachable
  have havoid : ∀ f, f ∈ rC.edges →
      f ∉ ({st, s(N, E)} : Set (Sym2 (FKIsingSquareWiredCarrier n))) := by
    intro f hf hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with rfl | rfl
    · exact hsupportNotSource (rC.fst_mem_support_of_mem_edges hf)
    · have hN : N ∈ rC.support := rC.fst_mem_support_of_mem_edges hf
      have hWN : C.Reachable W N :=
        ((rC.takeUntil N hN).mapLe (SimpleGraph.deleteEdges_le _)).reachable
      have hNE : C.Adj N E := by
        simpa only [C, N, E] using
          (fkIsingSquareWiredCompletedLoopGraph_closed_east_north_adj
            n hn omega e).symm
      have hsourceE : C.Reachable .source E := by
        rw [fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff]
        rw [← mem_fkIsingSquareWiredExplorationOrder_iff_reachable]
        simpa only [fkIsingSquareWiredPathUsesLocalSide, E] using heast
      exact hnotSource (hWN.trans hNE.reachable |>.trans hsourceE.symm)
  let rDel := rC.toDeleteEdges {st, s(N, E)} havoid
  have hrDel : rDel.IsPath :=
    hrC.toDeleteEdges (C.deleteEdges {s(W, S)}) {st, s(N, E)} havoid
  have hHnotST : st ∉ H.edgeSet := by
    change ¬ H.Adj (.source : FKIsingSquareWiredCarrier n) .terminal
    rw [fkIsingSquareWiredLoopGraph_adj_source_iff]
    simp
  have hsymWS : s(W, S) = s(S, W) := Sym2.eq_swap
  have hgraph :
      (C.deleteEdges {s(W, S)}).deleteEdges {st, s(N, E)} =
        H.deleteEdges {s(N, E), s(S, W)} := by
    ext x y
    simp only [SimpleGraph.deleteEdges_adj, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or, C, H,
      fkIsingSquareWiredCompletedLoopGraph, SimpleGraph.sup_adj,
      SimpleGraph.edge_adj]
    constructor
    · rintro ⟨⟨hxy | hst, hneWS⟩, hneST, hneNE⟩
      · exact ⟨hxy, hneNE, fun h => hneWS (h.trans hsymWS.symm)⟩
      · exact False.elim (hneST (Sym2.eq_iff.mpr hst.1))
    · rintro ⟨hxy, hneNE, hneSW⟩
      exact ⟨⟨Or.inl hxy, fun h => hneSW (h.trans hsymWS)⟩,
        (fun hstEq => hHnotST (by
          rw [← hstEq]
          exact hxy)), hneNE⟩
  let r : (H.deleteEdges {s(N, E), s(S, W)}).Walk W S :=
    oneVisitWalkCast hgraph rDel
  refine ⟨r, ?_, ?_⟩
  · simpa only [r, oneVisitWalkCast_isPath] using hrDel
  · rw [List.disjoint_left]
    intro z hzp hzr
    have hsourceZ : C.Reachable .source z := by
      have hzH : H.Reachable .source z := by
        rw [← mem_fkIsingSquareWiredExplorationOrder_iff_reachable]
        exact hzp
      exact hzH.mono (by
        intro x y hxy
        exact Or.inl hxy)
    have hzrC : z ∈ rC.support := by
      simpa only [r, oneVisitWalkCast_support, rDel,
        Walk.support_transfer] using hzr
    have hWz : C.Reachable W z :=
      ((rC.takeUntil z hzrC).mapLe (SimpleGraph.deleteEdges_le _)).reachable
    exact hnotSource (hWz.trans hsourceZ.symm)


theorem fkIsingSquareWired_one_visit_east_open_splice_support
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : ¬ fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    let H := fkIsingSquareWiredLoopGraph n hn (setClosed e.1 omega)
    let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
    let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
    let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
    let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
    ∃ r : (H.deleteEdges {s(N, E), s(S, W)}).Walk W S,
      r.IsPath ∧
      List.Disjoint
        (fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega))
        r.support ∧
      fkIsingSquareWiredExplorationOrder n hn (setOpen e.1 omega) =
        (fkIsingSquareWiredExplorationOrder n hn
          (setClosed e.1 omega)).take
            ((fkIsingSquareWiredExplorationOrder n hn
              (setClosed e.1 omega)).idxOf N + 1) ++
          r.support ++
          (fkIsingSquareWiredExplorationOrder n hn
            (setClosed e.1 omega)).drop
              ((fkIsingSquareWiredExplorationOrder n hn
                (setClosed e.1 omega)).idxOf E) := by
  classical
  let H := fkIsingSquareWiredLoopGraph n hn (setClosed e.1 omega)
  let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
  let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
  let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
  let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
  let p : H.Walk (.source : FKIsingSquareWiredCarrier n) .terminal :=
    fkIsingSquareWiredExplorationPath n hn (setClosed e.1 omega)
  obtain ⟨r, hr, hdisjoint⟩ :=
    fkIsingSquareWired_one_visit_east_cycleArc
    n hn omega e hwest heast
  have hNE := fkIsingSquareWired_closed_north_east_oriented_infix
    n hn omega e heast
  have hN : N ∈ p.support := by
    simpa only [N, p] using hNE.mem (by simp)
  have hE : E ∈ p.support := by
    simpa only [E, p] using hNE.mem (by simp)
  have hiNE := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareWiredExplorationOrder_nodup n hn
      (setClosed e.1 omega)) hNE
  have horder : p.support.idxOf N < p.support.idxOf E := by
    change p.support.idxOf E = p.support.idxOf N + 1 at hiNE
    omega
  have hW : W ∈ r.support := by
    simpa only [Walk.getVert_zero] using r.getVert_mem_support 0
  have hS : S ∈ r.support := by
    simpa only [Walk.getVert_length] using r.getVert_mem_support r.length
  obtain ⟨q, hq, hqSupport⟩ :=
    walkCycleArcSplice_of_order H p
      (fkIsingSquareWiredExplorationPath n hn
        (setClosed e.1 omega)).isPath
      hN hE horder r hr hW hS hdisjoint
  have hopenBase : fkIsingSquareWiredLoopGraph n hn (setOpen e.1 omega) =
      medialTwoEdgeSwitch H W S E N := by
    simpa only [H, W, S, E, N] using
      fkIsingSquareWiredLoopGraph_setOpen_eq_twoEdgeSwitch n hn omega e
  have hswitch : medialTwoEdgeSwitch H N E S W =
      medialTwoEdgeSwitch H W S E N := by
    calc
      medialTwoEdgeSwitch H N E S W = medialTwoEdgeSwitch H S W N E :=
        (medialTwoEdgeSwitch_swap_pairs H N E S W).symm
      _ = medialTwoEdgeSwitch H W S E N :=
        medialTwoEdgeSwitch_reverse_both_pairs_oneVisit H W S E N
  have hopen : fkIsingSquareWiredLoopGraph n hn (setOpen e.1 omega) =
      medialTwoEdgeSwitch H N E S W := hopenBase.trans hswitch.symm
  let qOpen : (fkIsingSquareWiredLoopGraph n hn
      (setOpen e.1 omega)).Walk
      (.source : FKIsingSquareWiredCarrier n) .terminal :=
    oneVisitWalkCast hopen.symm q
  have hqOpen : qOpen.IsPath := by
    simpa only [qOpen, oneVisitWalkCast_isPath] using hq
  have hcanonical : qOpen =
      (fkIsingSquareWiredExplorationPath n hn (setOpen e.1 omega) :
        (fkIsingSquareWiredLoopGraph n hn
          (setOpen e.1 omega)).Walk .source .terminal) :=
    fkIsingSquareWired_sourceTerminalPath_unique n hn
      (setOpen e.1 omega) qOpen _ hqOpen
        (fkIsingSquareWiredExplorationPath n hn
          (setOpen e.1 omega)).isPath
  refine ⟨r, hr, hdisjoint, ?_⟩
  change (fkIsingSquareWiredExplorationPath n hn (setOpen e.1 omega) :
    (fkIsingSquareWiredLoopGraph n hn
      (setOpen e.1 omega)).Walk .source .terminal).support = _
  rw [← hcanonical]
  simpa only [qOpen, oneVisitWalkCast_support, p, N, E] using hqSupport



theorem fkIsingSquareWired_one_visit_east_winding
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : ¬ fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    fkIsingSquareWiredLiftedWinding n hn (setOpen e.1 omega)
        (.dart (e, .east)) =
      fkIsingSquareWiredLiftedWinding n hn (setClosed e.1 omega)
        (.dart (e, .east)) := by
  classical
  let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
  let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
  let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
  let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
  let pClosed := fkIsingSquareWiredExplorationOrder n hn
    (setClosed e.1 omega)
  let pOpen := fkIsingSquareWiredExplorationOrder n hn
    (setOpen e.1 omega)
  obtain ⟨r, hr, hdisjoint, hsplice⟩ :=
    fkIsingSquareWired_one_visit_east_open_splice_support
    n hn omega e hwest heast
  have hNE := fkIsingSquareWired_closed_north_east_oriented_infix
    n hn omega e heast
  have hN : N ∈ pClosed := by
    simpa only [N, pClosed] using hNE.mem (by simp)
  have hE : E ∈ pClosed := by
    simpa only [E, pClosed] using hNE.mem (by simp)
  have hiNE := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareWiredExplorationOrder_nodup n hn
      (setClosed e.1 omega)) hNE
  change pClosed.idxOf E = pClosed.idxOf N + 1 at hiNE
  have hwestTrace : W ∉
      fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega) := by
    intro hW
    apply hwest
    rw [fkIsingSquareWiredPathUsesLocalSide,
      mem_fkIsingSquareWiredExplorationOrder_iff_trace]
    simpa only [W] using hW
  have heastTrace : E ∈
      fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega) := by
    rw [← mem_fkIsingSquareWiredExplorationOrder_iff_trace]
    exact hE
  have hopenAll :=
    fkIsingSquareWired_open_local_mem_of_closed_east_mem_not_west
      n hn omega e (by simpa only [E] using heastTrace)
        (by simpa only [W] using hwestTrace)
  have hEOpen : E ∈ pOpen := by
    rw [mem_fkIsingSquareWiredExplorationOrder_iff_trace]
    simpa only [E] using hopenAll .east
  let pre := pClosed.take (pClosed.idxOf N + 1) ++ r.support
  have hEPre : E ∉ pre := by
    simp only [pre, List.mem_append, not_or]
    constructor
    · rw [List.mem_take_iff_idxOf_lt hE]
      omega
    · exact fun hEr => hdisjoint hE hEr
  have hclosedNodup : pClosed.Nodup := by
    simpa only [pClosed] using
      fkIsingSquareWiredExplorationOrder_nodup n hn
        (setClosed e.1 omega)
  have hsplit : List.Disjoint
      (pClosed.take (pClosed.idxOf E + 1))
      (pClosed.drop (pClosed.idxOf E + 1)) := by
    have h : (pClosed.take (pClosed.idxOf E + 1) ++
        pClosed.drop (pClosed.idxOf E + 1)).Nodup := by
      simpa only [List.take_append_drop] using hclosedNodup
    exact h.disjoint
  have hcentralDrop (side : FKIsingMedialSide) :
      (.dart (e, side) : FKIsingSquareWiredCarrier n) ∉
        pClosed.drop (pClosed.idxOf E + 1) := by
    intro hdrop
    cases side with
    | east =>
        exact hsplit (by
          rw [List.mem_take_iff_idxOf_lt hE]
          omega) (by simpa only [E] using hdrop)
    | north =>
        exact hsplit (by
          rw [List.mem_take_iff_idxOf_lt hN]
          omega) (by simpa only [N] using hdrop)
    | west =>
        apply hwest
        exact (List.drop_sublist _ _).subset (by
          simpa only [W] using hdrop)
    | south =>
        have hS : S ∈ pClosed := (List.drop_sublist _ _).subset (by
          simpa only [S] using hdrop)
        have hSTrace : S ∈ fkIsingSquareWiredExplorationTrace n hn
            (setClosed e.1 omega) := by
          rw [← mem_fkIsingSquareWiredExplorationOrder_iff_trace]
          exact hS
        have hWTrace :=
          (fkIsingSquareWired_closed_west_mem_iff_south n hn omega e).2
            (by simpa only [S] using hSTrace)
        exact hwestTrace (by simpa only [W] using hWTrace)
  have hsplice' : pOpen = pre ++ pClosed.drop (pClosed.idxOf E) := by
    simpa only [pOpen, pClosed, pre, N, E, List.append_assoc] using hsplice
  have hwind := fkIsingSquareWired_winding_eq_of_terminal_suffix
    n hn omega e E pre hE hEOpen hEPre hcentralDrop hsplice'
  simpa only [E] using hwind


theorem fkIsingSquareWired_one_visit_east_phase
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : ¬ fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
        (setOpen e.1 omega) (.dart (e, .east)) =
      (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
        (setClosed e.1 omega) (.dart (e, .east)) := by
  have hwind := fkIsingSquareWired_one_visit_east_winding
    n hn omega e hwest heast
  unfold FKIsingDobrushinDomain.windingPhase
  simpa only [fkIsingSquareWiredDobrushinDomain, hwind]

end

end StatMech.Universality
