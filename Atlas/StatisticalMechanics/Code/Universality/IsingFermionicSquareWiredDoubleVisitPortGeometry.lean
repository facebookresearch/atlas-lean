/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicSquareWiredPortGeometry
import Code.Universality.IsingFermionicSquareWiredOpenFibers









namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section



theorem fkIsingSquareWired_double_visit_open_pair_exact
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    (fkIsingSquareWiredPathUsesLocalSide n hn
        (setOpen e.1 omega) e .west ∧
      fkIsingSquareWiredPathUsesLocalSide n hn
        (setOpen e.1 omega) e .north ∧
      ¬fkIsingSquareWiredPathUsesLocalSide n hn
        (setOpen e.1 omega) e .east ∧
      ¬fkIsingSquareWiredPathUsesLocalSide n hn
        (setOpen e.1 omega) e .south) ∨
    (¬fkIsingSquareWiredPathUsesLocalSide n hn
        (setOpen e.1 omega) e .west ∧
      ¬fkIsingSquareWiredPathUsesLocalSide n hn
        (setOpen e.1 omega) e .north ∧
      fkIsingSquareWiredPathUsesLocalSide n hn
        (setOpen e.1 omega) e .east ∧
      fkIsingSquareWiredPathUsesLocalSide n hn
        (setOpen e.1 omega) e .south) := by
  classical
  let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
  let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
  let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
  let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
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
  have hnodup : pClosed.Nodup :=
    fkIsingSquareWiredExplorationOrder_nodup n hn (setClosed e.1 omega)
  rcases fkIsingSquareWired_double_visit_open_splice_support
      n hn omega e hwest heast with
    ⟨hsplice, hWN⟩ | ⟨hsplice, hES⟩
  · right
    have hWN' : pClosed.idxOf W < pClosed.idxOf N := by
      simpa only [pClosed, W, N] using hWN
    have hsplice' : pOpen =
        pClosed.take (pClosed.idxOf S + 1) ++
          pClosed.drop (pClosed.idxOf E) := by
      simpa only [pOpen, pClosed, S, E] using hsplice
    have hSOpen : S ∈ pOpen := by
      rw [hsplice', List.mem_append]
      exact Or.inl ((List.mem_take_iff_idxOf_lt hS).2 (by omega))
    have hEOpen : E ∈ pOpen := by
      rw [hsplice', List.mem_append]
      right
      rw [List.drop_eq_getElem_cons
        (List.idxOf_lt_length_iff.mpr hE),
        List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hE)]
      simp
    have hWOpen : W ∉ pOpen := by
      rw [hsplice', List.mem_append]
      push Not
      constructor
      · rw [List.mem_take_iff_idxOf_lt hW]
        omega
      · have hsplit : (pClosed.take (pClosed.idxOf E) ++
            pClosed.drop (pClosed.idxOf E)).Nodup := by
          simpa only [List.take_append_drop] using hnodup
        exact fun hdrop => hsplit.disjoint
          ((List.mem_take_iff_idxOf_lt hW).2 (by omega)) hdrop
    have hNOpen : N ∉ pOpen := by
      rw [hsplice', List.mem_append]
      push Not
      constructor
      · rw [List.mem_take_iff_idxOf_lt hN]
        omega
      · have hsplit : (pClosed.take (pClosed.idxOf E) ++
            pClosed.drop (pClosed.idxOf E)).Nodup := by
          simpa only [List.take_append_drop] using hnodup
        exact fun hdrop => hsplit.disjoint
          ((List.mem_take_iff_idxOf_lt hN).2 (by omega)) hdrop
    simpa only [fkIsingSquareWiredPathUsesLocalSide, pOpen,
      W, N, E, S] using ⟨hWOpen, hNOpen, hEOpen, hSOpen⟩
  · left
    have hES' : pClosed.idxOf E < pClosed.idxOf S := by
      simpa only [pClosed, E, S] using hES
    have hsplice' : pOpen =
        pClosed.take (pClosed.idxOf N + 1) ++
          pClosed.drop (pClosed.idxOf W) := by
      simpa only [pOpen, pClosed, N, W] using hsplice
    have hNOpen : N ∈ pOpen := by
      rw [hsplice', List.mem_append]
      exact Or.inl ((List.mem_take_iff_idxOf_lt hN).2 (by omega))
    have hWOpen : W ∈ pOpen := by
      rw [hsplice', List.mem_append]
      right
      rw [List.drop_eq_getElem_cons
        (List.idxOf_lt_length_iff.mpr hW),
        List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hW)]
      simp
    have hEOpen : E ∉ pOpen := by
      rw [hsplice', List.mem_append]
      push Not
      constructor
      · rw [List.mem_take_iff_idxOf_lt hE]
        omega
      · have hsplit : (pClosed.take (pClosed.idxOf W) ++
            pClosed.drop (pClosed.idxOf W)).Nodup := by
          simpa only [List.take_append_drop] using hnodup
        exact fun hdrop => hsplit.disjoint
          ((List.mem_take_iff_idxOf_lt hE).2 (by omega)) hdrop
    have hSOpen : S ∉ pOpen := by
      rw [hsplice', List.mem_append]
      push Not
      constructor
      · rw [List.mem_take_iff_idxOf_lt hS]
        omega
      · have hsplit : (pClosed.take (pClosed.idxOf W) ++
            pClosed.drop (pClosed.idxOf W)).Nodup := by
          simpa only [List.take_append_drop] using hnodup
        exact fun hdrop => hsplit.disjoint
          ((List.mem_take_iff_idxOf_lt hS).2 (by omega)) hdrop
    simpa only [fkIsingSquareWiredPathUsesLocalSide, pOpen,
      W, N, E, S] using ⟨hWOpen, hNOpen, hEOpen, hSOpen⟩

private theorem zipWith_take_succ_take {A B C : Type*}
    (f : A → B → C) (l : List A) (r : List B) (k : Nat) :
    List.zipWith f (l.take (k + 1)) (r.take k) =
      List.zipWith f (l.take k) (r.take k) := by
  calc
    List.zipWith f (l.take (k + 1)) (r.take k) =
        (List.zipWith f (l.take (k + 1)) (r.take k)).take k := by
      symm
      rw [List.take_eq_self_iff]
      simp
    _ = List.zipWith f ((l.take (k + 1)).take k)
        ((r.take k).take k) := List.take_zipWith
    _ = List.zipWith f (l.take k) (r.take k) := by
      simp [List.take_take]

private def fkIsingSquareWiredDoubleVisitWalkCast
    {V : Type*} {G H : SimpleGraph V} (h : G = H)
    {u v : V} (p : G.Walk u v) : H.Walk u v := h ▸ p

@[simp] private theorem fkIsingSquareWiredDoubleVisitWalkCast_support
    {V : Type*} {G H : SimpleGraph V} (h : G = H)
    {u v : V} (p : G.Walk u v) :
    (fkIsingSquareWiredDoubleVisitWalkCast h p).support = p.support := by
  subst H
  rfl

@[simp] private theorem fkIsingSquareWiredDoubleVisitWalkCast_isPath
    {V : Type*} {G H : SimpleGraph V} (h : G = H)
    {u v : V} (p : G.Walk u v) :
    (fkIsingSquareWiredDoubleVisitWalkCast h p).IsPath ↔ p.IsPath := by
  subst H
  rfl

@[simp] private theorem fkIsingSquareWiredDoubleVisitWalkCast_length
    {V : Type*} {G H : SimpleGraph V} (h : G = H)
    {u v : V} (p : G.Walk u v) :
    (fkIsingSquareWiredDoubleVisitWalkCast h p).length = p.length := by
  subst H
  rfl

private theorem fkIsingSquareWired_walk_eq_of_isCycles_of_isPath_of_avoids_previous
    {V : Type*} {G : SimpleGraph V} (hcycles : G.IsCycles)
    {previous start finish : V} (hprevious : G.Adj previous start)
    (p q : G.Walk start finish)
    (hp : p.IsPath) (hq : q.IsPath)
    (hpPrevious : s(previous, start) ∉ p.edges)
    (hqPrevious : s(previous, start) ∉ q.edges) :
    p = q := by
  induction p generalizing previous with
  | nil => exact ((SimpleGraph.Walk.isPath_iff_eq_nil q).mp hq).symm
  | @cons _ next _ hstartNext ptail ih =>
      cases q with
      | nil =>
          have hnil := (SimpleGraph.Walk.isPath_iff_eq_nil
            (SimpleGraph.Walk.cons hstartNext ptail)).mp hp
          contradiction
      | @cons _ next' _ hstartNext' qtail =>
          have hnextPrevious : next ≠ previous := by
            intro heq
            subst next
            exact hpPrevious (by simp [Sym2.eq_swap])
          have hnextPrevious' : next' ≠ previous := by
            intro heq
            subst next'
            exact hqPrevious (by simp [Sym2.eq_swap])
          obtain ⟨other, _, hunique⟩ :=
            hcycles.existsUnique_ne_adj hprevious.symm
          have hnext : next = other := hunique next
            ⟨hnextPrevious.symm, hstartNext⟩
          have hnext' : next' = other := hunique next'
            ⟨hnextPrevious'.symm, hstartNext'⟩
          subst next
          subst next'
          congr 1
          exact ih hstartNext qtail hp.of_cons hq.of_cons
            ((SimpleGraph.Walk.isTrail_cons hstartNext ptail).mp hp.isTrail).2
            ((SimpleGraph.Walk.isTrail_cons hstartNext' qtail).mp hq.isTrail).2

private theorem fkIsingSquareWired_isCycle_eq_of_isCycles_of_snd_eq
    {V : Type*} {G : SimpleGraph V} (hcycles : G.IsCycles)
    {root : V} (p q : G.Walk root root)
    (hp : p.IsCycle) (hq : q.IsCycle)
    (hsnd : p.snd = q.snd) :
    p = q := by
  cases p with
  | nil => exact False.elim (hp.not_nil SimpleGraph.Walk.Nil.nil)
  | @cons _ pnext _ hpedge ptail =>
      cases q with
      | nil => exact False.elim (hq.not_nil SimpleGraph.Walk.Nil.nil)
      | @cons _ qnext _ hqedge qtail =>
          simp only [SimpleGraph.Walk.snd_cons] at hsnd
          subst qnext
          have htails : ptail = qtail :=
            fkIsingSquareWired_walk_eq_of_isCycles_of_isPath_of_avoids_previous
              hcycles hpedge ptail qtail
              (by simpa using hp.isPath_tail)
              (by simpa using hq.isPath_tail)
              ((SimpleGraph.Walk.cons_isCycle_iff ptail hpedge).mp hp).2
              ((SimpleGraph.Walk.cons_isCycle_iff qtail hqedge).mp hq).2
          subst qtail
          rfl

private theorem fkIsingSquareWiredRawTurnCount_sub_eq_interval_sum
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x y : FKIsingSquareWiredCarrier n)
    (hx : x ∈ fkIsingSquareWiredExplorationOrder n hn omega)
    (hy : y ∈ fkIsingSquareWiredExplorationOrder n hn omega)
    (hxy : (fkIsingSquareWiredExplorationOrder n hn omega).idxOf x ≤
      (fkIsingSquareWiredExplorationOrder n hn omega).idxOf y) :
    fkIsingSquareWiredRawTurnCount n hn omega y -
        fkIsingSquareWiredRawTurnCount n hn omega x =
      carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn omega)
        (((fkIsingSquareWiredExplorationOrder n hn omega).drop
            ((fkIsingSquareWiredExplorationOrder n hn omega).idxOf x)).take
          ((fkIsingSquareWiredExplorationOrder n hn omega).idxOf y -
            (fkIsingSquareWiredExplorationOrder n hn omega).idxOf x + 1)) := by
  let p := fkIsingSquareWiredExplorationOrder n hn omega
  let t := fkIsingSquareWiredExplorationTurnSteps n hn omega
  let ix := p.idxOf x
  let iy := p.idxOf y
  have hixy : ix ≤ iy := by simpa only [p, ix, iy] using hxy
  have hsum := List.sum_take_add_sum_drop (t.take iy) ix
  rw [List.take_take, Nat.min_eq_left hixy, List.drop_take] at hsum
  have hdiff : (t.take iy).sum - (t.take ix).sum =
      ((t.drop ix).take (iy - ix)).sum := by omega
  change (if y ∈ p then (t.take (p.idxOf y)).sum else 0) -
      (if x ∈ p then (t.take (p.idxOf x)).sum else 0) = _
  rw [if_pos hy, if_pos hx]
  change (t.take iy).sum - (t.take ix).sum = _
  rw [hdiff]
  simp only [t, fkIsingSquareWiredExplorationTurnSteps,
    carrierAdjacentSum, List.drop_zipWith, List.drop_tail,
    List.take_zipWith, List.tail_take_eq_take_tail,
    Nat.add_sub_cancel]
  change (List.zipWith (fkIsingSquareWiredTransitionTurn n hn omega)
      ((p.drop ix).take (iy - ix))
      ((p.drop (ix + 1)).take (iy - ix))).sum =
    (List.zipWith (fkIsingSquareWiredTransitionTurn n hn omega)
      ((p.drop ix).take (iy - ix + 1))
      ((p.drop ix).tail.take (iy - ix))).sum
  rw [List.tail_drop, zipWith_take_succ_take]

private theorem carrierAdjacentSum_chain_congr_double_visit
    {A : Type*} (left right : A → A → Int)
    (l : List A) (hchain : l.IsChain fun x y => left x y = right x y) :
    carrierAdjacentSum left l = carrierAdjacentSum right l := by
  induction l with
  | nil => rfl
  | cons a tail ih =>
      cases tail with
      | nil => rfl
      | cons b tail =>
          rw [carrierAdjacentSum_cons_cons, carrierAdjacentSum_cons_cons]
          rw [hchain.rel, ih hchain.of_cons]

private theorem fkIsingSquareWired_double_visit_carrierAdjacentSum_open_eq_closed
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    {a b : FKIsingSquareWiredCarrier n}
    (r : ((fkIsingSquareWiredLoopGraph n hn
      (setClosed e.1 omega)).deleteEdges
        {s((.dart (e, .west) : FKIsingSquareWiredCarrier n), .dart (e, .south)),
          s((.dart (e, .east) : FKIsingSquareWiredCarrier n), .dart (e, .north))}).Walk
            a b) :
    carrierAdjacentSum
        (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega)) r.support =
      carrierAdjacentSum
        (fkIsingSquareWiredTransitionTurn n hn (setClosed e.1 omega)) r.support := by
  apply carrierAdjacentSum_chain_congr_double_visit
  exact r.isChain_adj_support.imp (by
    intro x y hxy
    apply fkIsingSquareWiredTransitionTurn_open_eq_closed_of_nonlocal
    intro side hx side' hy
    subst x
    subst y
    cases side <;> cases side' <;>
      simp [SimpleGraph.deleteEdges_adj,
        fkIsingSquareWiredLoopGraph,
        fkIsingSquareWiredTransitionMate,
        fkIsingSquareWiredIncidenceMate,
        FKIsingMedialDart.localMate, setClosed] at hxy)

private theorem fkIsingSquareWired_double_visit_west_north_discarded_turn
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east)
    (hWN : (fkIsingSquareWiredExplorationOrder n hn
        (setClosed e.1 omega)).idxOf (.dart (e, .west)) <
      (fkIsingSquareWiredExplorationOrder n hn
        (setClosed e.1 omega)).idxOf (.dart (e, .north))) :
    fkIsingSquareWiredPhysicalTurnCount n hn (setClosed e.1 omega)
          (.dart (e, .north)) -
        fkIsingSquareWiredPhysicalTurnCount n hn (setClosed e.1 omega)
          (.dart (e, .west)) - 2 ≡ 8 [ZMOD 16] := by
  classical
  let closed := setClosed e.1 omega
  let opened := setOpen e.1 omega
  let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
  let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
  let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
  let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
  let G := fkIsingSquareWiredLoopGraph n hn closed
  let H := fkIsingSquareWiredCompletedLoopGraph n hn opened
  let p : G.Walk (.source : FKIsingSquareWiredCarrier n) .terminal :=
    fkIsingSquareWiredExplorationPath n hn closed
  let ix := p.support.idxOf W
  let iy := p.support.idxOf N
  have hp : p.IsPath := (fkIsingSquareWiredExplorationPath n hn closed).isPath
  have hSW := fkIsingSquareWired_closed_south_west_oriented_infix
    n hn omega e hwest
  have hNE := fkIsingSquareWired_closed_north_east_oriented_infix
    n hn omega e heast
  have hS : S ∈ p.support := by simpa [S, p, closed] using hSW.mem (by simp)
  have hW : W ∈ p.support := by simpa [W, p, closed] using hSW.mem (by simp)
  have hN : N ∈ p.support := by simpa [N, p, closed] using hNE.mem (by simp)
  have hE : E ∈ p.support := by simpa [E, p, closed] using hNE.mem (by simp)
  have hiSW := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareWiredExplorationOrder_nodup n hn closed) hSW
  have hiNE := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareWiredExplorationOrder_nodup n hn closed) hNE
  change ix = p.support.idxOf S + 1 at hiSW
  change p.support.idxOf E = iy + 1 at hiNE
  have hixy : ix < iy := by simpa [ix, iy, p, closed, W, N] using hWN
  have hixLength : ix < p.support.length := by
    exact List.idxOf_lt_length_iff.mpr hW
  have hiyLength : iy < p.support.length := by
    exact List.idxOf_lt_length_iff.mpr hN
  let r0 := (p.drop ix).take (iy - ix)
  have hrStart : p.getVert ix = W := by
    simpa only [ix] using p.getVert_support_idxOf hW
  have hrEnd : (p.drop ix).getVert (iy - ix) = N := by
    rw [p.drop_getVert]
    have hindex : ix + (iy - ix) = iy := by omega
    rw [hindex]
    exact p.getVert_support_idxOf hN
  let r : G.Walk W N := r0.copy hrStart hrEnd
  have hrPath : r.IsPath := by
    simpa only [r, fkIsingSquareWiredDoubleVisitWalkCast_isPath,
      SimpleGraph.Walk.isPath_copy] using (hp.drop ix).take (iy - ix)
  have hrSupport : r.support =
      (p.support.drop ix).take (iy - ix + 1) := by
    simp only [r, r0, SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.take_support_eq_support_take_succ,
      SimpleGraph.Walk.drop_support_eq_support_drop_min]
    rw [Nat.min_eq_left (by
      rw [p.length_support] at hiyLength
      omega)]
  have hSnot : S ∉ r.support := by
    intro hSr
    have hSdrop : S ∈ p.support.drop ix :=
      (List.take_sublist _ _).subset (hrSupport ▸ hSr)
    have hsplit : (p.support.take ix ++ p.support.drop ix).Nodup := by
      simpa only [List.take_append_drop] using hp.support_nodup
    exact hsplit.disjoint
      ((List.mem_take_iff_idxOf_lt hS).2 (by omega)) hSdrop
  have hrPrefix : ∀ {z}, z ∈ r.support → z ∈ p.support.take (iy + 1) := by
    intro z hz
    have hdropTake :
        (p.support.take (iy + 1)).drop ix =
          (p.support.drop ix).take (iy - ix + 1) := by
      rw [List.drop_take]
      congr 2
      omega
    apply (List.drop_sublist _ _).subset
    rw [hdropTake, ← hrSupport]
    exact hz
  have hEnot : E ∉ r.support := by
    intro hEr
    have hEtake := hrPrefix hEr
    rw [List.mem_take_iff_idxOf_lt hE] at hEtake
    omega
  let cut : Set (Sym2 (FKIsingSquareWiredCarrier n)) :=
    {s(W, S), s(E, N)}
  have hrAvoid : ∀ f, f ∈ r.edges → f ∉ cut := by
    intro f hf hcut
    simp only [cut, Set.mem_insert_iff, Set.mem_singleton_iff] at hcut
    rcases hcut with rfl | rfl
    · exact hSnot (r.snd_mem_support_of_mem_edges hf)
    · exact hEnot (r.fst_mem_support_of_mem_edges hf)
  let K := G.deleteEdges cut
  let M := medialTwoEdgeSwitch G W S E N
  let rK : K.Walk W N := r.toDeleteEdges cut hrAvoid
  have hrKSupport : rK.support = r.support := by
    change (r.transfer K _).support = r.support
    exact SimpleGraph.Walk.support_transfer r _
  have hrKLength : rK.length = r.length := by
    change (r.transfer K _).length = r.length
    exact SimpleGraph.Walk.length_transfer r _
  have hKle : K ≤ M := by
    intro x y hxy
    exact Or.inl (Or.inl hxy)
  let rM : M.Walk W N := rK.mapLe hKle
  have hopen : fkIsingSquareWiredLoopGraph n hn opened = M := by
    simpa [G, M, closed, opened, W, S, E, N] using
      fkIsingSquareWiredLoopGraph_setOpen_eq_twoEdgeSwitch n hn omega e
  let rOpen : (fkIsingSquareWiredLoopGraph n hn opened).Walk W N :=
    fkIsingSquareWiredDoubleVisitWalkCast hopen.symm rM
  have hrOpenPath : rOpen.IsPath := by
    have hrKPath : rK.IsPath := by
      rw [SimpleGraph.Walk.isPath_def]
      rw [hrKSupport]
      exact hrPath.support_nodup
    exact (fkIsingSquareWiredDoubleVisitWalkCast_isPath hopen.symm rM).2
      (hrKPath.mapLe hKle)
  let rH := rOpen.mapLe (show fkIsingSquareWiredLoopGraph n hn opened ≤ H
    from le_sup_left)
  have hWNOpen : (fkIsingSquareWiredLoopGraph n hn opened).Adj W N := by
    exact Or.inr (by simp [opened, W, N,
      fkIsingSquareWiredTransitionMate,
      FKIsingMedialDart.localMate, setOpen_self])
  have hWNH : H.Adj W N :=
    (show fkIsingSquareWiredLoopGraph n hn opened ≤ H from le_sup_left) hWNOpen
  let q : H.Walk W W := rH.reverse.cons hWNH
  have hrLength : 2 ≤ r.length := by
    have hpos : 0 < r.length := Nat.pos_of_ne_zero (by
      intro hzero
      have heq := r.eq_of_length_eq_zero hzero
      simp [W, N] at heq)
    by_contra hlt
    have hone : r.length = 1 := by omega
    have hadj := SimpleGraph.Walk.adj_of_length_eq_one hone
    simp [G, closed, W, N, fkIsingSquareWiredLoopGraph,
      fkIsingSquareWiredTransitionMate, fkIsingSquareWiredIncidenceMate,
      FKIsingMedialDart.localMate, setClosed_self] at hadj
  have hqCycle : q.IsCycle := by
    rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
    constructor
    · simpa [q, rH] using hrOpenPath.reverse
    · have hrHLength : rH.length = r.length := by
        calc
          rH.length = rOpen.length := SimpleGraph.Walk.length_map _ _
          _ = rM.length := fkIsingSquareWiredDoubleVisitWalkCast_length _ _
          _ = rK.length := SimpleGraph.Walk.length_map _ _
          _ = r.length := hrKLength
      simp [q, hrHLength]
      exact hrLength
  have hqSnd : q.snd = N := by simp [q]
  let d : FKIsingMedialDart (fkSquareBoxPlanar n) := (e, .west)
  have hroot : ¬H.Reachable (fkIsingSquareWiredBlackOfDart n d).1 .source := by
    intro hreach
    have hWOpen : W ∉ fkIsingSquareWiredExplorationOrder n hn opened := by
      rcases fkIsingSquareWired_double_visit_open_splice_support
          n hn omega e hwest heast with
        ⟨hsplice, _⟩ | ⟨_, hES⟩
      · have hsplice' : fkIsingSquareWiredExplorationOrder n hn opened =
            p.support.take (p.support.idxOf S + 1) ++
              p.support.drop (p.support.idxOf E) := by
          simpa [p, closed, opened, S, E] using hsplice
        rw [hsplice', List.mem_append]
        push Not
        constructor
        · rw [List.mem_take_iff_idxOf_lt hW]
          omega
        · have hsplit : (p.support.take (p.support.idxOf E) ++
              p.support.drop (p.support.idxOf E)).Nodup := by
            simpa only [List.take_append_drop] using hp.support_nodup
          exact fun hdrop => hsplit.disjoint
            ((List.mem_take_iff_idxOf_lt hW).2 (by omega)) hdrop
      · have hES' : p.support.idxOf E < p.support.idxOf S := by
          simpa [p, closed, E, S] using hES
        omega
    apply hWOpen
    rw [mem_fkIsingSquareWiredExplorationOrder_iff_reachable,
      ← fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff]
    simpa only [H, opened, d, W, fkIsingSquareWiredBlackOfDart] using hreach.symm
  obtain ⟨c, hc, hcSnd, hcTurn⟩ :=
    fkIsingSquareWiredCompletedGraph_exists_carrier_cycle_of_local_black_orbit
      n hn opened d hroot
  have hcMod := fkIsingSquareWired_local_black_orbit_transition_turn_mod_sixteen
    n hn opened d hroot
  dsimp only at hcMod
  rw [← hcTurn] at hcMod
  have hcSnd' : c.snd = N := by
    simpa [opened, d, N, fkIsingSquareWiredBlackOfDart,
      fkIsingSquareWiredTransitionMate, FKIsingMedialDart.localMate,
      setOpen_self] using hcSnd
  have hcEq : c = q := fkIsingSquareWired_isCycle_eq_of_isCycles_of_snd_eq
    (fkIsingSquareWiredCompletedLoopGraph_isCycles n hn opened)
    c q hc hqCycle (hcSnd'.trans hqSnd.symm)
  rw [hcEq] at hcMod
  have hopenClosed :=
    fkIsingSquareWired_double_visit_carrierAdjacentSum_open_eq_closed
      n hn omega e rK.reverse
  simp only [SimpleGraph.Walk.support_reverse, hrKSupport] at hopenClosed
  have hreverse :=
    fkIsingSquareWired_carrierAdjacentSum_add_reverse_mod_sixteen
      n hn closed r
  have hraw := fkIsingSquareWiredRawTurnCount_sub_eq_interval_sum
    n hn closed W N hW hN hixy.le
  change fkIsingSquareWiredRawTurnCount n hn closed N -
      fkIsingSquareWiredRawTurnCount n hn closed W =
    carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn closed)
      ((p.support.drop ix).take (iy - ix + 1)) at hraw
  rw [← hrSupport] at hraw
  have hphysical :
      fkIsingSquareWiredPhysicalTurnCount n hn closed N -
          fkIsingSquareWiredPhysicalTurnCount n hn closed W =
        carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn closed)
          r.support := by
    simpa [fkIsingSquareWiredPhysicalTurnCount] using hraw
  have hrrevSupport : r.reverse.support = N :: r.reverse.support.tail := by
    simpa [N] using r.reverse.cons_tail_support.symm
  have hqSupport : q.support = W :: r.reverse.support := by
    calc
      q.support = W :: rH.reverse.support := by simp [q]
      _ = W :: rH.support.reverse := by
        rw [SimpleGraph.Walk.support_reverse]
      _ = W :: rOpen.support.reverse := by
        rw [SimpleGraph.Walk.support_mapLe_eq_support]
      _ = W :: rM.support.reverse := by
        rw [fkIsingSquareWiredDoubleVisitWalkCast_support]
      _ = W :: rK.support.reverse := by
        rw [SimpleGraph.Walk.support_mapLe_eq_support]
      _ = W :: r.support.reverse := by rw [hrKSupport]
      _ = W :: r.reverse.support := by
        rw [SimpleGraph.Walk.support_reverse]
  have hqTurn :
      carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn opened)
          q.support =
        2 + carrierAdjacentSum
          (fkIsingSquareWiredTransitionTurn n hn opened) r.reverse.support := by
    rw [hqSupport, hrrevSupport, carrierAdjacentSum_cons_cons]
    rcases fkIsingSquareWiredTransitionTurn_local_table n hn omega e with
      ⟨_, _, _, _, hWNturn, _, _, _⟩
    simpa only [opened, W, N, ← hrrevSupport] using congrArg
      (fun z => z + carrierAdjacentSum
        (fkIsingSquareWiredTransitionTurn n hn opened) r.reverse.support)
      hWNturn
  have hqMod : 2 + carrierAdjacentSum
      (fkIsingSquareWiredTransitionTurn n hn opened) r.reverse.support ≡
      8 [ZMOD 16] := by
    rw [← hqTurn]
    exact hcMod
  have hreverse' := hreverse
  have hopenClosed' :
      carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn opened)
          r.reverse.support =
        carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn closed)
          r.reverse.support := by
    simpa only [opened, closed, SimpleGraph.Walk.support_reverse] using hopenClosed
  rw [← hphysical, ← hopenClosed'] at hreverse'
  have hsub := hreverse'.sub hqMod
  have hminus : (-8 : Int) ≡ 8 [ZMOD 16] := by decide
  simpa [closed, W, N] using hsub.trans hminus

private theorem fkIsingSquareWired_double_visit_east_south_discarded_turn
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east)
    (hES : (fkIsingSquareWiredExplorationOrder n hn
        (setClosed e.1 omega)).idxOf (.dart (e, .east)) <
      (fkIsingSquareWiredExplorationOrder n hn
        (setClosed e.1 omega)).idxOf (.dart (e, .south))) :
    fkIsingSquareWiredPhysicalTurnCount n hn (setClosed e.1 omega)
          (.dart (e, .south)) -
        fkIsingSquareWiredPhysicalTurnCount n hn (setClosed e.1 omega)
          (.dart (e, .east)) - 2 ≡ 8 [ZMOD 16] := by
  classical
  let closed := setClosed e.1 omega
  let opened := setOpen e.1 omega
  let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
  let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
  let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
  let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
  let G := fkIsingSquareWiredLoopGraph n hn closed
  let H := fkIsingSquareWiredCompletedLoopGraph n hn opened
  let p : G.Walk (.source : FKIsingSquareWiredCarrier n) .terminal :=
    fkIsingSquareWiredExplorationPath n hn closed
  let ix := p.support.idxOf E
  let iy := p.support.idxOf S
  have hp : p.IsPath := (fkIsingSquareWiredExplorationPath n hn closed).isPath
  have hNE := fkIsingSquareWired_closed_north_east_oriented_infix
    n hn omega e heast
  have hSW := fkIsingSquareWired_closed_south_west_oriented_infix
    n hn omega e hwest
  have hN : N ∈ p.support := by simpa [N, p, closed] using hNE.mem (by simp)
  have hE : E ∈ p.support := by simpa [E, p, closed] using hNE.mem (by simp)
  have hS : S ∈ p.support := by simpa [S, p, closed] using hSW.mem (by simp)
  have hW : W ∈ p.support := by simpa [W, p, closed] using hSW.mem (by simp)
  have hiNE := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareWiredExplorationOrder_nodup n hn closed) hNE
  have hiSW := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareWiredExplorationOrder_nodup n hn closed) hSW
  change ix = p.support.idxOf N + 1 at hiNE
  change p.support.idxOf W = iy + 1 at hiSW
  have hixy : ix < iy := by simpa [ix, iy, p, closed, E, S] using hES
  have hixLength : ix < p.support.length := by
    exact List.idxOf_lt_length_iff.mpr hE
  have hiyLength : iy < p.support.length := by
    exact List.idxOf_lt_length_iff.mpr hS
  let r0 := (p.drop ix).take (iy - ix)
  have hrStart : p.getVert ix = E := by
    simpa only [ix] using p.getVert_support_idxOf hE
  have hrEnd : (p.drop ix).getVert (iy - ix) = S := by
    rw [p.drop_getVert]
    have hindex : ix + (iy - ix) = iy := by omega
    rw [hindex]
    exact p.getVert_support_idxOf hS
  let r : G.Walk E S := r0.copy hrStart hrEnd
  have hrPath : r.IsPath := by
    simpa only [r, fkIsingSquareWiredDoubleVisitWalkCast_isPath,
      SimpleGraph.Walk.isPath_copy] using (hp.drop ix).take (iy - ix)
  have hrSupport : r.support =
      (p.support.drop ix).take (iy - ix + 1) := by
    simp only [r, r0, SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.take_support_eq_support_take_succ,
      SimpleGraph.Walk.drop_support_eq_support_drop_min]
    rw [Nat.min_eq_left (by
      rw [p.length_support] at hiyLength
      omega)]
  have hSnot : N ∉ r.support := by
    intro hSr
    have hSdrop : N ∈ p.support.drop ix :=
      (List.take_sublist _ _).subset (hrSupport ▸ hSr)
    have hsplit : (p.support.take ix ++ p.support.drop ix).Nodup := by
      simpa only [List.take_append_drop] using hp.support_nodup
    exact hsplit.disjoint
      ((List.mem_take_iff_idxOf_lt hN).2 (by omega)) hSdrop
  have hrPrefix : ∀ {z}, z ∈ r.support → z ∈ p.support.take (iy + 1) := by
    intro z hz
    have hdropTake :
        (p.support.take (iy + 1)).drop ix =
          (p.support.drop ix).take (iy - ix + 1) := by
      rw [List.drop_take]
      congr 2
      omega
    apply (List.drop_sublist _ _).subset
    rw [hdropTake, ← hrSupport]
    exact hz
  have hEnot : W ∉ r.support := by
    intro hEr
    have hEtake := hrPrefix hEr
    rw [List.mem_take_iff_idxOf_lt hW] at hEtake
    omega
  let cut : Set (Sym2 (FKIsingSquareWiredCarrier n)) :=
    {s(W, S), s(E, N)}
  have hrAvoid : ∀ f, f ∈ r.edges → f ∉ cut := by
    intro f hf hcut
    simp only [cut, Set.mem_insert_iff, Set.mem_singleton_iff] at hcut
    rcases hcut with rfl | rfl
    · exact hEnot (r.fst_mem_support_of_mem_edges hf)
    · exact hSnot (r.snd_mem_support_of_mem_edges hf)
  let K := G.deleteEdges cut
  let M := medialTwoEdgeSwitch G W S E N
  let rK : K.Walk E S := r.toDeleteEdges cut hrAvoid
  have hrKSupport : rK.support = r.support := by
    change (r.transfer K _).support = r.support
    exact SimpleGraph.Walk.support_transfer r _
  have hrKLength : rK.length = r.length := by
    change (r.transfer K _).length = r.length
    exact SimpleGraph.Walk.length_transfer r _
  have hKle : K ≤ M := by
    intro x y hxy
    exact Or.inl (Or.inl hxy)
  let rM : M.Walk E S := rK.mapLe hKle
  have hopen : fkIsingSquareWiredLoopGraph n hn opened = M := by
    simpa [G, M, closed, opened, E, N, W, S] using
      fkIsingSquareWiredLoopGraph_setOpen_eq_twoEdgeSwitch n hn omega e
  let rOpen : (fkIsingSquareWiredLoopGraph n hn opened).Walk E S :=
    fkIsingSquareWiredDoubleVisitWalkCast hopen.symm rM
  have hrOpenPath : rOpen.IsPath := by
    have hrKPath : rK.IsPath := by
      rw [SimpleGraph.Walk.isPath_def]
      rw [hrKSupport]
      exact hrPath.support_nodup
    exact (fkIsingSquareWiredDoubleVisitWalkCast_isPath hopen.symm rM).2
      (hrKPath.mapLe hKle)
  let rH := rOpen.mapLe (show fkIsingSquareWiredLoopGraph n hn opened ≤ H
    from le_sup_left)
  have hESOpen : (fkIsingSquareWiredLoopGraph n hn opened).Adj E S := by
    exact Or.inr (by simp [opened, E, S,
      fkIsingSquareWiredTransitionMate,
      FKIsingMedialDart.localMate, setOpen_self])
  have hESH : H.Adj E S :=
    (show fkIsingSquareWiredLoopGraph n hn opened ≤ H from le_sup_left) hESOpen
  let q : H.Walk E E := rH.reverse.cons hESH
  have hrLength : 2 ≤ r.length := by
    have hpos : 0 < r.length := Nat.pos_of_ne_zero (by
      intro hzero
      have heq := r.eq_of_length_eq_zero hzero
      simp [E, S] at heq)
    by_contra hlt
    have hone : r.length = 1 := by omega
    have hadj := SimpleGraph.Walk.adj_of_length_eq_one hone
    simp [G, closed, E, S, fkIsingSquareWiredLoopGraph,
      fkIsingSquareWiredTransitionMate, fkIsingSquareWiredIncidenceMate,
      FKIsingMedialDart.localMate, setClosed_self] at hadj
  have hqCycle : q.IsCycle := by
    rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
    constructor
    · simpa [q, rH] using hrOpenPath.reverse
    · have hrHLength : rH.length = r.length := by
        calc
          rH.length = rOpen.length := SimpleGraph.Walk.length_map _ _
          _ = rM.length := fkIsingSquareWiredDoubleVisitWalkCast_length _ _
          _ = rK.length := SimpleGraph.Walk.length_map _ _
          _ = r.length := hrKLength
      simp [q, hrHLength]
      exact hrLength
  have hqSnd : q.snd = S := by simp [q]
  let d : FKIsingMedialDart (fkSquareBoxPlanar n) := (e, .east)
  have hroot : ¬H.Reachable (fkIsingSquareWiredBlackOfDart n d).1 .source := by
    intro hreach
    have hWOpen : E ∉ fkIsingSquareWiredExplorationOrder n hn opened := by
      rcases fkIsingSquareWired_double_visit_open_splice_support
          n hn omega e hwest heast with
        ⟨_, hWN⟩ | ⟨hsplice, _⟩
      · have hWN' : p.support.idxOf W < p.support.idxOf N := by
          simpa [p, closed, W, N] using hWN
        omega
      · have hsplice' : fkIsingSquareWiredExplorationOrder n hn opened =
            p.support.take (p.support.idxOf N + 1) ++
              p.support.drop (p.support.idxOf W) := by
          simpa [p, closed, opened, N, W] using hsplice
        rw [hsplice', List.mem_append]
        push Not
        constructor
        · rw [List.mem_take_iff_idxOf_lt hE]
          omega
        · have hsplit : (p.support.take (p.support.idxOf W) ++
              p.support.drop (p.support.idxOf W)).Nodup := by
            simpa only [List.take_append_drop] using hp.support_nodup
          exact fun hdrop => hsplit.disjoint
            ((List.mem_take_iff_idxOf_lt hE).2 (by omega)) hdrop
    apply hWOpen
    rw [mem_fkIsingSquareWiredExplorationOrder_iff_reachable,
      ← fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff]
    simpa only [H, opened, d, E, fkIsingSquareWiredBlackOfDart] using hreach.symm
  obtain ⟨c, hc, hcSnd, hcTurn⟩ :=
    fkIsingSquareWiredCompletedGraph_exists_carrier_cycle_of_local_black_orbit
      n hn opened d hroot
  have hcMod := fkIsingSquareWired_local_black_orbit_transition_turn_mod_sixteen
    n hn opened d hroot
  dsimp only at hcMod
  rw [← hcTurn] at hcMod
  have hcSnd' : c.snd = S := by
    simpa [opened, d, S, fkIsingSquareWiredBlackOfDart,
      fkIsingSquareWiredTransitionMate, FKIsingMedialDart.localMate,
      setOpen_self] using hcSnd
  have hcEq : c = q := fkIsingSquareWired_isCycle_eq_of_isCycles_of_snd_eq
    (fkIsingSquareWiredCompletedLoopGraph_isCycles n hn opened)
    c q hc hqCycle (hcSnd'.trans hqSnd.symm)
  rw [hcEq] at hcMod
  have hopenClosed :=
    fkIsingSquareWired_double_visit_carrierAdjacentSum_open_eq_closed
      n hn omega e rK.reverse
  simp only [SimpleGraph.Walk.support_reverse, hrKSupport] at hopenClosed
  have hreverse :=
    fkIsingSquareWired_carrierAdjacentSum_add_reverse_mod_sixteen
      n hn closed r
  have hraw := fkIsingSquareWiredRawTurnCount_sub_eq_interval_sum
    n hn closed E S hE hS hixy.le
  change fkIsingSquareWiredRawTurnCount n hn closed S -
      fkIsingSquareWiredRawTurnCount n hn closed E =
    carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn closed)
      ((p.support.drop ix).take (iy - ix + 1)) at hraw
  rw [← hrSupport] at hraw
  have hphysical :
      fkIsingSquareWiredPhysicalTurnCount n hn closed S -
          fkIsingSquareWiredPhysicalTurnCount n hn closed E =
        carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn closed)
          r.support := by
    simpa [fkIsingSquareWiredPhysicalTurnCount] using hraw
  have hrrevSupport : r.reverse.support = S :: r.reverse.support.tail := by
    simpa [S] using r.reverse.cons_tail_support.symm
  have hqSupport : q.support = E :: r.reverse.support := by
    calc
      q.support = E :: rH.reverse.support := by simp [q]
      _ = E :: rH.support.reverse := by
        rw [SimpleGraph.Walk.support_reverse]
      _ = E :: rOpen.support.reverse := by
        rw [SimpleGraph.Walk.support_mapLe_eq_support]
      _ = E :: rM.support.reverse := by
        rw [fkIsingSquareWiredDoubleVisitWalkCast_support]
      _ = E :: rK.support.reverse := by
        rw [SimpleGraph.Walk.support_mapLe_eq_support]
      _ = E :: r.support.reverse := by rw [hrKSupport]
      _ = E :: r.reverse.support := by
        rw [SimpleGraph.Walk.support_reverse]
  have hqTurn :
      carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn opened)
          q.support =
        2 + carrierAdjacentSum
          (fkIsingSquareWiredTransitionTurn n hn opened) r.reverse.support := by
    rw [hqSupport, hrrevSupport, carrierAdjacentSum_cons_cons]
    rcases fkIsingSquareWiredTransitionTurn_local_table n hn omega e with
      ⟨_, _, _, _, _, _, hESturn, _⟩
    simpa only [opened, E, S, ← hrrevSupport] using congrArg
      (fun z => z + carrierAdjacentSum
        (fkIsingSquareWiredTransitionTurn n hn opened) r.reverse.support)
      hESturn
  have hqMod : 2 + carrierAdjacentSum
      (fkIsingSquareWiredTransitionTurn n hn opened) r.reverse.support ≡
      8 [ZMOD 16] := by
    rw [← hqTurn]
    exact hcMod
  have hreverse' := hreverse
  have hopenClosed' :
      carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn opened)
          r.reverse.support =
        carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn closed)
          r.reverse.support := by
    simpa only [opened, closed, SimpleGraph.Walk.support_reverse] using hopenClosed
  rw [← hphysical, ← hopenClosed'] at hreverse'
  have hsub := hreverse'.sub hqMod
  have hminus : (-8 : Int) ≡ 8 [ZMOD 16] := by decide
  simpa [closed, E, S] using hsub.trans hminus



private theorem fkIsingSquareWired_double_visit_open_east_of_west_before_north
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east)
    (hWN : (fkIsingSquareWiredExplorationOrder n hn
        (setClosed e.1 omega)).idxOf (.dart (e, .west)) <
      (fkIsingSquareWiredExplorationOrder n hn
        (setClosed e.1 omega)).idxOf (.dart (e, .north))) :
    fkIsingSquareWiredPathUsesLocalSide n hn
      (setOpen e.1 omega) e .east := by
  let p := fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)
  have hSW := fkIsingSquareWired_closed_south_west_oriented_infix
    n hn omega e hwest
  have hNE := fkIsingSquareWired_closed_north_east_oriented_infix
    n hn omega e heast
  have hiSW := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareWiredExplorationOrder_nodup n hn (setClosed e.1 omega)) hSW
  have hiNE := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareWiredExplorationOrder_nodup n hn (setClosed e.1 omega)) hNE
  change p.idxOf (.dart (e, .west)) = p.idxOf (.dart (e, .south)) + 1 at hiSW
  change p.idxOf (.dart (e, .east)) = p.idxOf (.dart (e, .north)) + 1 at hiNE
  rcases fkIsingSquareWired_double_visit_open_splice_support
      n hn omega e hwest heast with
    ⟨hsplice, _⟩ | ⟨_, hES⟩
  · change (.dart (e, .east) : FKIsingSquareWiredCarrier n) ∈
      fkIsingSquareWiredExplorationOrder n hn (setOpen e.1 omega)
    rw [hsplice, List.mem_append]
    right
    rw [List.drop_eq_getElem_cons
      (List.idxOf_lt_length_iff.mpr
        (hNE.mem (by simp : (.dart (e, .east) :
          FKIsingSquareWiredCarrier n) ∈ [(.dart (e, .north)), .dart (e, .east)]))),
      List.getElem_idxOf (List.idxOf_lt_length_iff.mpr
        (hNE.mem (by simp : (.dart (e, .east) :
          FKIsingSquareWiredCarrier n) ∈ [(.dart (e, .north)), .dart (e, .east)])))]
    simp
  · change p.idxOf (.dart (e, .east)) < p.idxOf (.dart (e, .south)) at hES
    change p.idxOf (.dart (e, .west)) < p.idxOf (.dart (e, .north)) at hWN
    omega



private theorem fkIsingSquareWired_double_visit_open_west_of_east_before_south
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east)
    (hES : (fkIsingSquareWiredExplorationOrder n hn
        (setClosed e.1 omega)).idxOf (.dart (e, .east)) <
      (fkIsingSquareWiredExplorationOrder n hn
        (setClosed e.1 omega)).idxOf (.dart (e, .south))) :
    fkIsingSquareWiredPathUsesLocalSide n hn
      (setOpen e.1 omega) e .west := by
  let p := fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)
  have hSW := fkIsingSquareWired_closed_south_west_oriented_infix
    n hn omega e hwest
  have hNE := fkIsingSquareWired_closed_north_east_oriented_infix
    n hn omega e heast
  have hiSW := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareWiredExplorationOrder_nodup n hn (setClosed e.1 omega)) hSW
  have hiNE := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareWiredExplorationOrder_nodup n hn (setClosed e.1 omega)) hNE
  change p.idxOf (.dart (e, .west)) = p.idxOf (.dart (e, .south)) + 1 at hiSW
  change p.idxOf (.dart (e, .east)) = p.idxOf (.dart (e, .north)) + 1 at hiNE
  rcases fkIsingSquareWired_double_visit_open_splice_support
      n hn omega e hwest heast with
    ⟨_, hWN⟩ | ⟨hsplice, _⟩
  · change p.idxOf (.dart (e, .west)) < p.idxOf (.dart (e, .north)) at hWN
    change p.idxOf (.dart (e, .east)) < p.idxOf (.dart (e, .south)) at hES
    omega
  · change (.dart (e, .west) : FKIsingSquareWiredCarrier n) ∈
      fkIsingSquareWiredExplorationOrder n hn (setOpen e.1 omega)
    rw [hsplice, List.mem_append]
    right
    rw [List.drop_eq_getElem_cons
      (List.idxOf_lt_length_iff.mpr
        (hSW.mem (by simp : (.dart (e, .west) :
          FKIsingSquareWiredCarrier n) ∈ [(.dart (e, .south)), .dart (e, .west)]))),
      List.getElem_idxOf (List.idxOf_lt_length_iff.mpr
        (hSW.mem (by simp : (.dart (e, .west) :
          FKIsingSquareWiredCarrier n) ∈ [(.dart (e, .south)), .dart (e, .west)])))]
    simp




def FKIsingSquareWiredDiscardedLoopTurnModSixteen
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) : Prop :=
  let p := fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)
  let T := fkIsingSquareWiredPhysicalTurnCount n hn (setClosed e.1 omega)
  (p.idxOf (.dart (e, .west)) < p.idxOf (.dart (e, .north)) →
      T (.dart (e, .north)) - T (.dart (e, .west)) - 2 ≡ 8 [ZMOD 16]) ∧
    (p.idxOf (.dart (e, .east)) < p.idxOf (.dart (e, .south)) →
      T (.dart (e, .south)) - T (.dart (e, .east)) - 2 ≡ 8 [ZMOD 16])



theorem fkIsingSquareWired_double_visit_discardedLoopTurn_mod_sixteen
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    FKIsingSquareWiredDiscardedLoopTurnModSixteen n hn omega e := by
  constructor
  · exact fkIsingSquareWired_double_visit_west_north_discarded_turn
      n hn omega e hwest heast
  · exact fkIsingSquareWired_double_visit_east_south_discarded_turn
      n hn omega e hwest heast



theorem fkIsingSquareWired_double_visit_source_side_phase_of_discardedLoopTurn_mod_sixteen
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east)
    (hloop : FKIsingSquareWiredDiscardedLoopTurnModSixteen n hn omega e) :
    (((fkIsingSquareWiredExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .west)) <
        (fkIsingSquareWiredExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .north))) ∧
      (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
          (setOpen e.1 omega) (.dart (e, .south)) =
        (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .south))) ∨
    (((fkIsingSquareWiredExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .east)) <
        (fkIsingSquareWiredExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .south))) ∧
      (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
          (setOpen e.1 omega) (.dart (e, .north)) =
        (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .north))) := by
  let D := fkIsingSquareWiredDobrushinDomain n hn
  let closed := setClosed e.1 omega
  let opened := setOpen e.1 omega
  let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
  let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
  let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
  let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
  rcases fkIsingSquareWired_double_visit_terminal_side_winding
      n hn omega e hwest heast with
    ⟨hWN, htermE⟩ | ⟨hES, htermW⟩
  · left
    refine ⟨hWN, ?_⟩
    have hturn := hloop.1 hWN
    obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hturn
    change 8 -
        (fkIsingSquareWiredPhysicalTurnCount n hn closed N -
          fkIsingSquareWiredPhysicalTurnCount n hn closed W - 2) =
      16 * k at hk
    have hclosedNE :
        fkIsingSquareWiredPhysicalTurnCount n hn closed N =
          fkIsingSquareWiredPhysicalTurnCount n hn closed E - 2 := by
      have hraw := fkIsingSquareWired_closed_east_north_rawTurnCount
        n hn omega e heast
      change fkIsingSquareWiredRawTurnCount n hn closed N =
        fkIsingSquareWiredRawTurnCount n hn closed E - 2 at hraw
      unfold fkIsingSquareWiredPhysicalTurnCount
      rw [hraw]
      omega
    have hcount :
        fkIsingSquareWiredPhysicalTurnCount n hn closed E -
          fkIsingSquareWiredPhysicalTurnCount n hn closed W =
        12 - 16 * k := by omega
    have hwindEW :
        fkIsingSquareWiredLiftedWinding n hn closed E =
          fkIsingSquareWiredLiftedWinding n hn closed W +
            ((3 - 4 * k : Int) : Real) * Real.pi := by
      unfold fkIsingSquareWiredLiftedWinding
      rw [show fkIsingSquareWiredPhysicalTurnCount n hn closed E =
          fkIsingSquareWiredPhysicalTurnCount n hn closed W +
            (12 - 16 * k) by omega]
      push_cast
      ring
    have hopenES := fkIsingSquareWired_open_east_south_winding
      n hn omega e
        (fkIsingSquareWired_double_visit_open_east_of_west_before_north
          n hn omega e hwest heast hWN)
    have hclosedSW := fkIsingSquareWired_closed_west_south_winding
      n hn omega e hwest
    have hsource : fkIsingSquareWiredLiftedWinding n hn opened S =
        fkIsingSquareWiredLiftedWinding n hn closed S +
          ((1 - k : Int) : Real) * (4 * Real.pi) := by
      rw [hopenES, htermE, hclosedSW, hwindEW]
      push_cast
      ring
    exact FKIsingDobrushinDomain.windingPhase_eq_of_winding_eq_add_four_pi_mul_int
      D closed opened S S (1 - k) (by
        simpa only [D, closed, opened, S,
          fkIsingSquareWiredDobrushinDomain] using hsource)
  · right
    refine ⟨hES, ?_⟩
    have hturn := hloop.2 hES
    obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hturn
    change 8 -
        (fkIsingSquareWiredPhysicalTurnCount n hn closed S -
          fkIsingSquareWiredPhysicalTurnCount n hn closed E - 2) =
      16 * k at hk
    have hclosedSW :
        fkIsingSquareWiredPhysicalTurnCount n hn closed S =
          fkIsingSquareWiredPhysicalTurnCount n hn closed W - 2 := by
      have hraw := fkIsingSquareWired_closed_west_south_rawTurnCount
        n hn omega e hwest
      change fkIsingSquareWiredRawTurnCount n hn closed S =
        fkIsingSquareWiredRawTurnCount n hn closed W - 2 at hraw
      unfold fkIsingSquareWiredPhysicalTurnCount
      rw [hraw]
      omega
    have hcount :
        fkIsingSquareWiredPhysicalTurnCount n hn closed W -
          fkIsingSquareWiredPhysicalTurnCount n hn closed E =
        12 - 16 * k := by omega
    have hwindWE :
        fkIsingSquareWiredLiftedWinding n hn closed W =
          fkIsingSquareWiredLiftedWinding n hn closed E +
            ((3 - 4 * k : Int) : Real) * Real.pi := by
      unfold fkIsingSquareWiredLiftedWinding
      rw [show fkIsingSquareWiredPhysicalTurnCount n hn closed W =
          fkIsingSquareWiredPhysicalTurnCount n hn closed E +
            (12 - 16 * k) by omega]
      push_cast
      ring
    have hopenWN := fkIsingSquareWired_open_west_north_winding
      n hn omega e
        (fkIsingSquareWired_double_visit_open_west_of_east_before_south
          n hn omega e hwest heast hES)
    have hclosedNE := fkIsingSquareWired_closed_east_north_winding
      n hn omega e heast
    have hsource : fkIsingSquareWiredLiftedWinding n hn opened N =
        fkIsingSquareWiredLiftedWinding n hn closed N +
          ((1 - k : Int) : Real) * (4 * Real.pi) := by
      rw [hopenWN, htermW, hclosedNE, hwindWE]
      push_cast
      ring
    exact FKIsingDobrushinDomain.windingPhase_eq_of_winding_eq_add_four_pi_mul_int
      D closed opened N N (1 - k) (by
        simpa only [D, closed, opened, N,
          fkIsingSquareWiredDobrushinDomain] using hsource)



theorem fkIsingSquareWired_double_visit_source_side_phase
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
          (setOpen e.1 omega) (.dart (e, .south)) =
        (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .south))) ∨
    (((fkIsingSquareWiredExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .east)) <
        (fkIsingSquareWiredExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .south))) ∧
      (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
          (setOpen e.1 omega) (.dart (e, .north)) =
        (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .north))) :=
  fkIsingSquareWired_double_visit_source_side_phase_of_discardedLoopTurn_mod_sixteen
    n hn omega e hwest heast
      (fkIsingSquareWired_double_visit_discardedLoopTurn_mod_sixteen
        n hn omega e hwest heast)



theorem fkIsingSquareWired_double_visit_pointwise_contour_balance
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    let D := fkIsingSquareWiredDobrushinDomain n hn
    let closed := setClosed e.1 omega
    let opened := setOpen e.1 omega
    let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
    let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
    let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
    let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
    (D.fermionicSummand closed W + D.fermionicSummand opened W) -
        (D.fermionicSummand closed E + D.fermionicSummand opened E) =
      Complex.I *
        ((D.fermionicSummand closed S + D.fermionicSummand opened S) -
          (D.fermionicSummand closed N + D.fermionicSummand opened N)) := by
  classical
  let D := fkIsingSquareWiredDobrushinDomain n hn
  let closed := setClosed e.1 omega
  let opened := setOpen e.1 omega
  let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
  let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
  let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
  let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
  let p := fkIsingSquareWiredExplorationOrder n hn closed
  change (D.fermionicSummand closed W + D.fermionicSummand opened W) -
      (D.fermionicSummand closed E + D.fermionicSummand opened E) =
    Complex.I *
      ((D.fermionicSummand closed S + D.fermionicSummand opened S) -
        (D.fermionicSummand closed N + D.fermionicSummand opened N))
  have hSW := fkIsingSquareWired_closed_south_west_oriented_infix
    n hn omega e hwest
  have hNE := fkIsingSquareWired_closed_north_east_oriented_infix
    n hn omega e heast
  have hiSW := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareWiredExplorationOrder_nodup n hn closed) hSW
  have hiNE := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareWiredExplorationOrder_nodup n hn closed) hNE
  change p.idxOf W = p.idxOf S + 1 at hiSW
  change p.idxOf E = p.idxOf N + 1 at hiNE
  have hW : W ∈ D.exploration closed := by
    rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
    exact hwest
  have hE : E ∈ D.exploration closed := by
    rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
    exact heast
  have hS : S ∈ D.exploration closed := by
    rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
    simpa only [p, closed, S] using hSW.mem (by simp)
  have hN : N ∈ D.exploration closed := by
    rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
    simpa only [p, closed, N] using hNE.mem (by simp)
  have hmass :=
    fkIsingSquareWiredExhaustive_double_visit_criticalMass_open_eq_sqrtTwo_mul_closed
      n hn omega e hwest heast
  have hmassC : (D.criticalMass opened : Complex) =
      (Real.sqrt 2 : Complex) * (D.criticalMass closed : Complex) := by
    exact_mod_cast hmass
  have hsource := fkIsingSquareWired_double_visit_source_side_phase
    n hn omega e hwest heast
  rcases hsource with ⟨hWN, hphaseS⟩ | ⟨hES, hphaseN⟩
  · have hopenE :=
      fkIsingSquareWired_double_visit_open_east_of_west_before_north
        n hn omega e hwest heast hWN
    obtain ⟨hOW', hON', hOE', hOS'⟩ :=
      (fkIsingSquareWired_double_visit_open_pair_exact
        n hn omega e hwest heast).resolve_left (by
          rintro ⟨_, _, hnotE, _⟩
          exact hnotE hopenE)
    have hOW : W ∉ D.exploration opened := by
      rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
      exact hOW'
    have hON : N ∉ D.exploration opened := by
      rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
      exact hON'
    have hOE : E ∈ D.exploration opened := by
      rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
      exact hOE'
    have hOS : S ∈ D.exploration opened := by
      rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
      exact hOS'
    have hphaseE : D.windingPhase opened E = D.windingPhase closed E := by
      rcases fkIsingSquareWired_double_visit_terminal_side_phase
          n hn omega e hwest heast with ⟨_, h⟩ | ⟨hES', _⟩
      · simpa only [D, opened, closed, E,
          fkIsingSquareWiredDobrushinDomain] using h
      · change p.idxOf E < p.idxOf S at hES'
        change p.idxOf W < p.idxOf N at hWN
        omega
    have hcS := fkIsingSquareWired_closed_west_south_phase
      n hn omega e hwest
    have hcN := fkIsingSquareWired_closed_east_north_phase
      n hn omega e heast
    have hoS := fkIsingSquareWired_open_east_south_phase
      n hn omega e hopenE
    unfold FKIsingDobrushinDomain.fermionicSummand
    rw [if_pos hW, if_neg hOW, if_pos hE, if_pos hOE,
      if_pos hS, if_pos hOS, if_pos hN, if_neg hON, hmassC]
    simp only [add_zero]
    apply fkIsingSquare_caseThree_eastSouth_contour_algebra
    · simpa only [D, closed, W, S,
        fkIsingSquareWiredDobrushinDomain] using hcS
    · simpa only [D, closed, E, N,
        fkIsingSquareWiredDobrushinDomain] using hcN
    · simpa only [D, opened, E, S,
        fkIsingSquareWiredDobrushinDomain] using hoS
    · exact hphaseS
    · exact hphaseE
  · have hopenW :=
      fkIsingSquareWired_double_visit_open_west_of_east_before_south
        n hn omega e hwest heast hES
    obtain ⟨hOW', hON', hOE', hOS'⟩ :=
      (fkIsingSquareWired_double_visit_open_pair_exact
        n hn omega e hwest heast).resolve_right (by
          rintro ⟨hnotW, _⟩
          exact hnotW hopenW)
    have hOW : W ∈ D.exploration opened := by
      rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
      exact hOW'
    have hON : N ∈ D.exploration opened := by
      rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
      exact hON'
    have hOE : E ∉ D.exploration opened := by
      rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
      exact hOE'
    have hOS : S ∉ D.exploration opened := by
      rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
      exact hOS'
    have hphaseW : D.windingPhase opened W = D.windingPhase closed W := by
      rcases fkIsingSquareWired_double_visit_terminal_side_phase
          n hn omega e hwest heast with ⟨hWN', _⟩ | ⟨_, h⟩
      · change p.idxOf W < p.idxOf N at hWN'
        change p.idxOf E < p.idxOf S at hES
        omega
      · simpa only [D, opened, closed, W,
          fkIsingSquareWiredDobrushinDomain] using h
    have hcS := fkIsingSquareWired_closed_west_south_phase
      n hn omega e hwest
    have hcN := fkIsingSquareWired_closed_east_north_phase
      n hn omega e heast
    have hoN := fkIsingSquareWired_open_west_north_phase
      n hn omega e hopenW
    unfold FKIsingDobrushinDomain.fermionicSummand
    rw [if_pos hW, if_pos hOW, if_pos hE, if_neg hOE,
      if_pos hS, if_neg hOS, if_pos hN, if_pos hON, hmassC]
    simp only [add_zero]
    apply fkIsingSquare_caseThree_westNorth_contour_algebra
    · simpa only [D, closed, W, S,
        fkIsingSquareWiredDobrushinDomain] using hcS
    · simpa only [D, closed, E, N,
        fkIsingSquareWiredDobrushinDomain] using hcN
    · simpa only [D, opened, W, N,
        fkIsingSquareWiredDobrushinDomain] using hoN
    · exact hphaseN
    · exact hphaseW



def fkIsingSquareWired_exhaustiveSwitchingLaw
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    (fkIsingSquareWiredDobrushinDomain n hn).ExhaustiveExplorationSwitchingLaw := by
  let D := fkIsingSquareWiredDobrushinDomain n hn
  refine {
    crossingEdge := e.1
    edges := fkIsingSquareWiredLocalCarrierDarts n e
    caseAt := ?_ }
  intro omega
  apply Classical.choice
  rcases fkIsingSquareWired_local_switch_component_classification
      n hn omega e with hzero | hwest | heast | hdouble
  · rcases hzero with ⟨hWTrace, hETrace, hopenTrace⟩
    have hW : ¬fkIsingSquareWiredPathUsesLocalSide n hn
        (setClosed e.1 omega) e .west := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hWTrace
    have hE : ¬fkIsingSquareWiredPathUsesLocalSide n hn
        (setClosed e.1 omega) e .east := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hETrace
    have hS : ¬fkIsingSquareWiredPathUsesLocalSide n hn
        (setClosed e.1 omega) e .south := by
      intro hS
      apply hW
      have hSmem : (.dart (e, .south) : FKIsingSquareWiredCarrier n) ∈
          (fkIsingSquareWiredDobrushinDomain n hn).exploration
            (setClosed e.1 omega) := by
        rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
        exact hS
      have hWmem := (fkIsingSquareWired_closed_west_mem_iff_south
        n hn omega e).2 hSmem
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hWmem
    have hN : ¬fkIsingSquareWiredPathUsesLocalSide n hn
        (setClosed e.1 omega) e .north := by
      intro hN
      apply hE
      have hNmem : (.dart (e, .north) : FKIsingSquareWiredCarrier n) ∈
          (fkIsingSquareWiredDobrushinDomain n hn).exploration
            (setClosed e.1 omega) := by
        rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
        exact hN
      have hEmem := (fkIsingSquareWired_closed_east_mem_iff_north
        n hn omega e).2 hNmem
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hEmem
    have hopen (side) : ¬fkIsingSquareWiredPathUsesLocalSide n hn
        (setOpen e.1 omega) e side := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hopenTrace side
    refine ⟨FKIsingDobrushinDomain.PointwiseExplorationSwitchingCase.caseOne ?_ ?_⟩
    · intro k
      rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
      fin_cases k
      · exact hW
      · exact hE
      · exact hS
      · exact hN
    · intro k
      rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
      fin_cases k
      · exact hopen .west
      · exact hopen .east
      · exact hopen .south
      · exact hopen .north
  · rcases hwest with ⟨hWTrace, hETrace, hopenTrace⟩
    have hW : fkIsingSquareWiredPathUsesLocalSide n hn
        (setClosed e.1 omega) e .west := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hWTrace
    have hE : ¬fkIsingSquareWiredPathUsesLocalSide n hn
        (setClosed e.1 omega) e .east := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hETrace
    have hopen (side) : fkIsingSquareWiredPathUsesLocalSide n hn
        (setOpen e.1 omega) e side := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hopenTrace side
    exact ⟨FKIsingDobrushinDomain.PointwiseExplorationSwitchingCase.caseTwo
      (fkIsingSquareWired_one_visit_west_contour_balance
      n hn omega e hW hE hopen
        (fkIsingSquareWired_one_visit_west_phase n hn omega e hW hE)
        (fkIsingSquareWired_one_visit_west_inserted_phase
          n hn omega e hW hE))⟩
  · rcases heast with ⟨hWTrace, hETrace, hopenTrace⟩
    have hW : ¬fkIsingSquareWiredPathUsesLocalSide n hn
        (setClosed e.1 omega) e .west := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hWTrace
    have hE : fkIsingSquareWiredPathUsesLocalSide n hn
        (setClosed e.1 omega) e .east := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hETrace
    have hopen (side) : fkIsingSquareWiredPathUsesLocalSide n hn
        (setOpen e.1 omega) e side := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hopenTrace side
    exact ⟨FKIsingDobrushinDomain.PointwiseExplorationSwitchingCase.caseTwo
      (fkIsingSquareWired_one_visit_east_contour_balance
      n hn omega e hW hE hopen
        (fkIsingSquareWired_one_visit_east_phase n hn omega e hW hE)
        (fkIsingSquareWired_one_visit_east_inserted_phase
          n hn omega e hW hE))⟩
  · rcases hdouble with ⟨hWTrace, hETrace⟩
    have hW : fkIsingSquareWiredPathUsesLocalSide n hn
        (setClosed e.1 omega) e .west := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hWTrace
    have hE : fkIsingSquareWiredPathUsesLocalSide n hn
        (setClosed e.1 omega) e .east := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hETrace
    exact ⟨FKIsingDobrushinDomain.PointwiseExplorationSwitchingCase.caseThree
      (fkIsingSquareWired_double_visit_pointwise_contour_balance
        n hn omega e hW hE)⟩



theorem fkIsingSquareWired_fermionicObservable_contour_relation
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    let D := fkIsingSquareWiredDobrushinDomain n hn
    let edges := fkIsingSquareWiredLocalCarrierDarts n e
    D.fermionicObservable (edges 0) - D.fermionicObservable (edges 1) =
      Complex.I *
        (D.fermionicObservable (edges 2) - D.fermionicObservable (edges 3)) := by
  let D := fkIsingSquareWiredDobrushinDomain n hn
  let L := fkIsingSquareWired_exhaustiveSwitchingLaw n hn e
  simpa only [D, L, fkIsingSquareWired_exhaustiveSwitchingLaw] using
    L.fermionicObservable_contour_relation D



theorem fkIsingSquareWired_double_visit_discarded_carrier_cycle_turn_mod_sixteen
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    (∃ c : (fkIsingSquareWiredCompletedLoopGraph n hn
          (setOpen e.1 omega)).Walk
            (.dart (e, .west)) (.dart (e, .west)),
        c.IsCycle ∧ c.snd = (.dart (e, .north) :
          FKIsingSquareWiredCarrier n) ∧
        carrierAdjacentSum
          (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega))
          c.support ≡ 8 [ZMOD 16]) ∨
      (∃ c : (fkIsingSquareWiredCompletedLoopGraph n hn
          (setOpen e.1 omega)).Walk
            (.dart (e, .east)) (.dart (e, .east)),
        c.IsCycle ∧ c.snd = (.dart (e, .south) :
          FKIsingSquareWiredCarrier n) ∧
        carrierAdjacentSum
          (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega))
          c.support ≡ 8 [ZMOD 16]) := by
  let opened := setOpen e.1 omega
  rcases fkIsingSquareWired_double_visit_open_pair_exact
      n hn omega e hwest heast with
    ⟨hW, _hN, _hE, _hS⟩ | ⟨_hW, _hN, hE, _hS⟩
  · right
    let d : FKIsingMedialDart (fkSquareBoxPlanar n) := (e, .east)
    have hroot : ¬(fkIsingSquareWiredCompletedLoopGraph n hn opened).Reachable
        (fkIsingSquareWiredBlackOfDart n d).1 .source := by
      intro hreach
      apply _hE
      rw [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_reachable,
        ← fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff]
      simpa only [opened, d, fkIsingSquareWiredBlackOfDart] using hreach.symm
    obtain ⟨c, hc, hcSnd, hcTurn⟩ :=
      fkIsingSquareWiredCompletedGraph_exists_carrier_cycle_of_local_black_orbit
        n hn opened d hroot
    have hmod := fkIsingSquareWired_local_black_orbit_transition_turn_mod_sixteen
      n hn opened d hroot
    dsimp only at hmod
    rw [← hcTurn] at hmod
    refine ⟨c, hc, ?_, hmod⟩
    simpa [opened, d, fkIsingSquareWiredBlackOfDart,
      fkIsingSquareWiredTransitionMate, FKIsingMedialDart.localMate,
      setOpen_self] using hcSnd
  · left
    let d : FKIsingMedialDart (fkSquareBoxPlanar n) := (e, .west)
    have hroot : ¬(fkIsingSquareWiredCompletedLoopGraph n hn opened).Reachable
        (fkIsingSquareWiredBlackOfDart n d).1 .source := by
      intro hreach
      apply _hW
      rw [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_reachable,
        ← fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff]
      simpa only [opened, d, fkIsingSquareWiredBlackOfDart] using hreach.symm
    obtain ⟨c, hc, hcSnd, hcTurn⟩ :=
      fkIsingSquareWiredCompletedGraph_exists_carrier_cycle_of_local_black_orbit
        n hn opened d hroot
    have hmod := fkIsingSquareWired_local_black_orbit_transition_turn_mod_sixteen
      n hn opened d hroot
    dsimp only at hmod
    rw [← hcTurn] at hmod
    refine ⟨c, hc, ?_, hmod⟩
    simpa [opened, d, fkIsingSquareWiredBlackOfDart,
      fkIsingSquareWiredTransitionMate, FKIsingMedialDart.localMate,
      setOpen_self] using hcSnd

end

end StatMech.Universality
