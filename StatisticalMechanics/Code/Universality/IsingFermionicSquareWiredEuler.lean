/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicSquareWiredSwitching
import Code.FrontierA.FKTutte










open Finset

namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

private theorem fkIsingSquareWiredEuler_openCount_toggle
    (n : Nat)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    openCount (fkSquareBoxPlanar n).G (setOpen e.1 omega) =
      openCount (fkSquareBoxPlanar n).G (setClosed e.1 omega) + 1 := by
  classical
  unfold openCount
  have hfilter :
      (fkSquareBoxPlanar n).G.edgeFinset.filter
          (fun f => setOpen e.1 omega f = true) =
        insert e.1 ((fkSquareBoxPlanar n).G.edgeFinset.filter
          (fun f => setClosed e.1 omega f = true)) := by
    ext f
    by_cases hf : f = e.1
    · subst f
      simp [e.2]
    · simp [setOpen, setClosed, hf]
  rw [hfilter, Finset.card_insert_of_notMem]
  simp



theorem fkIsingSquareWired_completedLoop_componentCount_of_not_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hsep : ¬ (openSub (fkSquareBoxPlanar n).G (setClosed e.1 omega) ⊔
        (fkIsingSquareWiredDobrushinDomain n hn).wiring).Reachable
      (fkIsingSquareOrientedEdge n e).tail
      (fkIsingSquareOrientedEdge n e).head) :
    Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn
        (setOpen e.1 omega)).ConnectedComponent + 1 =
      Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn
        (setClosed e.1 omega)).ConnectedComponent := by
  let G := fkIsingSquareWiredCompletedLoopGraph n hn (setClosed e.1 omega)
  let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
  let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
  let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
  let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
  have hWS : G.Adj W S := by
    simpa only [G, W, S] using
      fkIsingSquareWiredCompletedLoopGraph_closed_west_south_adj n hn omega e
  have hEN : G.Adj E N := by
    simpa only [G, E, N] using
      fkIsingSquareWiredCompletedLoopGraph_closed_east_north_adj n hn omega e
  have hWE : ¬ G.Reachable W E := by
    intro h
    have hloop : (fkIsingSquareWiredLoopGraph n hn
        (setClosed e.1 omega)).Reachable W E :=
      (fkIsingSquareWiredCompletedLoopGraph_reachable_iff
        n hn (setClosed e.1 omega) W E).1 h
    have hprimal :=
      fkIsingSquareWiredLoopGraph_reachable_primalLabel_reachable
        n hn (setClosed e.1 omega) hloop
    apply hsep
    simpa [W, E, fkIsingSquareWiredCarrierPrimalLabel,
      fkIsingSquareDartEndpoint, fkIsingSquareSideCorner,
      FKIsingDobrushinDomain.wiring,
      fkIsingSquareWiredDobrushinDomain] using hprimal
  have hcount := card_components_twoEdgeSwitch_of_not_reachable G
    (fkIsingSquareWiredCompletedLoopGraph_even_degree n hn
      (setClosed e.1 omega)) hWS hEN hWE
  rw [fkIsingSquareWiredCompletedLoopGraph_setOpen_eq_twoEdgeSwitch
    n hn omega e]
  simpa only [G, W, S, E, N, medialTwoEdgeSwitch] using hcount



theorem fkIsingSquareWiredEulerDefect_setOpen_eq_setClosed_of_not_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hsep : ¬ (openSub (fkSquareBoxPlanar n).G (setClosed e.1 omega) ⊔
        (fkIsingSquareWiredDobrushinDomain n hn).wiring).Reachable
      (fkIsingSquareOrientedEdge n e).tail
      (fkIsingSquareOrientedEdge n e).head) :
    fkIsingSquareWiredEulerDefect n hn (setOpen e.1 omega) =
      fkIsingSquareWiredEulerDefect n hn (setClosed e.1 omega) := by
  let a := (fkIsingSquareOrientedEdge n e).tail
  let b := (fkIsingSquareOrientedEdge n e).head
  have hab : (fkSquareBoxPlanar n).G.Adj a b := by
    rw [← SimpleGraph.mem_edgeSet, fkIsingSquareOrientedEdge_eq n e]
    exact e.2
  have hedge : s(a, b) = e.1 := by
    simpa only [a, b] using fkIsingSquareOrientedEdge_eq n e
  have hk0 :=
    FKIsingDobrushinDomain.numClustersBC_setClosed_eq_setOpen_add_one_of_not_reachable
      (fkIsingSquareWiredDobrushinDomain n hn) a b hab omega (by
        simpa only [a, b, fkIsingSquareOrientedEdge_eq n e] using hsep)
  have hk :
      numClustersBC (fkSquareBoxPlanar n).G
          (fkIsingSquareWiredDobrushinDomain n hn).wiring
          (setClosed e.1 omega) =
        numClustersBC (fkSquareBoxPlanar n).G
          (fkIsingSquareWiredDobrushinDomain n hn).wiring
          (setOpen e.1 omega) + 1 := by
    simpa only [hedge] using hk0
  have hm := fkIsingSquareWiredEuler_openCount_toggle n omega e
  have hL :=
    fkIsingSquareWired_completedLoop_componentCount_of_not_reachable
      n hn omega e hsep
  unfold fkIsingSquareWiredEulerDefect
  push_cast
  omega



theorem fkIsingSquareWiredEulerDefect_setClosed_le_setOpen
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredEulerDefect n hn (setClosed e.1 omega) ≤
      fkIsingSquareWiredEulerDefect n hn (setOpen e.1 omega) := by
  let a := (fkIsingSquareOrientedEdge n e).tail
  let b := (fkIsingSquareOrientedEdge n e).head
  have hab : (fkSquareBoxPlanar n).G.Adj a b := by
    rw [← SimpleGraph.mem_edgeSet, fkIsingSquareOrientedEdge_eq n e]
    exact e.2
  have hedge : s(a, b) = e.1 := by
    simpa only [a, b] using fkIsingSquareOrientedEdge_eq n e
  by_cases hsep : ¬
      (openSub (fkSquareBoxPlanar n).G (setClosed e.1 omega) ⊔
        (fkIsingSquareWiredDobrushinDomain n hn).wiring).Reachable a b
  · exact (fkIsingSquareWiredEulerDefect_setOpen_eq_setClosed_of_not_reachable
      n hn omega e (by simpa only [a, b] using hsep)).ge
  · have hreach :
        (openSub (fkSquareBoxPlanar n).G (setClosed e.1 omega) ⊔
          (fkIsingSquareWiredDobrushinDomain n hn).wiring).Reachable a b :=
        not_not.mp hsep
    have hk0 :=
      FKIsingDobrushinDomain.numClustersBC_setOpen_eq_setClosed_of_reachable
        (fkIsingSquareWiredDobrushinDomain n hn) a b hab omega (by
          simpa only [hedge] using hreach)
    have hk :
        numClustersBC (fkSquareBoxPlanar n).G
            (fkIsingSquareWiredDobrushinDomain n hn).wiring
            (setOpen e.1 omega) =
          numClustersBC (fkSquareBoxPlanar n).G
            (fkIsingSquareWiredDobrushinDomain n hn).wiring
            (setClosed e.1 omega) := by
      simpa only [hedge] using hk0
    have hm := fkIsingSquareWiredEuler_openCount_toggle n omega e
    let G := fkIsingSquareWiredCompletedLoopGraph n hn (setClosed e.1 omega)
    let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
    let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
    let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
    let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
    have hWS : G.Adj W S := by
      simpa only [G, W, S] using
        fkIsingSquareWiredCompletedLoopGraph_closed_west_south_adj n hn omega e
    have hL := card_components_twoEdgeSwitch_le_add_one G
      (fkIsingSquareWiredCompletedLoopGraph_even_degree n hn
        (setClosed e.1 omega)) (c := E) (d := N) hWS
    have hL' :
        Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn
            (setOpen e.1 omega)).ConnectedComponent ≤
          Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn
            (setClosed e.1 omega)).ConnectedComponent + 1 := by
      rw [fkIsingSquareWiredCompletedLoopGraph_setOpen_eq_twoEdgeSwitch
        n hn omega e]
      simpa only [G, W, S, E, N, medialTwoEdgeSwitch] using hL
    unfold fkIsingSquareWiredEulerDefect
    push_cast
    omega



theorem fkIsingSquareWiredEulerDefect_congr_on_edges
    (n : Nat) (hn : 0 < n)
    (omega eta : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (hagree : ∀ f ∈ (fkSquareBoxPlanar n).G.edgeFinset,
      omega f = eta f) :
    fkIsingSquareWiredEulerDefect n hn omega =
      fkIsingSquareWiredEulerDefect n hn eta := by
  classical
  have hopen : openSub (fkSquareBoxPlanar n).G omega =
      openSub (fkSquareBoxPlanar n).G eta := by
    ext x y
    simp only [openSub_adj]
    by_cases hxy : (fkSquareBoxPlanar n).G.Adj x y
    · simp only [hxy, true_and]
      rw [hagree s(x, y)
        (by simpa only [SimpleGraph.mem_edgeFinset] using hxy)]
    · simp only [hxy, false_and]
  have hcount : openCount (fkSquareBoxPlanar n).G omega =
      openCount (fkSquareBoxPlanar n).G eta := by
    unfold openCount
    congr 1
    ext f
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hf, hopenf⟩
      exact ⟨hf, by rwa [← hagree f hf]⟩
    · rintro ⟨hf, hopenf⟩
      exact ⟨hf, by rwa [hagree f hf]⟩
  have htransition : fkIsingSquareWiredTransitionMate n hn omega =
      fkIsingSquareWiredTransitionMate n hn eta := by
    funext x
    cases x with
    | source => rfl
    | terminal => rfl
    | bond d => rfl
    | dart d =>
        have hd : omega d.1 = eta d.1 :=
          hagree d.1 (by
            simpa only [SimpleGraph.mem_edgeFinset] using d.1.2)
        cases d with
        | mk e side =>
            cases side <;>
              simp [fkIsingSquareWiredTransitionMate,
                FKIsingMedialDart.localMate, hd]
  have hgraph : fkIsingSquareWiredCompletedLoopGraph n hn omega =
      fkIsingSquareWiredCompletedLoopGraph n hn eta := by
    ext x y
    simp only [fkIsingSquareWiredCompletedLoopGraph,
      SimpleGraph.sup_adj, fkIsingSquareWiredLoopGraph]
    rw [htransition]
  unfold fkIsingSquareWiredEulerDefect numClustersBC
  rw [hopen, hcount, hgraph]




theorem fkIsingSquareWiredEulerDefect_eq_of_empty_full_eq
    (n : Nat) (hn : 0 < n)
    (hends :
      fkIsingSquareWiredEulerDefect n hn
          (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset) =
        fkIsingSquareWiredEulerDefect n hn (FK.edgeSetConfig ∅))
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    fkIsingSquareWiredEulerDefect n hn omega =
      fkIsingSquareWiredEulerDefect n hn (FK.edgeSetConfig ∅) := by
  classical
  let E := (fkSquareBoxPlanar n).G.edgeFinset
  let defect := fkIsingSquareWiredEulerDefect n hn
  let F : Finset (Sym2 (fkSquareBoxPlanar n).V) → Int :=
    fun A => defect (FK.edgeSetConfig (A ∩ E))
  have hinsert : ∀ (A : Finset (Sym2 (fkSquareBoxPlanar n).V))
      (e : Sym2 (fkSquareBoxPlanar n).V), e ∉ A → F A ≤ F (insert e A) := by
    intro A e heA
    by_cases heE : e ∈ E
    · let em : FKIsingMedialVertex (fkSquareBoxPlanar n) :=
        ⟨e, by simpa only [E, SimpleGraph.mem_edgeFinset] using heE⟩
      have heAE : e ∉ A ∩ E := by simp [heA]
      have hclosed : setClosed e (FK.edgeSetConfig (A ∩ E)) =
          FK.edgeSetConfig (A ∩ E) := by
        funext f
        by_cases hfe : f = e
        · subst f
          simp [FK.edgeSetConfig, heAE]
        · simp [setClosed, hfe]
      have hopen : setOpen e (FK.edgeSetConfig (A ∩ E)) =
          FK.edgeSetConfig (insert e A ∩ E) := by
        funext f
        by_cases hfe : f = e
        · subst f
          simp [FK.edgeSetConfig, heE]
        · simp [FK.edgeSetConfig, setOpen, hfe]
      have hmono := fkIsingSquareWiredEulerDefect_setClosed_le_setOpen
        n hn (FK.edgeSetConfig (A ∩ E)) em
      simpa only [F, defect, em, hclosed, hopen] using hmono
    · have hinter : insert e A ∩ E = A ∩ E := by
        ext f
        simp only [Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hfA, hfE⟩
          · exact False.elim (heE hfE)
          · exact ⟨hfA, hfE⟩
        · rintro ⟨hfA, hfE⟩
          exact ⟨Or.inr hfA, hfE⟩
      rw [show F (insert e A) = F A by simp only [F, hinter]]
  have hmono : Monotone F :=
    Finset.monotone_iff_forall_le_insert.mpr hinsert
  let Aomega := E.filter (fun e => omega e = true)
  have hproject : ∀ e ∈ E, FK.edgeSetConfig Aomega e = omega e := by
    intro e he
    cases h : omega e
    · have hnot : e ∉ Aomega := by simp [Aomega, he, h]
      simp [FK.edgeSetConfig, hnot, h]
    · have hmem : e ∈ Aomega := by simp [Aomega, he, h]
      simp [FK.edgeSetConfig, hmem, h]
  have hcongr : defect omega = defect (FK.edgeSetConfig Aomega) := by
    exact fkIsingSquareWiredEulerDefect_congr_on_edges n hn omega
      (FK.edgeSetConfig Aomega) (fun e he => (hproject e he).symm)
  have hAE : Aomega ∩ E = Aomega := by
    apply Finset.inter_eq_left.mpr
    intro e he
    exact (Finset.mem_filter.mp he).1
  have hlower : F ∅ ≤ F Aomega := hmono (Finset.empty_subset Aomega)
  have hupper : F Aomega ≤ F Finset.univ := hmono (Finset.subset_univ Aomega)
  have hFempty : F ∅ = defect (FK.edgeSetConfig ∅) := by
    simp [F]
  have hFuniv : F Finset.univ = defect (FK.edgeSetConfig E) := by
    simp [F]
  have hFA : F Aomega = defect (FK.edgeSetConfig Aomega) := by
    simp only [F, hAE]
  rw [hFempty, hFA] at hlower
  rw [hFA, hFuniv] at hupper
  have hends' : defect (FK.edgeSetConfig E) =
      defect (FK.edgeSetConfig ∅) := by
    simpa only [defect, E] using hends
  rw [hends'] at hupper
  change defect omega = defect (FK.edgeSetConfig ∅)
  rw [hcongr]
  exact le_antisymm hupper hlower



theorem fkIsingSquareWiredEulerDefect_toggle_eq_of_empty_full_eq
    (n : Nat) (hn : 0 < n)
    (hends :
      fkIsingSquareWiredEulerDefect n hn
          (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset) =
        fkIsingSquareWiredEulerDefect n hn (FK.edgeSetConfig ∅))
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredEulerDefect n hn (setOpen e.1 omega) =
      fkIsingSquareWiredEulerDefect n hn (setClosed e.1 omega) := by
  calc
    fkIsingSquareWiredEulerDefect n hn (setOpen e.1 omega) =
        fkIsingSquareWiredEulerDefect n hn (FK.edgeSetConfig ∅) :=
      fkIsingSquareWiredEulerDefect_eq_of_empty_full_eq
        n hn hends (setOpen e.1 omega)
    _ = fkIsingSquareWiredEulerDefect n hn (setClosed e.1 omega) :=
      (fkIsingSquareWiredEulerDefect_eq_of_empty_full_eq
        n hn hends (setClosed e.1 omega)).symm

end

end StatMech.Universality
