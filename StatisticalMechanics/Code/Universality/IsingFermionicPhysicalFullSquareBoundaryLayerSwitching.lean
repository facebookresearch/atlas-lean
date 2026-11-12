/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayer










namespace StatMech.Universality

open Finset Complex SimpleGraph
open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareBoundary_openSub_eq_closePerimeter
    (n : Nat) (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    openSub (fkIsingSquareBoundaryDeletedPlanar n).G omega =
      openSub (fkSquareBoxPlanar n).G
        (fkIsingSquareClosePerimeter n omega) := by
  ext x y
  simp [openSub_adj, fkIsingSquareBoundaryDeletedPlanar,
    SimpleGraph.deleteEdges_adj, fkIsingSquareClosePerimeter]
  tauto

theorem fkIsingSquareClosePerimeter_setClosed
    (n : Nat) (e : Sym2 (fkSquareBoxPlanar n).V)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    fkIsingSquareClosePerimeter n (setClosed e omega) =
      setClosed e (fkIsingSquareClosePerimeter n omega) := by
  funext f
  by_cases hf : f = e
  · subst f
    simp [fkIsingSquareClosePerimeter, setClosed]
  · simp [fkIsingSquareClosePerimeter, setClosed, hf]

theorem fkIsingSquareClosePerimeter_setOpen_of_not_mem
    (n : Nat) (e : Sym2 (fkSquareBoxPlanar n).V)
    (he : e ∉ fkIsingSquarePerimeterPrimalEdgeFinset n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    fkIsingSquareClosePerimeter n (setOpen e omega) =
      setOpen e (fkIsingSquareClosePerimeter n omega) := by
  funext f
  by_cases hf : f = e
  · subst f
    simp [fkIsingSquareClosePerimeter, setOpen, he]
  · simp [fkIsingSquareClosePerimeter, setOpen, hf]

theorem fkIsingSquareBoundaryDeleted_adj_iff
    (n : Nat) (a b : (fkSquareBoxPlanar n).V) :
    (fkIsingSquareBoundaryDeletedPlanar n).G.Adj a b ↔
      (fkSquareBoxPlanar n).G.Adj a b ∧
        s(a, b) ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
  simp [fkIsingSquareBoundaryDeletedPlanar, SimpleGraph.deleteEdges_adj]

theorem fkIsingSquareBoundary_wiring_eq_wired
    (n : Nat) (hn : 0 < n) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).wiring =
      (fkIsingSquareWiredDobrushinDomain n hn).wiring := rfl

theorem fkIsingSquareBoundary_openWiringGraph_eq_closePerimeter
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    openSub (fkIsingSquareBoundaryDeletedPlanar n).G omega ⊔
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).wiring =
      openSub (fkSquareBoxPlanar n).G
          (fkIsingSquareClosePerimeter n omega) ⊔
        (fkIsingSquareWiredDobrushinDomain n hn).wiring := by
  rw [fkIsingSquareBoundary_openSub_eq_closePerimeter,
    fkIsingSquareBoundary_wiring_eq_wired]
  rfl

theorem fkIsingSquareBoundary_numClustersBC_eq_closePerimeter
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    numClustersBC (fkIsingSquareBoundaryDeletedPlanar n).G
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).wiring omega =
      numClustersBC (fkSquareBoxPlanar n).G
        (fkIsingSquareWiredDobrushinDomain n hn).wiring
          (fkIsingSquareClosePerimeter n omega) := by
  unfold numClustersBC
  rw [fkIsingSquareBoundary_openWiringGraph_eq_closePerimeter]
  rfl

@[simp] theorem fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (c : FKIsingSquareWiredCarrier n) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).windingPhase
        omega c =
      (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
        (fkIsingSquareClosePerimeter n omega) c := rfl



theorem fkIsingSquareBoundary_one_visit_west_contour_balance
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (he : e.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n)
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 (fkIsingSquareClosePerimeter n omega)) e .west)
    (heast : ¬fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 (fkIsingSquareClosePerimeter n omega)) e .east)
    (hopen : forall side, fkIsingSquareWiredPathUsesLocalSide n hn
      (setOpen e.1 (fkIsingSquareClosePerimeter n omega)) e side) :
    let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
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
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let omega' := fkIsingSquareClosePerimeter n omega
  let closed := setClosed e.1 omega
  let opened := setOpen e.1 omega
  let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
  let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
  let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
  let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
  let a := (fkIsingSquareOrientedEdge n e).tail
  let b := (fkIsingSquareOrientedEdge n e).head
  have habFull : (fkSquareBoxPlanar n).G.Adj a b := by
    rw [<- SimpleGraph.mem_edgeSet, fkIsingSquareOrientedEdge_eq n e]
    exact e.2
  have hedge : s(a, b) = e.1 := by
    simpa only [a, b] using fkIsingSquareOrientedEdge_eq n e
  have hclosed : setClosed s(a, b) omega = closed := by
    exact (congrArg (fun f => setClosed f omega) hedge).trans rfl
  have hopened : setOpen s(a, b) omega = opened := by
    exact (congrArg (fun f => setOpen f omega) hedge).trans rfl
  have hab : (fkIsingSquareBoundaryDeletedPlanar n).G.Adj a b := by
    apply (fkIsingSquareBoundaryDeleted_adj_iff n a b).2
    exact ⟨habFull, by
      simpa only [a, b, fkIsingSquareOrientedEdge_eq n e] using he⟩
  have hseparatedFull := fkIsingSquareWired_one_visit_separated
    n hn omega' e (Or.inl ⟨hwest, heast⟩)
  have hseparated : ¬
      (openSub (fkIsingSquareBoundaryDeletedPlanar n).G closed ⊔
        D.wiring).Reachable a b := by
    rw [fkIsingSquareBoundary_openWiringGraph_eq_closePerimeter,
      fkIsingSquareClosePerimeter_setClosed]
    simpa only [D, omega', closed, a, b] using hseparatedFull
  have hclusterFull :
      numClustersBC (fkSquareBoxPlanar n).G
          (fkIsingSquareWiredDobrushinDomain n hn).wiring
          (setClosed e.1 omega') =
        numClustersBC (fkSquareBoxPlanar n).G
          (fkIsingSquareWiredDobrushinDomain n hn).wiring
          (setOpen e.1 omega') + 1 := by
    have h := (fkIsingSquareWiredDobrushinDomain n hn).numClustersBC_setClosed_eq_setOpen_add_one_of_not_reachable
        a b habFull omega' (by
          simpa only [a, b, fkIsingSquareOrientedEdge_eq n e] using
            hseparatedFull)
    simpa only [a, b, fkIsingSquareOrientedEdge_eq n e] using h
  have hcluster :
      numClustersBC (fkIsingSquareBoundaryDeletedPlanar n).G D.wiring closed =
        numClustersBC (fkIsingSquareBoundaryDeletedPlanar n).G D.wiring opened + 1 := by
    rw [fkIsingSquareBoundary_numClustersBC_eq_closePerimeter,
      fkIsingSquareBoundary_numClustersBC_eq_closePerimeter,
      fkIsingSquareClosePerimeter_setClosed,
      fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he]
    exact hclusterFull
  have hmass := D.sqrtTwo_mul_criticalMass_setOpen_eq_setClosed_of_clusterMerge
    (by
      rw [SimpleGraph.mem_edgeFinset]
      change e.1 ∈ ((fkSquareBoxPlanar n).G.deleteEdges
        (fkIsingSquarePerimeterPrimalEdgeFinset n : Set _)).edgeSet
      rw [SimpleGraph.edgeSet_deleteEdges]
      exact ⟨e.2, by simpa using he⟩) omega hcluster
  have hmassC : (D.criticalMass closed : Complex) =
      (Real.sqrt 2 : Complex) * (D.criticalMass opened : Complex) := by
    exact_mod_cast hmass.symm
  have hcW : W ∈ D.exploration closed := by
    simpa only [D, omega', closed, W,
      fkIsingSquareBoundaryRestrictedDobrushinDomain,
      fkIsingSquareClosePerimeter_setClosed] using hwest
  have hcS : S ∈ D.exploration closed := by
    have htrace : (.dart (e, .west) : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega') := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hwest
    have h := (fkIsingSquareWired_closed_west_mem_iff_south
      n hn omega' e).1 htrace
    have horder : S ∈ fkIsingSquareWiredExplorationOrder n hn
        (setClosed e.1 omega') := by
      rw [mem_fkIsingSquareWiredExplorationOrder_iff_trace]
      exact h
    simpa only [D, omega', closed, S,
      fkIsingSquareBoundaryRestrictedDobrushinDomain,
      fkIsingSquareClosePerimeter_setClosed] using horder
  have hcE : E ∉ D.exploration closed := by
    simpa only [D, omega', closed, E,
      fkIsingSquareBoundaryRestrictedDobrushinDomain,
      fkIsingSquareClosePerimeter_setClosed] using heast
  have hcN : N ∉ D.exploration closed := by
    intro hN
    apply heast
    rw [fkIsingSquareWiredPathUsesLocalSide,
      mem_fkIsingSquareWiredExplorationOrder_iff_trace]
    apply (fkIsingSquareWired_closed_east_mem_iff_north n hn omega' e).2
    rw [<- mem_fkIsingSquareWiredExplorationOrder_iff_trace]
    simpa only [D, omega', closed, N,
      fkIsingSquareBoundaryRestrictedDobrushinDomain,
      fkIsingSquareClosePerimeter_setClosed] using hN
  have ho (side : FKIsingMedialSide) :
      (.dart (e, side) : FKIsingSquareWiredCarrier n) ∈
        D.exploration opened := by
    simpa only [D, omega', opened,
      fkIsingSquareBoundaryRestrictedDobrushinDomain,
      fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using hopen side
  have hcSphase : D.windingPhase closed S = isingLambda⁻¹ *
      D.windingPhase closed W := by
    simpa only [D, omega', closed, W, S,
      fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter,
      fkIsingSquareClosePerimeter_setClosed] using
        (fkIsingSquareWired_closed_west_south_phase n hn omega' e hwest)
  have hoNphase : D.windingPhase opened N = isingLambda *
      D.windingPhase opened W := by
    simpa only [D, omega', opened, W, N,
      fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter,
      fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using
        (fkIsingSquareWired_open_west_north_phase n hn omega' e (hopen .west))
  have hoSphase : D.windingPhase opened S = isingLambda *
      D.windingPhase opened E := by
    simpa only [D, omega', opened, E, S,
      fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter,
      fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using
        (fkIsingSquareWired_open_east_south_phase n hn omega' e (hopen .east))
  have hphaseW : D.windingPhase opened W = D.windingPhase closed W := by
    simpa only [D, omega', opened, closed, W,
      fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter,
      fkIsingSquareClosePerimeter_setClosed,
      fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using
        (fkIsingSquareWired_one_visit_west_phase n hn omega' e hwest heast)
  have hphaseS : D.windingPhase opened S = D.windingPhase closed S := by
    simpa only [D, omega', opened, closed, S,
      fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter,
      fkIsingSquareClosePerimeter_setClosed,
      fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using
        (fkIsingSquareWired_one_visit_west_inserted_phase
          n hn omega' e hwest heast)
  change (D.fermionicSummand closed W + D.fermionicSummand opened W) -
      (D.fermionicSummand closed E + D.fermionicSummand opened E) =
    Complex.I *
      ((D.fermionicSummand closed S + D.fermionicSummand opened S) -
        (D.fermionicSummand closed N + D.fermionicSummand opened N))
  unfold FKIsingDobrushinDomain.fermionicSummand
  rw [if_pos hcW, if_pos (ho .west), if_neg hcE, if_pos (ho .east),
    if_pos hcS, if_pos (ho .south), if_neg hcN, if_pos (ho .north),
    hmassC]
  simp only [zero_add]
  exact fkIsingSquare_caseTwo_westSouth_contour_algebra _ _ _ _ _ _ _
    hcSphase hoNphase hoSphase hphaseW hphaseS


theorem fkIsingSquareBoundary_one_visit_east_contour_balance
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (he : e.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n)
    (hwest : ¬fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 (fkIsingSquareClosePerimeter n omega)) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 (fkIsingSquareClosePerimeter n omega)) e .east)
    (hopen : forall side, fkIsingSquareWiredPathUsesLocalSide n hn
      (setOpen e.1 (fkIsingSquareClosePerimeter n omega)) e side) :
    let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
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
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let omega' := fkIsingSquareClosePerimeter n omega
  let closed := setClosed e.1 omega
  let opened := setOpen e.1 omega
  let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
  let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
  let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
  let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
  let a := (fkIsingSquareOrientedEdge n e).tail
  let b := (fkIsingSquareOrientedEdge n e).head
  have habFull : (fkSquareBoxPlanar n).G.Adj a b := by
    rw [<- SimpleGraph.mem_edgeSet, fkIsingSquareOrientedEdge_eq n e]
    exact e.2
  have hseparatedFull := fkIsingSquareWired_one_visit_separated
    n hn omega' e (Or.inr ⟨hwest, heast⟩)
  have hclusterFull :
      numClustersBC (fkSquareBoxPlanar n).G
          (fkIsingSquareWiredDobrushinDomain n hn).wiring
          (setClosed e.1 omega') =
        numClustersBC (fkSquareBoxPlanar n).G
          (fkIsingSquareWiredDobrushinDomain n hn).wiring
          (setOpen e.1 omega') + 1 := by
    have h := (fkIsingSquareWiredDobrushinDomain n hn).numClustersBC_setClosed_eq_setOpen_add_one_of_not_reachable
      a b habFull omega' (by
        simpa only [a, b, fkIsingSquareOrientedEdge_eq n e] using
          hseparatedFull)
    simpa only [a, b, fkIsingSquareOrientedEdge_eq n e] using h
  have hcluster :
      numClustersBC (fkIsingSquareBoundaryDeletedPlanar n).G D.wiring closed =
        numClustersBC (fkIsingSquareBoundaryDeletedPlanar n).G D.wiring opened + 1 := by
    rw [fkIsingSquareBoundary_numClustersBC_eq_closePerimeter,
      fkIsingSquareBoundary_numClustersBC_eq_closePerimeter,
      fkIsingSquareClosePerimeter_setClosed,
      fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he]
    exact hclusterFull
  have hmass := D.sqrtTwo_mul_criticalMass_setOpen_eq_setClosed_of_clusterMerge
    (by
      rw [SimpleGraph.mem_edgeFinset]
      change e.1 ∈ ((fkSquareBoxPlanar n).G.deleteEdges
        (fkIsingSquarePerimeterPrimalEdgeFinset n : Set _)).edgeSet
      rw [SimpleGraph.edgeSet_deleteEdges]
      exact ⟨e.2, by simpa using he⟩) omega hcluster
  have hmassC : (D.criticalMass closed : Complex) =
      (Real.sqrt 2 : Complex) * (D.criticalMass opened : Complex) := by
    exact_mod_cast hmass.symm
  have hcE : E ∈ D.exploration closed := by
    simpa only [D, omega', closed, E,
      fkIsingSquareBoundaryRestrictedDobrushinDomain,
      fkIsingSquareClosePerimeter_setClosed] using heast
  have hcN : N ∈ D.exploration closed := by
    have htrace : (.dart (e, .east) : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega') := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using heast
    have h := (fkIsingSquareWired_closed_east_mem_iff_north
      n hn omega' e).1 htrace
    have horder : N ∈ fkIsingSquareWiredExplorationOrder n hn
        (setClosed e.1 omega') := by
      rw [mem_fkIsingSquareWiredExplorationOrder_iff_trace]
      exact h
    simpa only [D, omega', closed, N,
      fkIsingSquareBoundaryRestrictedDobrushinDomain,
      fkIsingSquareClosePerimeter_setClosed] using horder
  have hcW : W ∉ D.exploration closed := by
    simpa only [D, omega', closed, W,
      fkIsingSquareBoundaryRestrictedDobrushinDomain,
      fkIsingSquareClosePerimeter_setClosed] using hwest
  have hcS : S ∉ D.exploration closed := by
    intro hS
    apply hwest
    rw [fkIsingSquareWiredPathUsesLocalSide,
      mem_fkIsingSquareWiredExplorationOrder_iff_trace]
    apply (fkIsingSquareWired_closed_west_mem_iff_south n hn omega' e).2
    rw [<- mem_fkIsingSquareWiredExplorationOrder_iff_trace]
    simpa only [D, omega', closed, S,
      fkIsingSquareBoundaryRestrictedDobrushinDomain,
      fkIsingSquareClosePerimeter_setClosed] using hS
  have ho (side : FKIsingMedialSide) :
      (.dart (e, side) : FKIsingSquareWiredCarrier n) ∈
        D.exploration opened := by
    simpa only [D, omega', opened,
      fkIsingSquareBoundaryRestrictedDobrushinDomain,
      fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using hopen side
  have hcNphase : D.windingPhase closed N = isingLambda⁻¹ *
      D.windingPhase closed E := by
    simpa only [D, omega', closed, E, N,
      fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter,
      fkIsingSquareClosePerimeter_setClosed] using
        (fkIsingSquareWired_closed_east_north_phase n hn omega' e heast)
  have hoNphase : D.windingPhase opened N = isingLambda *
      D.windingPhase opened W := by
    simpa only [D, omega', opened, W, N,
      fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter,
      fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using
        (fkIsingSquareWired_open_west_north_phase n hn omega' e (hopen .west))
  have hoSphase : D.windingPhase opened S = isingLambda *
      D.windingPhase opened E := by
    simpa only [D, omega', opened, E, S,
      fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter,
      fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using
        (fkIsingSquareWired_open_east_south_phase n hn omega' e (hopen .east))
  have hphaseE : D.windingPhase opened E = D.windingPhase closed E := by
    simpa only [D, omega', opened, closed, E,
      fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter,
      fkIsingSquareClosePerimeter_setClosed,
      fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using
        (fkIsingSquareWired_one_visit_east_phase n hn omega' e hwest heast)
  have hphaseN : D.windingPhase opened N = D.windingPhase closed N := by
    simpa only [D, omega', opened, closed, N,
      fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter,
      fkIsingSquareClosePerimeter_setClosed,
      fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using
        (fkIsingSquareWired_one_visit_east_inserted_phase
          n hn omega' e hwest heast)
  change (D.fermionicSummand closed W + D.fermionicSummand opened W) -
      (D.fermionicSummand closed E + D.fermionicSummand opened E) =
    Complex.I *
      ((D.fermionicSummand closed S + D.fermionicSummand opened S) -
        (D.fermionicSummand closed N + D.fermionicSummand opened N))
  unfold FKIsingDobrushinDomain.fermionicSummand
  rw [if_neg hcW, if_pos (ho .west), if_pos hcE, if_pos (ho .east),
    if_neg hcS, if_pos (ho .south), if_pos hcN, if_pos (ho .north),
    hmassC]
  simp only [zero_add]
  exact fkIsingSquare_caseTwo_eastNorth_contour_algebra _ _ _ _ _ _ _
    hcNphase hoNphase hoSphase hphaseE hphaseN

private theorem fkIsingSquareBoundary_double_visit_open_east
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
      n hn omega e hwest heast with ⟨hsplice, _⟩ | ⟨_, hES⟩
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

private theorem fkIsingSquareBoundary_double_visit_open_west
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
      n hn omega e hwest heast with ⟨_, hWN⟩ | ⟨hsplice, _⟩
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


theorem fkIsingSquareBoundary_double_visit_contour_balance
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (he : e.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n)
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 (fkIsingSquareClosePerimeter n omega)) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 (fkIsingSquareClosePerimeter n omega)) e .east) :
    let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
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
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let omega' := fkIsingSquareClosePerimeter n omega
  let closed := setClosed e.1 omega
  let opened := setOpen e.1 omega
  let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
  let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
  let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
  let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
  let p := fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega')
  change (D.fermionicSummand closed W + D.fermionicSummand opened W) -
      (D.fermionicSummand closed E + D.fermionicSummand opened E) =
    Complex.I *
      ((D.fermionicSummand closed S + D.fermionicSummand opened S) -
        (D.fermionicSummand closed N + D.fermionicSummand opened N))
  have hSW := fkIsingSquareWired_closed_south_west_oriented_infix
    n hn omega' e hwest
  have hNE := fkIsingSquareWired_closed_north_east_oriented_infix
    n hn omega' e heast
  have hiSW := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareWiredExplorationOrder_nodup n hn (setClosed e.1 omega')) hSW
  have hiNE := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareWiredExplorationOrder_nodup n hn (setClosed e.1 omega')) hNE
  change p.idxOf W = p.idxOf S + 1 at hiSW
  change p.idxOf E = p.idxOf N + 1 at hiNE
  have hW : W ∈ D.exploration closed := by
    simpa only [D, omega', closed, W,
      fkIsingSquareBoundaryRestrictedDobrushinDomain,
      fkIsingSquareClosePerimeter_setClosed] using hwest
  have hE : E ∈ D.exploration closed := by
    simpa only [D, omega', closed, E,
      fkIsingSquareBoundaryRestrictedDobrushinDomain,
      fkIsingSquareClosePerimeter_setClosed] using heast
  have hS : S ∈ D.exploration closed := by
    have horder : S ∈ fkIsingSquareWiredExplorationOrder n hn
        (setClosed e.1 omega') := by
      simpa only [p, S] using hSW.mem (by simp)
    simpa only [D, omega', closed, S,
      fkIsingSquareBoundaryRestrictedDobrushinDomain,
      fkIsingSquareClosePerimeter_setClosed] using horder
  have hN : N ∈ D.exploration closed := by
    have horder : N ∈ fkIsingSquareWiredExplorationOrder n hn
        (setClosed e.1 omega') := by
      simpa only [p, N] using hNE.mem (by simp)
    simpa only [D, omega', closed, N,
      fkIsingSquareBoundaryRestrictedDobrushinDomain,
      fkIsingSquareClosePerimeter_setClosed] using horder
  have hclusterFull :=
    fkIsingSquareWiredExhaustive_double_visit_clusterCount_eq
      n hn omega' e hwest heast
  have hcluster :
      numClustersBC (fkIsingSquareBoundaryDeletedPlanar n).G D.wiring opened =
        numClustersBC (fkIsingSquareBoundaryDeletedPlanar n).G D.wiring closed := by
    rw [fkIsingSquareBoundary_numClustersBC_eq_closePerimeter,
      fkIsingSquareBoundary_numClustersBC_eq_closePerimeter,
      fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he,
      fkIsingSquareClosePerimeter_setClosed]
    exact hclusterFull
  have hmass := D.criticalMass_setOpen_eq_sqrtTwo_mul_setClosed_of_clusterCount_eq
    (by
      rw [SimpleGraph.mem_edgeFinset]
      change e.1 ∈ ((fkSquareBoxPlanar n).G.deleteEdges
        (fkIsingSquarePerimeterPrimalEdgeFinset n : Set _)).edgeSet
      rw [SimpleGraph.edgeSet_deleteEdges]
      exact ⟨e.2, by simpa using he⟩) omega hcluster
  have hmassC : (D.criticalMass opened : Complex) =
      (Real.sqrt 2 : Complex) * (D.criticalMass closed : Complex) := by
    exact_mod_cast hmass
  have hsource := fkIsingSquareWired_double_visit_source_side_phase
    n hn omega' e hwest heast
  rcases hsource with ⟨hWN, hphaseS'⟩ | ⟨hES, hphaseN'⟩
  · have hopenE :=
      fkIsingSquareBoundary_double_visit_open_east
        n hn omega' e hwest heast hWN
    obtain ⟨hOW', hON', hOE', hOS'⟩ :=
      (fkIsingSquareWired_double_visit_open_pair_exact
        n hn omega' e hwest heast).resolve_left (by
          rintro ⟨_, _, hnotE, _⟩
          exact hnotE hopenE)
    have hOW : W ∉ D.exploration opened := by
      simpa only [D, omega', opened, W,
        fkIsingSquareBoundaryRestrictedDobrushinDomain,
        fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using hOW'
    have hON : N ∉ D.exploration opened := by
      simpa only [D, omega', opened, N,
        fkIsingSquareBoundaryRestrictedDobrushinDomain,
        fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using hON'
    have hOE : E ∈ D.exploration opened := by
      simpa only [D, omega', opened, E,
        fkIsingSquareBoundaryRestrictedDobrushinDomain,
        fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using hOE'
    have hOS : S ∈ D.exploration opened := by
      simpa only [D, omega', opened, S,
        fkIsingSquareBoundaryRestrictedDobrushinDomain,
        fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using hOS'
    have hphaseS : D.windingPhase opened S = D.windingPhase closed S := by
      simpa only [D, omega', opened, closed, S,
        fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter,
        fkIsingSquareClosePerimeter_setClosed,
        fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using hphaseS'
    have hphaseE : D.windingPhase opened E = D.windingPhase closed E := by
      rcases fkIsingSquareWired_double_visit_terminal_side_phase
          n hn omega' e hwest heast with ⟨_, h⟩ | ⟨hES', _⟩
      · simpa only [D, omega', opened, closed, E,
          fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter,
          fkIsingSquareClosePerimeter_setClosed,
          fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using h
      · change p.idxOf E < p.idxOf S at hES'
        change p.idxOf W < p.idxOf N at hWN
        omega
    have hcS := fkIsingSquareWired_closed_west_south_phase
      n hn omega' e hwest
    have hcN := fkIsingSquareWired_closed_east_north_phase
      n hn omega' e heast
    have hoS := fkIsingSquareWired_open_east_south_phase
      n hn omega' e hopenE
    unfold FKIsingDobrushinDomain.fermionicSummand
    rw [if_pos hW, if_neg hOW, if_pos hE, if_pos hOE,
      if_pos hS, if_pos hOS, if_pos hN, if_neg hON, hmassC]
    simp only [add_zero]
    apply fkIsingSquare_caseThree_eastSouth_contour_algebra
    · simpa only [D, omega', closed, W, S,
        fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter,
        fkIsingSquareClosePerimeter_setClosed] using hcS
    · simpa only [D, omega', closed, E, N,
        fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter,
        fkIsingSquareClosePerimeter_setClosed] using hcN
    · simpa only [D, omega', opened, E, S,
        fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter,
        fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using hoS
    · exact hphaseS
    · exact hphaseE
  · have hopenW :=
      fkIsingSquareBoundary_double_visit_open_west
        n hn omega' e hwest heast hES
    obtain ⟨hOW', hON', hOE', hOS'⟩ :=
      (fkIsingSquareWired_double_visit_open_pair_exact
        n hn omega' e hwest heast).resolve_right (by
          rintro ⟨hnotW, _⟩
          exact hnotW hopenW)
    have hOW : W ∈ D.exploration opened := by
      simpa only [D, omega', opened, W,
        fkIsingSquareBoundaryRestrictedDobrushinDomain,
        fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using hOW'
    have hON : N ∈ D.exploration opened := by
      simpa only [D, omega', opened, N,
        fkIsingSquareBoundaryRestrictedDobrushinDomain,
        fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using hON'
    have hOE : E ∉ D.exploration opened := by
      simpa only [D, omega', opened, E,
        fkIsingSquareBoundaryRestrictedDobrushinDomain,
        fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using hOE'
    have hOS : S ∉ D.exploration opened := by
      simpa only [D, omega', opened, S,
        fkIsingSquareBoundaryRestrictedDobrushinDomain,
        fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using hOS'
    have hphaseN : D.windingPhase opened N = D.windingPhase closed N := by
      simpa only [D, omega', opened, closed, N,
        fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter,
        fkIsingSquareClosePerimeter_setClosed,
        fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using hphaseN'
    have hphaseW : D.windingPhase opened W = D.windingPhase closed W := by
      rcases fkIsingSquareWired_double_visit_terminal_side_phase
          n hn omega' e hwest heast with ⟨hWN', _⟩ | ⟨_, h⟩
      · change p.idxOf W < p.idxOf N at hWN'
        change p.idxOf E < p.idxOf S at hES
        omega
      · simpa only [D, omega', opened, closed, W,
          fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter,
          fkIsingSquareClosePerimeter_setClosed,
          fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using h
    have hcS := fkIsingSquareWired_closed_west_south_phase
      n hn omega' e hwest
    have hcN := fkIsingSquareWired_closed_east_north_phase
      n hn omega' e heast
    have hoN := fkIsingSquareWired_open_west_north_phase
      n hn omega' e hopenW
    unfold FKIsingDobrushinDomain.fermionicSummand
    rw [if_pos hW, if_pos hOW, if_pos hE, if_neg hOE,
      if_pos hS, if_neg hOS, if_pos hN, if_pos hON, hmassC]
    simp only [add_zero]
    apply fkIsingSquare_caseThree_westNorth_contour_algebra
    · simpa only [D, omega', closed, W, S,
        fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter,
        fkIsingSquareClosePerimeter_setClosed] using hcS
    · simpa only [D, omega', closed, E, N,
        fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter,
        fkIsingSquareClosePerimeter_setClosed] using hcN
    · simpa only [D, omega', opened, W, N,
        fkIsingSquareBoundary_windingPhase_eq_wired_closePerimeter,
        fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he] using hoN
    · exact hphaseN
    · exact hphaseW


def fkIsingSquareBoundary_exhaustiveSwitchingLaw
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (he : e.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).ExhaustiveExplorationSwitchingLaw := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  refine {
    crossingEdge := e.1
    edges := fkIsingSquareWiredLocalCarrierDarts n e
    caseAt := ?_ }
  intro omega
  let omega' := fkIsingSquareClosePerimeter n omega
  apply Classical.choice
  rcases fkIsingSquareWired_local_switch_component_classification
      n hn omega' e with hzero | hwest | heast | hdouble
  · rcases hzero with ⟨hWTrace, hETrace, hopenTrace⟩
    have hW : ¬fkIsingSquareWiredPathUsesLocalSide n hn
        (setClosed e.1 omega') e .west := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hWTrace
    have hE : ¬fkIsingSquareWiredPathUsesLocalSide n hn
        (setClosed e.1 omega') e .east := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hETrace
    have hS : ¬fkIsingSquareWiredPathUsesLocalSide n hn
        (setClosed e.1 omega') e .south := by
      intro hS
      apply hW
      rw [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace]
      apply (fkIsingSquareWired_closed_west_mem_iff_south n hn omega' e).2
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hS
    have hN : ¬fkIsingSquareWiredPathUsesLocalSide n hn
        (setClosed e.1 omega') e .north := by
      intro hN
      apply hE
      rw [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace]
      apply (fkIsingSquareWired_closed_east_mem_iff_north n hn omega' e).2
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hN
    have hopen (side) : ¬fkIsingSquareWiredPathUsesLocalSide n hn
        (setOpen e.1 omega') e side := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hopenTrace side
    have hclosedSide (side : FKIsingMedialSide)
        (h : ¬fkIsingSquareWiredPathUsesLocalSide n hn
          (setClosed e.1 omega') e side) :
        (.dart (e, side) : FKIsingSquareWiredCarrier n) ∉
          D.exploration (setClosed e.1 omega) := by
      change (.dart (e, side) : FKIsingSquareWiredCarrier n) ∉
        fkIsingSquareWiredExplorationOrder n hn
          (fkIsingSquareClosePerimeter n (setClosed e.1 omega))
      rw [fkIsingSquareClosePerimeter_setClosed]
      simpa only [omega', fkIsingSquareWiredPathUsesLocalSide] using h
    have hopenSide (side : FKIsingMedialSide)
        (h : ¬fkIsingSquareWiredPathUsesLocalSide n hn
          (setOpen e.1 omega') e side) :
        (.dart (e, side) : FKIsingSquareWiredCarrier n) ∉
          D.exploration (setOpen e.1 omega) := by
      change (.dart (e, side) : FKIsingSquareWiredCarrier n) ∉
        fkIsingSquareWiredExplorationOrder n hn
          (fkIsingSquareClosePerimeter n (setOpen e.1 omega))
      rw [fkIsingSquareClosePerimeter_setOpen_of_not_mem n e.1 he]
      simpa only [omega', fkIsingSquareWiredPathUsesLocalSide] using h
    refine ⟨FKIsingDobrushinDomain.PointwiseExplorationSwitchingCase.caseOne ?_ ?_⟩
    · intro k
      fin_cases k
      · exact hclosedSide .west hW
      · exact hclosedSide .east hE
      · exact hclosedSide .south hS
      · exact hclosedSide .north hN
    · intro k
      fin_cases k
      · exact hopenSide .west (hopen .west)
      · exact hopenSide .east (hopen .east)
      · exact hopenSide .south (hopen .south)
      · exact hopenSide .north (hopen .north)
  · rcases hwest with ⟨hWTrace, hETrace, hopenTrace⟩
    have hW : fkIsingSquareWiredPathUsesLocalSide n hn
        (setClosed e.1 omega') e .west := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hWTrace
    have hE : ¬fkIsingSquareWiredPathUsesLocalSide n hn
        (setClosed e.1 omega') e .east := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hETrace
    have hopen (side) : fkIsingSquareWiredPathUsesLocalSide n hn
        (setOpen e.1 omega') e side := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hopenTrace side
    exact ⟨FKIsingDobrushinDomain.PointwiseExplorationSwitchingCase.caseTwo
      (fkIsingSquareBoundary_one_visit_west_contour_balance
        n hn omega e he hW hE hopen)⟩
  · rcases heast with ⟨hWTrace, hETrace, hopenTrace⟩
    have hW : ¬fkIsingSquareWiredPathUsesLocalSide n hn
        (setClosed e.1 omega') e .west := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hWTrace
    have hE : fkIsingSquareWiredPathUsesLocalSide n hn
        (setClosed e.1 omega') e .east := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hETrace
    have hopen (side) : fkIsingSquareWiredPathUsesLocalSide n hn
        (setOpen e.1 omega') e side := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hopenTrace side
    exact ⟨FKIsingDobrushinDomain.PointwiseExplorationSwitchingCase.caseTwo
      (fkIsingSquareBoundary_one_visit_east_contour_balance
        n hn omega e he hW hE hopen)⟩
  · rcases hdouble with ⟨hWTrace, hETrace⟩
    have hW : fkIsingSquareWiredPathUsesLocalSide n hn
        (setClosed e.1 omega') e .west := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hWTrace
    have hE : fkIsingSquareWiredPathUsesLocalSide n hn
        (setClosed e.1 omega') e .east := by
      simpa only [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hETrace
    exact ⟨FKIsingDobrushinDomain.PointwiseExplorationSwitchingCase.caseThree
      (fkIsingSquareBoundary_double_visit_contour_balance
        n hn omega e he hW hE)⟩


theorem fkIsingSquareBoundary_fermionicObservable_contour_relation
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (he : e.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n) :
    let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
    let edges := fkIsingSquareWiredLocalCarrierDarts n e
    D.fermionicObservable (edges 0) - D.fermionicObservable (edges 1) =
      Complex.I *
        (D.fermionicObservable (edges 2) - D.fermionicObservable (edges 3)) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let L := fkIsingSquareBoundary_exhaustiveSwitchingLaw n hn e he
  simpa only [D, L, fkIsingSquareBoundary_exhaustiveSwitchingLaw] using
    L.fermionicObservable_contour_relation D


def fkIsingSquareBoundaryPrimitiveIncrement
    (n : Nat) (hn : 0 < n) (z : FKIsingSquareWiredCarrier n) : Real :=
  isingPrimitiveIncrement
    ((fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable z)



theorem fkIsingSquareBoundaryPrimitiveIncrement_bondDartMate
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
    fkIsingSquareBoundaryPrimitiveIncrement n hn
        (.dart (fkIsingSquareWiredBondMate n hn d)) =
      fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart d) := by
  unfold fkIsingSquareBoundaryPrimitiveIncrement isingPrimitiveIncrement
  rw [<- fkIsingSquareBoundaryLayer_fermionicObservable_incidence
      n hn (fkIsingSquareWiredBondMate n hn d),
    fkIsingSquareBoundaryLayer_fermionicObservable_bondMate
      n hn d hsource hterminal,
    Complex.normSq_mul, fkIsingSquareWiredBondPhase_normSq, mul_one,
    fkIsingSquareBoundaryLayer_fermionicObservable_incidence]

theorem fkIsingSquareBoundaryPrimitiveIncrement_inward_eq_endpoint
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    fkIsingSquareBoundaryPrimitiveIncrement n hn
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerInwardSide side)) =
      fkIsingSquareBoundaryPrimitiveIncrement n hn
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerEndpointSide side)) := by
  unfold fkIsingSquareBoundaryPrimitiveIncrement isingPrimitiveIncrement
  rw [fkIsingSquareBoundaryLayer_fermionicObservable_endpoint,
    Complex.normSq_mul]
  have hlam : Complex.normSq isingLambda⁻¹ = 1 := by
    rw [isingLambda_inv_val]
    norm_num [Complex.normSq_apply]
  rw [hlam, mul_one]

theorem fkIsingSquareBoundaryPrimitiveIncrement_complement_inward_eq_endpoint
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    fkIsingSquareBoundaryPrimitiveIncrement n hn
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerComplementInwardSide side)) =
      fkIsingSquareBoundaryPrimitiveIncrement n hn
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerComplementEndpointSide side)) := by
  unfold fkIsingSquareBoundaryPrimitiveIncrement isingPrimitiveIncrement
  rw [fkIsingSquareBoundaryLayer_fermionicObservable_complement_endpoint,
    Complex.normSq_mul]
  have hlam : Complex.normSq isingLambda⁻¹ = 1 := by
    rw [isingLambda_inv_val]
    norm_num [Complex.normSq_apply]
  rw [hlam, mul_one]

theorem fkIsingSquareBoundary_tangent_mul_observable_sq_eq_increment
    (n : Nat) (hn : 0 < n) (z : FKIsingSquareWiredCarrier n) :
    fkIsingSquareWiredDirectedTangent n hn z *
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          z ^ 2 =
      (fkIsingSquareBoundaryPrimitiveIncrement n hn z : Complex) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let phase := fkIsingSquareWiredDirectedPhase n hn z
  have hphase : forall omega, z ∈ D.exploration omega ->
      D.windingPhase omega z ^ 2 = phase ^ 2 := by
    intro omega hz
    exact fkIsingSquareBoundaryLayer_windingPhase_sq n hn omega z hz
  have hobs := D.fermionicObservable_eq_signedExplorationMass_mul_phase
    z phase hphase
  have hnorm : Complex.normSq phase = 1 := by
    simpa only [phase] using fkIsingSquareWiredDirectedPhase_normSq n hn z
  unfold fkIsingSquareBoundaryPrimitiveIncrement isingPrimitiveIncrement
  rw [hobs]
  let mass := D.signedExplorationMass z phase
  change fkIsingSquareWiredDirectedTangent n hn z *
      ((mass : Complex) * phase) ^ 2 =
    (Complex.normSq ((mass : Complex) * phase) : Complex)
  calc
    fkIsingSquareWiredDirectedTangent n hn z *
        ((mass : Complex) * phase) ^ 2 =
      (mass : Complex) ^ 2 *
        (fkIsingSquareWiredDirectedTangent n hn z * phase ^ 2) := by ring
    _ = (mass : Complex) ^ 2 := by
      rw [fkIsingSquareWiredDirectedTangent_mul_phase_sq]
      ring
    _ = (Complex.normSq ((mass : Complex) * phase) : Complex) := by
      rw [Complex.normSq_mul, hnorm, mul_one]
      simp [Complex.normSq_apply]
      ring



theorem fkIsingSquareBoundaryPrimitiveIncrement_local_closed
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (he : e.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n) :
    fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .west)) +
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .east)) =
      fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .south)) +
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .north)) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let W := D.fermionicObservable (.dart (e, .west))
  let E := D.fermionicObservable (.dart (e, .east))
  let S := D.fermionicObservable (.dart (e, .south))
  let N := D.fermionicObservable (.dart (e, .north))
  have hcontour : W - E = Complex.I * (S - N) := by
    simpa only [W, E, S, N, D] using
      fkIsingSquareBoundary_fermionicObservable_contour_relation n hn e he
  have hline (z : FKIsingSquareWiredCarrier n) :
      (starRingEnd Complex) (D.fermionicObservable z) =
        fkIsingSquareWiredDirectedTangent n hn z * D.fermionicObservable z := by
    apply conj_eq_tangent_mul_of_tangent_mul_sq_eq_normSq
    simpa only [D, fkIsingSquareBoundaryPrimitiveIncrement,
      isingPrimitiveIncrement] using
        fkIsingSquareBoundary_tangent_mul_observable_sq_eq_increment n hn z
  unfold fkIsingSquareBoundaryPrimitiveIncrement isingPrimitiveIncrement
  change Complex.normSq W + Complex.normSq E =
    Complex.normSq S + Complex.normSq N
  cases haxis : (fkIsingSquareOrientedEdge n e).axis with
  | horizontal =>
      rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn e haxis with
        ⟨hW, hE, hS, hN⟩
      apply isingFermionic_horizontal_normSq_balance W E S N
      · simpa only [W, hW, one_mul] using hline (.dart (e, .west))
      · simpa only [E, hE, neg_mul, one_mul] using hline (.dart (e, .east))
      · simpa only [S, hS] using hline (.dart (e, .south))
      · simpa only [N, hN, neg_mul] using hline (.dart (e, .north))
      · exact hcontour
  | vertical =>
      rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn e haxis with
        ⟨hW, hE, hS, hN⟩
      apply isingFermionic_vertical_normSq_balance W E S N
      · simpa only [W, hW, neg_mul] using hline (.dart (e, .west))
      · simpa only [E, hE] using hline (.dart (e, .east))
      · simpa only [S, hS, one_mul] using hline (.dart (e, .south))
      · simpa only [N, hN, neg_mul, one_mul] using hline (.dart (e, .north))
      · exact hcontour



theorem fkIsingSquareInteriorRadialCell_not_mem_perimeter
    (n : Nat) (e : FKIsingSquareInteriorRadialCell n) :
    e.1.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
  intro he
  simp only [fkIsingSquarePerimeterPrimalEdgeFinset, Finset.mem_biUnion,
    Finset.mem_univ, true_and, Finset.mem_image] at he
  obtain ⟨side, k, hk⟩ := he
  have hval : e.1.1 = (fkIsingSquarePerimeterEdge n side k).1 := hk.symm
  cases side with
  | bottom =>
      have h := e.2 .east
      have heq : e.1 = fkIsingSquarePerimeterEdge n .bottom k :=
        Subtype.ext hval
      rw [heq] at h
      simp [fkIsingSquareInteriorFaceKey, fkIsingSquareWedgeFaceKey,
        fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
        fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
        fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] at h

  | right =>
      have h := e.2 .east
      have heq : e.1 = fkIsingSquarePerimeterEdge n .right k :=
        Subtype.ext hval
      rw [heq] at h
      simp [fkIsingSquareInteriorFaceKey, fkIsingSquareWedgeFaceKey,
        fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
        fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
        fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] at h

  | top =>
      have h := e.2 .west
      have heq : e.1 = fkIsingSquarePerimeterEdge n .top k :=
        Subtype.ext hval
      rw [heq] at h
      simp [fkIsingSquareInteriorFaceKey, fkIsingSquareWedgeFaceKey,
        fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
        fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
        fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] at h
  | left =>
      have h := e.2 .west
      have heq : e.1 = fkIsingSquarePerimeterEdge n .left k :=
        Subtype.ext hval
      rw [heq] at h
      simp [fkIsingSquareInteriorFaceKey, fkIsingSquareWedgeFaceKey,
        fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
        fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
        fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] at h

theorem fkIsingSquareDirectionEdge_not_mem_perimeter_of_interior
    (n : Nat) (x : (fkSquareBoxPlanar n).V)
    (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n x d)
    (heast : fkIsingSquareDirectionAvailable n x .east)
    (hnorth : fkIsingSquareDirectionAvailable n x .north)
    (hwest : fkIsingSquareDirectionAvailable n x .west)
    (hsouth : fkIsingSquareDirectionAvailable n x .south) :
    (fkIsingSquareDirectionEdge n x d hd).1 ∉
      fkIsingSquarePerimeterPrimalEdgeFinset n := by
  intro hper
  simp only [fkIsingSquarePerimeterPrimalEdgeFinset, Finset.mem_biUnion,
    Finset.mem_univ, true_and, Finset.mem_image] at hper
  obtain ⟨side, k, hk⟩ := hper
  have hx0 := fkIsingSquareVertex_coordinate_bounds n x 0
  have hx1 := fkIsingSquareVertex_coordinate_bounds n x 1
  simp [fkIsingSquareDirectionAvailable] at heast hnorth hwest hsouth
  simp only [fkIsingSquarePerimeterEdge, fkIsingSquareDirectionEdge] at hk
  rw [Sym2.eq_iff] at hk
  rcases hk with ⟨hbx, _⟩ | ⟨_, hnbx⟩
  · cases side <;>
      simp [fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite] at hbx <;>
      have h0 := congrArg (fun z : (fkSquareBoxPlanar n).V => z.1 0) hbx <;>
      have h1 := congrArg (fun z : (fkSquareBoxPlanar n).V => z.1 1) hbx <;>
      simp at h0 h1 <;> omega
  · cases side <;>
      simp [fkIsingSquarePerimeterDirection, fkIsingSquareBoundaryVertex,
        fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] at hnbx <;>
      have h0 := congrArg (fun z : (fkSquareBoxPlanar n).V => z.1 0) hnbx <;>
      have h1 := congrArg (fun z : (fkSquareBoxPlanar n).V => z.1 1) hnbx <;>
      simp at h0 h1 <;> omega



theorem fkIsingSquareBoundaryLayerRadialCell_increment_closed
    (n : Nat) (hn : 0 < n)
    (e : FKIsingSquareInteriorRadialCell n) :
    fkIsingSquareBoundaryLayerRadialIncrement n hn
          (fkIsingSquareInteriorRadialCellIncidence n hn e .west) +
        fkIsingSquareBoundaryLayerRadialIncrement n hn
          (fkIsingSquareInteriorRadialCellIncidence n hn e .east) =
      fkIsingSquareBoundaryLayerRadialIncrement n hn
          (fkIsingSquareInteriorRadialCellIncidence n hn e .south) +
        fkIsingSquareBoundaryLayerRadialIncrement n hn
          (fkIsingSquareInteriorRadialCellIncidence n hn e .north) := by
  change fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e.1, .west)) +
      fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e.1, .east)) =
    fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e.1, .south)) +
      fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e.1, .north))
  exact fkIsingSquareBoundaryPrimitiveIncrement_local_closed n hn e.1
    (fkIsingSquareInteriorRadialCell_not_mem_perimeter n e)

theorem fkIsingSquareBoundary_fermionicObservable_opposite_sum
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (he : e.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (e, .west)) +
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (e, .east)) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (e, .south)) +
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (e, .north)) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let W := D.fermionicObservable (.dart (e, .west))
  let E := D.fermionicObservable (.dart (e, .east))
  let S := D.fermionicObservable (.dart (e, .south))
  let N := D.fermionicObservable (.dart (e, .north))
  have hcontour : W - E = Complex.I * (S - N) := by
    simpa only [W, E, S, N, D] using
      fkIsingSquareBoundary_fermionicObservable_contour_relation n hn e he
  have hline (z : FKIsingSquareWiredCarrier n) :
      (starRingEnd Complex) (D.fermionicObservable z) =
        fkIsingSquareWiredDirectedTangent n hn z * D.fermionicObservable z := by
    apply conj_eq_tangent_mul_of_tangent_mul_sq_eq_normSq
    simpa only [D, fkIsingSquareBoundaryPrimitiveIncrement,
      isingPrimitiveIncrement] using
        fkIsingSquareBoundary_tangent_mul_observable_sq_eq_increment n hn z
  change W + E = S + N
  cases haxis : (fkIsingSquareOrientedEdge n e).axis with
  | horizontal =>
      rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn e haxis with
        ⟨hW, hE, hS, hN⟩
      apply isingFermionic_horizontal_sum_balance W E S N
      · simpa only [W, hW, one_mul] using hline (.dart (e, .west))
      · simpa only [E, hE, neg_mul, one_mul] using hline (.dart (e, .east))
      · simpa only [S, hS] using hline (.dart (e, .south))
      · simpa only [N, hN, neg_mul] using hline (.dart (e, .north))
      · exact hcontour
  | vertical =>
      rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn e haxis with
        ⟨hW, hE, hS, hN⟩
      apply isingFermionic_vertical_sum_balance W E S N
      · simpa only [W, hW, neg_mul] using hline (.dart (e, .west))
      · simpa only [E, hE] using hline (.dart (e, .east))
      · simpa only [S, hS, one_mul] using hline (.dart (e, .south))
      · simpa only [N, hN, neg_mul, one_mul] using hline (.dart (e, .north))
      · exact hcontour

noncomputable def fkIsingSquareBoundaryFullMedialObservable
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) : Complex :=
  (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
      (.dart (e, .west)) +
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
      (.dart (e, .east))

theorem fkIsingSquareBoundaryFullMedialObservable_eq_south_add_north
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (he : e.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n) :
    fkIsingSquareBoundaryFullMedialObservable n hn e =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (e, .south)) +
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (e, .north)) :=
  fkIsingSquareBoundary_fermionicObservable_opposite_sum n hn e he

theorem fkIsingSquareBoundaryFullMedialObservable_projection
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (he : e.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n)
    (s : FKIsingMedialSide) :
    isingProj (fkIsingSquareWiredDirectedTangent n hn (.dart (e, s)))
        (fkIsingSquareBoundaryFullMedialObservable n hn e) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (e, s)) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let W := D.fermionicObservable (.dart (e, .west))
  let E := D.fermionicObservable (.dart (e, .east))
  let S := D.fermionicObservable (.dart (e, .south))
  let N := D.fermionicObservable (.dart (e, .north))
  have hline (z : FKIsingSquareWiredCarrier n) :
      (starRingEnd Complex) (D.fermionicObservable z) =
        fkIsingSquareWiredDirectedTangent n hn z * D.fermionicObservable z := by
    apply conj_eq_tangent_mul_of_tangent_mul_sq_eq_normSq
    simpa only [D, fkIsingSquareBoundaryPrimitiveIncrement,
      isingPrimitiveIncrement] using
        fkIsingSquareBoundary_tangent_mul_observable_sq_eq_increment n hn z
  have hsum : W + E = S + N := by
    simpa only [W, E, S, N, D] using
      fkIsingSquareBoundary_fermionicObservable_opposite_sum n hn e he
  change isingProj _ (W + E) = _
  cases haxis : (fkIsingSquareOrientedEdge n e).axis with
  | horizontal =>
      rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn e haxis with
        ⟨htW, htE, htS, htN⟩
      cases s
      · rw [htW]
        apply isingProj_add_of_complementary_arg
        · norm_num
        · simpa only [W, htW, one_mul] using hline (.dart (e, .west))
        · simpa only [E, htE, neg_mul, one_mul] using hline (.dart (e, .east))
      · rw [htE, add_comm]
        apply isingProj_add_of_complementary_arg
        · norm_num
        · simpa only [E, htE] using hline (.dart (e, .east))
        · simpa only [W, htW, one_mul, neg_neg, neg_one_mul] using
            hline (.dart (e, .west))
      · rw [htS, hsum]
        apply isingProj_add_of_complementary_arg
        · norm_num
        · simpa only [S, htS] using hline (.dart (e, .south))
        · simpa only [N, htN, neg_mul, neg_neg] using hline (.dart (e, .north))
      · rw [htN, hsum, add_comm]
        apply isingProj_add_of_complementary_arg
        · norm_num
        · simpa only [N, htN, neg_mul] using hline (.dart (e, .north))
        · simpa only [S, htS, neg_neg] using hline (.dart (e, .south))
  | vertical =>
      rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn e haxis with
        ⟨htW, htE, htS, htN⟩
      cases s
      · rw [htW]
        apply isingProj_add_of_complementary_arg
        · norm_num
        · simpa only [W, htW, neg_mul] using hline (.dart (e, .west))
        · simpa only [E, htE, neg_neg] using hline (.dart (e, .east))
      · rw [htE, add_comm]
        apply isingProj_add_of_complementary_arg
        · norm_num
        · simpa only [E, htE] using hline (.dart (e, .east))
        · simpa only [W, htW, neg_mul, neg_neg] using hline (.dart (e, .west))
      · rw [htS, hsum]
        apply isingProj_add_of_complementary_arg
        · norm_num
        · simpa only [S, htS, one_mul] using hline (.dart (e, .south))
        · simpa only [N, htN, neg_mul, one_mul] using hline (.dart (e, .north))
      · rw [htN, hsum, add_comm]
        apply isingProj_add_of_complementary_arg
        · norm_num
        · simpa only [N, htN, neg_mul, one_mul] using hline (.dart (e, .north))
        · simpa only [S, htS, one_mul, neg_neg, neg_one_mul] using
            hline (.dart (e, .south))

theorem fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (he : e.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n)
    (s : FKIsingMedialSide) :
    fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, s)) =
      Complex.normSq
        (isingProj (fkIsingSquareWiredDirectedTangent n hn (.dart (e, s)))
          (fkIsingSquareBoundaryFullMedialObservable n hn e)) := by
  unfold fkIsingSquareBoundaryPrimitiveIncrement isingPrimitiveIncrement
  rw [fkIsingSquareBoundaryFullMedialObservable_projection n hn e he s]



theorem fkIsingSquareBoundary_fermionicObservable_bondMate_eq_of_code_modEq
    (n : Nat) (hn : 0 < n) (d : FKIsingSquareInteriorRadialDart n)
    (hcode : fkIsingSquareWiredDirectedTangentCode n hn
        (.bond (fkIsingSquareInteriorRadialBondMate n hn d)) ≡
      fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8]) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareInteriorRadialBondMate n hn d).1) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart d.1) := by
  have hturn :=
    fkIsingSquareInteriorRadial_bondTurn_eq_zero_of_directedTangentCode_eq
      n hn d hcode
  have hphase : fkIsingSquareWiredBondPhase n hn d.1 = 1 := by
    unfold fkIsingSquareWiredBondPhase
    rw [show fkIsingSquareWiredBondTurn n hn d.1
        (fkIsingSquareWiredBondMate n hn d.1) = 0 by exact hturn]
    norm_num
  calc
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareInteriorRadialBondMate n hn d).1) =
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.bond (fkIsingSquareInteriorRadialBondMate n hn d).1) := by
      rw [fkIsingSquareBoundaryLayer_fermionicObservable_incidence]
    _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.bond d.1) *
        fkIsingSquareWiredBondPhase n hn d.1 := by
      change (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
            (.bond (fkIsingSquareWiredBondMate n hn d.1)) = _
      exact fkIsingSquareBoundaryLayer_fermionicObservable_bondMate
        n hn d.1
          (fkIsingSquareInteriorRadialDart_ne_source n hn d)
          (fkIsingSquareInteriorRadialDart_ne_terminal n hn d)
    _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart d.1) := by
      rw [hphase, mul_one,
        fkIsingSquareBoundaryLayer_fermionicObservable_incidence]

end

end StatMech.Universality
