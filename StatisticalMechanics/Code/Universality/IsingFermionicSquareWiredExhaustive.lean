/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicSquareWiredCompletion
import Code.Universality.IsingFermionicSquareExhaustive








namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC
  StatMech.FrontierD

noncomputable section


def fkIsingSquareWiredLocalCarrierDarts (n : Nat)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    Fin 4 → FKIsingSquareWiredCarrier n
  | 0 => .dart (e, .west)
  | 1 => .dart (e, .east)
  | 2 => .dart (e, .south)
  | 3 => .dart (e, .north)

theorem fkIsingSquareWired_closed_west_south_phase
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west) :
    (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
        (setClosed e.1 omega) (.dart (e, .south)) =
      isingLambda⁻¹ *
        (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .west)) := by
  rw [FKIsingDobrushinDomain.windingPhase_eq_exp_turn_mul
    (fkIsingSquareWiredDobrushinDomain n hn)
    (setClosed e.1 omega) (setClosed e.1 omega)
    (.dart (e, .west)) (.dart (e, .south)) (-(Real.pi / 2))]
  · rw [FKIsingDobrushinDomain.exp_isHalf_turn_neg_pi_div_two_eq_isingLambda_inv]
  · simpa only [fkIsingSquareWiredDobrushinDomain] using
      fkIsingSquareWired_closed_west_south_winding n hn omega e h

theorem fkIsingSquareWired_closed_east_north_phase
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
        (setClosed e.1 omega) (.dart (e, .north)) =
      isingLambda⁻¹ *
        (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .east)) := by
  rw [FKIsingDobrushinDomain.windingPhase_eq_exp_turn_mul
    (fkIsingSquareWiredDobrushinDomain n hn)
    (setClosed e.1 omega) (setClosed e.1 omega)
    (.dart (e, .east)) (.dart (e, .north)) (-(Real.pi / 2))]
  · rw [FKIsingDobrushinDomain.exp_isHalf_turn_neg_pi_div_two_eq_isingLambda_inv]
  · simpa only [fkIsingSquareWiredDobrushinDomain] using
      fkIsingSquareWired_closed_east_north_winding n hn omega e h

theorem fkIsingSquareWired_open_west_north_phase
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquareWiredPathUsesLocalSide n hn
      (setOpen e.1 omega) e .west) :
    (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
        (setOpen e.1 omega) (.dart (e, .north)) =
      isingLambda *
        (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
          (setOpen e.1 omega) (.dart (e, .west)) := by
  rw [FKIsingDobrushinDomain.windingPhase_eq_exp_turn_mul
    (fkIsingSquareWiredDobrushinDomain n hn)
    (setOpen e.1 omega) (setOpen e.1 omega)
    (.dart (e, .west)) (.dart (e, .north)) (Real.pi / 2)]
  · rw [FKIsingDobrushinDomain.exp_isHalf_turn_pi_div_two_eq_isingLambda]
  · simpa only [fkIsingSquareWiredDobrushinDomain] using
      fkIsingSquareWired_open_west_north_winding n hn omega e h

theorem fkIsingSquareWired_open_east_south_phase
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquareWiredPathUsesLocalSide n hn
      (setOpen e.1 omega) e .east) :
    (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
        (setOpen e.1 omega) (.dart (e, .south)) =
      isingLambda *
        (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
          (setOpen e.1 omega) (.dart (e, .east)) := by
  rw [FKIsingDobrushinDomain.windingPhase_eq_exp_turn_mul
    (fkIsingSquareWiredDobrushinDomain n hn)
    (setOpen e.1 omega) (setOpen e.1 omega)
    (.dart (e, .east)) (.dart (e, .south)) (Real.pi / 2)]
  · rw [FKIsingDobrushinDomain.exp_isHalf_turn_pi_div_two_eq_isingLambda]
  · simpa only [fkIsingSquareWiredDobrushinDomain] using
      fkIsingSquareWired_open_east_south_winding n hn omega e h

theorem mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareWiredCarrier n) :
    z ∈ (fkIsingSquareWiredDobrushinDomain n hn).exploration omega ↔
      z ∈ fkIsingSquareWiredExplorationOrder n hn omega := by
  change z ∈ fkIsingSquareWiredExplorationTrace n hn omega ↔ _
  exact (mem_fkIsingSquareWiredExplorationOrder_iff_trace n hn omega z).symm



theorem fkIsingSquareWired_no_visit_pointwise_contour_balance
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hclosed : ∀ side, ¬ fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e side)
    (hopen : ∀ side, ¬ fkIsingSquareWiredPathUsesLocalSide n hn
      (setOpen e.1 omega) e side) :
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
  let D := fkIsingSquareWiredDobrushinDomain n hn
  let closed := setClosed e.1 omega
  let opened := setOpen e.1 omega
  let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
  let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
  let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
  let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
  have hc (side : FKIsingMedialSide) :
      (.dart (e, side) : FKIsingSquareWiredCarrier n) ∉
        D.exploration closed := by
    rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
    exact hclosed side
  have ho (side : FKIsingMedialSide) :
      (.dart (e, side) : FKIsingSquareWiredCarrier n) ∉
        D.exploration opened := by
    rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
    exact hopen side
  change (D.fermionicSummand closed W + D.fermionicSummand opened W) -
      (D.fermionicSummand closed E + D.fermionicSummand opened E) =
    Complex.I *
      ((D.fermionicSummand closed S + D.fermionicSummand opened S) -
        (D.fermionicSummand closed N + D.fermionicSummand opened N))
  unfold FKIsingDobrushinDomain.fermionicSummand
  simp [W, E, S, N, hc, ho]



theorem fkIsingSquareWired_one_visit_west_pointwise_contour_balance
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : ¬ fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east)
    (hopen : ∀ side, fkIsingSquareWiredPathUsesLocalSide n hn
      (setOpen e.1 omega) e side)
    (hseparated : ¬
      (fkIsingSquareLiftPhysicalGraph n
          (openSub (fkSquareBoxPlanar n).G (setClosed e.1 omega)) ⊔
        fkIsingSquareWiredExteriorGadget n).Reachable
          (.physical (fkIsingSquareOrientedEdge n e).tail)
          (.physical (fkIsingSquareOrientedEdge n e).head))
    (hphaseW : (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
      (setOpen e.1 omega) (.dart (e, .west)) =
        (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .west)))
    (hphaseS : (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
      (setOpen e.1 omega) (.dart (e, .south)) =
        (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .south))) :
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
  let a := (fkIsingSquareOrientedEdge n e).tail
  let b := (fkIsingSquareOrientedEdge n e).head
  have hab : (fkSquareBoxPlanar n).G.Adj a b := by
    rw [← SimpleGraph.mem_edgeSet, fkIsingSquareOrientedEdge_eq n e]
    exact e.2
  have hsepClique : ¬
      (openSub (fkSquareBoxPlanar n).G closed ⊔ D.wiring).Reachable a b := by
    rw [FKIsingDobrushinDomain.wiring]
    exact fun h => hseparated
      ((fkIsingSquare_openWiredExteriorGadget_reachable_iff n closed a b).2 h)
  have hcluster :
      numClustersBC (fkSquareBoxPlanar n).G D.wiring closed =
        numClustersBC (fkSquareBoxPlanar n).G D.wiring opened + 1 := by
    have h := D.numClustersBC_setClosed_eq_setOpen_add_one_of_not_reachable
      a b hab omega (by
        simpa only [a, b, closed, fkIsingSquareOrientedEdge_eq n e] using
          hsepClique)
    simpa only [a, b, closed, opened,
      fkIsingSquareOrientedEdge_eq n e] using h
  have hmass := D.sqrtTwo_mul_criticalMass_setOpen_eq_setClosed_of_clusterMerge
    (by simpa only [SimpleGraph.mem_edgeFinset] using e.2) omega hcluster
  have hmassC : (D.criticalMass closed : Complex) =
      (Real.sqrt 2 : Complex) * (D.criticalMass opened : Complex) := by
    exact_mod_cast hmass.symm
  have hcW : W ∈ D.exploration closed := by
    rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
    exact hwest
  have hcS : S ∈ D.exploration closed := by
    exact (fkIsingSquareWired_closed_west_mem_iff_south
      n hn omega e).1 hcW
  have hcE : E ∉ D.exploration closed := by
    rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
    exact heast
  have hcN : N ∉ D.exploration closed := by
    intro hN
    apply hcE
    exact (fkIsingSquareWired_closed_east_mem_iff_north
      n hn omega e).2 hN
  have ho (side : FKIsingMedialSide) :
      (.dart (e, side) : FKIsingSquareWiredCarrier n) ∈
        D.exploration opened := by
    rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
    exact hopen side
  have hcSphase := fkIsingSquareWired_closed_west_south_phase
    n hn omega e hwest
  have hoNphase := fkIsingSquareWired_open_west_north_phase
    n hn omega e (hopen .west)
  have hoSphase := fkIsingSquareWired_open_east_south_phase
    n hn omega e (hopen .east)
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
  apply fkIsingSquare_caseTwo_westSouth_contour_algebra
  · simpa only [D, closed, W, S, fkIsingSquareWiredDobrushinDomain] using
      hcSphase
  · simpa only [D, opened, W, N, fkIsingSquareWiredDobrushinDomain] using
      hoNphase
  · simpa only [D, opened, E, S, fkIsingSquareWiredDobrushinDomain] using
      hoSphase
  · simpa only [D, opened, closed, W,
      fkIsingSquareWiredDobrushinDomain] using hphaseW
  · simpa only [D, opened, closed, S,
      fkIsingSquareWiredDobrushinDomain] using hphaseS


theorem fkIsingSquareWired_one_visit_east_pointwise_contour_balance
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : ¬ fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east)
    (hopen : ∀ side, fkIsingSquareWiredPathUsesLocalSide n hn
      (setOpen e.1 omega) e side)
    (hseparated : ¬
      (fkIsingSquareLiftPhysicalGraph n
          (openSub (fkSquareBoxPlanar n).G (setClosed e.1 omega)) ⊔
        fkIsingSquareWiredExteriorGadget n).Reachable
          (.physical (fkIsingSquareOrientedEdge n e).tail)
          (.physical (fkIsingSquareOrientedEdge n e).head))
    (hphaseE : (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
      (setOpen e.1 omega) (.dart (e, .east)) =
        (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .east)))
    (hphaseN : (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
      (setOpen e.1 omega) (.dart (e, .north)) =
        (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .north))) :
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
  let a := (fkIsingSquareOrientedEdge n e).tail
  let b := (fkIsingSquareOrientedEdge n e).head
  have hab : (fkSquareBoxPlanar n).G.Adj a b := by
    rw [← SimpleGraph.mem_edgeSet, fkIsingSquareOrientedEdge_eq n e]
    exact e.2
  have hsepClique : ¬
      (openSub (fkSquareBoxPlanar n).G closed ⊔ D.wiring).Reachable a b := by
    rw [FKIsingDobrushinDomain.wiring]
    exact fun h => hseparated
      ((fkIsingSquare_openWiredExteriorGadget_reachable_iff n closed a b).2 h)
  have hcluster :
      numClustersBC (fkSquareBoxPlanar n).G D.wiring closed =
        numClustersBC (fkSquareBoxPlanar n).G D.wiring opened + 1 := by
    have h := D.numClustersBC_setClosed_eq_setOpen_add_one_of_not_reachable
      a b hab omega (by
        simpa only [a, b, closed, fkIsingSquareOrientedEdge_eq n e] using
          hsepClique)
    simpa only [a, b, closed, opened,
      fkIsingSquareOrientedEdge_eq n e] using h
  have hmass := D.sqrtTwo_mul_criticalMass_setOpen_eq_setClosed_of_clusterMerge
    (by simpa only [SimpleGraph.mem_edgeFinset] using e.2) omega hcluster
  have hmassC : (D.criticalMass closed : Complex) =
      (Real.sqrt 2 : Complex) * (D.criticalMass opened : Complex) := by
    exact_mod_cast hmass.symm
  have hcE : E ∈ D.exploration closed := by
    rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
    exact heast
  have hcN : N ∈ D.exploration closed := by
    exact (fkIsingSquareWired_closed_east_mem_iff_north
      n hn omega e).1 hcE
  have hcW : W ∉ D.exploration closed := by
    rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
    exact hwest
  have hcS : S ∉ D.exploration closed := by
    intro hS
    apply hcW
    exact (fkIsingSquareWired_closed_west_mem_iff_south
      n hn omega e).2 hS
  have ho (side : FKIsingMedialSide) :
      (.dart (e, side) : FKIsingSquareWiredCarrier n) ∈
        D.exploration opened := by
    rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
    exact hopen side
  have hcNphase := fkIsingSquareWired_closed_east_north_phase
    n hn omega e heast
  have hoNphase := fkIsingSquareWired_open_west_north_phase
    n hn omega e (hopen .west)
  have hoSphase := fkIsingSquareWired_open_east_south_phase
    n hn omega e (hopen .east)
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
  apply fkIsingSquare_caseTwo_eastNorth_contour_algebra
  · simpa only [D, closed, E, N, fkIsingSquareWiredDobrushinDomain] using
      hcNphase
  · simpa only [D, opened, W, N, fkIsingSquareWiredDobrushinDomain] using
      hoNphase
  · simpa only [D, opened, E, S, fkIsingSquareWiredDobrushinDomain] using
      hoSphase
  · simpa only [D, opened, closed, E,
      fkIsingSquareWiredDobrushinDomain] using hphaseE
  · simpa only [D, opened, closed, N,
      fkIsingSquareWiredDobrushinDomain] using hphaseN


def fkIsingSquareWiredExhaustiveCarrierPrimalLabel (n : Nat) (hn : 0 < n) :
    FKIsingSquareWiredCarrier n → (fkSquareBoxPlanar n).V
  | .dart d | .bond d => fkIsingSquareDartEndpoint n d
  | .source => fkIsingSquareMarkedA n
  | .terminal => fkIsingSquareMarkedB n

theorem fkIsingSquareWiredExhaustiveBoundaryDart_endpoint_mem_wiredArc
    (n : Nat) (hn : 0 < n)
    (i : FKIsingSquareWiredBoundaryDartIndex n) :
    fkIsingSquareWiredArc n
      (fkIsingSquareDartEndpoint n
        (fkIsingSquareWiredBoundaryDart n hn i)) := by
  cases i <;>
    simp [fkIsingSquareWiredBoundaryDart, fkIsingSquareWiredArc,
      fkIsingSquareMarkedA, fkIsingSquareMarkedB,
      fkIsingSquareLeftVerticalLower, fkIsingSquareLeftVerticalUpper]



theorem fkIsingSquareWiredShiftDart_label_eq_or_wired
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareDartEndpoint n d =
        fkIsingSquareDartEndpoint n
          (fkIsingSquareWiredShiftDartEquiv n hn d) ∨
      (fkIsingSquareWiredArc n (fkIsingSquareDartEndpoint n d) ∧
        fkIsingSquareWiredArc n
          (fkIsingSquareDartEndpoint n
            (fkIsingSquareWiredShiftDartEquiv n hn d))) := by
  classical
  let f := fkIsingSquareWiredBoundaryEmbedding n hn
  by_cases hd : d ∈ Set.range f
  · obtain ⟨i, rfl⟩ := hd
    right
    have hs := fkIsingSquareWiredShiftDartEquiv_apply_boundary n hn i
    constructor
    · simpa only [f, fkIsingSquareWiredBoundaryEmbedding] using
        fkIsingSquareWiredExhaustiveBoundaryDart_endpoint_mem_wiredArc n hn i
    · change fkIsingSquareWiredArc n
        (fkIsingSquareDartEndpoint n
          (fkIsingSquareWiredShiftDartEquiv n hn
            (fkIsingSquareWiredBoundaryDart n hn i)))
      rw [hs]
      exact fkIsingSquareWiredExhaustiveBoundaryDart_endpoint_mem_wiredArc n hn
        (fkIsingSquareWiredShift n hn i)
  · left
    exact (congrArg (fkIsingSquareDartEndpoint n)
      (Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
        (fkIsingSquareWiredShiftEquiv n hn) f hd)).symm

theorem fkIsingSquareWiredShiftDart_symm_label_eq_or_wired
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareDartEndpoint n d =
        fkIsingSquareDartEndpoint n
          ((fkIsingSquareWiredShiftDartEquiv n hn).symm d) ∨
      (fkIsingSquareWiredArc n (fkIsingSquareDartEndpoint n d) ∧
        fkIsingSquareWiredArc n
          (fkIsingSquareDartEndpoint n
            ((fkIsingSquareWiredShiftDartEquiv n hn).symm d))) := by
  have h := fkIsingSquareWiredShiftDart_label_eq_or_wired n hn
    ((fkIsingSquareWiredShiftDartEquiv n hn).symm d)
  rw [(fkIsingSquareWiredShiftDartEquiv n hn).apply_symm_apply] at h
  rcases h with h | ⟨hleft, hright⟩
  · exact Or.inl h.symm
  · exact Or.inr ⟨hright, hleft⟩

private theorem fkIsingSquare_reachable_of_label_eq_or_wired
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : (fkSquareBoxPlanar n).V}
    (h : x = y ∨ (fkIsingSquareWiredArc n x ∧
      fkIsingSquareWiredArc n y)) :
    (openSub (fkSquareBoxPlanar n).G omega ⊔
      (fkIsingSquareWiredDobrushinDomain n hn).wiring).Reachable x y := by
  classical
  rcases h with rfl | ⟨hx, hy⟩
  · exact SimpleGraph.Reachable.refl _
  · by_cases hxy : x = y
    · subst y
      exact SimpleGraph.Reachable.refl _
    · apply SimpleGraph.Adj.reachable
      right
      rw [FKIsingDobrushinDomain.wiring, boundaryCliqueGraph_adj]
      exact ⟨hxy, hx, hy⟩



theorem fkIsingSquareWiredExhaustiveBondMate_primalLabel_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (openSub (fkSquareBoxPlanar n).G omega ⊔
        (fkIsingSquareWiredDobrushinDomain n hn).wiring).Reachable
      (fkIsingSquareDartEndpoint n d)
      (fkIsingSquareDartEndpoint n
        (fkIsingSquareWiredBondMate n hn d)) := by
  let sigma := fkIsingSquareWiredShiftDartEquiv n hn
  let d' := sigma.symm d
  let f := fkIsingSquareBondMate n hn d'
  have h1 := fkIsingSquare_reachable_of_label_eq_or_wired n hn omega
    (fkIsingSquareWiredShiftDart_symm_label_eq_or_wired n hn d)
  have h2 : (openSub (fkSquareBoxPlanar n).G omega ⊔
        (fkIsingSquareWiredDobrushinDomain n hn).wiring).Reachable
      (fkIsingSquareDartEndpoint n d')
      (fkIsingSquareDartEndpoint n f) := by
    rw [fkIsingSquareDartEndpoint_bondMate]
  have h3 := fkIsingSquare_reachable_of_label_eq_or_wired n hn omega
    (fkIsingSquareWiredShiftDart_label_eq_or_wired n hn f)
  have hmate : fkIsingSquareWiredBondMate n hn d = sigma f := by
    dsimp only [sigma, d', f]
    rfl
  rw [hmate]
  exact h1.trans (h2.trans h3)

theorem fkIsingSquareWiredTransitionMate_primalLabel_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x : FKIsingSquareWiredCarrier n) :
    (openSub (fkSquareBoxPlanar n).G omega ⊔
        (fkIsingSquareWiredDobrushinDomain n hn).wiring).Reachable
      (fkIsingSquareWiredExhaustiveCarrierPrimalLabel n hn x)
      (fkIsingSquareWiredExhaustiveCarrierPrimalLabel n hn
        (fkIsingSquareWiredTransitionMate n hn omega x)) := by
  cases x with
  | source =>
      change (openSub (fkSquareBoxPlanar n).G omega ⊔
          (fkIsingSquareWiredDobrushinDomain n hn).wiring).Reachable
        (fkIsingSquareMarkedA n)
        (fkIsingSquareDartEndpoint n
          (fkIsingSquareWiredBoundaryDart n hn .bottom))
      rw [show fkIsingSquareDartEndpoint n
          (fkIsingSquareWiredBoundaryDart n hn .bottom) =
          fkIsingSquareMarkedA n by
        simp [fkIsingSquareWiredBoundaryDart]]
  | terminal =>
      change (openSub (fkSquareBoxPlanar n).G omega ⊔
          (fkIsingSquareWiredDobrushinDomain n hn).wiring).Reachable
        (fkIsingSquareMarkedB n)
        (fkIsingSquareDartEndpoint n
          (fkIsingSquareWiredBoundaryDart n hn .top))
      rw [show fkIsingSquareDartEndpoint n
          (fkIsingSquareWiredBoundaryDart n hn .top) =
          fkIsingSquareMarkedB n by
        simp [fkIsingSquareWiredBoundaryDart]]
  | dart d =>
      simpa only [fkIsingSquareWiredExhaustiveCarrierPrimalLabel,
        fkIsingSquareWiredTransitionMate,
        FKIsingDobrushinDomain.wiring] using
          fkIsingSquare_localMate_primalLabel_reachable n hn omega d
  | bond d =>
      by_cases ha : d = fkIsingSquareWiredSourceDart n hn
      · subst d
        simpa [fkIsingSquareWiredExhaustiveCarrierPrimalLabel,
          fkIsingSquareWiredTransitionMate, fkIsingSquareWiredSourceDart,
          fkIsingSquareWiredBoundaryDart] using
          (SimpleGraph.Reachable.refl (fkIsingSquareMarkedA n) :
            (openSub (fkSquareBoxPlanar n).G omega ⊔
              (fkIsingSquareWiredDobrushinDomain n hn).wiring).Reachable
                (fkIsingSquareMarkedA n) (fkIsingSquareMarkedA n))
      by_cases hb : d = fkIsingSquareWiredTerminalDart n hn
      · subst d
        simp only [fkIsingSquareWiredExhaustiveCarrierPrimalLabel,
          fkIsingSquareWiredTransitionMate]
        rw [if_neg (fkIsingSquareWiredSourceDart_ne_terminalDart n hn).symm]
        simp only [if_true]
        change (openSub (fkSquareBoxPlanar n).G omega ⊔
            (fkIsingSquareWiredDobrushinDomain n hn).wiring).Reachable
          (fkIsingSquareDartEndpoint n
            (fkIsingSquareWiredBoundaryDart n hn .top))
          (fkIsingSquareMarkedB n)
        rw [show fkIsingSquareDartEndpoint n
            (fkIsingSquareWiredBoundaryDart n hn .top) =
            fkIsingSquareMarkedB n by
          simp [fkIsingSquareWiredBoundaryDart]]
      · simpa [fkIsingSquareWiredExhaustiveCarrierPrimalLabel,
          fkIsingSquareWiredTransitionMate, ha, hb] using
          fkIsingSquareWiredExhaustiveBondMate_primalLabel_reachable n hn omega d



theorem fkIsingSquareWiredExhaustiveLoopGraph_adj_primalLabel_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareWiredCarrier n}
    (hxy : (fkIsingSquareWiredLoopGraph n hn omega).Adj x y) :
    (openSub (fkSquareBoxPlanar n).G omega ⊔
        (fkIsingSquareWiredDobrushinDomain n hn).wiring).Reachable
      (fkIsingSquareWiredExhaustiveCarrierPrimalLabel n hn x)
      (fkIsingSquareWiredExhaustiveCarrierPrimalLabel n hn y) := by
  rcases hxy with ⟨hxs, hxt, rfl⟩ | rfl
  · cases x <;> simp_all [fkIsingSquareWiredIncidenceMate,
      fkIsingSquareWiredExhaustiveCarrierPrimalLabel]
  · exact fkIsingSquareWiredTransitionMate_primalLabel_reachable
      n hn omega x

private theorem fkIsingSquareWiredExhaustiveLoopGraph_walk_primalLabel_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareWiredCarrier n}
    (p : (fkIsingSquareWiredLoopGraph n hn omega).Walk x y) :
    (openSub (fkSquareBoxPlanar n).G omega ⊔
        (fkIsingSquareWiredDobrushinDomain n hn).wiring).Reachable
      (fkIsingSquareWiredExhaustiveCarrierPrimalLabel n hn x)
      (fkIsingSquareWiredExhaustiveCarrierPrimalLabel n hn y) := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons u v w huv p ih =>
      exact (fkIsingSquareWiredExhaustiveLoopGraph_adj_primalLabel_reachable
        n hn omega huv).trans ih

theorem fkIsingSquareWiredExhaustiveLoopGraph_reachable_primalLabel_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareWiredCarrier n}
    (hxy : (fkIsingSquareWiredLoopGraph n hn omega).Reachable x y) :
    (openSub (fkSquareBoxPlanar n).G omega ⊔
        (fkIsingSquareWiredDobrushinDomain n hn).wiring).Reachable
      (fkIsingSquareWiredExhaustiveCarrierPrimalLabel n hn x)
      (fkIsingSquareWiredExhaustiveCarrierPrimalLabel n hn y) := by
  obtain ⟨p⟩ := hxy
  exact fkIsingSquareWiredExhaustiveLoopGraph_walk_primalLabel_reachable n hn omega p



theorem fkIsingSquareWiredExhaustive_double_visit_closed_endpoints_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    (openSub (fkSquareBoxPlanar n).G (setClosed e.1 omega) ⊔
        (fkIsingSquareWiredDobrushinDomain n hn).wiring).Reachable
      (fkIsingSquareOrientedEdge n e).tail
      (fkIsingSquareOrientedEdge n e).head := by
  have hW : (fkIsingSquareWiredLoopGraph n hn
      (setClosed e.1 omega)).Reachable
        (.source : FKIsingSquareWiredCarrier n) (.dart (e, .west)) := by
    rw [← mem_fkIsingSquareWiredExplorationOrder_iff_reachable]
    exact hwest
  have hE : (fkIsingSquareWiredLoopGraph n hn
      (setClosed e.1 omega)).Reachable
        (.source : FKIsingSquareWiredCarrier n) (.dart (e, .east)) := by
    rw [← mem_fkIsingSquareWiredExplorationOrder_iff_reachable]
    exact heast
  have hproject := fkIsingSquareWiredExhaustiveLoopGraph_reachable_primalLabel_reachable
    n hn (setClosed e.1 omega) (hW.symm.trans hE)
  simpa [fkIsingSquareWiredExhaustiveCarrierPrimalLabel,
    fkIsingSquareDartEndpoint, fkIsingSquareSideCorner] using hproject

theorem fkIsingSquareWiredExhaustive_double_visit_clusterCount_eq
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    numClustersBC (fkSquareBoxPlanar n).G
        (fkIsingSquareWiredDobrushinDomain n hn).wiring
        (setOpen e.1 omega) =
      numClustersBC (fkSquareBoxPlanar n).G
        (fkIsingSquareWiredDobrushinDomain n hn).wiring
        (setClosed e.1 omega) := by
  let a := (fkIsingSquareOrientedEdge n e).tail
  let b := (fkIsingSquareOrientedEdge n e).head
  have hab : (fkSquareBoxPlanar n).G.Adj a b := by
    rw [← SimpleGraph.mem_edgeSet, fkIsingSquareOrientedEdge_eq n e]
    exact e.2
  have hreach := fkIsingSquareWiredExhaustive_double_visit_closed_endpoints_reachable
    n hn omega e hwest heast
  have hcount :=
    FKIsingDobrushinDomain.numClustersBC_setOpen_eq_setClosed_of_reachable
      (fkIsingSquareWiredDobrushinDomain n hn) a b hab omega (by
        simpa only [a, b, fkIsingSquareOrientedEdge_eq n e] using hreach)
  simpa only [a, b, fkIsingSquareOrientedEdge_eq n e] using hcount

theorem fkIsingSquareWiredExhaustive_double_visit_criticalMass_open_eq_sqrtTwo_mul_closed
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    (fkIsingSquareWiredDobrushinDomain n hn).criticalMass
        (setOpen e.1 omega) =
      Real.sqrt 2 *
        (fkIsingSquareWiredDobrushinDomain n hn).criticalMass
          (setClosed e.1 omega) := by
  exact FKIsingDobrushinDomain.criticalMass_setOpen_eq_sqrtTwo_mul_setClosed_of_clusterCount_eq
    (fkIsingSquareWiredDobrushinDomain n hn)
    (by simpa only [SimpleGraph.mem_edgeFinset] using e.2) omega
    (fkIsingSquareWiredExhaustive_double_visit_clusterCount_eq
      n hn omega e hwest heast)

end

end StatMech.Universality
