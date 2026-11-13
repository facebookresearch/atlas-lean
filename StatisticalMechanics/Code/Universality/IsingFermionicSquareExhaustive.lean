/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicSquarePrimalConnectivity










namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC
  StatMech.FrontierD

noncomputable section



theorem fkIsingSquare_caseTwo_westSouth_contour_algebra
    (m cW cS oW oE oS oN : Complex)
    (hcS : cS = isingLambda⁻¹ * cW)
    (hoN : oN = isingLambda * oW)
    (hoS : oS = isingLambda * oE)
    (hW : oW = cW) (hS : oS = cS) :
    ((Real.sqrt 2 : Complex) * m * cW + m * oW) - m * oE =
      Complex.I *
        (((Real.sqrt 2 : Complex) * m * cS + m * oS) - m * oN) := by
  have hoE : oE = isingLambda⁻¹ * cS := by
    calc
      oE = isingLambda⁻¹ * (isingLambda * oE) := by
        field_simp [isingLambda_ne]
      _ = isingLambda⁻¹ * oS := by rw [hoS]
      _ = isingLambda⁻¹ * cS := by rw [hS]
  rw [hoN, hW, hS, hoE, hcS, isingLambda_inv, isingLambda_val]
  field_simp [isingSqrt2_ne]
  ring_nf
  rw [isingSqrt2_sq, Complex.I_sq]
  have hs3 : (Real.sqrt 2 : Complex) ^ 3 =
      2 * (Real.sqrt 2 : Complex) := by
    rw [show (3 : Nat) = 2 + 1 by omega, pow_succ, isingSqrt2_sq]
  have hs4 : (Real.sqrt 2 : Complex) ^ 4 = 4 := by
    rw [show (4 : Nat) = 2 + 2 by omega, pow_add, isingSqrt2_sq]
    norm_num
  rw [hs3, hs4]
  ring



theorem fkIsingSquare_caseTwo_eastNorth_contour_algebra
    (m cE cN oW oE oS oN : Complex)
    (hcN : cN = isingLambda⁻¹ * cE)
    (hoN : oN = isingLambda * oW)
    (hoS : oS = isingLambda * oE)
    (hE : oE = cE) (hN : oN = cN) :
    (m * oW) - ((Real.sqrt 2 : Complex) * m * cE + m * oE) =
      Complex.I *
        ((m * oS) - ((Real.sqrt 2 : Complex) * m * cN + m * oN)) := by
  have hoW : oW = isingLambda⁻¹ * cN := by
    calc
      oW = isingLambda⁻¹ * (isingLambda * oW) := by
        field_simp [isingLambda_ne]
      _ = isingLambda⁻¹ * oN := by rw [hoN]
      _ = isingLambda⁻¹ * cN := by rw [hN]
  rw [hoS, hE, hN, hoW, hcN, isingLambda_inv, isingLambda_val]
  field_simp [isingSqrt2_ne]
  ring_nf
  rw [isingSqrt2_sq, Complex.I_sq]
  have hs3 : (Real.sqrt 2 : Complex) ^ 3 =
      2 * (Real.sqrt 2 : Complex) := by
    rw [show (3 : Nat) = 2 + 1 by omega, pow_succ, isingSqrt2_sq]
  have hs4 : (Real.sqrt 2 : Complex) ^ 4 = 4 := by
    rw [show (4 : Nat) = 2 + 2 by omega, pow_add, isingSqrt2_sq]
    norm_num
  rw [hs3, hs4]
  ring



theorem fkIsingSquare_no_visit_pointwise_contour_balance
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hclosed : ∀ side, ¬ fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e side)
    (hopen : ∀ side, ¬ fkIsingSquarePathUsesLocalSide n hn
      (setOpen e.1 omega) e side) :
    let D := fkIsingSquareDobrushinDomain n hn
    let closed := setClosed e.1 omega
    let opened := setOpen e.1 omega
    let W : FKIsingSquareMedialCarrier n := .dart (e, .west)
    let E : FKIsingSquareMedialCarrier n := .dart (e, .east)
    let S : FKIsingSquareMedialCarrier n := .dart (e, .south)
    let N : FKIsingSquareMedialCarrier n := .dart (e, .north)
    (D.fermionicSummand closed W + D.fermionicSummand opened W) -
        (D.fermionicSummand closed E + D.fermionicSummand opened E) =
      Complex.I *
        ((D.fermionicSummand closed S + D.fermionicSummand opened S) -
          (D.fermionicSummand closed N + D.fermionicSummand opened N)) := by
  let D := fkIsingSquareDobrushinDomain n hn
  let closed := setClosed e.1 omega
  let opened := setOpen e.1 omega
  let W : FKIsingSquareMedialCarrier n := .dart (e, .west)
  let E : FKIsingSquareMedialCarrier n := .dart (e, .east)
  let S : FKIsingSquareMedialCarrier n := .dart (e, .south)
  let N : FKIsingSquareMedialCarrier n := .dart (e, .north)
  have hc (side : FKIsingMedialSide) :
      (.dart (e, side) : FKIsingSquareMedialCarrier n) ∉
        D.exploration closed := by
    simpa only [D, closed, fkIsingSquareDobrushinDomain,
      fkIsingSquarePathUsesLocalSide] using hclosed side
  have ho (side : FKIsingMedialSide) :
      (.dart (e, side) : FKIsingSquareMedialCarrier n) ∉
        D.exploration opened := by
    simpa only [D, opened, fkIsingSquareDobrushinDomain,
      fkIsingSquarePathUsesLocalSide] using hopen side
  change (D.fermionicSummand closed W + D.fermionicSummand opened W) -
      (D.fermionicSummand closed E + D.fermionicSummand opened E) =
    Complex.I *
      ((D.fermionicSummand closed S + D.fermionicSummand opened S) -
        (D.fermionicSummand closed N + D.fermionicSummand opened N))
  unfold FKIsingDobrushinDomain.fermionicSummand
  simp [W, E, S, N, hc, ho]





theorem fkIsingSquare_one_visit_west_pointwise_contour_balance
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : ¬ fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .east)
    (hopen : ∀ side, fkIsingSquarePathUsesLocalSide n hn
      (setOpen e.1 omega) e side)
    (hseparated : ¬
      (openSub (fkSquareBoxPlanar n).G (setClosed e.1 omega) ⊔
        (fkIsingSquareDobrushinDomain n hn).wiring).Reachable
          (fkIsingSquareOrientedEdge n e).tail
          (fkIsingSquareOrientedEdge n e).head)
    (hphaseW : (fkIsingSquareDobrushinDomain n hn).windingPhase
      (setOpen e.1 omega) (.dart (e, .west)) =
        (fkIsingSquareDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .west)))
    (hphaseS : (fkIsingSquareDobrushinDomain n hn).windingPhase
      (setOpen e.1 omega) (.dart (e, .south)) =
        (fkIsingSquareDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .south))) :
    let D := fkIsingSquareDobrushinDomain n hn
    let closed := setClosed e.1 omega
    let opened := setOpen e.1 omega
    let W : FKIsingSquareMedialCarrier n := .dart (e, .west)
    let E : FKIsingSquareMedialCarrier n := .dart (e, .east)
    let S : FKIsingSquareMedialCarrier n := .dart (e, .south)
    let N : FKIsingSquareMedialCarrier n := .dart (e, .north)
    (D.fermionicSummand closed W + D.fermionicSummand opened W) -
        (D.fermionicSummand closed E + D.fermionicSummand opened E) =
      Complex.I *
        ((D.fermionicSummand closed S + D.fermionicSummand opened S) -
          (D.fermionicSummand closed N + D.fermionicSummand opened N)) := by
  classical
  let D := fkIsingSquareDobrushinDomain n hn
  let closed := setClosed e.1 omega
  let opened := setOpen e.1 omega
  let W : FKIsingSquareMedialCarrier n := .dart (e, .west)
  let E : FKIsingSquareMedialCarrier n := .dart (e, .east)
  let S : FKIsingSquareMedialCarrier n := .dart (e, .south)
  let N : FKIsingSquareMedialCarrier n := .dart (e, .north)
  let a := (fkIsingSquareOrientedEdge n e).tail
  let b := (fkIsingSquareOrientedEdge n e).head
  have hab : (fkSquareBoxPlanar n).G.Adj a b := by
    rw [← SimpleGraph.mem_edgeSet, fkIsingSquareOrientedEdge_eq n e]
    exact e.2
  have hcluster :
      numClustersBC (fkSquareBoxPlanar n).G D.wiring closed =
        numClustersBC (fkSquareBoxPlanar n).G D.wiring opened + 1 := by
    have h := D.numClustersBC_setClosed_eq_setOpen_add_one_of_not_reachable
      a b hab omega (by
        simpa only [a, b, fkIsingSquareOrientedEdge_eq n e,
          D, closed] using hseparated)
    simpa only [a, b, fkIsingSquareOrientedEdge_eq n e,
      closed, opened] using h
  have hmass := D.sqrtTwo_mul_criticalMass_setOpen_eq_setClosed_of_clusterMerge
    (by simpa only [SimpleGraph.mem_edgeFinset] using e.2) omega hcluster
  have hmassC : (D.criticalMass closed : Complex) =
      (Real.sqrt 2 : Complex) * (D.criticalMass opened : Complex) := by
    exact_mod_cast hmass.symm
  have hcW : W ∈ D.exploration closed := by
    simpa only [D, closed, W, fkIsingSquareDobrushinDomain,
      fkIsingSquarePathUsesLocalSide] using hwest
  have hcS : S ∈ D.exploration closed := by
    have h := (fkIsingSquare_closed_pathUses_west_iff_south
      n hn omega e).1 hwest
    simpa only [D, closed, S, fkIsingSquareDobrushinDomain,
      fkIsingSquarePathUsesLocalSide] using h
  have hcE : E ∉ D.exploration closed := by
    simpa only [D, closed, E, fkIsingSquareDobrushinDomain,
      fkIsingSquarePathUsesLocalSide] using heast
  have hcN : N ∉ D.exploration closed := by
    intro hN
    apply heast
    apply (fkIsingSquare_closed_pathUses_east_iff_north n hn omega e).2
    simpa only [D, closed, N, fkIsingSquareDobrushinDomain,
      fkIsingSquarePathUsesLocalSide] using hN
  have ho (side : FKIsingMedialSide) :
      (.dart (e, side) : FKIsingSquareMedialCarrier n) ∈
        D.exploration opened := by
    simpa only [D, opened, fkIsingSquareDobrushinDomain,
      fkIsingSquarePathUsesLocalSide] using hopen side
  have hcSphase := fkIsingSquare_closed_west_south_phase
    n hn omega e hwest
  have hoNphase := fkIsingSquare_open_west_north_phase
    n hn omega e (hopen .west)
  have hoSphase := fkIsingSquare_open_east_south_phase
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
  · simpa only [D, closed, W, S, fkIsingSquareDobrushinDomain] using hcSphase
  · simpa only [D, opened, W, N, fkIsingSquareDobrushinDomain] using hoNphase
  · simpa only [D, opened, E, S, fkIsingSquareDobrushinDomain] using hoSphase
  · simpa only [D, opened, closed, W, fkIsingSquareDobrushinDomain] using hphaseW
  · simpa only [D, opened, closed, S, fkIsingSquareDobrushinDomain] using hphaseS


theorem fkIsingSquare_one_visit_east_pointwise_contour_balance
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : ¬ fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .east)
    (hopen : ∀ side, fkIsingSquarePathUsesLocalSide n hn
      (setOpen e.1 omega) e side)
    (hseparated : ¬
      (openSub (fkSquareBoxPlanar n).G (setClosed e.1 omega) ⊔
        (fkIsingSquareDobrushinDomain n hn).wiring).Reachable
          (fkIsingSquareOrientedEdge n e).tail
          (fkIsingSquareOrientedEdge n e).head)
    (hphaseE : (fkIsingSquareDobrushinDomain n hn).windingPhase
      (setOpen e.1 omega) (.dart (e, .east)) =
        (fkIsingSquareDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .east)))
    (hphaseN : (fkIsingSquareDobrushinDomain n hn).windingPhase
      (setOpen e.1 omega) (.dart (e, .north)) =
        (fkIsingSquareDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .north))) :
    let D := fkIsingSquareDobrushinDomain n hn
    let closed := setClosed e.1 omega
    let opened := setOpen e.1 omega
    let W : FKIsingSquareMedialCarrier n := .dart (e, .west)
    let E : FKIsingSquareMedialCarrier n := .dart (e, .east)
    let S : FKIsingSquareMedialCarrier n := .dart (e, .south)
    let N : FKIsingSquareMedialCarrier n := .dart (e, .north)
    (D.fermionicSummand closed W + D.fermionicSummand opened W) -
        (D.fermionicSummand closed E + D.fermionicSummand opened E) =
      Complex.I *
        ((D.fermionicSummand closed S + D.fermionicSummand opened S) -
          (D.fermionicSummand closed N + D.fermionicSummand opened N)) := by
  classical
  let D := fkIsingSquareDobrushinDomain n hn
  let closed := setClosed e.1 omega
  let opened := setOpen e.1 omega
  let W : FKIsingSquareMedialCarrier n := .dart (e, .west)
  let E : FKIsingSquareMedialCarrier n := .dart (e, .east)
  let S : FKIsingSquareMedialCarrier n := .dart (e, .south)
  let N : FKIsingSquareMedialCarrier n := .dart (e, .north)
  let a := (fkIsingSquareOrientedEdge n e).tail
  let b := (fkIsingSquareOrientedEdge n e).head
  have hab : (fkSquareBoxPlanar n).G.Adj a b := by
    rw [← SimpleGraph.mem_edgeSet, fkIsingSquareOrientedEdge_eq n e]
    exact e.2
  have hcluster :
      numClustersBC (fkSquareBoxPlanar n).G D.wiring closed =
        numClustersBC (fkSquareBoxPlanar n).G D.wiring opened + 1 := by
    have h := D.numClustersBC_setClosed_eq_setOpen_add_one_of_not_reachable
      a b hab omega (by
        simpa only [a, b, fkIsingSquareOrientedEdge_eq n e,
          D, closed] using hseparated)
    simpa only [a, b, fkIsingSquareOrientedEdge_eq n e,
      closed, opened] using h
  have hmass := D.sqrtTwo_mul_criticalMass_setOpen_eq_setClosed_of_clusterMerge
    (by simpa only [SimpleGraph.mem_edgeFinset] using e.2) omega hcluster
  have hmassC : (D.criticalMass closed : Complex) =
      (Real.sqrt 2 : Complex) * (D.criticalMass opened : Complex) := by
    exact_mod_cast hmass.symm
  have hcE : E ∈ D.exploration closed := by
    simpa only [D, closed, E, fkIsingSquareDobrushinDomain,
      fkIsingSquarePathUsesLocalSide] using heast
  have hcN : N ∈ D.exploration closed := by
    have h := (fkIsingSquare_closed_pathUses_east_iff_north
      n hn omega e).1 heast
    simpa only [D, closed, N, fkIsingSquareDobrushinDomain,
      fkIsingSquarePathUsesLocalSide] using h
  have hcW : W ∉ D.exploration closed := by
    simpa only [D, closed, W, fkIsingSquareDobrushinDomain,
      fkIsingSquarePathUsesLocalSide] using hwest
  have hcS : S ∉ D.exploration closed := by
    intro hS
    apply hwest
    apply (fkIsingSquare_closed_pathUses_west_iff_south n hn omega e).2
    simpa only [D, closed, S, fkIsingSquareDobrushinDomain,
      fkIsingSquarePathUsesLocalSide] using hS
  have ho (side : FKIsingMedialSide) :
      (.dart (e, side) : FKIsingSquareMedialCarrier n) ∈
        D.exploration opened := by
    simpa only [D, opened, fkIsingSquareDobrushinDomain,
      fkIsingSquarePathUsesLocalSide] using hopen side
  have hcNphase := fkIsingSquare_closed_east_north_phase
    n hn omega e heast
  have hoNphase := fkIsingSquare_open_west_north_phase
    n hn omega e (hopen .west)
  have hoSphase := fkIsingSquare_open_east_south_phase
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
  · simpa only [D, closed, E, N, fkIsingSquareDobrushinDomain] using hcNphase
  · simpa only [D, opened, W, N, fkIsingSquareDobrushinDomain] using hoNphase
  · simpa only [D, opened, E, S, fkIsingSquareDobrushinDomain] using hoSphase
  · simpa only [D, opened, closed, E, fkIsingSquareDobrushinDomain] using hphaseE
  · simpa only [D, opened, closed, N, fkIsingSquareDobrushinDomain] using hphaseN





structure FKIsingSquareSwitchingGeometry (n : Nat) (hn : 0 < n) where
  oneVisitSeparated : ∀
      (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
      (e : FKIsingMedialVertex (fkSquareBoxPlanar n)),
    ((fkIsingSquarePathUsesLocalSide n hn
        (setClosed e.1 omega) e .west ∧
      ¬ fkIsingSquarePathUsesLocalSide n hn
        (setClosed e.1 omega) e .east) ∨
     (¬ fkIsingSquarePathUsesLocalSide n hn
        (setClosed e.1 omega) e .west ∧
      fkIsingSquarePathUsesLocalSide n hn
        (setClosed e.1 omega) e .east)) →
      ¬ (fkIsingSquareLiftPhysicalGraph n
            (openSub (fkSquareBoxPlanar n).G (setClosed e.1 omega)) ⊔
          fkIsingSquareWiredExteriorGadget n).Reachable
        (.physical (fkIsingSquareOrientedEdge n e).tail)
        (.physical (fkIsingSquareOrientedEdge n e).head)
  oneVisitWestPhase : ∀
      (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
      (e : FKIsingMedialVertex (fkSquareBoxPlanar n)),
    fkIsingSquarePathUsesLocalSide n hn
        (setClosed e.1 omega) e .west →
      ¬ fkIsingSquarePathUsesLocalSide n hn
        (setClosed e.1 omega) e .east →
      ((fkIsingSquareDobrushinDomain n hn).windingPhase
          (setOpen e.1 omega) (.dart (e, .west)) =
        (fkIsingSquareDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .west))) ∧
      ((fkIsingSquareDobrushinDomain n hn).windingPhase
          (setOpen e.1 omega) (.dart (e, .south)) =
        (fkIsingSquareDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .south)))
  oneVisitEastPhase : ∀
      (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
      (e : FKIsingMedialVertex (fkSquareBoxPlanar n)),
    ¬ fkIsingSquarePathUsesLocalSide n hn
        (setClosed e.1 omega) e .west →
      fkIsingSquarePathUsesLocalSide n hn
        (setClosed e.1 omega) e .east →
      ((fkIsingSquareDobrushinDomain n hn).windingPhase
          (setOpen e.1 omega) (.dart (e, .east)) =
        (fkIsingSquareDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .east))) ∧
      ((fkIsingSquareDobrushinDomain n hn).windingPhase
          (setOpen e.1 omega) (.dart (e, .north)) =
        (fkIsingSquareDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .north)))
  doubleVisitLoopTurn : ∀
      (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
      (e : FKIsingMedialVertex (fkSquareBoxPlanar n)),
    fkIsingSquarePathUsesLocalSide n hn
        (setClosed e.1 omega) e .west →
      fkIsingSquarePathUsesLocalSide n hn
        (setClosed e.1 omega) e .east →
      FKIsingSquareDiscardedLoopTurn n hn omega e




def fkIsingSquare_exhaustiveSwitchingLaw
    (n : Nat) (hn : 0 < n)
    (geometry : FKIsingSquareSwitchingGeometry n hn)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    (fkIsingSquareDobrushinDomain n hn).ExhaustiveExplorationSwitchingLaw := by
  let D := fkIsingSquareDobrushinDomain n hn
  refine {
    crossingEdge := e.1
    edges := fkIsingSquareLocalCarrierDarts n e
    caseAt := ?_ }
  intro omega
  apply Classical.choice
  rcases fkIsingSquare_local_switch_path_membership_classification
      n hn omega e with hzero | hwest | heast | hdouble
  · rcases hzero with ⟨hW, hE, hopen⟩
    have hS : ¬ fkIsingSquarePathUsesLocalSide n hn
        (setClosed e.1 omega) e .south := by
      intro h
      exact hW ((fkIsingSquare_closed_pathUses_west_iff_south
        n hn omega e).2 h)
    have hN : ¬ fkIsingSquarePathUsesLocalSide n hn
        (setClosed e.1 omega) e .north := by
      intro h
      exact hE ((fkIsingSquare_closed_pathUses_east_iff_north
        n hn omega e).2 h)
    refine ⟨FKIsingDobrushinDomain.PointwiseExplorationSwitchingCase.caseOne ?_ ?_⟩
    · intro k
      fin_cases k
      · simpa only [D, fkIsingSquareLocalCarrierDarts,
          fkIsingSquareDobrushinDomain, fkIsingSquarePathUsesLocalSide] using hW
      · simpa only [D, fkIsingSquareLocalCarrierDarts,
          fkIsingSquareDobrushinDomain, fkIsingSquarePathUsesLocalSide] using hE
      · simpa only [D, fkIsingSquareLocalCarrierDarts,
          fkIsingSquareDobrushinDomain, fkIsingSquarePathUsesLocalSide] using hS
      · simpa only [D, fkIsingSquareLocalCarrierDarts,
          fkIsingSquareDobrushinDomain, fkIsingSquarePathUsesLocalSide] using hN
    · intro k
      fin_cases k
      · simpa only [D, fkIsingSquareLocalCarrierDarts,
          fkIsingSquareDobrushinDomain, fkIsingSquarePathUsesLocalSide] using hopen .west
      · simpa only [D, fkIsingSquareLocalCarrierDarts,
          fkIsingSquareDobrushinDomain, fkIsingSquarePathUsesLocalSide] using hopen .east
      · simpa only [D, fkIsingSquareLocalCarrierDarts,
          fkIsingSquareDobrushinDomain, fkIsingSquarePathUsesLocalSide] using hopen .south
      · simpa only [D, fkIsingSquareLocalCarrierDarts,
          fkIsingSquareDobrushinDomain, fkIsingSquarePathUsesLocalSide] using hopen .north
  · rcases hwest with ⟨hW, hE, hopen⟩
    have hsepGadget := geometry.oneVisitSeparated omega e (Or.inl ⟨hW, hE⟩)
    have hsep : ¬
        (openSub (fkSquareBoxPlanar n).G (setClosed e.1 omega) ⊔
          (fkIsingSquareDobrushinDomain n hn).wiring).Reachable
            (fkIsingSquareOrientedEdge n e).tail
            (fkIsingSquareOrientedEdge n e).head := by
      rw [FKIsingDobrushinDomain.wiring]
      exact fun h => hsepGadget
        ((fkIsingSquare_openWiredExteriorGadget_reachable_iff n
          (setClosed e.1 omega) _ _).2 h)
    obtain ⟨hphaseW, hphaseS⟩ := geometry.oneVisitWestPhase omega e hW hE
    exact ⟨FKIsingDobrushinDomain.PointwiseExplorationSwitchingCase.caseTwo
      (fkIsingSquare_one_visit_west_pointwise_contour_balance
        n hn omega e hW hE hopen hsep hphaseW hphaseS)⟩
  · rcases heast with ⟨hW, hE, hopen⟩
    have hsepGadget := geometry.oneVisitSeparated omega e (Or.inr ⟨hW, hE⟩)
    have hsep : ¬
        (openSub (fkSquareBoxPlanar n).G (setClosed e.1 omega) ⊔
          (fkIsingSquareDobrushinDomain n hn).wiring).Reachable
            (fkIsingSquareOrientedEdge n e).tail
            (fkIsingSquareOrientedEdge n e).head := by
      rw [FKIsingDobrushinDomain.wiring]
      exact fun h => hsepGadget
        ((fkIsingSquare_openWiredExteriorGadget_reachable_iff n
          (setClosed e.1 omega) _ _).2 h)
    obtain ⟨hphaseE, hphaseN⟩ := geometry.oneVisitEastPhase omega e hW hE
    exact ⟨FKIsingDobrushinDomain.PointwiseExplorationSwitchingCase.caseTwo
      (fkIsingSquare_one_visit_east_pointwise_contour_balance
        n hn omega e hW hE hopen hsep hphaseE hphaseN)⟩
  · rcases hdouble with ⟨hW, hE⟩
    exact ⟨FKIsingDobrushinDomain.PointwiseExplorationSwitchingCase.caseThree
      (fkIsingSquare_double_visit_pointwise_contour_balance_of_discardedLoopTurn
        n hn omega e hW hE
          (geometry.doubleVisitLoopTurn omega e hW hE))⟩



theorem fkIsingSquare_fermionicObservable_contour_relation
    (n : Nat) (hn : 0 < n)
    (geometry : FKIsingSquareSwitchingGeometry n hn)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    let D := fkIsingSquareDobrushinDomain n hn
    let edges := fkIsingSquareLocalCarrierDarts n e
    D.fermionicObservable (edges 0) - D.fermionicObservable (edges 1) =
      Complex.I *
        (D.fermionicObservable (edges 2) - D.fermionicObservable (edges 3)) := by
  let D := fkIsingSquareDobrushinDomain n hn
  let L := fkIsingSquare_exhaustiveSwitchingLaw n hn geometry e
  simpa only [D, L, fkIsingSquare_exhaustiveSwitchingLaw] using
    L.fermionicObservable_contour_relation D

end

end StatMech.Universality
