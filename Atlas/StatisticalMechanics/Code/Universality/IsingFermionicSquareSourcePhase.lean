/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicSquareSwitching










namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC
  StatMech.FrontierD

noncomputable section



theorem fkIsingSquareLiftedWinding_sub_eq_turnCount_sub
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x y : FKIsingSquareMedialCarrier n) :
    fkIsingSquareLiftedWinding n hn omega x -
        fkIsingSquareLiftedWinding n hn omega y =
      ((fkIsingSquarePhysicalTurnCount n hn omega x -
          fkIsingSquarePhysicalTurnCount n hn omega y : Int) : Real) *
        (Real.pi / 4) := by
  simp only [fkIsingSquareLiftedWinding]
  push_cast
  ring



theorem fkIsingSquare_double_visit_open_source_side_membership
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
      fkIsingSquarePathUsesLocalSide n hn
        (setOpen e.1 omega) e .west) ∨
    (((fkIsingSquareExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .north)) <
        (fkIsingSquareExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .west))) ∧
      fkIsingSquarePathUsesLocalSide n hn
        (setOpen e.1 omega) e .east) := by
  classical
  let W : FKIsingSquareMedialCarrier n := .dart (e, .west)
  let E : FKIsingSquareMedialCarrier n := .dart (e, .east)
  let pClosed := fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)
  have hW : W ∈ pClosed := by
    simpa only [W, pClosed, fkIsingSquarePathUsesLocalSide] using hwest
  have hE : E ∈ pClosed := by
    simpa only [E, pClosed, fkIsingSquarePathUsesLocalSide] using heast
  rcases fkIsingSquare_double_visit_open_splice_support
      n hn omega e hwest heast with ⟨hsplice, hSE⟩ | ⟨hsplice, hNW⟩
  · left
    refine ⟨hSE, ?_⟩
    change W ∈ fkIsingSquareExplorationOrder n hn (setOpen e.1 omega)
    rw [hsplice, List.mem_append]
    left
    have hW' : (.dart (e, .west) : FKIsingSquareMedialCarrier n) ∈
        fkIsingSquareExplorationOrder n hn (setClosed e.1 omega) := by
      simpa only [W, pClosed] using hW
    exact (List.mem_take_iff_idxOf_lt hW').2 (by omega)
  · right
    refine ⟨hNW, ?_⟩
    change E ∈ fkIsingSquareExplorationOrder n hn (setOpen e.1 omega)
    rw [hsplice, List.mem_append]
    left
    have hE' : (.dart (e, .east) : FKIsingSquareMedialCarrier n) ∈
        fkIsingSquareExplorationOrder n hn (setClosed e.1 omega) := by
      simpa only [E, pClosed] using hE
    exact (List.mem_take_iff_idxOf_lt hE').2 (by omega)




def FKIsingSquareDiscardedLoopTurn (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) : Prop :=
  let p := fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)
  let T := fkIsingSquarePhysicalTurnCount n hn (setClosed e.1 omega)
  (p.idxOf (.dart (e, .south)) < p.idxOf (.dart (e, .east)) ->
      T (.dart (e, .east)) - T (.dart (e, .south)) + 2 = 8 ∨
      T (.dart (e, .east)) - T (.dart (e, .south)) + 2 = -8) ∧
    (p.idxOf (.dart (e, .north)) < p.idxOf (.dart (e, .west)) ->
      T (.dart (e, .west)) - T (.dart (e, .north)) + 2 = 8 ∨
      T (.dart (e, .west)) - T (.dart (e, .north)) + 2 = -8)




theorem fkIsingSquare_double_visit_source_side_phase_of_discardedLoopTurn
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .east)
    (hloop : FKIsingSquareDiscardedLoopTurn n hn omega e) :
    (((fkIsingSquareExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .south)) <
        (fkIsingSquareExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .east))) ∧
      (fkIsingSquareDobrushinDomain n hn).windingPhase
          (setOpen e.1 omega) (.dart (e, .west)) =
        (fkIsingSquareDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .west))) ∨
    (((fkIsingSquareExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .north)) <
        (fkIsingSquareExplorationOrder n hn
          (setClosed e.1 omega)).idxOf (.dart (e, .west))) ∧
      (fkIsingSquareDobrushinDomain n hn).windingPhase
          (setOpen e.1 omega) (.dart (e, .east)) =
        (fkIsingSquareDobrushinDomain n hn).windingPhase
          (setClosed e.1 omega) (.dart (e, .east))) := by
  let D := fkIsingSquareDobrushinDomain n hn
  let closed := setClosed e.1 omega
  let opened := setOpen e.1 omega
  let W : FKIsingSquareMedialCarrier n := .dart (e, .west)
  let E : FKIsingSquareMedialCarrier n := .dart (e, .east)
  let S : FKIsingSquareMedialCarrier n := .dart (e, .south)
  let N : FKIsingSquareMedialCarrier n := .dart (e, .north)
  have hterminal := fkIsingSquare_double_visit_terminal_side_winding
    n hn omega e hwest heast
  have hsource := fkIsingSquare_double_visit_open_source_side_membership
    n hn omega e hwest heast
  rcases hterminal with ⟨hSE, htermN⟩ | ⟨hNW, htermS⟩
  · left
    refine ⟨hSE, ?_⟩
    have hopenW : fkIsingSquarePathUsesLocalSide n hn opened e .west := by
      rcases hsource with ⟨_, h⟩ | ⟨hNW', _⟩
      · exact h
      · have hWS := fkIsingSquare_closed_west_south_oriented_infix
          n hn omega e hwest
        have hEN := fkIsingSquare_closed_east_north_oriented_infix
          n hn omega e heast
        have hiWS := idxOf_succ_of_pair_infix_nodup
          (fkIsingSquareExplorationOrder_nodup n hn closed) hWS
        have hiEN := idxOf_succ_of_pair_infix_nodup
          (fkIsingSquareExplorationOrder_nodup n hn closed) hEN
        dsimp only [closed] at hiWS hiEN
        omega
    have hopenWN := fkIsingSquare_open_west_north_winding
      n hn omega e hopenW
    have hclosedWS := fkIsingSquare_closed_west_south_winding
      n hn omega e hwest
    have hclosedEN := fkIsingSquare_closed_east_north_winding
      n hn omega e heast
    have hturn := hloop.1 hSE
    rcases hturn with hplus | hminus
    · have hcount :
          fkIsingSquarePhysicalTurnCount n hn closed E -
              fkIsingSquarePhysicalTurnCount n hn closed W = 4 := by
        have hWS := fkIsingSquare_closed_west_south_turnCount
          n hn omega e hwest
        simp only [fkIsingSquarePhysicalTurnCount,
          fkIsingSquareObservationFrameTurn, add_zero] at hplus ⊢
        have hplus' : fkIsingSquareLiftedTurnCount n hn closed E -
            fkIsingSquareLiftedTurnCount n hn closed S + 2 = 8 := by
          simpa only [closed, E, S] using hplus
        have hWS' : fkIsingSquareLiftedTurnCount n hn closed S =
            fkIsingSquareLiftedTurnCount n hn closed W - 2 := by
          simpa only [closed, S, W] using hWS
        omega
      have hwind := fkIsingSquareLiftedWinding_sub_eq_turnCount_sub
        n hn closed E W
      rw [hcount] at hwind
      have hwind' : fkIsingSquareLiftedWinding n hn closed E -
          fkIsingSquareLiftedWinding n hn closed W = Real.pi := by
        rw [hwind]
        ring
      have hwinding :
          fkIsingSquareLiftedWinding n hn opened W =
            fkIsingSquareLiftedWinding n hn closed W := by
        have hopenWN' := hopenWN
        have hclosedEN' := hclosedEN
        have htermN' := htermN
        linarith
      change Complex.exp (Complex.I *
          (((fkIsingSquareLiftedWinding n hn opened W) / 2 : Real) : Complex)) =
        Complex.exp (Complex.I *
          (((fkIsingSquareLiftedWinding n hn closed W) / 2 : Real) : Complex))
      rw [hwinding]
    · have hcount :
          fkIsingSquarePhysicalTurnCount n hn closed E -
              fkIsingSquarePhysicalTurnCount n hn closed W = -12 := by
        have hWS := fkIsingSquare_closed_west_south_turnCount
          n hn omega e hwest
        simp only [fkIsingSquarePhysicalTurnCount,
          fkIsingSquareObservationFrameTurn, add_zero] at hminus ⊢
        have hminus' : fkIsingSquareLiftedTurnCount n hn closed E -
            fkIsingSquareLiftedTurnCount n hn closed S + 2 = -8 := by
          simpa only [closed, E, S] using hminus
        have hWS' : fkIsingSquareLiftedTurnCount n hn closed S =
            fkIsingSquareLiftedTurnCount n hn closed W - 2 := by
          simpa only [closed, S, W] using hWS
        omega
      have hwind := fkIsingSquareLiftedWinding_sub_eq_turnCount_sub
        n hn closed E W
      rw [hcount] at hwind
      have hwind' : fkIsingSquareLiftedWinding n hn closed E -
          fkIsingSquareLiftedWinding n hn closed W = -3 * Real.pi := by
        rw [hwind]
        ring
      have hwinding :
          fkIsingSquareLiftedWinding n hn closed W =
            fkIsingSquareLiftedWinding n hn opened W + 4 * Real.pi := by
        have hopenWN' := hopenWN
        have hclosedEN' := hclosedEN
        have htermN' := htermN
        linarith
      exact (FKIsingDobrushinDomain.windingPhase_eq_of_winding_eq_add_four_pi
        D opened closed W W (by
          simpa only [D, opened, closed, W, fkIsingSquareDobrushinDomain]
            using hwinding)).symm
  · right
    refine ⟨hNW, ?_⟩
    have hopenE : fkIsingSquarePathUsesLocalSide n hn opened e .east := by
      rcases hsource with ⟨hSE', _⟩ | ⟨_, h⟩
      · have hWS := fkIsingSquare_closed_west_south_oriented_infix
          n hn omega e hwest
        have hEN := fkIsingSquare_closed_east_north_oriented_infix
          n hn omega e heast
        have hiWS := idxOf_succ_of_pair_infix_nodup
          (fkIsingSquareExplorationOrder_nodup n hn closed) hWS
        have hiEN := idxOf_succ_of_pair_infix_nodup
          (fkIsingSquareExplorationOrder_nodup n hn closed) hEN
        dsimp only [closed] at hiWS hiEN
        omega
      · exact h
    have hopenES := fkIsingSquare_open_east_south_winding
      n hn omega e hopenE
    have hclosedWS := fkIsingSquare_closed_west_south_winding
      n hn omega e hwest
    have hclosedEN := fkIsingSquare_closed_east_north_winding
      n hn omega e heast
    have hturn := hloop.2 hNW
    rcases hturn with hplus | hminus
    · have hcount :
          fkIsingSquarePhysicalTurnCount n hn closed W -
              fkIsingSquarePhysicalTurnCount n hn closed E = 4 := by
        have hEN := fkIsingSquare_closed_east_north_turnCount
          n hn omega e heast
        simp only [fkIsingSquarePhysicalTurnCount,
          fkIsingSquareObservationFrameTurn, add_zero] at hplus ⊢
        have hplus' : fkIsingSquareLiftedTurnCount n hn closed W -
            fkIsingSquareLiftedTurnCount n hn closed N + 2 = 8 := by
          simpa only [closed, W, N] using hplus
        have hEN' : fkIsingSquareLiftedTurnCount n hn closed N =
            fkIsingSquareLiftedTurnCount n hn closed E - 2 := by
          simpa only [closed, N, E] using hEN
        omega
      have hwind := fkIsingSquareLiftedWinding_sub_eq_turnCount_sub
        n hn closed W E
      rw [hcount] at hwind
      have hwind' : fkIsingSquareLiftedWinding n hn closed W -
          fkIsingSquareLiftedWinding n hn closed E = Real.pi := by
        rw [hwind]
        ring
      have hwinding :
          fkIsingSquareLiftedWinding n hn opened E =
            fkIsingSquareLiftedWinding n hn closed E := by
        have hopenES' := hopenES
        have hclosedWS' := hclosedWS
        have htermS' := htermS
        linarith
      change Complex.exp (Complex.I *
          (((fkIsingSquareLiftedWinding n hn opened E) / 2 : Real) : Complex)) =
        Complex.exp (Complex.I *
          (((fkIsingSquareLiftedWinding n hn closed E) / 2 : Real) : Complex))
      rw [hwinding]
    · have hcount :
          fkIsingSquarePhysicalTurnCount n hn closed W -
              fkIsingSquarePhysicalTurnCount n hn closed E = -12 := by
        have hEN := fkIsingSquare_closed_east_north_turnCount
          n hn omega e heast
        simp only [fkIsingSquarePhysicalTurnCount,
          fkIsingSquareObservationFrameTurn, add_zero] at hminus ⊢
        have hminus' : fkIsingSquareLiftedTurnCount n hn closed W -
            fkIsingSquareLiftedTurnCount n hn closed N + 2 = -8 := by
          simpa only [closed, W, N] using hminus
        have hEN' : fkIsingSquareLiftedTurnCount n hn closed N =
            fkIsingSquareLiftedTurnCount n hn closed E - 2 := by
          simpa only [closed, N, E] using hEN
        omega
      have hwind := fkIsingSquareLiftedWinding_sub_eq_turnCount_sub
        n hn closed W E
      rw [hcount] at hwind
      have hwind' : fkIsingSquareLiftedWinding n hn closed W -
          fkIsingSquareLiftedWinding n hn closed E = -3 * Real.pi := by
        rw [hwind]
        ring
      have hwinding :
          fkIsingSquareLiftedWinding n hn closed E =
            fkIsingSquareLiftedWinding n hn opened E + 4 * Real.pi := by
        have hopenES' := hopenES
        have hclosedWS' := hclosedWS
        have htermS' := htermS
        linarith
      exact (FKIsingDobrushinDomain.windingPhase_eq_of_winding_eq_add_four_pi
        D opened closed E E (by
          simpa only [D, opened, closed, E, fkIsingSquareDobrushinDomain]
            using hwinding)).symm

end

end StatMech.Universality
