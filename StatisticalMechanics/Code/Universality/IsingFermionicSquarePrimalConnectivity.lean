/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicSquareSourcePhase











open SimpleGraph

namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC
  StatMech.FrontierD

noncomputable section



theorem fkIsingSquare_openWiredExteriorGadget_reachable_iff
    (n : Nat)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x y : (fkSquareBoxPlanar n).V) :
    (fkIsingSquareLiftPhysicalGraph n
          (openSub (fkSquareBoxPlanar n).G omega) ⊔
        fkIsingSquareWiredExteriorGadget n).Reachable
        (.physical x) (.physical y) ↔
      (openSub (fkSquareBoxPlanar n).G omega ⊔
        boundaryCliqueGraph (fkIsingSquareWiredArc n)).Reachable x y :=
  fkIsingSquare_wiredExteriorGadget_reachable_iff_clique n
    (openSub (fkSquareBoxPlanar n).G omega) x y


theorem fkIsingSquare_caseThree_westNorth_contour_algebra
    (m cW cE cS cN oW oN : Complex)
    (hcS : cS = isingLambda⁻¹ * cW)
    (hcN : cN = isingLambda⁻¹ * cE)
    (hoN : oN = isingLambda * oW)
    (hterminal : oN = cN) (hsource : oW = cW) :
    (m * cW + (Real.sqrt 2 : Complex) * m * oW) - m * cE =
      Complex.I *
        (m * cS - (m * cN + (Real.sqrt 2 : Complex) * m * oN)) := by
  have hcE : cE = isingLambda ^ 2 * cW := by
    calc
      cE = isingLambda * (isingLambda⁻¹ * cE) := by
        field_simp [isingLambda_ne]
      _ = isingLambda * cN := by rw [← hcN]
      _ = isingLambda * oN := by rw [hterminal]
      _ = isingLambda * (isingLambda * oW) := by rw [hoN]
      _ = isingLambda ^ 2 * cW := by rw [hsource]; ring
  rw [hterminal, hcS, hcN, hsource, hcE,
    isingLambda_inv, isingLambda_sq, isingLambda_val]
  field_simp [isingSqrt2_ne]
  ring_nf
  rw [isingSqrt2_sq, Complex.I_sq]
  have hs3 : (Real.sqrt 2 : Complex) ^ 3 =
      2 * (Real.sqrt 2 : Complex) := by
    rw [show (3 : Nat) = 2 + 1 by omega, pow_succ, isingSqrt2_sq]
  rw [hs3, show Complex.I ^ 3 = -Complex.I by
    rw [pow_succ, Complex.I_sq]; ring]
  ring


theorem fkIsingSquare_caseThree_eastSouth_contour_algebra
    (m cW cE cS cN oE oS : Complex)
    (hcS : cS = isingLambda⁻¹ * cW)
    (hcN : cN = isingLambda⁻¹ * cE)
    (hoS : oS = isingLambda * oE)
    (hterminal : oS = cS) (hsource : oE = cE) :
    m * cW - (m * cE + (Real.sqrt 2 : Complex) * m * oE) =
      Complex.I *
        ((m * cS + (Real.sqrt 2 : Complex) * m * oS) - m * cN) := by
  have hcW : cW = isingLambda ^ 2 * cE := by
    calc
      cW = isingLambda * (isingLambda⁻¹ * cW) := by
        field_simp [isingLambda_ne]
      _ = isingLambda * cS := by rw [← hcS]
      _ = isingLambda * oS := by rw [hterminal]
      _ = isingLambda * (isingLambda * oE) := by rw [hoS]
      _ = isingLambda ^ 2 * cE := by rw [hsource]; ring
  rw [hterminal, hcS, hcN, hsource, hcW,
    isingLambda_inv, isingLambda_sq, isingLambda_val]
  field_simp [isingSqrt2_ne]
  ring_nf
  rw [isingSqrt2_sq, Complex.I_sq]
  have hs3 : (Real.sqrt 2 : Complex) ^ 3 =
      2 * (Real.sqrt 2 : Complex) := by
    rw [show (3 : Nat) = 2 + 1 by omega, pow_succ, isingSqrt2_sq]
  rw [hs3, show Complex.I ^ 3 = -Complex.I by
    rw [pow_succ, Complex.I_sq]; ring]
  ring


def fkIsingSquareCarrierPrimalLabel (n : Nat) (hn : 0 < n) :
    FKIsingSquareMedialCarrier n -> (fkSquareBoxPlanar n).V
  | .dart d => fkIsingSquareDartEndpoint n d
  | .source => fkIsingSquareMarkedA n
  | .terminal => fkIsingSquareMarkedB n

@[simp] theorem fkIsingSquareCarrierPrimalLabel_source
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareCarrierPrimalLabel n hn .source =
      fkIsingSquareMarkedA n := rfl

@[simp] theorem fkIsingSquareCarrierPrimalLabel_terminal
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareCarrierPrimalLabel n hn .terminal =
      fkIsingSquareMarkedB n := rfl

@[simp] theorem fkIsingSquareCarrierPrimalLabel_sourceAttachment
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareCarrierPrimalLabel n hn
        (fkIsingSquareSourceAttachment n hn) =
      fkIsingSquareMarkedA n := by
  exact fkIsingSquareDartEndpoint_sourceAttachment n hn

@[simp] theorem fkIsingSquareCarrierPrimalLabel_terminalAttachment
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareCarrierPrimalLabel n hn
        (fkIsingSquareTerminalAttachment n hn) =
      fkIsingSquareMarkedB n := by
  exact fkIsingSquareDartEndpoint_terminalAttachment n hn



theorem fkIsingSquare_localMate_primalLabel_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (openSub (fkSquareBoxPlanar n).G omega ⊔
        (fkIsingSquareDobrushinDomain n hn).wiring).Reachable
      (fkIsingSquareCarrierPrimalLabel n hn (.dart d))
      (fkIsingSquareCarrierPrimalLabel n hn
        (.dart (FKIsingMedialDart.localMate omega d))) := by
  rcases d with ⟨e, side⟩
  let o := fkIsingSquareOrientedEdge n e
  have hadj : (fkSquareBoxPlanar n).G.Adj o.tail o.head := by
    rw [← SimpleGraph.mem_edgeSet]
    rw [fkIsingSquareOrientedEdge_eq n e]
    exact e.2
  have hcross (hopen : omega e.1 = true) :
      (openSub (fkSquareBoxPlanar n).G omega ⊔
          (fkIsingSquareDobrushinDomain n hn).wiring).Reachable
        o.tail o.head := by
    apply Adj.reachable
    left
    refine ⟨hadj, ?_⟩
    rwa [fkIsingSquareOrientedEdge_eq n e]
  cases hopen : omega e.1
  · cases side
    · rw [show FKIsingMedialDart.localMate omega (e, .west) =
          (e, .south) by simp [FKIsingMedialDart.localMate, hopen]]
      exact Reachable.refl _
    · rw [show FKIsingMedialDart.localMate omega (e, .east) =
          (e, .north) by simp [FKIsingMedialDart.localMate, hopen]]
      exact Reachable.refl _
    · rw [show FKIsingMedialDart.localMate omega (e, .south) =
          (e, .west) by simp [FKIsingMedialDart.localMate, hopen]]
      exact Reachable.refl _
    · rw [show FKIsingMedialDart.localMate omega (e, .north) =
          (e, .east) by simp [FKIsingMedialDart.localMate, hopen]]
      exact Reachable.refl _
  · cases side
    · rw [show FKIsingMedialDart.localMate omega (e, .west) =
          (e, .north) by simp [FKIsingMedialDart.localMate, hopen]]
      exact hcross hopen
    · rw [show FKIsingMedialDart.localMate omega (e, .east) =
          (e, .south) by simp [FKIsingMedialDart.localMate, hopen]]
      exact (hcross hopen).symm
    · rw [show FKIsingMedialDart.localMate omega (e, .south) =
          (e, .east) by simp [FKIsingMedialDart.localMate, hopen]]
      exact hcross hopen
    · rw [show FKIsingMedialDart.localMate omega (e, .north) =
          (e, .west) by simp [FKIsingMedialDart.localMate, hopen]]
      exact (hcross hopen).symm




theorem fkIsingSquare_cutBondMate_primalLabel_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x : FKIsingSquareMedialCarrier n) :
    (openSub (fkSquareBoxPlanar n).G omega ⊔
        (fkIsingSquareDobrushinDomain n hn).wiring).Reachable
      (fkIsingSquareCarrierPrimalLabel n hn x)
      (fkIsingSquareCarrierPrimalLabel n hn
        (fkIsingSquareCutBondMate n hn x)) := by
  classical
  let a := fkIsingSquareSourceInteriorDart n hn
  let b := fkIsingSquareTerminalInteriorDart n hn
  let B := fkIsingSquareBondMate n hn
  let H := openSub (fkSquareBoxPlanar n).G omega ⊔
    (fkIsingSquareDobrushinDomain n hn).wiring
  have hAB : H.Reachable
      (fkIsingSquareMarkedA n) (fkIsingSquareMarkedB n) := by
    apply Adj.reachable
    right
    rw [FKIsingDobrushinDomain.wiring, boundaryCliqueGraph_adj]
    exact ⟨fkIsingSquareMarkedA_ne_markedB n hn,
      fkIsingSquareMarkedA_mem_wiredArc n,
      fkIsingSquareMarkedB_mem_wiredArc n⟩
  have hab : a ≠ b :=
    fkIsingSquareSourceAttachment_ne_terminalAttachment n hn
  have hBaA : B a ≠ a := fkIsingSquareBondMate_ne n hn a
  have hBbB : B b ≠ b := fkIsingSquareBondMate_ne n hn b
  have hBaB : B a ≠ b :=
    fkIsingSquareBondMate_sourceAttachment_ne_terminalAttachment n hn
  have haBb : a ≠ B b := by
    intro h
    have hh := congrArg B h
    dsimp only [B] at hh
    rw [fkIsingSquareBondMate_involutive n hn b] at hh
    exact hBaB hh
  have hBaBb : B a ≠ B b := by
    intro h
    exact hab ((fkIsingSquareBondMate_involutive n hn).injective h)
  have hBaLabel : fkIsingSquareDartEndpoint n (B a) =
      fkIsingSquareMarkedA n := by
    rw [fkIsingSquareDartEndpoint_bondMate]
    exact fkIsingSquareDartEndpoint_sourceAttachment n hn
  have hBbLabel : fkIsingSquareDartEndpoint n (B b) =
      fkIsingSquareMarkedB n := by
    rw [fkIsingSquareDartEndpoint_bondMate]
    exact fkIsingSquareDartEndpoint_terminalAttachment n hn
  cases x with
  | source =>
      simpa [H, a, fkIsingSquareSourceInteriorDart,
        fkIsingSquareCutBondMate,
        fkIsingSquareCarrierPrimalLabel] using
          (Reachable.refl (fkIsingSquareMarkedA n) :
            H.Reachable (fkIsingSquareMarkedA n) (fkIsingSquareMarkedA n))
  | terminal =>
      simpa [H, b, fkIsingSquareTerminalInteriorDart,
        fkIsingSquareCutBondMate,
        fkIsingSquareCarrierPrimalLabel] using
          (Reachable.refl (fkIsingSquareMarkedB n) :
            H.Reachable (fkIsingSquareMarkedB n) (fkIsingSquareMarkedB n))
  | dart d =>
      by_cases ha : d = a
      · subst d
        simpa [H, a, b, B, fkIsingSquareSourceInteriorDart,
          fkIsingSquareCutBondMate,
          fkIsingSquareCarrierPrimalLabel] using
            (Reachable.refl (fkIsingSquareMarkedA n) :
              H.Reachable (fkIsingSquareMarkedA n) (fkIsingSquareMarkedA n))
      by_cases hb : d = b
      · subst d
        have hba' :
            (fkIsingSquareTerminalPrimalEdge n hn, FKIsingMedialSide.north) ≠
              fkIsingSquareSourceInteriorDart n hn := by
          simpa only [fkIsingSquareSourceInteriorDart] using
            (fkIsingSquareSourceAttachment_ne_terminalAttachment n hn).symm
        simpa [H, a, b, B, ha, hba',
          fkIsingSquareTerminalInteriorDart, fkIsingSquareCutBondMate,
          fkIsingSquareCarrierPrimalLabel] using
            (Reachable.refl (fkIsingSquareMarkedB n) :
              H.Reachable (fkIsingSquareMarkedB n) (fkIsingSquareMarkedB n))
      by_cases hba : d = B a
      · subst d
        simpa [H, a, b, B, hBaA, hBaB, hBaBb, haBb,
          hBaLabel, hBbLabel, fkIsingSquareCutBondMate,
          fkIsingSquareCarrierPrimalLabel] using hAB
      by_cases hbb : d = B b
      · subst d
        simpa [H, a, b, B, hBbB, haBb.symm, hBaBb.symm,
          hBaA, hBaB, hBaLabel, hBbLabel,
          fkIsingSquareCutBondMate, fkIsingSquareCarrierPrimalLabel] using
            hAB.symm
      · have hsame : fkIsingSquareDartEndpoint n (B d) =
            fkIsingSquareDartEndpoint n d :=
          fkIsingSquareDartEndpoint_bondMate n hn d
        simpa [H, a, b, B, ha, hb, hba, hbb, hsame,
          fkIsingSquareCutBondMate, fkIsingSquareCarrierPrimalLabel] using
            (Reachable.refl (fkIsingSquareDartEndpoint n d) :
              H.Reachable (fkIsingSquareDartEndpoint n d)
                (fkIsingSquareDartEndpoint n d))


theorem fkIsingSquareLoopGraph_adj_primalLabel_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareMedialCarrier n}
    (hxy : (fkIsingSquareLoopGraph n hn omega).Adj x y) :
    (openSub (fkSquareBoxPlanar n).G omega ⊔
        (fkIsingSquareDobrushinDomain n hn).wiring).Reachable
      (fkIsingSquareCarrierPrimalLabel n hn x)
      (fkIsingSquareCarrierPrimalLabel n hn y) := by
  cases x with
  | source =>
      rw [fkIsingSquareLoopGraph_adj_source_iff] at hxy
      subst y
      exact fkIsingSquare_cutBondMate_primalLabel_reachable
        n hn omega .source
  | terminal =>
      rw [fkIsingSquareLoopGraph_adj_terminal_iff] at hxy
      subst y
      exact fkIsingSquare_cutBondMate_primalLabel_reachable
        n hn omega .terminal
  | dart d =>
      rw [fkIsingSquareLoopGraph_adj_dart_iff] at hxy
      rcases hxy with rfl | rfl
      · exact fkIsingSquare_localMate_primalLabel_reachable n hn omega d
      · exact fkIsingSquare_cutBondMate_primalLabel_reachable
          n hn omega (.dart d)

private theorem fkIsingSquareLoopGraph_walk_primalLabel_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareMedialCarrier n}
    (p : (fkIsingSquareLoopGraph n hn omega).Walk x y) :
    (openSub (fkSquareBoxPlanar n).G omega ⊔
        (fkIsingSquareDobrushinDomain n hn).wiring).Reachable
      (fkIsingSquareCarrierPrimalLabel n hn x)
      (fkIsingSquareCarrierPrimalLabel n hn y) := by
  induction p with
  | nil => exact Reachable.refl _
  | @cons u v w huv p ih =>
      exact (fkIsingSquareLoopGraph_adj_primalLabel_reachable
        n hn omega huv).trans ih



theorem fkIsingSquareLoopGraph_reachable_primalLabel_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareMedialCarrier n}
    (hxy : (fkIsingSquareLoopGraph n hn omega).Reachable x y) :
    (openSub (fkSquareBoxPlanar n).G omega ⊔
        (fkIsingSquareDobrushinDomain n hn).wiring).Reachable
      (fkIsingSquareCarrierPrimalLabel n hn x)
      (fkIsingSquareCarrierPrimalLabel n hn y) := by
  obtain ⟨p⟩ := hxy
  exact fkIsingSquareLoopGraph_walk_primalLabel_reachable n hn omega p



theorem fkIsingSquareCompletedLoopGraph_reachable_iff
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x y : FKIsingSquareMedialCarrier n) :
    (fkIsingSquareCompletedLoopGraph n hn omega).Reachable x y ↔
      (fkIsingSquareLoopGraph n hn omega).Reachable x y := by
  rw [fkIsingSquareCompletedLoopGraph, reachable_sup_edge_iff]
  constructor
  · rintro (hxy | ⟨hxs, hty⟩ | ⟨hxt, hsy⟩)
    · exact hxy
    · exact hxs.trans
        ((fkIsingSquareLoopGraph_source_reachable_terminal n hn omega).trans hty)
    · exact hxt.trans
        ((fkIsingSquareLoopGraph_source_reachable_terminal n hn omega).symm.trans hsy)
  · exact Or.inl



theorem fkIsingSquareCompletedLoopGraph_reachable_primalLabel_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareMedialCarrier n}
    (hxy : (fkIsingSquareCompletedLoopGraph n hn omega).Reachable x y) :
    (openSub (fkSquareBoxPlanar n).G omega ⊔
        (fkIsingSquareDobrushinDomain n hn).wiring).Reachable
      (fkIsingSquareCarrierPrimalLabel n hn x)
      (fkIsingSquareCarrierPrimalLabel n hn y) := by
  apply fkIsingSquareLoopGraph_reachable_primalLabel_reachable n hn omega
  exact (fkIsingSquareCompletedLoopGraph_reachable_iff n hn omega x y).1 hxy



theorem fkIsingSquare_one_visit_completedLoop_componentCount
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hone :
      (fkIsingSquarePathUsesLocalSide n hn
          (setClosed e.1 omega) e .west ∧
        ¬ fkIsingSquarePathUsesLocalSide n hn
          (setClosed e.1 omega) e .east) ∨
      (¬ fkIsingSquarePathUsesLocalSide n hn
          (setClosed e.1 omega) e .west ∧
        fkIsingSquarePathUsesLocalSide n hn
          (setClosed e.1 omega) e .east)) :
    Nat.card (fkIsingSquareCompletedLoopGraph n hn
        (setOpen e.1 omega)).ConnectedComponent + 1 =
      Nat.card (fkIsingSquareCompletedLoopGraph n hn
        (setClosed e.1 omega)).ConnectedComponent := by
  let G := fkIsingSquareCompletedLoopGraph n hn (setClosed e.1 omega)
  let W : FKIsingSquareMedialCarrier n := .dart (e, .west)
  let E : FKIsingSquareMedialCarrier n := .dart (e, .east)
  let S : FKIsingSquareMedialCarrier n := .dart (e, .south)
  let N : FKIsingSquareMedialCarrier n := .dart (e, .north)
  have hWS : G.Adj W S := by
    change (fkIsingSquareCompletedLoopGraph n hn
      (setClosed e.1 omega)).Adj (.dart (e, .west)) (.dart (e, .south))
    apply Or.inl
    exact Or.inl ⟨(e, .west), rfl, by
      simp [FKIsingMedialDart.localMate]⟩
  have hEN : G.Adj E N := by
    change (fkIsingSquareCompletedLoopGraph n hn
      (setClosed e.1 omega)).Adj (.dart (e, .east)) (.dart (e, .north))
    apply Or.inl
    exact Or.inl ⟨(e, .east), rfl, by
      simp [FKIsingMedialDart.localMate]⟩
  have hdisc : ¬ G.Reachable W E := by
    rcases hone with ⟨hW, hE⟩ | ⟨hW, hE⟩
    · intro hWE
      apply hE
      rw [fkIsingSquarePathUsesLocalSide,
        mem_fkIsingSquareExplorationOrder_iff_reachable]
      have hsW : (fkIsingSquareLoopGraph n hn
          (setClosed e.1 omega)).Reachable .source W := by
        rw [← mem_fkIsingSquareExplorationOrder_iff_reachable]
        exact hW
      have hWE' : (fkIsingSquareLoopGraph n hn
          (setClosed e.1 omega)).Reachable W E :=
        (fkIsingSquareCompletedLoopGraph_reachable_iff
          n hn (setClosed e.1 omega) W E).1 hWE
      exact hsW.trans hWE'
    · intro hWE
      apply hW
      rw [fkIsingSquarePathUsesLocalSide,
        mem_fkIsingSquareExplorationOrder_iff_reachable]
      have hsE : (fkIsingSquareLoopGraph n hn
          (setClosed e.1 omega)).Reachable .source E := by
        rw [← mem_fkIsingSquareExplorationOrder_iff_reachable]
        exact hE
      have hWE' : (fkIsingSquareLoopGraph n hn
          (setClosed e.1 omega)).Reachable W E :=
        (fkIsingSquareCompletedLoopGraph_reachable_iff
          n hn (setClosed e.1 omega) W E).1 hWE
      exact hsE.trans hWE'.symm
  have hcount := StatMech.FrontierD.card_components_twoEdgeSwitch_of_not_reachable
    G (fkIsingSquareCompletedLoopGraph_even_degree n hn
      (setClosed e.1 omega)) hWS hEN hdisc
  rw [fkIsingSquareCompletedLoopGraph_setOpen_eq_twoEdgeSwitch n hn omega e]
  simpa only [G, W, S, E, N, medialTwoEdgeSwitch] using hcount




theorem fkIsingSquare_double_visit_closed_endpoints_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    (openSub (fkSquareBoxPlanar n).G (setClosed e.1 omega) ⊔
        (fkIsingSquareDobrushinDomain n hn).wiring).Reachable
      (fkIsingSquareOrientedEdge n e).tail
      (fkIsingSquareOrientedEdge n e).head := by
  have hW : (fkIsingSquareLoopGraph n hn (setClosed e.1 omega)).Reachable
      (.source : FKIsingSquareMedialCarrier n) (.dart (e, .west)) := by
    rw [← mem_fkIsingSquareExplorationOrder_iff_reachable]
    exact hwest
  have hE : (fkIsingSquareLoopGraph n hn (setClosed e.1 omega)).Reachable
      (.source : FKIsingSquareMedialCarrier n) (.dart (e, .east)) := by
    rw [← mem_fkIsingSquareExplorationOrder_iff_reachable]
    exact heast
  have hWE := hW.symm.trans hE
  have hproject :=
    fkIsingSquareLoopGraph_reachable_primalLabel_reachable
      n hn (setClosed e.1 omega) hWE
  simpa [fkIsingSquareCarrierPrimalLabel,
    fkIsingSquareDartEndpoint, fkIsingSquareSideCorner] using hproject



theorem fkIsingSquare_double_visit_clusterCount_eq
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    numClustersBC (fkSquareBoxPlanar n).G
        (fkIsingSquareDobrushinDomain n hn).wiring (setOpen e.1 omega) =
      numClustersBC (fkSquareBoxPlanar n).G
        (fkIsingSquareDobrushinDomain n hn).wiring
          (setClosed e.1 omega) := by
  let a := (fkIsingSquareOrientedEdge n e).tail
  let b := (fkIsingSquareOrientedEdge n e).head
  have hab : (fkSquareBoxPlanar n).G.Adj a b := by
    rw [← SimpleGraph.mem_edgeSet]
    rw [fkIsingSquareOrientedEdge_eq n e]
    exact e.2
  have hreach := fkIsingSquare_double_visit_closed_endpoints_reachable
    n hn omega e hwest heast
  have hcount :=
    FKIsingDobrushinDomain.numClustersBC_setOpen_eq_setClosed_of_reachable
      (fkIsingSquareDobrushinDomain n hn) a b hab omega (by
      simpa only [a, b, fkIsingSquareOrientedEdge_eq n e] using hreach)
  simpa only [a, b, fkIsingSquareOrientedEdge_eq n e] using hcount


theorem fkIsingSquare_double_visit_criticalMass_open_eq_sqrtTwo_mul_closed
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    (fkIsingSquareDobrushinDomain n hn).criticalMass (setOpen e.1 omega) =
      Real.sqrt 2 *
        (fkIsingSquareDobrushinDomain n hn).criticalMass
          (setClosed e.1 omega) := by
  exact FKIsingDobrushinDomain.criticalMass_setOpen_eq_sqrtTwo_mul_setClosed_of_clusterCount_eq
      (fkIsingSquareDobrushinDomain n hn)
      (by simpa only [SimpleGraph.mem_edgeFinset] using e.2) omega
      (fkIsingSquare_double_visit_clusterCount_eq
        n hn omega e hwest heast)





theorem fkIsingSquare_double_visit_pointwise_contour_balance_of_discardedLoopTurn
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .east)
    (hloop : FKIsingSquareDiscardedLoopTurn n hn omega e) :
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
  let p := fkIsingSquareExplorationOrder n hn closed
  change (D.fermionicSummand closed W + D.fermionicSummand opened W) -
      (D.fermionicSummand closed E + D.fermionicSummand opened E) =
    Complex.I *
      ((D.fermionicSummand closed S + D.fermionicSummand opened S) -
        (D.fermionicSummand closed N + D.fermionicSummand opened N))
  have hWS := fkIsingSquare_closed_west_south_oriented_infix
    n hn omega e hwest
  have hEN := fkIsingSquare_closed_east_north_oriented_infix
    n hn omega e heast
  have hW : W ∈ D.exploration closed := by
    simpa only [D, closed, W, fkIsingSquareDobrushinDomain,
      fkIsingSquarePathUsesLocalSide] using hwest
  have hE : E ∈ D.exploration closed := by
    simpa only [D, closed, E, fkIsingSquareDobrushinDomain,
      fkIsingSquarePathUsesLocalSide] using heast
  have hS : S ∈ D.exploration closed := by
    simpa only [D, closed, S, fkIsingSquareDobrushinDomain] using
      hWS.mem (by simp)
  have hN : N ∈ D.exploration closed := by
    simpa only [D, closed, N, fkIsingSquareDobrushinDomain] using
      hEN.mem (by simp)
  have hiWS := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareExplorationOrder_nodup n hn closed) hWS
  have hiEN := idxOf_succ_of_pair_infix_nodup
    (fkIsingSquareExplorationOrder_nodup n hn closed) hEN
  change p.idxOf S = p.idxOf W + 1 at hiWS
  change p.idxOf N = p.idxOf E + 1 at hiEN
  have hmass :=
    fkIsingSquare_double_visit_criticalMass_open_eq_sqrtTwo_mul_closed
      n hn omega e hwest heast
  have hmassC : (D.criticalMass opened : Complex) =
      (Real.sqrt 2 : Complex) * (D.criticalMass closed : Complex) := by
    exact_mod_cast hmass
  have hsource :=
    fkIsingSquare_double_visit_source_side_phase_of_discardedLoopTurn
      n hn omega e hwest heast hloop
  rcases hsource with ⟨hSE, hphaseW⟩ | ⟨hNW, hphaseE⟩
  · have hSEp : p.idxOf S < p.idxOf E := by
      simpa only [p, closed, S, E] using hSE
    have hnotNW : ¬p.idxOf N < p.idxOf W := by
      intro h
      omega
    have hopenSource :=
      fkIsingSquare_double_visit_open_source_side_membership
        n hn omega e hwest heast
    have hOW : W ∈ D.exploration opened := by
      rcases hopenSource with ⟨_, h⟩ | ⟨h, _⟩
      · simpa only [D, opened, W, fkIsingSquareDobrushinDomain,
          fkIsingSquarePathUsesLocalSide] using h
      · exact False.elim (hnotNW (by simpa only [p, N, W, closed] using h))
    have hopenPair := fkIsingSquare_double_visit_open_pair_exact
      n hn omega e hwest heast
    obtain ⟨hOW', hON', hOE', hOS'⟩ := hopenPair.resolve_right (by
      rintro ⟨hnotW, _⟩
      exact hnotW (by simpa only [D, opened, W,
        fkIsingSquareDobrushinDomain, fkIsingSquarePathUsesLocalSide] using hOW))
    have hON : N ∈ D.exploration opened := by
      simpa only [D, opened, N, fkIsingSquareDobrushinDomain,
        fkIsingSquarePathUsesLocalSide] using hON'
    have hOE : E ∉ D.exploration opened := by
      simpa only [D, opened, E, fkIsingSquareDobrushinDomain,
        fkIsingSquarePathUsesLocalSide] using hOE'
    have hOS : S ∉ D.exploration opened := by
      simpa only [D, opened, S, fkIsingSquareDobrushinDomain,
        fkIsingSquarePathUsesLocalSide] using hOS'
    have hterminal := fkIsingSquare_double_visit_terminal_side_phase
      n hn omega e hwest heast
    have hphaseN : D.windingPhase opened N = D.windingPhase closed N := by
      rcases hterminal with ⟨_, h⟩ | ⟨h, _⟩
      · simpa only [D, opened, closed, N, fkIsingSquareDobrushinDomain]
          using h
      · exact False.elim (hnotNW (by simpa only [p, N, W, closed] using h))
    have hcS := fkIsingSquare_closed_west_south_phase
      n hn omega e hwest
    have hcN := fkIsingSquare_closed_east_north_phase
      n hn omega e heast
    have hoN := fkIsingSquare_open_west_north_phase
      n hn omega e (by simpa only [D, opened, W,
        fkIsingSquareDobrushinDomain, fkIsingSquarePathUsesLocalSide] using hOW)
    unfold FKIsingDobrushinDomain.fermionicSummand
    rw [if_pos hW, if_pos hOW, if_pos hE, if_neg hOE,
      if_pos hS, if_neg hOS, if_pos hN, if_pos hON, hmassC]
    simp only [add_zero, zero_add]
    apply fkIsingSquare_caseThree_westNorth_contour_algebra
    · simpa only [D, closed, W, S, fkIsingSquareDobrushinDomain] using hcS
    · simpa only [D, closed, E, N, fkIsingSquareDobrushinDomain] using hcN
    · simpa only [D, opened, W, N, fkIsingSquareDobrushinDomain] using hoN
    · exact hphaseN
    · simpa only [D, opened, closed, W, fkIsingSquareDobrushinDomain]
        using hphaseW
  · have hNWp : p.idxOf N < p.idxOf W := by
      simpa only [p, closed, N, W] using hNW
    have hnotSE : ¬p.idxOf S < p.idxOf E := by
      intro h
      omega
    have hopenSource :=
      fkIsingSquare_double_visit_open_source_side_membership
        n hn omega e hwest heast
    have hOE : E ∈ D.exploration opened := by
      rcases hopenSource with ⟨h, _⟩ | ⟨_, h⟩
      · exact False.elim (hnotSE (by simpa only [p, S, E, closed] using h))
      · simpa only [D, opened, E, fkIsingSquareDobrushinDomain,
          fkIsingSquarePathUsesLocalSide] using h
    have hopenPair := fkIsingSquare_double_visit_open_pair_exact
      n hn omega e hwest heast
    obtain ⟨hOW', hON', hOE', hOS'⟩ := hopenPair.resolve_left (by
      rintro ⟨_, _, hnotE, _⟩
      exact hnotE (by simpa only [D, opened, E,
        fkIsingSquareDobrushinDomain, fkIsingSquarePathUsesLocalSide] using hOE))
    have hOW : W ∉ D.exploration opened := by
      simpa only [D, opened, W, fkIsingSquareDobrushinDomain,
        fkIsingSquarePathUsesLocalSide] using hOW'
    have hON : N ∉ D.exploration opened := by
      simpa only [D, opened, N, fkIsingSquareDobrushinDomain,
        fkIsingSquarePathUsesLocalSide] using hON'
    have hOS : S ∈ D.exploration opened := by
      simpa only [D, opened, S, fkIsingSquareDobrushinDomain,
        fkIsingSquarePathUsesLocalSide] using hOS'
    have hterminal := fkIsingSquare_double_visit_terminal_side_phase
      n hn omega e hwest heast
    have hphaseS : D.windingPhase opened S = D.windingPhase closed S := by
      rcases hterminal with ⟨h, _⟩ | ⟨_, h⟩
      · exact False.elim (hnotSE (by simpa only [p, S, E, closed] using h))
      · simpa only [D, opened, closed, S, fkIsingSquareDobrushinDomain]
          using h
    have hcS := fkIsingSquare_closed_west_south_phase
      n hn omega e hwest
    have hcN := fkIsingSquare_closed_east_north_phase
      n hn omega e heast
    have hoS := fkIsingSquare_open_east_south_phase
      n hn omega e (by simpa only [D, opened, E,
        fkIsingSquareDobrushinDomain, fkIsingSquarePathUsesLocalSide] using hOE)
    unfold FKIsingDobrushinDomain.fermionicSummand
    rw [if_pos hW, if_neg hOW, if_pos hE, if_pos hOE,
      if_pos hS, if_pos hOS, if_pos hN, if_neg hON, hmassC]
    simp only [add_zero, zero_add]
    apply fkIsingSquare_caseThree_eastSouth_contour_algebra
    · simpa only [D, closed, W, S, fkIsingSquareDobrushinDomain] using hcS
    · simpa only [D, closed, E, N, fkIsingSquareDobrushinDomain] using hcN
    · simpa only [D, opened, E, S, fkIsingSquareDobrushinDomain] using hoS
    · exact hphaseS
    · simpa only [D, opened, closed, E, fkIsingSquareDobrushinDomain]
        using hphaseE

end

end StatMech.Universality
