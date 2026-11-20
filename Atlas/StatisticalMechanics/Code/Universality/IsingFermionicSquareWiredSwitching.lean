/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicSquareWiredCompletion
import Code.Universality.IsingFermionicSquareExhaustive








open Finset Complex

namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC
  StatMech.FrontierD

noncomputable section

def fkIsingSquareWiredSwitchingLocalCarrierDarts (n : Nat)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    Fin 4 → FKIsingSquareWiredCarrier n
  | 0 => .dart (e, .west)
  | 1 => .dart (e, .east)
  | 2 => .dart (e, .south)
  | 3 => .dart (e, .north)






def fkIsingSquareWiredCarrierPrimalLabel (n : Nat) (hn : 0 < n) :
    FKIsingSquareWiredCarrier n -> (fkSquareBoxPlanar n).V
  | .dart d | .bond d => fkIsingSquareDartEndpoint n d
  | .source => fkIsingSquareMarkedA n
  | .terminal => fkIsingSquareMarkedB n

theorem fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc
    (n : Nat) (hn : 0 < n)
    (i : FKIsingSquareWiredBoundaryDartIndex n) :
    fkIsingSquareWiredArc n
      (fkIsingSquareDartEndpoint n
        (fkIsingSquareWiredBoundaryDart n hn i)) := by
  cases i with
  | bottom =>
      simp [fkIsingSquareWiredBoundaryDart,
        fkIsingSquareMarkedA, fkIsingSquareWiredArc]
  | west k =>
      simp [fkIsingSquareWiredBoundaryDart,
        fkIsingSquareLeftVerticalLower, fkIsingSquareWiredArc]
  | north k =>
      simp [fkIsingSquareWiredBoundaryDart,
        fkIsingSquareLeftVerticalUpper, fkIsingSquareWiredArc]
  | top =>
      simp [fkIsingSquareWiredBoundaryDart,
        fkIsingSquareMarkedB, fkIsingSquareWiredArc]

private theorem fkIsingSquareWiredShiftDart_primalLabel_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (openSub (fkSquareBoxPlanar n).G omega ⊔
        boundaryCliqueGraph (fkIsingSquareWiredArc n)).Reachable
      (fkIsingSquareDartEndpoint n d)
      (fkIsingSquareDartEndpoint n
        (fkIsingSquareWiredShiftDartEquiv n hn d)) := by
  classical
  by_cases hd : d ∈ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)
  · obtain ⟨i, rfl⟩ := hd
    simp only [fkIsingSquareWiredShiftDartEquiv,
      Equiv.Perm.viaFintypeEmbedding_apply_image]
    change (openSub (fkSquareBoxPlanar n).G omega ⊔
        boundaryCliqueGraph (fkIsingSquareWiredArc n)).Reachable
      (fkIsingSquareDartEndpoint n
        (fkIsingSquareWiredBoundaryDart n hn i))
      (fkIsingSquareDartEndpoint n
        (fkIsingSquareWiredBoundaryDart n hn
          (fkIsingSquareWiredShiftEquiv n hn i)))
    by_cases hlabel : fkIsingSquareDartEndpoint n
        (fkIsingSquareWiredBoundaryDart n hn i) =
      fkIsingSquareDartEndpoint n
        (fkIsingSquareWiredBoundaryDart n hn
          (fkIsingSquareWiredShiftEquiv n hn i))
    · rw [hlabel]
    · apply SimpleGraph.Adj.reachable
      right
      rw [boundaryCliqueGraph_adj]
      exact ⟨hlabel,
        fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc n hn i,
        fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc n hn
          (fkIsingSquareWiredShiftEquiv n hn i)⟩
  · simp only [fkIsingSquareWiredShiftDartEquiv,
      Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ hd]
    exact SimpleGraph.Reachable.refl _

private theorem fkIsingSquareWiredShiftDart_symm_primalLabel_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (openSub (fkSquareBoxPlanar n).G omega ⊔
        boundaryCliqueGraph (fkIsingSquareWiredArc n)).Reachable
      (fkIsingSquareDartEndpoint n d)
      (fkIsingSquareDartEndpoint n
        ((fkIsingSquareWiredShiftDartEquiv n hn).symm d)) := by
  have h := fkIsingSquareWiredShiftDart_primalLabel_reachable n hn omega
    ((fkIsingSquareWiredShiftDartEquiv n hn).symm d)
  simpa using h.symm



theorem fkIsingSquareWiredBondMate_primalLabel_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (openSub (fkSquareBoxPlanar n).G omega ⊔
        boundaryCliqueGraph (fkIsingSquareWiredArc n)).Reachable
      (fkIsingSquareDartEndpoint n d)
      (fkIsingSquareDartEndpoint n
        (fkIsingSquareWiredBondMate n hn d)) := by
  let S := fkIsingSquareWiredShiftDartEquiv n hn
  let d' := S.symm d
  let f' := fkIsingSquareBondMate n hn d'
  have hS := fkIsingSquareWiredShiftDart_symm_primalLabel_reachable
    n hn omega d
  have hB : fkIsingSquareDartEndpoint n d' =
      fkIsingSquareDartEndpoint n f' := by
    exact (fkIsingSquareDartEndpoint_bondMate n hn d').symm
  have hS' := fkIsingSquareWiredShiftDart_primalLabel_reachable
    n hn omega f'
  have hS0 :
      (openSub (fkSquareBoxPlanar n).G omega ⊔
          boundaryCliqueGraph (fkIsingSquareWiredArc n)).Reachable
        (fkIsingSquareDartEndpoint n d)
        (fkIsingSquareDartEndpoint n d') := by
    simpa only [d', S] using hS
  have hB0 :
      (openSub (fkSquareBoxPlanar n).G omega ⊔
          boundaryCliqueGraph (fkIsingSquareWiredArc n)).Reachable
        (fkIsingSquareDartEndpoint n d')
        (fkIsingSquareDartEndpoint n f') := by
    rw [hB]
  have hout : fkIsingSquareWiredBondMate n hn d = S f' := by
    rfl
  rw [hout]
  exact hS0.trans (hB0.trans (by simpa only [S, f'] using hS'))

private theorem fkIsingSquareWiredTransitionMate_primalLabel_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x : FKIsingSquareWiredCarrier n) :
    (openSub (fkSquareBoxPlanar n).G omega ⊔
        boundaryCliqueGraph (fkIsingSquareWiredArc n)).Reachable
      (fkIsingSquareWiredCarrierPrimalLabel n hn x)
      (fkIsingSquareWiredCarrierPrimalLabel n hn
        (fkIsingSquareWiredTransitionMate n hn omega x)) := by
  cases x with
  | source =>
      simp [fkIsingSquareWiredCarrierPrimalLabel,
        fkIsingSquareWiredTransitionMate,
        fkIsingSquareWiredSourceDart,
        fkIsingSquareWiredBoundaryDart]
  | terminal =>
      have hne := (fkIsingSquareWiredSourceDart_ne_terminalDart n hn).symm
      simp only [fkIsingSquareWiredTransitionMate, hne, ↓reduceIte]
      simp [fkIsingSquareWiredCarrierPrimalLabel,
        fkIsingSquareWiredTerminalDart,
        fkIsingSquareWiredBoundaryDart]
  | dart d =>
      simpa [fkIsingSquareWiredCarrierPrimalLabel,
        FKIsingDobrushinDomain.wiring,
        fkIsingSquareWiredDobrushinDomain] using
        (fkIsingSquare_localMate_primalLabel_reachable n hn omega d)
  | bond d =>
      by_cases ha : d = fkIsingSquareWiredSourceDart n hn
      · subst d
        simp [fkIsingSquareWiredCarrierPrimalLabel,
          fkIsingSquareWiredTransitionMate,
          fkIsingSquareWiredSourceDart,
          fkIsingSquareWiredBoundaryDart]
      by_cases hb : d = fkIsingSquareWiredTerminalDart n hn
      · subst d
        have hne := (fkIsingSquareWiredSourceDart_ne_terminalDart n hn).symm
        simp only [fkIsingSquareWiredTransitionMate, hne, ↓reduceIte]
        simp [fkIsingSquareWiredCarrierPrimalLabel,
          fkIsingSquareWiredTerminalDart,
          fkIsingSquareWiredBoundaryDart]
      · simpa [fkIsingSquareWiredCarrierPrimalLabel,
          fkIsingSquareWiredTransitionMate, ha, hb] using
          (fkIsingSquareWiredBondMate_primalLabel_reachable
            n hn omega d)


theorem fkIsingSquareWiredLoopGraph_adj_primalLabel_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareWiredCarrier n}
    (hxy : (fkIsingSquareWiredLoopGraph n hn omega).Adj x y) :
    (openSub (fkSquareBoxPlanar n).G omega ⊔
        boundaryCliqueGraph (fkIsingSquareWiredArc n)).Reachable
      (fkIsingSquareWiredCarrierPrimalLabel n hn x)
      (fkIsingSquareWiredCarrierPrimalLabel n hn y) := by
  rcases hxy with ⟨hxs, hxt, rfl⟩ | rfl
  · cases x <;>
      simp_all [fkIsingSquareWiredIncidenceMate,
        fkIsingSquareWiredCarrierPrimalLabel]
  · exact fkIsingSquareWiredTransitionMate_primalLabel_reachable
      n hn omega x

private theorem fkIsingSquareWiredLoopGraph_walk_primalLabel_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareWiredCarrier n}
    (p : (fkIsingSquareWiredLoopGraph n hn omega).Walk x y) :
    (openSub (fkSquareBoxPlanar n).G omega ⊔
        boundaryCliqueGraph (fkIsingSquareWiredArc n)).Reachable
      (fkIsingSquareWiredCarrierPrimalLabel n hn x)
      (fkIsingSquareWiredCarrierPrimalLabel n hn y) := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons u v w huv p ih =>
      exact (fkIsingSquareWiredLoopGraph_adj_primalLabel_reachable
        n hn omega huv).trans ih



theorem fkIsingSquareWiredLoopGraph_reachable_primalLabel_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareWiredCarrier n}
    (hxy : (fkIsingSquareWiredLoopGraph n hn omega).Reachable x y) :
    (openSub (fkSquareBoxPlanar n).G omega ⊔
        boundaryCliqueGraph (fkIsingSquareWiredArc n)).Reachable
      (fkIsingSquareWiredCarrierPrimalLabel n hn x)
      (fkIsingSquareWiredCarrierPrimalLabel n hn y) := by
  obtain ⟨p⟩ := hxy
  exact fkIsingSquareWiredLoopGraph_walk_primalLabel_reachable
    n hn omega p



theorem fkIsingSquareWired_double_visit_closed_endpoints_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .west)
    (heast : fkIsingSquareWiredPathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    (openSub (fkSquareBoxPlanar n).G (setClosed e.1 omega) ⊔
        boundaryCliqueGraph (fkIsingSquareWiredArc n)).Reachable
      (fkIsingSquareOrientedEdge n e).tail
      (fkIsingSquareOrientedEdge n e).head := by
  have hW : (fkIsingSquareWiredLoopGraph n hn
      (setClosed e.1 omega)).Reachable
      (.source : FKIsingSquareWiredCarrier n) (.dart (e, .west)) := by
    rw [← fkIsingSquareWiredPath_mem_support_iff_reachable n hn
      (setClosed e.1 omega)
      (fkIsingSquareWiredExplorationPath n hn (setClosed e.1 omega))
      (fkIsingSquareWiredExplorationPath n hn
        (setClosed e.1 omega)).isPath]
    exact hwest
  have hE : (fkIsingSquareWiredLoopGraph n hn
      (setClosed e.1 omega)).Reachable
      (.source : FKIsingSquareWiredCarrier n) (.dart (e, .east)) := by
    rw [← fkIsingSquareWiredPath_mem_support_iff_reachable n hn
      (setClosed e.1 omega)
      (fkIsingSquareWiredExplorationPath n hn (setClosed e.1 omega))
      (fkIsingSquareWiredExplorationPath n hn
        (setClosed e.1 omega)).isPath]
    exact heast
  have hproject :=
    fkIsingSquareWiredLoopGraph_reachable_primalLabel_reachable
      n hn (setClosed e.1 omega) (hW.symm.trans hE)
  simpa [fkIsingSquareWiredCarrierPrimalLabel,
    fkIsingSquareDartEndpoint, fkIsingSquareSideCorner] using hproject



theorem fkIsingSquareWiredCompletedLoopGraph_reachable_iff
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x y : FKIsingSquareWiredCarrier n) :
    (fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable x y ↔
      (fkIsingSquareWiredLoopGraph n hn omega).Reachable x y := by
  rw [fkIsingSquareWiredCompletedLoopGraph, reachable_sup_edge_iff]
  constructor
  · rintro (hxy | ⟨hxs, hty⟩ | ⟨hxt, hsy⟩)
    · exact hxy
    · exact hxs.trans
        ((fkIsingSquareWiredLoopGraph_source_reachable_terminal
          n hn omega).trans hty)
    · exact hxt.trans
        ((fkIsingSquareWiredLoopGraph_source_reachable_terminal
          n hn omega).symm.trans hsy)
  · exact Or.inl



theorem fkIsingSquareWired_one_visit_completedLoop_componentCount
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hone :
      (fkIsingSquareWiredPathUsesLocalSide n hn
          (setClosed e.1 omega) e .west ∧
        ¬ fkIsingSquareWiredPathUsesLocalSide n hn
          (setClosed e.1 omega) e .east) ∨
      (¬ fkIsingSquareWiredPathUsesLocalSide n hn
          (setClosed e.1 omega) e .west ∧
        fkIsingSquareWiredPathUsesLocalSide n hn
          (setClosed e.1 omega) e .east)) :
    Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn
        (setOpen e.1 omega)).ConnectedComponent + 1 =
      Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn
        (setClosed e.1 omega)).ConnectedComponent := by
  let G := fkIsingSquareWiredCompletedLoopGraph n hn
    (setClosed e.1 omega)
  let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
  let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
  let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
  let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
  have hWS : G.Adj W S := by
    simpa only [G, W, S] using
      fkIsingSquareWiredCompletedLoopGraph_closed_west_south_adj
        n hn omega e
  have hEN : G.Adj E N := by
    simpa only [G, E, N] using
      fkIsingSquareWiredCompletedLoopGraph_closed_east_north_adj
        n hn omega e
  have hdisc : ¬ G.Reachable W E := by
    rcases hone with ⟨hW, hE⟩ | ⟨hW, hE⟩
    · intro hWE
      apply hE
      have hsW : (fkIsingSquareWiredLoopGraph n hn
          (setClosed e.1 omega)).Reachable .source W := by
        rw [← mem_fkIsingSquareWiredExplorationOrder_iff_reachable]
        simpa only [fkIsingSquareWiredPathUsesLocalSide, W] using hW
      have hWE' : (fkIsingSquareWiredLoopGraph n hn
          (setClosed e.1 omega)).Reachable W E :=
        (fkIsingSquareWiredCompletedLoopGraph_reachable_iff
          n hn (setClosed e.1 omega) W E).1 hWE
      rw [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_reachable]
      simpa only [E] using hsW.trans hWE'
    · intro hWE
      apply hW
      have hsE : (fkIsingSquareWiredLoopGraph n hn
          (setClosed e.1 omega)).Reachable .source E := by
        rw [← mem_fkIsingSquareWiredExplorationOrder_iff_reachable]
        simpa only [fkIsingSquareWiredPathUsesLocalSide, E] using hE
      have hWE' : (fkIsingSquareWiredLoopGraph n hn
          (setClosed e.1 omega)).Reachable W E :=
        (fkIsingSquareWiredCompletedLoopGraph_reachable_iff
          n hn (setClosed e.1 omega) W E).1 hWE
      rw [fkIsingSquareWiredPathUsesLocalSide,
        mem_fkIsingSquareWiredExplorationOrder_iff_reachable]
      simpa only [W] using hsE.trans hWE'.symm
  have hcount := StatMech.FrontierD.card_components_twoEdgeSwitch_of_not_reachable
    G (fkIsingSquareWiredCompletedLoopGraph_even_degree n hn
      (setClosed e.1 omega)) hWS hEN hdisc
  rw [fkIsingSquareWiredCompletedLoopGraph_setOpen_eq_twoEdgeSwitch
    n hn omega e]
  simpa only [G, W, S, E, N, medialTwoEdgeSwitch] using hcount



theorem fkIsingSquareWired_double_visit_clusterCount_eq
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
  have hreach := fkIsingSquareWired_double_visit_closed_endpoints_reachable
    n hn omega e hwest heast
  have hcount :=
    FKIsingDobrushinDomain.numClustersBC_setOpen_eq_setClosed_of_reachable
      (fkIsingSquareWiredDobrushinDomain n hn) a b hab omega (by
        simpa only [a, b, FKIsingDobrushinDomain.wiring,
          fkIsingSquareWiredDobrushinDomain,
          fkIsingSquareOrientedEdge_eq n e] using hreach)
  simpa only [a, b, fkIsingSquareOrientedEdge_eq n e] using hcount


theorem fkIsingSquareWired_double_visit_criticalMass_open_eq_sqrtTwo_mul_closed
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
    (fkIsingSquareWired_double_visit_clusterCount_eq
      n hn omega e hwest heast)






def fkIsingSquareWiredEulerDefect (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) : Int :=
  2 * (numClustersBC (fkSquareBoxPlanar n).G
      (fkIsingSquareWiredDobrushinDomain n hn).wiring omega : Int) +
    (StatMech.FK.openCount (fkSquareBoxPlanar n).G omega : Int) -
    (Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn omega).ConnectedComponent : Int)

private theorem fkIsingSquare_openCount_setOpen_eq_setClosed_add_one
    (n : Nat)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    StatMech.FK.openCount (fkSquareBoxPlanar n).G (setOpen e.1 omega) =
      StatMech.FK.openCount (fkSquareBoxPlanar n).G
        (setClosed e.1 omega) + 1 := by
  classical
  unfold StatMech.FK.openCount
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



theorem fkIsingSquareWired_one_visit_separated_of_eulerDefect_eq
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hone :
      (fkIsingSquareWiredPathUsesLocalSide n hn
          (setClosed e.1 omega) e .west ∧
        ¬ fkIsingSquareWiredPathUsesLocalSide n hn
          (setClosed e.1 omega) e .east) ∨
      (¬ fkIsingSquareWiredPathUsesLocalSide n hn
          (setClosed e.1 omega) e .west ∧
        fkIsingSquareWiredPathUsesLocalSide n hn
          (setClosed e.1 omega) e .east))
    (heuler : fkIsingSquareWiredEulerDefect n hn (setOpen e.1 omega) =
      fkIsingSquareWiredEulerDefect n hn (setClosed e.1 omega)) :
    ¬ (openSub (fkSquareBoxPlanar n).G (setClosed e.1 omega) ⊔
        (fkIsingSquareWiredDobrushinDomain n hn).wiring).Reachable
      (fkIsingSquareOrientedEdge n e).tail
      (fkIsingSquareOrientedEdge n e).head := by
  intro hreach
  let a := (fkIsingSquareOrientedEdge n e).tail
  let b := (fkIsingSquareOrientedEdge n e).head
  have hab : (fkSquareBoxPlanar n).G.Adj a b := by
    rw [← SimpleGraph.mem_edgeSet, fkIsingSquareOrientedEdge_eq n e]
    exact e.2
  have hk :=
    FKIsingDobrushinDomain.numClustersBC_setOpen_eq_setClosed_of_reachable
      (fkIsingSquareWiredDobrushinDomain n hn) a b hab omega (by
        simpa only [a, b, fkIsingSquareOrientedEdge_eq n e] using hreach)
  have hk' :
      numClustersBC (fkSquareBoxPlanar n).G
          (fkIsingSquareWiredDobrushinDomain n hn).wiring
          (setOpen e.1 omega) =
        numClustersBC (fkSquareBoxPlanar n).G
          (fkIsingSquareWiredDobrushinDomain n hn).wiring
          (setClosed e.1 omega) := by
    simpa only [a, b, fkIsingSquareOrientedEdge_eq n e] using hk
  have hm := fkIsingSquare_openCount_setOpen_eq_setClosed_add_one
    n omega e
  have hL := fkIsingSquareWired_one_visit_completedLoop_componentCount
    n hn omega e hone
  unfold fkIsingSquareWiredEulerDefect at heuler
  push_cast at heuler
  rw [hk'] at heuler
  omega

namespace LegacyWiredSwitching

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
      (.dart (e, side) : FKIsingSquareWiredCarrier n) ∉ D.exploration closed := by
    simpa only [D, closed, fkIsingSquareWiredDobrushinDomain,
      fkIsingSquareWiredPathUsesLocalSide,
      mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hclosed side
  have ho (side : FKIsingMedialSide) :
      (.dart (e, side) : FKIsingSquareWiredCarrier n) ∉ D.exploration opened := by
    simpa only [D, opened, fkIsingSquareWiredDobrushinDomain,
      fkIsingSquareWiredPathUsesLocalSide,
      mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hopen side
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
      (openSub (fkSquareBoxPlanar n).G (setClosed e.1 omega) ⊔
        (fkIsingSquareWiredDobrushinDomain n hn).wiring).Reachable
          (fkIsingSquareOrientedEdge n e).tail
          (fkIsingSquareOrientedEdge n e).head)
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
  have hcluster :
      numClustersBC (fkSquareBoxPlanar n).G D.wiring closed =
        numClustersBC (fkSquareBoxPlanar n).G D.wiring opened + 1 := by
    have h := D.numClustersBC_setClosed_eq_setOpen_add_one_of_not_reachable
      a b hab omega (by simpa only [a, b, fkIsingSquareOrientedEdge_eq n e,
        D, closed] using hseparated)
    simpa only [a, b, fkIsingSquareOrientedEdge_eq n e,
      closed, opened] using h
  have hmass := D.sqrtTwo_mul_criticalMass_setOpen_eq_setClosed_of_clusterMerge
    (by simpa only [SimpleGraph.mem_edgeFinset] using e.2) omega hcluster
  have hmassC : (D.criticalMass closed : Complex) =
      (Real.sqrt 2 : Complex) * (D.criticalMass opened : Complex) := by
    exact_mod_cast hmass.symm
  have hcW : W ∈ D.exploration closed := by
    simpa only [D, closed, W, fkIsingSquareWiredDobrushinDomain,
      fkIsingSquareWiredPathUsesLocalSide,
      mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hwest
  have hcS : S ∈ D.exploration closed := by
    have htrace : (.dart (e, .west) : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn closed := by
      simpa only [closed, ← mem_fkIsingSquareWiredExplorationOrder_iff_trace,
        fkIsingSquareWiredPathUsesLocalSide] using hwest
    have h := (fkIsingSquareWired_closed_west_mem_iff_south
      n hn omega e).1 htrace
    simpa only [D, closed, S, fkIsingSquareWiredDobrushinDomain] using h
  have hcE : E ∉ D.exploration closed := by
    simpa only [D, closed, E, fkIsingSquareWiredDobrushinDomain,
      fkIsingSquareWiredPathUsesLocalSide,
      mem_fkIsingSquareWiredExplorationOrder_iff_trace] using heast
  have hcN : N ∉ D.exploration closed := by
    intro hN
    apply heast
    rw [fkIsingSquareWiredPathUsesLocalSide,
      mem_fkIsingSquareWiredExplorationOrder_iff_trace]
    apply (fkIsingSquareWired_closed_east_mem_iff_north n hn omega e).2
    simpa only [D, closed, N, fkIsingSquareWiredDobrushinDomain] using hN
  have ho (side : FKIsingMedialSide) :
      (.dart (e, side) : FKIsingSquareWiredCarrier n) ∈
        D.exploration opened := by
    simpa only [D, opened, fkIsingSquareWiredDobrushinDomain,
      fkIsingSquareWiredPathUsesLocalSide,
      mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hopen side
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
  · simpa only [D, closed, W, S, fkIsingSquareWiredDobrushinDomain] using hcSphase
  · simpa only [D, opened, W, N, fkIsingSquareWiredDobrushinDomain] using hoNphase
  · simpa only [D, opened, E, S, fkIsingSquareWiredDobrushinDomain] using hoSphase
  · simpa only [D, opened, closed, W, fkIsingSquareWiredDobrushinDomain] using hphaseW
  · simpa only [D, opened, closed, S, fkIsingSquareWiredDobrushinDomain] using hphaseS

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
      (openSub (fkSquareBoxPlanar n).G (setClosed e.1 omega) ⊔
        (fkIsingSquareWiredDobrushinDomain n hn).wiring).Reachable
          (fkIsingSquareOrientedEdge n e).tail
          (fkIsingSquareOrientedEdge n e).head)
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
  have hcluster :
      numClustersBC (fkSquareBoxPlanar n).G D.wiring closed =
        numClustersBC (fkSquareBoxPlanar n).G D.wiring opened + 1 := by
    have h := D.numClustersBC_setClosed_eq_setOpen_add_one_of_not_reachable
      a b hab omega (by simpa only [a, b, fkIsingSquareOrientedEdge_eq n e,
        D, closed] using hseparated)
    simpa only [a, b, fkIsingSquareOrientedEdge_eq n e,
      closed, opened] using h
  have hmass := D.sqrtTwo_mul_criticalMass_setOpen_eq_setClosed_of_clusterMerge
    (by simpa only [SimpleGraph.mem_edgeFinset] using e.2) omega hcluster
  have hmassC : (D.criticalMass closed : Complex) =
      (Real.sqrt 2 : Complex) * (D.criticalMass opened : Complex) := by
    exact_mod_cast hmass.symm
  have hcE : E ∈ D.exploration closed := by
    simpa only [D, closed, E, fkIsingSquareWiredDobrushinDomain,
      fkIsingSquareWiredPathUsesLocalSide,
      mem_fkIsingSquareWiredExplorationOrder_iff_trace] using heast
  have hcN : N ∈ D.exploration closed := by
    have htrace : (.dart (e, .east) : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn closed := by
      simpa only [closed, ← mem_fkIsingSquareWiredExplorationOrder_iff_trace,
        fkIsingSquareWiredPathUsesLocalSide] using heast
    have h := (fkIsingSquareWired_closed_east_mem_iff_north
      n hn omega e).1 htrace
    simpa only [D, closed, N, fkIsingSquareWiredDobrushinDomain] using h
  have hcW : W ∉ D.exploration closed := by
    simpa only [D, closed, W, fkIsingSquareWiredDobrushinDomain,
      fkIsingSquareWiredPathUsesLocalSide,
      mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hwest
  have hcS : S ∉ D.exploration closed := by
    intro hS
    apply hwest
    rw [fkIsingSquareWiredPathUsesLocalSide,
      mem_fkIsingSquareWiredExplorationOrder_iff_trace]
    apply (fkIsingSquareWired_closed_west_mem_iff_south n hn omega e).2
    simpa only [D, closed, S, fkIsingSquareWiredDobrushinDomain] using hS
  have ho (side : FKIsingMedialSide) :
      (.dart (e, side) : FKIsingSquareWiredCarrier n) ∈
        D.exploration opened := by
    simpa only [D, opened, fkIsingSquareWiredDobrushinDomain,
      fkIsingSquareWiredPathUsesLocalSide,
      mem_fkIsingSquareWiredExplorationOrder_iff_trace] using hopen side
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
  · simpa only [D, closed, E, N, fkIsingSquareWiredDobrushinDomain] using hcNphase
  · simpa only [D, opened, W, N, fkIsingSquareWiredDobrushinDomain] using hoNphase
  · simpa only [D, opened, E, S, fkIsingSquareWiredDobrushinDomain] using hoSphase
  · simpa only [D, opened, closed, E, fkIsingSquareWiredDobrushinDomain] using hphaseE
  · simpa only [D, opened, closed, N, fkIsingSquareWiredDobrushinDomain] using hphaseN

end LegacyWiredSwitching

end

end StatMech.Universality
