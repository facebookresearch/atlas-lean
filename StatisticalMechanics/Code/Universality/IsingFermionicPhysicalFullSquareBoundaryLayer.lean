/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalFullSquareBoundaryCancellation












namespace StatMech.Universality

open Finset Complex SimpleGraph
open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section


def fkIsingSquarePerimeterPrimalEdgeFinset (n : Nat) :
    Finset (Sym2 (fkSquareBoxPlanar n).V) :=
  Finset.univ.biUnion fun side : FKIsingSquareBoundarySide =>
    Finset.univ.image fun k : Fin (2 * n) =>
      (fkIsingSquarePerimeterEdge n side k).1


def fkIsingSquareClosePerimeter (n : Nat)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    ConfigSpace (Sym2 (fkSquareBoxPlanar n).V) :=
  fun e => if e ∈ fkIsingSquarePerimeterPrimalEdgeFinset n then false
    else omega e

@[simp] theorem fkIsingSquareClosePerimeter_perimeterEdge
    (n : Nat) (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    fkIsingSquareClosePerimeter n omega
        (fkIsingSquarePerimeterEdge n side k).1 = false := by
  simp [fkIsingSquareClosePerimeter,
    fkIsingSquarePerimeterPrimalEdgeFinset]

theorem setClosed_fkIsingSquareClosePerimeter_perimeterEdge
    (n : Nat) (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    setClosed (fkIsingSquarePerimeterEdge n side k).1
        (fkIsingSquareClosePerimeter n omega) =
      fkIsingSquareClosePerimeter n omega := by
  funext e
  by_cases h : e = (fkIsingSquarePerimeterEdge n side k).1
  · subst e
    simp [setClosed, fkIsingSquareClosePerimeter_perimeterEdge]
  · simp [setClosed, h]



def fkIsingSquareBoundaryDeletedPlanar (n : Nat) : PlanarZ2Subgraph where
  V := (fkSquareBoxPlanar n).V
  finV := inferInstance
  decV := inferInstance
  G := (fkSquareBoxPlanar n).G.deleteEdges
    (fkIsingSquarePerimeterPrimalEdgeFinset n :
      Set (Sym2 (fkSquareBoxPlanar n).V))
  emb := (fkSquareBoxPlanar n).emb
  isSub := by
    intro x y hxy
    exact (fkSquareBoxPlanar n).isSub hxy.1


def fkIsingSquareBoundaryLayerInwardSide :
    FKIsingSquareBoundarySide -> FKIsingMedialSide
  | .bottom | .right => .west
  | .top | .left => .east



def fkIsingSquareBoundaryLayerEndpointSide :
    FKIsingSquareBoundarySide -> FKIsingMedialSide
  | .bottom | .right => .south
  | .top | .left => .north




def fkIsingSquareBoundaryLayerComplementInwardSide :
    FKIsingSquareBoundarySide -> FKIsingMedialSide
  | .bottom | .right => .east
  | .top | .left => .west

def fkIsingSquareBoundaryLayerComplementEndpointSide :
    FKIsingSquareBoundarySide -> FKIsingMedialSide
  | .bottom | .right => .north
  | .top | .left => .south

theorem fkIsingSquareBoundaryLayerInwardSide_eq_interiorSide
    (side : FKIsingSquareBoundarySide) :
    fkIsingSquareBoundaryLayerInwardSide side =
      fkIsingSquarePerimeterInteriorSide side := by
  cases side <;> rfl

@[simp] theorem fkIsingSquareBoundaryLayer_localMate
    (n : Nat) (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    FKIsingMedialDart.localMate (fkIsingSquareClosePerimeter n omega)
        (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerInwardSide side) =
      (fkIsingSquarePerimeterEdge n side k,
        fkIsingSquareBoundaryLayerEndpointSide side) := by
  cases side <;>
    simp [FKIsingMedialDart.localMate,
      fkIsingSquareBoundaryLayerInwardSide,
      fkIsingSquareBoundaryLayerEndpointSide,
      fkIsingSquareClosePerimeter_perimeterEdge]

@[simp] theorem fkIsingSquareBoundaryLayer_complement_localMate
    (n : Nat) (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    FKIsingMedialDart.localMate (fkIsingSquareClosePerimeter n omega)
        (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerComplementInwardSide side) =
      (fkIsingSquarePerimeterEdge n side k,
        fkIsingSquareBoundaryLayerComplementEndpointSide side) := by
  cases side <;>
    simp [FKIsingMedialDart.localMate,
      fkIsingSquareBoundaryLayerComplementInwardSide,
      fkIsingSquareBoundaryLayerComplementEndpointSide,
      fkIsingSquareClosePerimeter_perimeterEdge]




def fkIsingSquareBoundaryRestrictedDobrushinDomain
    (n : Nat) (hn : 0 < n) :
    FKIsingDobrushinDomain (fkIsingSquareBoundaryDeletedPlanar n)
      (FKIsingSquareWiredCarrier n) where
  wiredArc := fkIsingSquareWiredArc n
  markedA := fkIsingSquareMarkedA n
  markedB := fkIsingSquareMarkedB n
  markedA_mem := fkIsingSquareMarkedA_mem_wiredArc n
  markedB_mem := fkIsingSquareMarkedB_mem_wiredArc n
  sourceEdge := .source
  terminalEdge := .terminal
  medialPosition := fkIsingSquareWiredCarrierPosition n hn
  exploration := fun omega =>
    fkIsingSquareWiredExplorationOrder n hn
      (fkIsingSquareClosePerimeter n omega)
  source_mem := fun omega =>
    fkIsingSquareWiredExplorationOrder_source_mem n hn _
  terminal_mem := fun omega =>
    fkIsingSquareWiredExplorationOrder_terminal_mem n hn _
  winding := fun omega =>
    fkIsingSquareWiredLiftedWinding n hn
      (fkIsingSquareClosePerimeter n omega)
  winding_terminal := fun omega =>
    fkIsingSquareWiredLiftedWinding_terminal n hn _



theorem fkIsingSquareBoundaryLayer_mem_inward_iff_endpoint
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    (.dart (fkIsingSquarePerimeterEdge n side k,
        fkIsingSquareBoundaryLayerInwardSide side) :
      FKIsingSquareWiredCarrier n) ∈
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).exploration
          omega <->
    (.dart (fkIsingSquarePerimeterEdge n side k,
        fkIsingSquareBoundaryLayerEndpointSide side) :
      FKIsingSquareWiredCarrier n) ∈
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).exploration
          omega := by
  let omega' := fkIsingSquareClosePerimeter n omega
  let e := fkIsingSquarePerimeterEdge n side k
  let a : FKIsingSquareWiredCarrier n :=
    .dart (e, fkIsingSquareBoundaryLayerInwardSide side)
  let b : FKIsingSquareWiredCarrier n :=
    .dart (e, fkIsingSquareBoundaryLayerEndpointSide side)
  change a ∈ fkIsingSquareWiredExplorationOrder n hn omega' <->
    b ∈ fkIsingSquareWiredExplorationOrder n hn omega'
  have hm : FKIsingMedialDart.localMate omega'
      (e, fkIsingSquareBoundaryLayerInwardSide side) =
        (e, fkIsingSquareBoundaryLayerEndpointSide side) := by
    exact fkIsingSquareBoundaryLayer_localMate n omega side k
  constructor
  · intro ha
    have hpair := fkIsingSquareWired_localMate_infix_explorationOrder
      n hn omega' e (fkIsingSquareBoundaryLayerInwardSide side) ha
    exact hpair.elim (fun h => h.mem (by simp [b, hm]))
      (fun h => h.mem (by simp [b, hm]))
  · intro hb
    have hinv := FKIsingMedialDart.localMate_involutive omega'
      (e, fkIsingSquareBoundaryLayerInwardSide side)
    have hm' : FKIsingMedialDart.localMate omega'
        (e, fkIsingSquareBoundaryLayerEndpointSide side) =
          (e, fkIsingSquareBoundaryLayerInwardSide side) := by
      rw [<- hm]
      exact hinv
    have hpair := fkIsingSquareWired_localMate_infix_explorationOrder
      n hn omega' e (fkIsingSquareBoundaryLayerEndpointSide side) hb
    exact hpair.elim (fun h => h.mem (by simp [a, hm']))
      (fun h => h.mem (by simp [a, hm']))



theorem fkIsingSquareBoundaryLayer_winding_endpoint
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n))
    (hmem : (.dart (fkIsingSquarePerimeterEdge n side k,
        fkIsingSquareBoundaryLayerInwardSide side) :
      FKIsingSquareWiredCarrier n) ∈
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).exploration
          omega) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).winding omega
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerEndpointSide side)) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).winding omega
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerInwardSide side)) - Real.pi / 2 := by
  let omega' := fkIsingSquareClosePerimeter n omega
  let e := fkIsingSquarePerimeterEdge n side k
  have hclosed : setClosed e.1 omega' = omega' := by
    exact setClosed_fkIsingSquareClosePerimeter_perimeterEdge
      n omega side k
  change fkIsingSquareWiredLiftedWinding n hn omega'
      (.dart (e, fkIsingSquareBoundaryLayerEndpointSide side)) =
    fkIsingSquareWiredLiftedWinding n hn omega'
      (.dart (e, fkIsingSquareBoundaryLayerInwardSide side)) - Real.pi / 2
  change fkIsingSquareWiredPathUsesLocalSide n hn omega' e
      (fkIsingSquareBoundaryLayerInwardSide side) at hmem
  cases side with
  | bottom =>
      have h := fkIsingSquareWired_closed_west_south_winding
        n hn omega' e (by simpa [hclosed] using hmem)
      simpa [hclosed, fkIsingSquareBoundaryLayerInwardSide,
        fkIsingSquareBoundaryLayerEndpointSide] using h
  | right =>
      have h := fkIsingSquareWired_closed_west_south_winding
        n hn omega' e (by simpa [hclosed] using hmem)
      simpa [hclosed, fkIsingSquareBoundaryLayerInwardSide,
        fkIsingSquareBoundaryLayerEndpointSide] using h
  | top =>
      have h := fkIsingSquareWired_closed_east_north_winding
        n hn omega' e (by simpa [hclosed] using hmem)
      simpa [hclosed, fkIsingSquareBoundaryLayerInwardSide,
        fkIsingSquareBoundaryLayerEndpointSide] using h
  | left =>
      have h := fkIsingSquareWired_closed_east_north_winding
        n hn omega' e (by simpa [hclosed] using hmem)
      simpa [hclosed, fkIsingSquareBoundaryLayerInwardSide,
        fkIsingSquareBoundaryLayerEndpointSide] using h



theorem fkIsingSquareBoundaryLayer_windingPhase_endpoint
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n))
    (hmem : (.dart (fkIsingSquarePerimeterEdge n side k,
        fkIsingSquareBoundaryLayerInwardSide side) :
      FKIsingSquareWiredCarrier n) ∈
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).exploration
          omega) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).windingPhase omega
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerEndpointSide side)) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).windingPhase omega
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerInwardSide side)) * isingLambda⁻¹ := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let a : FKIsingSquareWiredCarrier n :=
    .dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquareBoundaryLayerInwardSide side)
  let b : FKIsingSquareWiredCarrier n :=
    .dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquareBoundaryLayerEndpointSide side)
  have hw := fkIsingSquareBoundaryLayer_winding_endpoint
    n hn omega side k hmem
  change Complex.exp (Complex.I * (((D.winding omega b) / 2 : Real) :
      Complex)) =
    Complex.exp (Complex.I * (((D.winding omega a) / 2 : Real) :
      Complex)) * isingLambda⁻¹
  rw [hw]
  rw [show isingLambda⁻¹ =
      Complex.exp (-((Real.pi / 4 : Real) : Complex) * Complex.I) by
    rw [isingLambda, <- Complex.exp_neg]
    congr 1
    ring]
  rw [<- Complex.exp_add]
  congr 1
  push_cast
  ring



theorem fkIsingSquareBoundaryLayer_fermionicSummand_endpoint
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicSummand
        omega
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerEndpointSide side)) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicSummand
        omega
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerInwardSide side)) * isingLambda⁻¹ := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let a : FKIsingSquareWiredCarrier n :=
    .dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquareBoundaryLayerInwardSide side)
  let b : FKIsingSquareWiredCarrier n :=
    .dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquareBoundaryLayerEndpointSide side)
  change D.fermionicSummand omega b = D.fermionicSummand omega a * _
  unfold FKIsingDobrushinDomain.fermionicSummand
  by_cases ha : a ∈ D.exploration omega
  · have hb : b ∈ D.exploration omega :=
      (fkIsingSquareBoundaryLayer_mem_inward_iff_endpoint
        n hn omega side k).1 ha
    rw [if_pos ha, if_pos hb,
      fkIsingSquareBoundaryLayer_windingPhase_endpoint n hn omega side k ha]
    ring
  · have hb : b ∉ D.exploration omega := fun h =>
      ha ((fkIsingSquareBoundaryLayer_mem_inward_iff_endpoint
        n hn omega side k).2 h)
    rw [if_neg ha, if_neg hb, zero_mul]


theorem fkIsingSquareBoundaryLayer_fermionicObservable_endpoint
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerEndpointSide side)) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerInwardSide side)) * isingLambda⁻¹ := by
  unfold FKIsingDobrushinDomain.fermionicObservable
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro omega _
  exact fkIsingSquareBoundaryLayer_fermionicSummand_endpoint
    n hn omega side k



theorem fkIsingSquareBoundaryLayer_mem_complement_inward_iff_endpoint
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    (.dart (fkIsingSquarePerimeterEdge n side k,
        fkIsingSquareBoundaryLayerComplementInwardSide side) :
      FKIsingSquareWiredCarrier n) ∈
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).exploration
          omega <->
    (.dart (fkIsingSquarePerimeterEdge n side k,
        fkIsingSquareBoundaryLayerComplementEndpointSide side) :
      FKIsingSquareWiredCarrier n) ∈
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).exploration
          omega := by
  let omega' := fkIsingSquareClosePerimeter n omega
  let e := fkIsingSquarePerimeterEdge n side k
  let a : FKIsingSquareWiredCarrier n :=
    .dart (e, fkIsingSquareBoundaryLayerComplementInwardSide side)
  let b : FKIsingSquareWiredCarrier n :=
    .dart (e, fkIsingSquareBoundaryLayerComplementEndpointSide side)
  change a ∈ fkIsingSquareWiredExplorationOrder n hn omega' <->
    b ∈ fkIsingSquareWiredExplorationOrder n hn omega'
  have hm : FKIsingMedialDart.localMate omega'
      (e, fkIsingSquareBoundaryLayerComplementInwardSide side) =
        (e, fkIsingSquareBoundaryLayerComplementEndpointSide side) := by
    exact fkIsingSquareBoundaryLayer_complement_localMate n omega side k
  constructor
  · intro ha
    have hpair := fkIsingSquareWired_localMate_infix_explorationOrder
      n hn omega' e (fkIsingSquareBoundaryLayerComplementInwardSide side) ha
    exact hpair.elim (fun h => h.mem (by simp [b, hm]))
      (fun h => h.mem (by simp [b, hm]))
  · intro hb
    have hinv := FKIsingMedialDart.localMate_involutive omega'
      (e, fkIsingSquareBoundaryLayerComplementInwardSide side)
    have hm' : FKIsingMedialDart.localMate omega'
        (e, fkIsingSquareBoundaryLayerComplementEndpointSide side) =
          (e, fkIsingSquareBoundaryLayerComplementInwardSide side) := by
      rw [<- hm]
      exact hinv
    have hpair := fkIsingSquareWired_localMate_infix_explorationOrder
      n hn omega' e (fkIsingSquareBoundaryLayerComplementEndpointSide side) hb
    exact hpair.elim (fun h => h.mem (by simp [a, hm']))
      (fun h => h.mem (by simp [a, hm']))



theorem fkIsingSquareBoundaryLayer_winding_complement_endpoint
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n))
    (hmem : (.dart (fkIsingSquarePerimeterEdge n side k,
        fkIsingSquareBoundaryLayerComplementInwardSide side) :
      FKIsingSquareWiredCarrier n) ∈
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).exploration
          omega) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).winding omega
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerComplementEndpointSide side)) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).winding omega
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerComplementInwardSide side)) - Real.pi / 2 := by
  let omega' := fkIsingSquareClosePerimeter n omega
  let e := fkIsingSquarePerimeterEdge n side k
  have hclosed : setClosed e.1 omega' = omega' :=
    setClosed_fkIsingSquareClosePerimeter_perimeterEdge n omega side k
  change fkIsingSquareWiredLiftedWinding n hn omega'
      (.dart (e, fkIsingSquareBoundaryLayerComplementEndpointSide side)) =
    fkIsingSquareWiredLiftedWinding n hn omega'
      (.dart (e, fkIsingSquareBoundaryLayerComplementInwardSide side)) -
        Real.pi / 2
  change fkIsingSquareWiredPathUsesLocalSide n hn omega' e
      (fkIsingSquareBoundaryLayerComplementInwardSide side) at hmem
  cases side with
  | bottom =>
      have h := fkIsingSquareWired_closed_east_north_winding
        n hn omega' e (by simpa [hclosed] using hmem)
      simpa [hclosed, fkIsingSquareBoundaryLayerComplementInwardSide,
        fkIsingSquareBoundaryLayerComplementEndpointSide] using h
  | right =>
      have h := fkIsingSquareWired_closed_east_north_winding
        n hn omega' e (by simpa [hclosed] using hmem)
      simpa [hclosed, fkIsingSquareBoundaryLayerComplementInwardSide,
        fkIsingSquareBoundaryLayerComplementEndpointSide] using h
  | top =>
      have h := fkIsingSquareWired_closed_west_south_winding
        n hn omega' e (by simpa [hclosed] using hmem)
      simpa [hclosed, fkIsingSquareBoundaryLayerComplementInwardSide,
        fkIsingSquareBoundaryLayerComplementEndpointSide] using h
  | left =>
      have h := fkIsingSquareWired_closed_west_south_winding
        n hn omega' e (by simpa [hclosed] using hmem)
      simpa [hclosed, fkIsingSquareBoundaryLayerComplementInwardSide,
        fkIsingSquareBoundaryLayerComplementEndpointSide] using h

theorem fkIsingSquareBoundaryLayer_windingPhase_complement_endpoint
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n))
    (hmem : (.dart (fkIsingSquarePerimeterEdge n side k,
        fkIsingSquareBoundaryLayerComplementInwardSide side) :
      FKIsingSquareWiredCarrier n) ∈
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).exploration
          omega) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).windingPhase omega
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerComplementEndpointSide side)) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).windingPhase omega
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerComplementInwardSide side)) *
            isingLambda⁻¹ := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let a : FKIsingSquareWiredCarrier n :=
    .dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquareBoundaryLayerComplementInwardSide side)
  let b : FKIsingSquareWiredCarrier n :=
    .dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquareBoundaryLayerComplementEndpointSide side)
  have hw := fkIsingSquareBoundaryLayer_winding_complement_endpoint
    n hn omega side k hmem
  change Complex.exp (Complex.I * (((D.winding omega b) / 2 : Real) :
      Complex)) =
    Complex.exp (Complex.I * (((D.winding omega a) / 2 : Real) :
      Complex)) * isingLambda⁻¹
  rw [hw]
  rw [show isingLambda⁻¹ =
      Complex.exp (-((Real.pi / 4 : Real) : Complex) * Complex.I) by
    rw [isingLambda, <- Complex.exp_neg]
    congr 1
    ring]
  rw [<- Complex.exp_add]
  congr 1
  push_cast
  ring

theorem fkIsingSquareBoundaryLayer_fermionicSummand_complement_endpoint
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicSummand
        omega
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerComplementEndpointSide side)) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicSummand
        omega
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerComplementInwardSide side)) *
            isingLambda⁻¹ := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let a : FKIsingSquareWiredCarrier n :=
    .dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquareBoundaryLayerComplementInwardSide side)
  let b : FKIsingSquareWiredCarrier n :=
    .dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquareBoundaryLayerComplementEndpointSide side)
  change D.fermionicSummand omega b = D.fermionicSummand omega a * _
  unfold FKIsingDobrushinDomain.fermionicSummand
  by_cases ha : a ∈ D.exploration omega
  · have hb : b ∈ D.exploration omega :=
      (fkIsingSquareBoundaryLayer_mem_complement_inward_iff_endpoint
        n hn omega side k).1 ha
    rw [if_pos ha, if_pos hb,
      fkIsingSquareBoundaryLayer_windingPhase_complement_endpoint
        n hn omega side k ha]
    ring
  · have hb : b ∉ D.exploration omega := fun h =>
      ha ((fkIsingSquareBoundaryLayer_mem_complement_inward_iff_endpoint
        n hn omega side k).2 h)
    rw [if_neg ha, if_neg hb, zero_mul]

theorem fkIsingSquareBoundaryLayer_fermionicObservable_complement_endpoint
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerComplementEndpointSide side)) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerComplementInwardSide side)) *
            isingLambda⁻¹ := by
  unfold FKIsingDobrushinDomain.fermionicObservable
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro omega _
  exact fkIsingSquareBoundaryLayer_fermionicSummand_complement_endpoint
    n hn omega side k


noncomputable def isingFermionicBoundaryVertexNormalization : Real :=
  2 / (2 + Real.sqrt 2)

theorem isingFermionicBoundaryVertexNormalization_pos :
    0 < isingFermionicBoundaryVertexNormalization := by
  unfold isingFermionicBoundaryVertexNormalization
  positivity



noncomputable def fkIsingSquareBoundaryLayerVertexFermion
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) : Complex :=
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  (isingFermionicBoundaryVertexNormalization : Complex) *
    (D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerInwardSide side)) +
      D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerEndpointSide side)))



noncomputable def fkIsingSquareBoundaryLayerNormal :
    FKIsingSquareBoundarySide -> Complex
  | .bottom => isingLambda
  | .right => isingLambda⁻¹
  | .top => -isingLambda
  | .left => -isingLambda⁻¹

theorem fkIsingSquareBoundaryLayerInward_directedTangent
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    fkIsingSquareWiredDirectedTangent n hn
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerInwardSide side)) =
      match side with
      | .bottom => 1
      | .right => -Complex.I
      | .top => -1
      | .left => Complex.I := by
  let e := fkIsingSquarePerimeterEdge n side k
  cases side with
  | bottom =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal :=
        fkIsingSquarePerimeterEdge_axis n .bottom k
      exact (fkIsingSquareWiredDirectedTangent_horizontal_local
        n hn e haxis).1
  | right =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .vertical :=
        fkIsingSquarePerimeterEdge_axis n .right k
      exact (fkIsingSquareWiredDirectedTangent_vertical_local
        n hn e haxis).1
  | top =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal :=
        fkIsingSquarePerimeterEdge_axis n .top k
      exact (fkIsingSquareWiredDirectedTangent_horizontal_local
        n hn e haxis).2.1
  | left =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .vertical :=
        fkIsingSquarePerimeterEdge_axis n .left k
      exact (fkIsingSquareWiredDirectedTangent_vertical_local
        n hn e haxis).2.1


theorem fkIsingSquareBoundaryLayerNormal_mul_edgeSumFactor_sq
    (side : FKIsingSquareBoundarySide) :
    fkIsingSquareBoundaryLayerNormal side * (1 + isingLambda⁻¹) ^ 2 =
      ((2 + Real.sqrt 2 : Real) : Complex) *
        match side with
        | .bottom => 1
        | .right => -Complex.I
        | .top => -1
        | .left => Complex.I := by
  have hbase : isingLambda * (1 + isingLambda⁻¹) ^ 2 =
      ((2 + Real.sqrt 2 : Real) : Complex) := by
    calc
      _ = isingLambda + 2 + isingLambda⁻¹ := by
        field_simp [isingLambda_ne]
        ring
      _ = _ := by rw [isingLambda_inv]; push_cast; ring
  have hinvSq : isingLambda⁻¹ ^ 2 = -Complex.I := by
    rw [inv_pow, isingLambda_sq]
    simp
  cases side with
  | bottom => simpa [fkIsingSquareBoundaryLayerNormal] using hbase
  | right =>
      simp only [fkIsingSquareBoundaryLayerNormal]
      calc
        isingLambda⁻¹ * (1 + isingLambda⁻¹) ^ 2 =
            isingLambda⁻¹ ^ 2 *
              (isingLambda * (1 + isingLambda⁻¹) ^ 2) := by
          field_simp [isingLambda_ne]
        _ = _ := by rw [hinvSq, hbase]; ring
  | top =>
      simp only [fkIsingSquareBoundaryLayerNormal]
      rw [neg_mul, hbase]
      ring
  | left =>
      simp only [fkIsingSquareBoundaryLayerNormal]
      calc
        -isingLambda⁻¹ * (1 + isingLambda⁻¹) ^ 2 =
            -(isingLambda⁻¹ ^ 2 *
              (isingLambda * (1 + isingLambda⁻¹) ^ 2)) := by
          field_simp [isingLambda_ne]
        _ = _ := by rw [hinvSq, hbase]; ring



theorem fkIsingSquareBoundaryLayer_windingPhase_sq
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareWiredCarrier n)
    (hz : z ∈
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).exploration
        omega) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).windingPhase
        omega z ^ 2 =
      fkIsingSquareWiredDirectedPhase n hn z ^ 2 := by
  change (fkIsingSquareWiredDobrushinDomain n hn).windingPhase
      (fkIsingSquareClosePerimeter n omega) z ^ 2 = _
  apply fkIsingSquareWired_windingPhase_sq n hn
  simpa [fkIsingSquareBoundaryRestrictedDobrushinDomain] using hz



theorem fkIsingSquareBoundaryLayer_inward_exists_nonnegative_square
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    ∃ t : Real, 0 <= t ∧
      fkIsingSquareWiredDirectedTangent n hn
          (.dart (fkIsingSquarePerimeterEdge n side k,
            fkIsingSquareBoundaryLayerInwardSide side)) *
        ((fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
            (.dart (fkIsingSquarePerimeterEdge n side k,
              fkIsingSquareBoundaryLayerInwardSide side))) ^ 2 =
        (t : Complex) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let z : FKIsingSquareWiredCarrier n :=
    .dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquareBoundaryLayerInwardSide side)
  apply D.exists_nonnegative_boundary_square_of_phase_sq z
    (fkIsingSquareWiredDirectedTangent n hn z)
    (fkIsingSquareWiredDirectedPhase n hn z) 1
  · intro omega hz
    exact fkIsingSquareBoundaryLayer_windingPhase_sq n hn omega z hz
  · exact zero_le_one
  · exact fkIsingSquareWiredDirectedTangent_mul_phase_sq n hn z



theorem fkIsingSquareBoundaryLayerVertexFermion_exists_nonnegative_square
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    ∃ t : Real, 0 <= t ∧
      fkIsingSquareBoundaryLayerNormal side *
          fkIsingSquareBoundaryLayerVertexFermion n hn side k ^ 2 =
        (t : Complex) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let z : FKIsingSquareWiredCarrier n :=
    .dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquareBoundaryLayerInwardSide side)
  let F := D.fermionicObservable z
  let c := isingFermionicBoundaryVertexNormalization
  obtain ⟨u, hu, hF⟩ :=
    fkIsingSquareBoundaryLayer_inward_exists_nonnegative_square
      n hn side k
  have hnormal : fkIsingSquareBoundaryLayerNormal side *
        (1 + isingLambda⁻¹) ^ 2 =
      ((2 + Real.sqrt 2 : Real) : Complex) *
        fkIsingSquareWiredDirectedTangent n hn z := by
    rw [fkIsingSquareBoundaryLayerNormal_mul_edgeSumFactor_sq,
      fkIsingSquareBoundaryLayerInward_directedTangent]
  have hvertex : fkIsingSquareBoundaryLayerVertexFermion n hn side k =
      (c : Complex) * (F * (1 + isingLambda⁻¹)) := by
    unfold fkIsingSquareBoundaryLayerVertexFermion
    change (c : Complex) *
      (F + D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerEndpointSide side))) = _
    rw [fkIsingSquareBoundaryLayer_fermionicObservable_endpoint]
    change (c : Complex) * (F + F * isingLambda⁻¹) = _
    ring
  refine ⟨c ^ 2 * (2 + Real.sqrt 2) * u,
    mul_nonneg (mul_nonneg (sq_nonneg c) (by positivity)) hu, ?_⟩
  rw [hvertex]
  calc
    fkIsingSquareBoundaryLayerNormal side *
          ((c : Complex) * (F * (1 + isingLambda⁻¹))) ^ 2 =
        (c : Complex) ^ 2 *
          (fkIsingSquareBoundaryLayerNormal side *
            (1 + isingLambda⁻¹) ^ 2) * F ^ 2 := by ring
    _ = (c : Complex) ^ 2 *
          (((2 + Real.sqrt 2 : Real) : Complex) *
            fkIsingSquareWiredDirectedTangent n hn z) * F ^ 2 := by
      rw [hnormal]
    _ = (c : Complex) ^ 2 *
          ((2 + Real.sqrt 2 : Real) : Complex) * (u : Complex) := by
      have hTF : fkIsingSquareWiredDirectedTangent n hn z * F ^ 2 =
          (u : Complex) := by
        simpa only [D, z, F] using hF
      rw [show (c : Complex) ^ 2 *
          (((2 + Real.sqrt 2 : Real) : Complex) *
            fkIsingSquareWiredDirectedTangent n hn z) * F ^ 2 =
        (c : Complex) ^ 2 * ((2 + Real.sqrt 2 : Real) : Complex) *
          (fkIsingSquareWiredDirectedTangent n hn z * F ^ 2) by ring,
        hTF]
    _ = ((c ^ 2 * (2 + Real.sqrt 2) * u : Real) : Complex) := by
      push_cast
      ring

theorem isingFermionicBoundaryVertexNormalization_sq_mul_edgeSumNormSq :
    isingFermionicBoundaryVertexNormalization ^ 2 *
        (2 + Real.sqrt 2) =
      isingFermionicBoundaryVertexNormSqFactor := by
  have hsqrt : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num : (0 : Real) <= 2)
  have hden : 2 + Real.sqrt 2 ≠ 0 := by positivity
  unfold isingFermionicBoundaryVertexNormalization
    isingFermionicBoundaryVertexNormSqFactor
  field_simp [hden]
  nlinarith

theorem isingLambda_inv_val :
    isingLambda⁻¹ = (1 - Complex.I) / (Real.sqrt 2 : Complex) := by
  have hsqrt : (Real.sqrt 2 : Complex) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : Real) <= 2)
  have hsqrt_ne : (Real.sqrt 2 : Complex) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : Real) < 2))
  rw [isingLambda_inv, isingLambda_val]
  field_simp [hsqrt_ne]
  rw [hsqrt]
  ring

theorem isingLambda_one_add_inv_normSq :
    Complex.normSq (1 + isingLambda⁻¹) = 2 + Real.sqrt 2 := by
  rw [isingLambda_inv_val]
  have hsqrt : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num : (0 : Real) <= 2)
  have hsqrt_ne : Real.sqrt 2 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : Real) < 2))
  simp [Complex.normSq_apply, Complex.div_re, Complex.div_im,
    Complex.normSq_ofReal, hsqrt_ne]
  field_simp [hsqrt_ne]
  nlinarith


theorem fkIsingSquareBoundaryLayerVertexFermion_normSq
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    Complex.normSq
        (fkIsingSquareBoundaryLayerVertexFermion n hn side k) =
      isingFermionicBoundaryVertexNormSqFactor *
        Complex.normSq
          ((fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
              (.dart (fkIsingSquarePerimeterEdge n side k,
                fkIsingSquareBoundaryLayerInwardSide side))) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let z : FKIsingSquareWiredCarrier n :=
    .dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquareBoundaryLayerInwardSide side)
  let F := D.fermionicObservable z
  let c := isingFermionicBoundaryVertexNormalization
  have hvertex : fkIsingSquareBoundaryLayerVertexFermion n hn side k =
      (c : Complex) * (F * (1 + isingLambda⁻¹)) := by
    unfold fkIsingSquareBoundaryLayerVertexFermion
    change (c : Complex) *
      (F + D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerEndpointSide side))) = _
    rw [fkIsingSquareBoundaryLayer_fermionicObservable_endpoint]
    change (c : Complex) * (F + F * isingLambda⁻¹) = _
    ring
  rw [hvertex, Complex.normSq_mul, Complex.normSq_mul,
    Complex.normSq_ofReal, isingLambda_one_add_inv_normSq]
  change (c * c) *
      (Complex.normSq F * (2 + Real.sqrt 2)) =
    isingFermionicBoundaryVertexNormSqFactor * Complex.normSq F
  rw [show c * c = c ^ 2 by ring]
  calc
    c ^ 2 * (Complex.normSq F * (2 + Real.sqrt 2)) =
        (c ^ 2 * (2 + Real.sqrt 2)) * Complex.normSq F := by ring
    _ = _ := by
      rw [isingFermionicBoundaryVertexNormalization_sq_mul_edgeSumNormSq]



noncomputable def fkIsingSquareBoundaryLayerInwardIncrement
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) : Real :=
  Complex.normSq
    ((fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerInwardSide side)))

theorem fkIsingSquareBoundaryLayerInwardIncrement_nonneg
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    0 <= fkIsingSquareBoundaryLayerInwardIncrement n hn side k := by
  exact Complex.normSq_nonneg _



noncomputable def fkIsingSquareBoundaryLayerFirstFaceTrace
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) : Real :=
  FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn
      (fkIsingSquareBoundaryVertex n (side, k)) +
    fkIsingSquareBoundaryLayerInwardIncrement n hn side k

theorem fkIsingSquareBoundaryLayerFirstFaceTrace_sub_vertex
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    fkIsingSquareBoundaryLayerFirstFaceTrace n hn side k -
        FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn
          (fkIsingSquareBoundaryVertex n (side, k)) =
      fkIsingSquareBoundaryLayerInwardIncrement n hn side k := by
  unfold fkIsingSquareBoundaryLayerFirstFaceTrace
  ring

theorem fkIsingSquareBoundaryLayer_vertex_le_firstFaceTrace
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn
        (fkIsingSquareBoundaryVertex n (side, k)) <=
      fkIsingSquareBoundaryLayerFirstFaceTrace n hn side k := by
  rw [<- sub_nonneg]
  rw [fkIsingSquareBoundaryLayerFirstFaceTrace_sub_vertex]
  exact fkIsingSquareBoundaryLayerInwardIncrement_nonneg n hn side k



theorem fkIsingSquareBoundaryLayer_halfDiagonal_normSq
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    Real.sqrt 2 / 2 * Complex.normSq
        (fkIsingSquareBoundaryLayerVertexFermion n hn side k) =
      isingFermionicGhostCoefficient *
        fkIsingSquareBoundaryLayerInwardIncrement n hn side k := by
  rw [fkIsingSquareBoundaryLayerVertexFermion_normSq,
    fkIsingSquareBoundaryLayerInwardIncrement]
  rw [<- mul_assoc,
    isingFermionic_halfDiagonal_mul_boundaryVertexNormSqFactor]


theorem fkIsingSquareBoundaryLayer_fermionicSummand_incidence
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicSummand
        omega (.bond d) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicSummand
        omega (.dart d) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let omega' := fkIsingSquareClosePerimeter n omega
  by_cases hd : (.dart d : FKIsingSquareWiredCarrier n) ∈
      D.exploration omega
  · have hpair := fkIsingSquareWired_incidence_infix_explorationOrder
      n hn omega' d (by simpa [D, omega',
        fkIsingSquareBoundaryRestrictedDobrushinDomain] using hd)
    have hb : (.bond d : FKIsingSquareWiredCarrier n) ∈
        D.exploration omega := by
      change (.bond d : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationOrder n hn omega'
      exact hpair.elim (fun h => h.mem (by simp))
        (fun h => h.mem (by simp))
    have hwind := fkIsingSquareWiredLiftedWinding_incidence
      n hn omega' d (by simpa [D, omega',
        fkIsingSquareBoundaryRestrictedDobrushinDomain] using hd)
    unfold FKIsingDobrushinDomain.fermionicSummand
    rw [if_pos hd, if_pos hb]
    unfold FKIsingDobrushinDomain.windingPhase
    change (D.criticalMass omega : Complex) *
        Complex.exp (Complex.I *
          (((fkIsingSquareWiredLiftedWinding n hn omega' (.bond d)) / 2 :
            Real) : Complex)) = _
    rw [hwind]
    change (D.criticalMass omega : Complex) *
        Complex.exp (Complex.I *
          (((fkIsingSquareWiredLiftedWinding n hn omega' (.dart d)) / 2 :
            Real) : Complex)) =
      (D.criticalMass omega : Complex) *
        Complex.exp (Complex.I *
          (((fkIsingSquareWiredLiftedWinding n hn omega' (.dart d)) / 2 :
            Real) : Complex))
    rfl
  · have hb : (.bond d : FKIsingSquareWiredCarrier n) ∉
        D.exploration omega := by
      intro hbond
      have htrace : (.bond d : FKIsingSquareWiredCarrier n) ∈
          fkIsingSquareWiredExplorationTrace n hn omega' := by
        rw [mem_fkIsingSquareWiredExplorationTrace_iff]
        rw [<- mem_fkIsingSquareWiredExplorationOrder_iff_reachable]
        simpa [D, omega', fkIsingSquareBoundaryRestrictedDobrushinDomain]
          using hbond
      have hdtrace :=
        (fkIsingSquareWired_incidence_mem_trace_iff n hn omega' d).1 htrace
      apply hd
      change (.dart d : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationOrder n hn omega'
      rw [mem_fkIsingSquareWiredExplorationOrder_iff_trace]
      exact hdtrace
    unfold FKIsingDobrushinDomain.fermionicSummand
    rw [if_neg hd, if_neg hb]

theorem fkIsingSquareBoundaryLayer_fermionicObservable_incidence
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.bond d) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart d) := by
  unfold FKIsingDobrushinDomain.fermionicObservable
  apply Finset.sum_congr rfl
  intro omega _
  exact fkIsingSquareBoundaryLayer_fermionicSummand_incidence
    n hn omega d



theorem fkIsingSquareBoundaryLayer_fermionicSummand_bondMate
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicSummand
        omega (.bond (fkIsingSquareWiredBondMate n hn d)) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicSummand
          omega (.bond d) *
        fkIsingSquareWiredBondPhase n hn d := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let omega' := fkIsingSquareClosePerimeter n omega
  have hmem := fkIsingSquareWired_bondMate_mem_trace_iff
    n hn omega' d hsource hterminal
  by_cases hd : (.bond d : FKIsingSquareWiredCarrier n) ∈
      D.exploration omega
  · have hdtrace : (.bond d : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn omega' := by
      rw [<- mem_fkIsingSquareWiredExplorationOrder_iff_trace]
      simpa [D, omega', fkIsingSquareBoundaryRestrictedDobrushinDomain]
        using hd
    have hftrace := hmem.mpr hdtrace
    have hf : (.bond (fkIsingSquareWiredBondMate n hn d) :
        FKIsingSquareWiredCarrier n) ∈ D.exploration omega := by
      change _ ∈ fkIsingSquareWiredExplorationOrder n hn omega'
      rw [mem_fkIsingSquareWiredExplorationOrder_iff_trace]
      exact hftrace
    have hwind := fkIsingSquareWiredLiftedWinding_bondMate
      n hn omega' d hsource hterminal (by
        simpa [D, omega', fkIsingSquareBoundaryRestrictedDobrushinDomain]
          using hd)
    unfold FKIsingDobrushinDomain.fermionicSummand
    rw [if_pos hd, if_pos hf]
    unfold FKIsingDobrushinDomain.windingPhase
    change (D.criticalMass omega : Complex) *
        Complex.exp (Complex.I *
          (((fkIsingSquareWiredLiftedWinding n hn omega'
            (.bond (fkIsingSquareWiredBondMate n hn d))) / 2 : Real) :
              Complex)) = _
    rw [hwind]
    unfold fkIsingSquareWiredBondPhase
    rw [show Complex.I *
          (((fkIsingSquareWiredLiftedWinding n hn omega' (.bond d) +
              (fkIsingSquareWiredBondTurn n hn d
                (fkIsingSquareWiredBondMate n hn d) : Real) *
                  (Real.pi / 4)) / 2 : Real) : Complex) =
        Complex.I *
            ((fkIsingSquareWiredLiftedWinding n hn omega' (.bond d) / 2 :
              Real) : Complex) +
          Complex.I *
            ((((fkIsingSquareWiredBondTurn n hn d
              (fkIsingSquareWiredBondMate n hn d) : Int) : Real) *
                (Real.pi / 8) : Real) : Complex) by push_cast; ring,
      Complex.exp_add]
    change (D.criticalMass omega : Complex) * (_ * _) =
      (D.criticalMass omega : Complex) *
        Complex.exp (Complex.I *
          (((fkIsingSquareWiredLiftedWinding n hn omega' (.bond d)) / 2 :
            Real) : Complex)) * _
    ring
  · have hf : (.bond (fkIsingSquareWiredBondMate n hn d) :
        FKIsingSquareWiredCarrier n) ∉ D.exploration omega := by
      intro hmate
      have hftrace : (.bond (fkIsingSquareWiredBondMate n hn d) :
          FKIsingSquareWiredCarrier n) ∈
          fkIsingSquareWiredExplorationTrace n hn omega' := by
        rw [<- mem_fkIsingSquareWiredExplorationOrder_iff_trace]
        simpa [D, omega', fkIsingSquareBoundaryRestrictedDobrushinDomain]
          using hmate
      apply hd
      change (.bond d : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationOrder n hn omega'
      rw [mem_fkIsingSquareWiredExplorationOrder_iff_trace]
      exact hmem.mp hftrace
    unfold FKIsingDobrushinDomain.fermionicSummand
    rw [if_neg hd, if_neg hf, zero_mul]

theorem fkIsingSquareBoundaryLayer_fermionicObservable_bondMate
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.bond (fkIsingSquareWiredBondMate n hn d)) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.bond d) *
        fkIsingSquareWiredBondPhase n hn d := by
  unfold FKIsingDobrushinDomain.fermionicObservable
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro omega _
  exact fkIsingSquareBoundaryLayer_fermionicSummand_bondMate
    n hn omega d hsource hterminal

private theorem fkIsingSquareBoundaryLayer_eq_of_sameCycle_of_step
    {A B : Type*} [Fintype A] [DecidableEq A]
    (sigma : Equiv.Perm A) (f : A -> B)
    (hstep : forall x, f (sigma x) = f x) {x y : A}
    (hxy : sigma.SameCycle x y) : f x = f y := by
  obtain ⟨k, hk⟩ := hxy.exists_nat_pow_eq
  have hpow : forall m : Nat, f ((sigma ^ m) x) = f x := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ', Equiv.Perm.mul_apply, hstep]
        exact ih
  calc
    f x = f ((sigma ^ k) x) := (hpow k).symm
    _ = f y := congrArg f hk


noncomputable def fkIsingSquareBoundaryLayerRadialIncrement
    (n : Nat) (hn : 0 < n) :
    FKIsingSquareInteriorRadialIncidence n hn -> Real :=
  Quot.lift (fun d : FKIsingSquareInteriorRadialDart n =>
      Complex.normSq
        ((fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart d.1)))
    (fun _ _ hxy => fkIsingSquareBoundaryLayer_eq_of_sameCycle_of_step
      (fkIsingSquareInteriorRadialBondPerm n hn)
      (fun d : FKIsingSquareInteriorRadialDart n =>
        Complex.normSq
          ((fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
            (.dart d.1)))
      (fun d => by
        change Complex.normSq
            ((fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
              (.dart (fkIsingSquareInteriorRadialBondMate n hn d).1)) =
          Complex.normSq
            ((fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
              (.dart d.1))
        rw [<- fkIsingSquareBoundaryLayer_fermionicObservable_incidence
          n hn (fkIsingSquareInteriorRadialBondMate n hn d).1]
        change Complex.normSq
            ((fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
              (.bond (fkIsingSquareWiredBondMate n hn d.1))) = _
        rw [fkIsingSquareBoundaryLayer_fermionicObservable_bondMate
            n hn d.1
              (fkIsingSquareInteriorRadialDart_ne_source n hn d)
              (fkIsingSquareInteriorRadialDart_ne_terminal n hn d),
          Complex.normSq_mul, fkIsingSquareWiredBondPhase_normSq, mul_one,
          fkIsingSquareBoundaryLayer_fermionicObservable_incidence])
      hxy)

@[simp] theorem fkIsingSquareBoundaryLayerRadialIncrement_mk
    (n : Nat) (hn : 0 < n) (d : FKIsingSquareInteriorRadialDart n) :
    fkIsingSquareBoundaryLayerRadialIncrement n hn (Quot.mk _ d) =
      Complex.normSq
        ((fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart d.1)) := rfl

theorem fkIsingSquareBoundaryLayerRadialIncrement_nonneg
    (n : Nat) (hn : 0 < n)
    (e : FKIsingSquareInteriorRadialIncidence n hn) :
    0 <= fkIsingSquareBoundaryLayerRadialIncrement n hn e := by
  induction e using Quot.ind with
  | _ d => exact Complex.normSq_nonneg _
end

end StatMech.Universality
