/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalFullSquareIntegratedPrimitive















namespace StatMech.Universality

open Finset Complex SimpleGraph
open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareWired_terminalBond_mem_explorationOrder
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (.bond (fkIsingSquareWiredTerminalDart n hn) :
        FKIsingSquareWiredCarrier n) ∈
      fkIsingSquareWiredExplorationOrder n hn omega := by
  have hadj : (fkIsingSquareWiredLoopGraph n hn omega).Adj
      (.terminal : FKIsingSquareWiredCarrier n)
      (.bond (fkIsingSquareWiredTerminalDart n hn)) := by
    simp
  have hedge := fkIsingSquareWiredExplorationPath_mem_edges_of_adj
    n hn omega (fkIsingSquareWiredExplorationOrder_terminal_mem n hn omega)
      hadj
  have hinfix := Walk.infix_support_iff_mem_edges.mpr hedge
  rcases hinfix with h | h
  · exact h.mem (by simp)
  · exact h.mem (by simp)

theorem fkIsingSquareWired_terminalBond_rawTurnCount
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    fkIsingSquareWiredRawTurnCount n hn omega
        (.bond (fkIsingSquareWiredTerminalDart n hn)) =
      fkIsingSquareWiredRawTurnCount n hn omega .terminal := by
  let p := fkIsingSquareWiredExplorationOrder n hn omega
  let x : FKIsingSquareWiredCarrier n := .terminal
  let y : FKIsingSquareWiredCarrier n :=
    .bond (fkIsingSquareWiredTerminalDart n hn)
  have hadj : (fkIsingSquareWiredLoopGraph n hn omega).Adj x y := by
    simp [x, y]
  have hxy := Walk.infix_support_iff_mem_edges.mpr
    (fkIsingSquareWiredExplorationPath_mem_edges_of_adj n hn omega
      (fkIsingSquareWiredExplorationOrder_terminal_mem n hn omega) hadj)
  have hx : x ∈ p := by simp [x, p]
  have hy : y ∈ p := by
    simpa [y, p] using
      fkIsingSquareWired_terminalBond_mem_explorationOrder n hn omega
  have hix : p.idxOf x < p.length := List.idxOf_lt_length_iff.mpr hx
  have hiy : p.idxOf y < p.length := List.idxOf_lt_length_iff.mpr hy
  rcases hxy with hf | hb
  · have hi := idxOf_succ_of_pair_infix_nodup
        (fkIsingSquareWiredExplorationOrder_nodup n hn omega) hf
    have hs := fkIsingSquareWiredRawTurnCount_succ n hn omega (p.idxOf x)
      (by rw [← hi]; exact hiy)
    simpa only [p, x, y, List.getElem_idxOf hix,
      ← hi, List.getElem_idxOf hiy, fkIsingSquareWiredTransitionTurn,
      add_zero] using hs
  · have hi := idxOf_succ_of_pair_infix_nodup
        (fkIsingSquareWiredExplorationOrder_nodup n hn omega) hb
    have hs := fkIsingSquareWiredRawTurnCount_succ n hn omega (p.idxOf y)
      (by rw [← hi]; exact hix)
    have hs' : fkIsingSquareWiredRawTurnCount n hn omega .terminal =
        fkIsingSquareWiredRawTurnCount n hn omega
          (.bond (fkIsingSquareWiredTerminalDart n hn)) := by
      simpa only [p, x, y, List.getElem_idxOf hiy,
        ← hi, List.getElem_idxOf hix, fkIsingSquareWiredTransitionTurn,
        add_zero] using hs
    exact hs'.symm

theorem fkIsingSquareWired_terminalBond_observable
    (n : Nat) (hn : 0 < n) :
    (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.bond (fkIsingSquareWiredTerminalDart n hn)) = 1 := by
  rw [← fkIsingSquareWired_fermionicObservable_terminal n hn]
  unfold FKIsingDobrushinDomain.fermionicObservable
  apply Finset.sum_congr rfl
  intro omega _
  have hbmem : (.bond (fkIsingSquareWiredTerminalDart n hn) :
      FKIsingSquareWiredCarrier n) ∈
      fkIsingSquareWiredExplorationTrace n hn omega := by
    rw [mem_fkIsingSquareWiredExplorationTrace_iff]
    exact (fkIsingSquareWiredLoopGraph_source_reachable_terminal n hn omega).trans
      (show (fkIsingSquareWiredLoopGraph n hn omega).Adj
        (.terminal : FKIsingSquareWiredCarrier n)
        (.bond (fkIsingSquareWiredTerminalDart n hn)) by simp).reachable
  have htmem : (.terminal : FKIsingSquareWiredCarrier n) ∈
      fkIsingSquareWiredExplorationTrace n hn omega := by
    rw [mem_fkIsingSquareWiredExplorationTrace_iff]
    exact fkIsingSquareWiredLoopGraph_source_reachable_terminal n hn omega
  simp only [FKIsingDobrushinDomain.fermionicSummand,
    fkIsingSquareWiredDobrushinDomain, hbmem, htmem, if_true,
    FKIsingDobrushinDomain.windingPhase]
  rw [show fkIsingSquareWiredLiftedWinding n hn omega
        (.bond (fkIsingSquareWiredTerminalDart n hn)) = 0 by
    unfold fkIsingSquareWiredLiftedWinding
      fkIsingSquareWiredPhysicalTurnCount
    rw [fkIsingSquareWired_terminalBond_rawTurnCount n hn omega]
    norm_num]
  simp

theorem fkIsingSquareWired_terminalDart_observable
    (n : Nat) (hn : 0 < n) :
    (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareWiredTerminalDart n hn)) = 1 := by
  rw [← fkIsingSquareWired_fermionicObservable_incidence]
  exact fkIsingSquareWired_terminalBond_observable n hn

theorem fkIsingSquareWired_terminalDart_increment
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredPrimitiveIncrement n hn
        (.dart (fkIsingSquareWiredTerminalDart n hn)) = 1 := by
  unfold fkIsingSquareWiredPrimitiveIncrement isingPrimitiveIncrement
  rw [fkIsingSquareWired_terminalDart_observable n hn]
  norm_num

namespace FKIsingSquareFullIntegratedPrimitive

theorem vertex_eq_of_common_face_increment_eq
    (n : Nat) (hn : 0 < n)
    (e f : FKIsingSquareInteriorRadialIncidence n hn)
    (hface : fkIsingSquareFullFaceOfRadialIncidence n hn e =
      fkIsingSquareFullFaceOfRadialIncidence n hn f)
    (hinc : fkIsingSquareInteriorRadialIncrement n hn e =
      fkIsingSquareInteriorRadialIncrement n hn f) :
    vertexPrimitive n hn (fkIsingSquareInteriorRadialEndpoint n hn e) =
      vertexPrimitive n hn
        (fkIsingSquareInteriorRadialEndpoint n hn f) := by
  have he := face_sub_vertex n hn e
  have hf := face_sub_vertex n hn f
  rw [hface] at he
  linarith

theorem face_eq_of_common_vertex_increment_eq
    (n : Nat) (hn : 0 < n)
    (e f : FKIsingSquareInteriorRadialIncidence n hn)
    (hvertex : fkIsingSquareInteriorRadialEndpoint n hn e =
      fkIsingSquareInteriorRadialEndpoint n hn f)
    (hinc : fkIsingSquareInteriorRadialIncrement n hn e =
      fkIsingSquareInteriorRadialIncrement n hn f) :
    facePrimitive n hn (fkIsingSquareFullFaceOfRadialIncidence n hn e) =
      facePrimitive n hn
        (fkIsingSquareFullFaceOfRadialIncidence n hn f) := by
  have he := face_sub_vertex n hn e
  have hf := face_sub_vertex n hn f
  rw [hvertex] at he
  linarith

private def leftInteriorEastDart
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(fkIsingSquareLeftVerticalEdge n hn k, .east), by
    simp [fkIsingSquareInteriorFaceKey, fkIsingSquareWedgeFaceKey,
      fkIsingSquareLeftVerticalEdge, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareSideCorner,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareLeftVerticalUpper, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite]
    have hk := k.isLt
    omega⟩

private def leftInteriorSouthDart
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(fkIsingSquareLeftVerticalEdge n hn k, .south), by
    simp [fkIsingSquareInteriorFaceKey, fkIsingSquareWedgeFaceKey,
      fkIsingSquareLeftVerticalEdge, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareSideCorner,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareLeftVerticalUpper, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite]
    have hk := k.isLt
    omega⟩

theorem left_boundary_interior_increment_eq
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    fkIsingSquareInteriorRadialIncrement n hn
        (Quot.mk _ (leftInteriorEastDart n hn k)) =
      fkIsingSquareInteriorRadialIncrement n hn
        (Quot.mk _ (leftInteriorSouthDart n hn k)) := by
  let e := fkIsingSquareLeftVerticalEdge n hn k
  have hwestNorth :
      fkIsingSquareWiredPrimitiveIncrement n hn (.dart (e, .west)) =
        fkIsingSquareWiredPrimitiveIncrement n hn (.dart (e, .north)) := by
    let w := fkIsingSquareWiredBoundaryDart n hn (.west k)
    have hw : w = (e, .west) := by
      apply Prod.ext
      · apply Subtype.ext
        change s(fkIsingSquareLeftVerticalLower n hn k,
            fkIsingSquareNeighbor n
              (fkIsingSquareLeftVerticalLower n hn k) .north
              (fkIsingSquareLeftVerticalLower_north_available n hn k)) =
          s(fkIsingSquareLeftVerticalUpper n hn k,
            fkIsingSquareNeighbor n
              (fkIsingSquareLeftVerticalUpper n hn k) .south
              (fkIsingSquareLeftVerticalUpper_south_available n hn k))
        rw [Sym2.eq_iff]
        apply Or.inr
        constructor <;>
          apply Subtype.ext <;>
          funext i <;>
          fin_cases i <;>
          simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
            fkIsingSquareLeftVerticalLower,
            fkIsingSquareLeftVerticalUpper]
      · rfl
    have hnorth : fkIsingSquareWiredBondMate n hn w = (e, .north) := by
      rw [fkIsingSquareWiredBondMate_west]
      rfl
    have hsource : w ≠ fkIsingSquareWiredSourceDart n hn := by
      intro h
      have hi := fkIsingSquareWiredBoundaryDart_injective n hn h
      cases hi
    have hterminal : w ≠ fkIsingSquareWiredTerminalDart n hn := by
      intro h
      have hi := fkIsingSquareWiredBoundaryDart_injective n hn h
      cases hi
    have h := fkIsingSquareWiredPrimitiveIncrement_bondDartMate
      n hn w hsource hterminal
    rw [hnorth, hw] at h
    exact h.symm
  have hclosed :=
    fkIsingSquareWiredPrimitiveIncrement_local_closed n hn e
  change fkIsingSquareWiredPrimitiveIncrement n hn (.dart (e, .east)) =
    fkIsingSquareWiredPrimitiveIncrement n hn (.dart (e, .south))
  linarith

theorem wiredArc_vertex_step
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    vertexPrimitive n hn (fkIsingSquareLeftVerticalLower n hn k) =
      vertexPrimitive n hn (fkIsingSquareLeftVerticalUpper n hn k) := by
  let east : FKIsingSquareInteriorRadialIncidence n hn :=
    Quot.mk _ (leftInteriorEastDart n hn k)
  let south : FKIsingSquareInteriorRadialIncidence n hn :=
    Quot.mk _ (leftInteriorSouthDart n hn k)
  have hface : fkIsingSquareFullFaceOfRadialIncidence n hn east =
      fkIsingSquareFullFaceOfRadialIncidence n hn south := by
    apply fkIsingSquareInteriorCellKey_injective n
    simp only [fkIsingSquareFullFaceOfRadialIncidence_key]
    change fkIsingSquareWedgeFaceKey n
        (fkIsingSquareLeftVerticalEdge n hn k, .east) =
      fkIsingSquareWedgeFaceKey n
        (fkIsingSquareLeftVerticalEdge n hn k, .south)
    simp [fkIsingSquareWedgeFaceKey, fkIsingSquareLeftVerticalEdge,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareLeftVerticalUpper, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite]
  have h := vertex_eq_of_common_face_increment_eq n hn south east hface.symm
    (left_boundary_interior_increment_eq n hn k).symm
  change vertexPrimitive n hn
      (fkIsingSquareDartEndpoint n
        (fkIsingSquareLeftVerticalEdge n hn k, .south)) =
    vertexPrimitive n hn
      (fkIsingSquareDartEndpoint n
        (fkIsingSquareLeftVerticalEdge n hn k, .east)) at h
  simpa [fkIsingSquareLeftVerticalEdge, fkIsingSquareDartEndpoint,
    fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
    fkIsingSquareDirectionEdgeOrientation, fkIsingSquareNeighbor,
    fkIsingSquareNeighborSite, fkIsingSquareLeftVerticalLower,
    fkIsingSquareLeftVerticalUpper] using h

private theorem wiredArc_lower_const
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    vertexPrimitive n hn (fkIsingSquareLeftVerticalLower n hn k) =
      vertexPrimitive n hn
        (fkIsingSquareLeftVerticalLower n hn ⟨0, by omega⟩) := by
  let P : Nat → Prop := fun j ↦ ∀ hj : j < 2 * n,
    vertexPrimitive n hn
        (fkIsingSquareLeftVerticalLower n hn ⟨j, hj⟩) =
      vertexPrimitive n hn
        (fkIsingSquareLeftVerticalLower n hn ⟨0, by omega⟩)
  have hP : ∀ j, P j := by
    intro j
    induction j with
    | zero => intro hj; rfl
    | succ j ih =>
        intro hj
        have hstep := wiredArc_vertex_step n hn ⟨j, by omega⟩
        have heq : fkIsingSquareLeftVerticalUpper n hn ⟨j, by omega⟩ =
            fkIsingSquareLeftVerticalLower n hn ⟨j + 1, hj⟩ := by
          apply Subtype.ext
          funext i
          fin_cases i <;>
            simp [fkIsingSquareLeftVerticalUpper,
              fkIsingSquareLeftVerticalLower] <;> ring
        rw [heq] at hstep
        exact hstep.symm.trans (ih (by omega))
  exact hP k.val k.isLt

private theorem wiredArc_lower_zero
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    vertexPrimitive n hn (fkIsingSquareLeftVerticalLower n hn k) = 0 := by
  let last : Fin (2 * n) := ⟨2 * n - 1, by omega⟩
  have hlast := wiredArc_vertex_step n hn last
  have hupper : fkIsingSquareLeftVerticalUpper n hn last =
      fkIsingSquareMarkedB n := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [last, fkIsingSquareLeftVerticalUpper,
        fkIsingSquareMarkedB] <;> omega
  rw [hupper, markedB_base] at hlast
  calc
    _ = vertexPrimitive n hn
          (fkIsingSquareLeftVerticalLower n hn last) := by
        rw [wiredArc_lower_const n hn k,
          wiredArc_lower_const n hn last]
    _ = 0 := hlast

theorem vertex_fixedBoundary_eq_zero
    (n : Nat) (hn : 0 < n) (x : FKIsingSquareFullVertexNode n)
    (hx : fkIsingSquareFullVertexFixedBoundary n x) :
    vertexPrimitive n hn x = 0 := by
  have hx0 : x.1 0 = -(n : Int) := hx
  have hx1 := fkIsingSquareVertex_coordinate_bounds n x 1
  by_cases htop : x.1 1 = (n : Int)
  · have heq : x = fkIsingSquareMarkedB n := by
      apply Subtype.ext
      funext i
      fin_cases i
      · simpa [fkIsingSquareMarkedB] using hx0
      · simpa [fkIsingSquareMarkedB] using htop
    rw [heq, markedB_base]
  · let j : Nat := (x.1 1 + (n : Int)).toNat
    have hj0 : 0 ≤ x.1 1 + (n : Int) := by omega
    have hj : j < 2 * n := by
      rw [show j = Int.toNat (x.1 1 + (n : Int)) from rfl,
        Int.toNat_lt] <;> omega
    let k : Fin (2 * n) := ⟨j, hj⟩
    have heq : x = fkIsingSquareLeftVerticalLower n hn k := by
      apply Subtype.ext
      funext i
      fin_cases i
      · simpa [k, j, fkIsingSquareLeftVerticalLower] using hx0
      · simp [k, j, fkIsingSquareLeftVerticalLower,
          Int.toNat_of_nonneg hj0]
    rw [heq, wiredArc_lower_zero]

theorem vertex_fixedBoundary_nonneg
    (n : Nat) (hn : 0 < n) (x : FKIsingSquareFullVertexNode n)
    (hx : fkIsingSquareFullVertexFixedBoundary n x) :
    0 ≤ vertexPrimitive n hn x := by
  rw [vertex_fixedBoundary_eq_zero n hn x hx]


def terminalAdjacentIncidence (n : Nat) (hn : 0 < n) :
    FKIsingSquareInteriorRadialIncidence n hn :=
  Quot.mk _ (leftInteriorEastDart n hn ⟨2 * n - 1, by omega⟩)

def terminalAdjacentFace (n : Nat) (hn : 0 < n) :
    FKIsingSquareFullFaceNode n :=
  fkIsingSquareFullFaceOfRadialIncidence n hn
    (terminalAdjacentIncidence n hn)

theorem terminalAdjacentFace_fixedBoundary (n : Nat) (hn : 0 < n) :
    fkIsingSquareFullFaceFixedBoundary n
      (terminalAdjacentFace n hn) := by
  right
  right
  have hkey' : fkIsingSquareInteriorCellKey n
      (terminalAdjacentFace n hn) =
        (-(n : Int), (n : Int) - 1) := by
    rw [show terminalAdjacentFace n hn =
      fkIsingSquareFullFaceOfRadialIncidence n hn
        (terminalAdjacentIncidence n hn) from rfl,
      fkIsingSquareFullFaceOfRadialIncidence_key]
    change fkIsingSquareWedgeFaceKey n
      (fkIsingSquareLeftVerticalEdge n hn
        ⟨2 * n - 1, by omega⟩, .east) = _
    simp [fkIsingSquareWedgeFaceKey, fkIsingSquareLeftVerticalEdge,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareLeftVerticalUpper, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite]
    omega
  have hsecond := congrArg Prod.snd hkey'
  simp [fkIsingSquareInteriorCellKey] at hsecond
  omega

theorem terminalAdjacentFace_le_one (n : Nat) (hn : 0 < n) :
    facePrimitive n hn (terminalAdjacentFace n hn) ≤ 1 := by
  let e := terminalAdjacentIncidence n hn
  have hcompat := face_sub_vertex n hn e
  have hend : fkIsingSquareInteriorRadialEndpoint n hn e =
      fkIsingSquareMarkedB n := by
    change fkIsingSquareDartEndpoint n
        (fkIsingSquareLeftVerticalEdge n hn
          ⟨2 * n - 1, by omega⟩, .east) = _
    unfold fkIsingSquareDartEndpoint
    simp only [fkIsingSquareSideCorner]
    change (fkIsingSquareOrientedEdge n
      (fkIsingSquareLeftVerticalEdge n hn
        ⟨2 * n - 1, by omega⟩)).head = _
    unfold fkIsingSquareLeftVerticalEdge
    rw [fkIsingSquareOrientedEdge_directionEdge]
    change fkIsingSquareLeftVerticalUpper n hn
      ⟨2 * n - 1, by omega⟩ = _
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [fkIsingSquareLeftVerticalUpper,
        fkIsingSquareMarkedB] <;> omega
  rw [hend, markedB_base, sub_zero] at hcompat
  rw [show terminalAdjacentFace n hn =
      fkIsingSquareFullFaceOfRadialIncidence n hn e from rfl,
    hcompat]
  change fkIsingSquareWiredPrimitiveIncrement n hn
    (.dart (leftInteriorEastDart n hn
      ⟨2 * n - 1, by omega⟩).1) ≤ 1
  exact fkIsingSquareWiredPrimitiveIncrement_le_one n hn _

end FKIsingSquareFullIntegratedPrimitive

end

end StatMech.Universality
