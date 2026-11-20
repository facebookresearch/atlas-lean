/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerIntegration

namespace StatMech.Universality

open Complex SimpleGraph
open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

private def boundaryVertexEdge (n : Nat)
    (x : (fkSquareBoxPlanar n).V) (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n x d) :=
  fkIsingSquareDirectionEdge n x d hd

private def boundaryVertexCornerDart (n : Nat)
    (x : (fkSquareBoxPlanar n).V)
    (d : FKIsingSquareDirection) (hd : fkIsingSquareDirectionAvailable n x d)
    (s : FKIsingMedialSide)
    (hs : fkIsingSquareInteriorFaceKey n
      (fkIsingSquareWedgeFaceKey n (boundaryVertexEdge n x d hd, s))) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(boundaryVertexEdge n x d hd, s), hs⟩



theorem fkIsingSquareBoundaryFullVertexFullObservable_quad
    (n : Nat) (hn : 0 < n)
    (x : (fkSquareBoxPlanar n).V)
    (heast : fkIsingSquareDirectionAvailable n x .east)
    (hnorth : fkIsingSquareDirectionAvailable n x .north)
    (hwest : fkIsingSquareDirectionAvailable n x .west)
    (hsouth : fkIsingSquareDirectionAvailable n x .south) :
    IsingSquareSHolomorphicQuad
      (fkIsingSquareBoundaryFullMedialObservable n hn
        (boundaryVertexEdge n x .south hsouth))
      (fkIsingSquareBoundaryFullMedialObservable n hn
        (boundaryVertexEdge n x .west hwest))
      (fkIsingSquareBoundaryFullMedialObservable n hn
        (boundaryVertexEdge n x .north hnorth))
      (fkIsingSquareBoundaryFullMedialObservable n hn
        (boundaryVertexEdge n x .east heast)) := by
  let eN := boundaryVertexEdge n x .north hnorth
  let eE := boundaryVertexEdge n x .east heast
  let eS := boundaryVertexEdge n x .south hsouth
  let eW := boundaryVertexEdge n x .west hwest
  have heN : eN.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
    exact fkIsingSquareDirectionEdge_not_mem_perimeter_of_interior
      n x .north hnorth heast hnorth hwest hsouth
  have heE : eE.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
    exact fkIsingSquareDirectionEdge_not_mem_perimeter_of_interior
      n x .east heast heast hnorth hwest hsouth
  have heS : eS.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
    exact fkIsingSquareDirectionEdge_not_mem_perimeter_of_interior
      n x .south hsouth heast hnorth hwest hsouth
  have heW : eW.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
    exact fkIsingSquareDirectionEdge_not_mem_perimeter_of_interior
      n x .west hwest heast hnorth hwest hsouth
  have haxisN : (fkIsingSquareOrientedEdge n eN).axis = .vertical := by
    dsimp [eN, boundaryVertexEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisE : (fkIsingSquareOrientedEdge n eE).axis = .horizontal := by
    dsimp [eE, boundaryVertexEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisS : (fkIsingSquareOrientedEdge n eS).axis = .vertical := by
    dsimp [eS, boundaryVertexEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisW : (fkIsingSquareOrientedEdge n eW).axis = .horizontal := by
    dsimp [eW, boundaryVertexEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn eN haxisN with
    ⟨hNW, _, hNS, _⟩
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn eE haxisE with
    ⟨hEW, _, hES, _⟩
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn eS haxisS with
    ⟨_, hSE, _, hSN⟩
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn eW haxisW with
    ⟨_, hWE, _, hWN⟩
  have hNEobs :
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .south)) =
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eE, .west)) := by
    have hd : fkIsingSquareInteriorFaceKey n
        (fkIsingSquareWedgeFaceKey n (eN, .south)) := by
      simp [eN, boundaryVertexEdge, fkIsingSquareWedgeFaceKey,
        fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
        fkIsingSquareInteriorFaceKey, fkIsingSquareDirectionAvailable]
        at heast hnorth ⊢
      have hx0 := fkIsingSquareVertex_coordinate_bounds n x 0
      have hx1 := fkIsingSquareVertex_coordinate_bounds n x 1
      omega
    let d := boundaryVertexCornerDart n x .north hnorth .south hd
    have hmate : fkIsingSquareWiredBondMate n hn d.1 = (eE, .west) := by
      have heast' : x.1 0 < (n : Int) := heast
      rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn _ d.2]
      apply fkIsingSquareDart_key_injective n
      simp [d, boundaryVertexCornerDart, eN, eE, boundaryVertexEdge,
        fkIsingSquareBondMate, fkIsingSquarePreviousDirection,
        fkIsingSquareDirectionAvailable, heast', fkIsingSquareDirectionDart,
        fkIsingSquareSideCorner, fkIsingSquareCornerSide,
        fkIsingSquareEndpointForDirection]
    have hcode : fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareInteriorRadialBondMate n hn d)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8] := by
      change fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareWiredBondMate n hn d.1)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8]
      rw [hmate]
      have hcE := fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local
        n hn eE haxisE
      have hcN := fkIsingSquareWiredDirectedTangentCode_bond_vertical_local
        n hn eN haxisN
      change fkIsingSquareWiredDirectedTangentCode n hn (.bond (eE, .west)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond (eN, .south)) [ZMOD 8]
      rw [hcE.1, hcN.2.2.1]
      decide
    have h :=
      fkIsingSquareBoundary_fermionicObservable_bondMate_eq_of_code_modEq
        n hn d hcode
    change (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (fkIsingSquareWiredBondMate n hn d.1)) = _ at h
    rw [hmate] at h
    simpa [d, boundaryVertexCornerDart] using h.symm
  have hESobs :
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eE, .south)) =
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .east)) := by
    have hd : fkIsingSquareInteriorFaceKey n
        (fkIsingSquareWedgeFaceKey n (eE, .south)) := by
      simp [eE, boundaryVertexEdge, fkIsingSquareWedgeFaceKey,
        fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
        fkIsingSquareInteriorFaceKey, fkIsingSquareDirectionAvailable]
        at heast hsouth ⊢
      have hx0 := fkIsingSquareVertex_coordinate_bounds n x 0
      have hx1 := fkIsingSquareVertex_coordinate_bounds n x 1
      omega
    let d := boundaryVertexCornerDart n x .east heast .south hd
    have hmate : fkIsingSquareWiredBondMate n hn d.1 = (eS, .east) := by
      have hsouth' : -(n : Int) < x.1 1 := hsouth
      rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn _ d.2]
      apply fkIsingSquareDart_key_injective n
      simp [d, boundaryVertexCornerDart, eE, eS, boundaryVertexEdge,
        fkIsingSquareBondMate, fkIsingSquarePreviousDirection,
        fkIsingSquareDirectionAvailable, hsouth', fkIsingSquareDirectionDart,
        fkIsingSquareSideCorner, fkIsingSquareCornerSide,
        fkIsingSquareEndpointForDirection]
    have hcode : fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareInteriorRadialBondMate n hn d)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8] := by
      change fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareWiredBondMate n hn d.1)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8]
      rw [hmate]
      have hcE := fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local
        n hn eE haxisE
      have hcS := fkIsingSquareWiredDirectedTangentCode_bond_vertical_local
        n hn eS haxisS
      change fkIsingSquareWiredDirectedTangentCode n hn (.bond (eS, .east)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond (eE, .south)) [ZMOD 8]
      rw [hcS.2.1, hcE.2.2.1]
    have h :=
      fkIsingSquareBoundary_fermionicObservable_bondMate_eq_of_code_modEq
        n hn d hcode
    change (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (fkIsingSquareWiredBondMate n hn d.1)) = _ at h
    rw [hmate] at h
    simpa [d, boundaryVertexCornerDart] using h.symm
  have hSWobs :
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .north)) =
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .east)) := by
    have hd : fkIsingSquareInteriorFaceKey n
        (fkIsingSquareWedgeFaceKey n (eS, .north)) := by
      simp [eS, boundaryVertexEdge, fkIsingSquareWedgeFaceKey,
        fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
        fkIsingSquareInteriorFaceKey, fkIsingSquareDirectionAvailable]
        at hsouth hwest ⊢
      have hx0 := fkIsingSquareVertex_coordinate_bounds n x 0
      have hx1 := fkIsingSquareVertex_coordinate_bounds n x 1
      omega
    let d := boundaryVertexCornerDart n x .south hsouth .north hd
    have hmate : fkIsingSquareWiredBondMate n hn d.1 = (eW, .east) := by
      have hwest' : -(n : Int) < x.1 0 := hwest
      rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn _ d.2]
      apply fkIsingSquareDart_key_injective n
      simp [d, boundaryVertexCornerDart, eS, eW, boundaryVertexEdge,
        fkIsingSquareBondMate, fkIsingSquarePreviousDirection,
        fkIsingSquareDirectionAvailable, hwest', fkIsingSquareDirectionDart,
        fkIsingSquareSideCorner, fkIsingSquareCornerSide,
        fkIsingSquareEndpointForDirection]
    have hcode : fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareInteriorRadialBondMate n hn d)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8] := by
      change fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareWiredBondMate n hn d.1)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8]
      rw [hmate]
      have hcS := fkIsingSquareWiredDirectedTangentCode_bond_vertical_local
        n hn eS haxisS
      have hcW := fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local
        n hn eW haxisW
      change fkIsingSquareWiredDirectedTangentCode n hn (.bond (eW, .east)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond (eS, .north)) [ZMOD 8]
      rw [hcW.2.1, hcS.2.2.2]
      decide
    have h :=
      fkIsingSquareBoundary_fermionicObservable_bondMate_eq_of_code_modEq
        n hn d hcode
    change (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (fkIsingSquareWiredBondMate n hn d.1)) = _ at h
    rw [hmate] at h
    simpa [d, boundaryVertexCornerDart] using h.symm
  have hWNobs :
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .north)) =
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .west)) := by
    have hd : fkIsingSquareInteriorFaceKey n
        (fkIsingSquareWedgeFaceKey n (eW, .north)) := by
      simp [eW, boundaryVertexEdge, fkIsingSquareWedgeFaceKey,
        fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
        fkIsingSquareInteriorFaceKey, fkIsingSquareDirectionAvailable]
        at hwest hnorth ⊢
      have hx0 := fkIsingSquareVertex_coordinate_bounds n x 0
      have hx1 := fkIsingSquareVertex_coordinate_bounds n x 1
      omega
    let d := boundaryVertexCornerDart n x .west hwest .north hd
    have hmate : fkIsingSquareWiredBondMate n hn d.1 = (eN, .west) := by
      have hnorth' : x.1 1 < (n : Int) := hnorth
      rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn _ d.2]
      change fkIsingSquareBondMate n hn
        (fkIsingSquareDirectionDart n x .west hwest .clockwise) = _
      simp only [fkIsingSquareBondMate,
        fkIsingSquareDirectionDart_endpoint,
        fkIsingSquareDirectionDart_direction,
        fkIsingSquareDirectionDart_turn]
      have hdir : fkIsingSquarePreviousDirection n x .west = .north := by
        simp [fkIsingSquarePreviousDirection,
          fkIsingSquareDirectionAvailable, hnorth']
      calc
        _ = fkIsingSquareDirectionDart n x .north hnorth .counterclockwise :=
          fkIsingSquareDirectionDart_congr n x hdir _ _ _
        _ = (eN, .west) := rfl
    have hcode : fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareInteriorRadialBondMate n hn d)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8] := by
      change fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareWiredBondMate n hn d.1)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8]
      rw [hmate]
      have hcW := fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local
        n hn eW haxisW
      have hcN := fkIsingSquareWiredDirectedTangentCode_bond_vertical_local
        n hn eN haxisN
      change fkIsingSquareWiredDirectedTangentCode n hn (.bond (eN, .west)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond (eW, .north)) [ZMOD 8]
      rw [hcN.1, hcW.2.2.2]
      decide
    have h :=
      fkIsingSquareBoundary_fermionicObservable_bondMate_eq_of_code_modEq
        n hn d hcode
    change (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (fkIsingSquareWiredBondMate n hn d.1)) = _ at h
    rw [hmate] at h
    simpa [d, boundaryVertexCornerDart] using h.symm
  let north := fkIsingSquareBoundaryFullMedialObservable n hn eN
  let east := fkIsingSquareBoundaryFullMedialObservable n hn eE
  let south := fkIsingSquareBoundaryFullMedialObservable n hn eS
  let west := fkIsingSquareBoundaryFullMedialObservable n hn eW
  change IsingSquareSHolomorphicQuad south west north east
  apply isingSquareSHolomorphicQuad_of_projection_cycle north east south west
  · calc
      isingProj 1 north = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eN, .south)))
          north := by rw [hNS]
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .south)) := by
        simpa [north] using
          fkIsingSquareBoundaryFullMedialObservable_projection
            n hn eN heN .south
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eE, .west)) := hNEobs
      _ = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eE, .west)))
          east := by
        symm
        simpa [east] using
          fkIsingSquareBoundaryFullMedialObservable_projection
            n hn eE heE .west
      _ = isingProj 1 east := by rw [hEW]
  · calc
      isingProj Complex.I east = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eE, .south)))
          east := by rw [hES]
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eE, .south)) := by
        simpa [east] using
          fkIsingSquareBoundaryFullMedialObservable_projection
            n hn eE heE .south
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .east)) := hESobs
      _ = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eS, .east)))
          south := by
        symm
        simpa [south] using
          fkIsingSquareBoundaryFullMedialObservable_projection
            n hn eS heS .east
      _ = isingProj Complex.I south := by rw [hSE]
  · calc
      isingProj (-1) south = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eS, .north)))
          south := by rw [hSN]
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .north)) := by
        simpa [south] using
          fkIsingSquareBoundaryFullMedialObservable_projection
            n hn eS heS .north
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .east)) := hSWobs
      _ = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eW, .east)))
          west := by
        symm
        simpa [west] using
          fkIsingSquareBoundaryFullMedialObservable_projection
            n hn eW heW .east
      _ = isingProj (-1) west := by rw [hWE]
  · calc
      isingProj (-Complex.I) west = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eW, .north)))
          west := by rw [hWN]
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .north)) := by
        simpa [west] using
          fkIsingSquareBoundaryFullMedialObservable_projection
            n hn eW heW .north
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .west)) := hWNobs
      _ = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eN, .west)))
          north := by
        symm
        simpa [north] using
          fkIsingSquareBoundaryFullMedialObservable_projection
            n hn eN heN .west
      _ = isingProj (-Complex.I) north := by rw [hNW]

end

end StatMech.Universality
