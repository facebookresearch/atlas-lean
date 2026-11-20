/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalFullSquareBoundary










namespace StatMech.Universality

open Complex SimpleGraph
open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

private def fullVertexNorthEdge (n : Nat)
    (x : (fkSquareBoxPlanar n).V)
    (h : fkIsingSquareDirectionAvailable n x .north) :=
  fkIsingSquareDirectionEdge n x .north h

private def fullVertexEastEdge (n : Nat)
    (x : (fkSquareBoxPlanar n).V)
    (h : fkIsingSquareDirectionAvailable n x .east) :=
  fkIsingSquareDirectionEdge n x .east h

private def fullVertexSouthEdge (n : Nat)
    (x : (fkSquareBoxPlanar n).V)
    (h : fkIsingSquareDirectionAvailable n x .south) :=
  fkIsingSquareDirectionEdge n x .south h

private def fullVertexWestEdge (n : Nat)
    (x : (fkSquareBoxPlanar n).V)
    (h : fkIsingSquareDirectionAvailable n x .west) :=
  fkIsingSquareDirectionEdge n x .west h

private def northSouthDart (n : Nat) (x : (fkSquareBoxPlanar n).V)
    (hnorth : fkIsingSquareDirectionAvailable n x .north)
    (heast : fkIsingSquareDirectionAvailable n x .east) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(fullVertexNorthEdge n x hnorth, .south), by
    simp [fullVertexNorthEdge, fkIsingSquareWedgeFaceKey,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareSideCorner, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareInteriorFaceKey,
      fkIsingSquareDirectionAvailable] at heast hnorth ⊢
    have hx0 := fkIsingSquareVertex_coordinate_bounds n x 0
    have hx1 := fkIsingSquareVertex_coordinate_bounds n x 1
    omega⟩

private def eastSouthDart (n : Nat) (x : (fkSquareBoxPlanar n).V)
    (heast : fkIsingSquareDirectionAvailable n x .east)
    (hsouth : fkIsingSquareDirectionAvailable n x .south) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(fullVertexEastEdge n x heast, .south), by
    simp [fullVertexEastEdge, fkIsingSquareWedgeFaceKey,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareSideCorner, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareInteriorFaceKey,
      fkIsingSquareDirectionAvailable] at heast hsouth ⊢
    have hx0 := fkIsingSquareVertex_coordinate_bounds n x 0
    have hx1 := fkIsingSquareVertex_coordinate_bounds n x 1
    omega⟩

private def southNorthDart (n : Nat) (x : (fkSquareBoxPlanar n).V)
    (hsouth : fkIsingSquareDirectionAvailable n x .south)
    (hwest : fkIsingSquareDirectionAvailable n x .west) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(fullVertexSouthEdge n x hsouth, .north), by
    simp [fullVertexSouthEdge, fkIsingSquareWedgeFaceKey,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareSideCorner, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareInteriorFaceKey,
      fkIsingSquareDirectionAvailable] at hsouth hwest ⊢
    have hx0 := fkIsingSquareVertex_coordinate_bounds n x 0
    have hx1 := fkIsingSquareVertex_coordinate_bounds n x 1
    omega⟩

private def westNorthDart (n : Nat) (x : (fkSquareBoxPlanar n).V)
    (hwest : fkIsingSquareDirectionAvailable n x .west)
    (hnorth : fkIsingSquareDirectionAvailable n x .north) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(fullVertexWestEdge n x hwest, .north), by
    simp [fullVertexWestEdge, fkIsingSquareWedgeFaceKey,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareSideCorner, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareInteriorFaceKey,
      fkIsingSquareDirectionAvailable] at hwest hnorth ⊢
    have hx0 := fkIsingSquareVertex_coordinate_bounds n x 0
    have hx1 := fkIsingSquareVertex_coordinate_bounds n x 1
    omega⟩

private theorem eastSouth_bondMate (n : Nat) (hn : 0 < n)
    (x : (fkSquareBoxPlanar n).V)
    (heast : fkIsingSquareDirectionAvailable n x .east)
    (hsouth : fkIsingSquareDirectionAvailable n x .south) :
    fkIsingSquareWiredBondMate n hn (eastSouthDart n x heast hsouth).1 =
      (fullVertexSouthEdge n x hsouth, .east) := by
  have hsouth' : -(n : Int) < x.1 1 := hsouth
  rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn _
    (eastSouthDart n x heast hsouth).2]
  apply fkIsingSquareDart_key_injective n
  simp [eastSouthDart, fullVertexEastEdge, fullVertexSouthEdge,
    fkIsingSquareBondMate, fkIsingSquarePreviousDirection,
    fkIsingSquareDirectionAvailable, hsouth', fkIsingSquareDirectionDart,
    fkIsingSquareSideCorner, fkIsingSquareCornerSide,
    fkIsingSquareEndpointForDirection]

private theorem southNorth_bondMate (n : Nat) (hn : 0 < n)
    (x : (fkSquareBoxPlanar n).V)
    (hsouth : fkIsingSquareDirectionAvailable n x .south)
    (hwest : fkIsingSquareDirectionAvailable n x .west) :
    fkIsingSquareWiredBondMate n hn (southNorthDart n x hsouth hwest).1 =
      (fullVertexWestEdge n x hwest, .east) := by
  have hwest' : -(n : Int) < x.1 0 := hwest
  rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn _
    (southNorthDart n x hsouth hwest).2]
  apply fkIsingSquareDart_key_injective n
  simp [southNorthDart, fullVertexSouthEdge, fullVertexWestEdge,
    fkIsingSquareBondMate, fkIsingSquarePreviousDirection,
    fkIsingSquareDirectionAvailable, hwest', fkIsingSquareDirectionDart,
    fkIsingSquareSideCorner, fkIsingSquareCornerSide,
    fkIsingSquareEndpointForDirection]

private theorem westNorth_bondMate (n : Nat) (hn : 0 < n)
    (x : (fkSquareBoxPlanar n).V)
    (hwest : fkIsingSquareDirectionAvailable n x .west)
    (hnorth : fkIsingSquareDirectionAvailable n x .north) :
    fkIsingSquareWiredBondMate n hn (westNorthDart n x hwest hnorth).1 =
      (fullVertexNorthEdge n x hnorth, .west) := by
  have hnorth' : x.1 1 < (n : Int) := hnorth
  rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn _
    (westNorthDart n x hwest hnorth).2]
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
    _ = (fullVertexNorthEdge n x hnorth, .west) := rfl

theorem fkIsingSquareFullVertexFullObservable_quad (n : Nat) (hn : 0 < n)
    (x : (fkSquareBoxPlanar n).V)
    (heast : fkIsingSquareDirectionAvailable n x .east)
    (hnorth : fkIsingSquareDirectionAvailable n x .north)
    (hwest : fkIsingSquareDirectionAvailable n x .west)
    (hsouth : fkIsingSquareDirectionAvailable n x .south) :
    IsingSquareSHolomorphicQuad
      (fkIsingSquareWiredFullMedialObservable n hn
        (fullVertexSouthEdge n x hsouth))
      (fkIsingSquareWiredFullMedialObservable n hn
        (fullVertexWestEdge n x hwest))
      (fkIsingSquareWiredFullMedialObservable n hn
        (fullVertexNorthEdge n x hnorth))
      (fkIsingSquareWiredFullMedialObservable n hn
        (fullVertexEastEdge n x heast)) := by
  let eN := fullVertexNorthEdge n x hnorth
  let eE := fullVertexEastEdge n x heast
  let eS := fullVertexSouthEdge n x hsouth
  let eW := fullVertexWestEdge n x hwest
  have haxisN : (fkIsingSquareOrientedEdge n eN).axis = .vertical := by
    dsimp [eN, fullVertexNorthEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisE : (fkIsingSquareOrientedEdge n eE).axis = .horizontal := by
    dsimp [eE, fullVertexEastEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisS : (fkIsingSquareOrientedEdge n eS).axis = .vertical := by
    dsimp [eS, fullVertexSouthEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisW : (fkIsingSquareOrientedEdge n eW).axis = .horizontal := by
    dsimp [eW, fullVertexWestEdge]
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
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .south)) =
        (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eE, .west)) := by
    let d := northSouthDart n x hnorth heast
    have hmate : fkIsingSquareWiredBondMate n hn d.1 = (eE, .west) := by
      simpa [d, eE] using (show
        fkIsingSquareWiredBondMate n hn (northSouthDart n x hnorth heast).1 =
          (fullVertexEastEdge n x heast, .west) by
            have heast' : x.1 0 < (n : Int) := heast
            rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn _
              (northSouthDart n x hnorth heast).2]
            apply fkIsingSquareDart_key_injective n
            simp [northSouthDart, fullVertexNorthEdge, fullVertexEastEdge,
              fkIsingSquareBondMate, fkIsingSquarePreviousDirection,
              fkIsingSquareDirectionAvailable, heast',
              fkIsingSquareDirectionDart, fkIsingSquareSideCorner,
              fkIsingSquareCornerSide, fkIsingSquareEndpointForDirection])
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
      simp [d, northSouthDart, eN, hcE.1, hcN.2.2.1, Int.ModEq]
    have h :=
      fkIsingSquareInteriorRadial_fermionicObservable_bondMate_eq_of_code_modEq
        n hn d hcode
    change (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareWiredBondMate n hn d.1)) =
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart d.1) at h
    rw [hmate] at h
    simpa [d, northSouthDart, eN] using h.symm
  have hESobs :
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eE, .south)) =
        (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .east)) := by
    let d := eastSouthDart n x heast hsouth
    have hmate : fkIsingSquareWiredBondMate n hn d.1 = (eS, .east) := by
      simpa [d, eS] using eastSouth_bondMate n hn x heast hsouth
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
      simp [d, eastSouthDart, eE, hcE.2.2.1, hcS.2.1, Int.ModEq]
    have h :=
      fkIsingSquareInteriorRadial_fermionicObservable_bondMate_eq_of_code_modEq
        n hn d hcode
    change (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareWiredBondMate n hn d.1)) =
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart d.1) at h
    rw [hmate] at h
    simpa [d, eastSouthDart, eE] using h.symm
  have hSWobs :
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .north)) =
        (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .east)) := by
    let d := southNorthDart n x hsouth hwest
    have hmate : fkIsingSquareWiredBondMate n hn d.1 = (eW, .east) := by
      simpa [d, eW] using southNorth_bondMate n hn x hsouth hwest
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
      simp [d, southNorthDart, eS, hcS.2.2.2, hcW.2.1, Int.ModEq]
    have h :=
      fkIsingSquareInteriorRadial_fermionicObservable_bondMate_eq_of_code_modEq
        n hn d hcode
    change (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareWiredBondMate n hn d.1)) =
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart d.1) at h
    rw [hmate] at h
    simpa [d, southNorthDart, eS] using h.symm
  have hWNobs :
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .north)) =
        (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .west)) := by
    let d := westNorthDart n x hwest hnorth
    have hmate : fkIsingSquareWiredBondMate n hn d.1 = (eN, .west) := by
      simpa [d, eN] using westNorth_bondMate n hn x hwest hnorth
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
      simp [d, westNorthDart, eW, hcW.2.2.2, hcN.1, Int.ModEq]
    have h :=
      fkIsingSquareInteriorRadial_fermionicObservable_bondMate_eq_of_code_modEq
        n hn d hcode
    change (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareWiredBondMate n hn d.1)) =
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.dart d.1) at h
    rw [hmate] at h
    simpa [d, westNorthDart, eW] using h.symm
  let north := fkIsingSquareWiredFullMedialObservable n hn eN
  let east := fkIsingSquareWiredFullMedialObservable n hn eE
  let south := fkIsingSquareWiredFullMedialObservable n hn eS
  let west := fkIsingSquareWiredFullMedialObservable n hn eW
  change IsingSquareSHolomorphicQuad south west north east
  apply isingSquareSHolomorphicQuad_of_projection_cycle north east south west
  · calc
      isingProj 1 north = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eN, .south)))
          north := by rw [hNS]
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .south)) := by
        simpa [north] using
          fkIsingSquareWiredFullMedialObservable_projection n hn eN .south
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eE, .west)) := hNEobs
      _ = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eE, .west)))
          east := by
        symm
        simpa [east] using
          fkIsingSquareWiredFullMedialObservable_projection n hn eE .west
      _ = isingProj 1 east := by rw [hEW]
  · calc
      isingProj Complex.I east = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eE, .south)))
          east := by rw [hES]
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eE, .south)) := by
        simpa [east] using
          fkIsingSquareWiredFullMedialObservable_projection n hn eE .south
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .east)) := hESobs
      _ = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eS, .east)))
          south := by
        symm
        simpa [south] using
          fkIsingSquareWiredFullMedialObservable_projection n hn eS .east
      _ = isingProj Complex.I south := by rw [hSE]
  · calc
      isingProj (-1) south = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eS, .north)))
          south := by rw [hSN]
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .north)) := by
        simpa [south] using
          fkIsingSquareWiredFullMedialObservable_projection n hn eS .north
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .east)) := hSWobs
      _ = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eW, .east)))
          west := by
        symm
        simpa [west] using
          fkIsingSquareWiredFullMedialObservable_projection n hn eW .east
      _ = isingProj (-1) west := by rw [hWE]
  · calc
      isingProj (-Complex.I) west = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eW, .north)))
          west := by rw [hWN]
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .north)) := by
        simpa [west] using
          fkIsingSquareWiredFullMedialObservable_projection n hn eW .north
      _ = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .west)) := hWNobs
      _ = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eN, .west)))
          north := by
        symm
        simpa [north] using
          fkIsingSquareWiredFullMedialObservable_projection n hn eN .west
      _ = isingProj (-Complex.I) north := by rw [hNW]

theorem fkIsingSquareFullVertex_neighborFinset
    (n : Nat) (x : (fkSquareBoxPlanar n).V)
    (heast : fkIsingSquareDirectionAvailable n x .east)
    (hnorth : fkIsingSquareDirectionAvailable n x .north)
    (hwest : fkIsingSquareDirectionAvailable n x .west)
    (hsouth : fkIsingSquareDirectionAvailable n x .south) :
    (fkSquareBoxPlanar n).G.neighborFinset x =
      {fkIsingSquareNeighbor n x .east heast,
        fkIsingSquareNeighbor n x .north hnorth,
        fkIsingSquareNeighbor n x .west hwest,
        fkIsingSquareNeighbor n x .south hsouth} := by
  ext y
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro hxy
    change (hypercubicLattice 2).Adj x.1 y.1 at hxy
    rcases adj_neighbor_cases x.1 y.1 hxy with h | h | h | h
    · right; right; left
      apply Subtype.ext
      funext k
      fin_cases k
      · have hk := congrFun h 0
        simp [Pi.add_apply] at hk
        change y.1 0 = x.1 0 - 1
        omega
      · have hk := congrFun h 1
        simp [Pi.add_apply] at hk
        simpa [fkIsingSquareNeighbor, fkIsingSquareNeighborSite] using hk.symm
    · left
      apply Subtype.ext
      funext k
      fin_cases k
      · have hk := congrFun h 0
        simp [Pi.add_apply] at hk
        change y.1 0 = x.1 0 + 1
        omega
      · have hk := congrFun h 1
        simp [Pi.add_apply] at hk
        simpa [fkIsingSquareNeighbor, fkIsingSquareNeighborSite] using hk.symm
    · right; right; right
      apply Subtype.ext
      funext k
      fin_cases k
      · have hk := congrFun h 0
        simp [Pi.add_apply] at hk
        simpa [fkIsingSquareNeighbor, fkIsingSquareNeighborSite] using hk.symm
      · have hk := congrFun h 1
        simp [Pi.add_apply] at hk
        change y.1 1 = x.1 1 - 1
        omega
    · right; left
      apply Subtype.ext
      funext k
      fin_cases k
      · have hk := congrFun h 0
        simp [Pi.add_apply] at hk
        simpa [fkIsingSquareNeighbor, fkIsingSquareNeighborSite] using hk.symm
      · have hk := congrFun h 1
        simp [Pi.add_apply] at hk
        change y.1 1 = x.1 1 + 1
        omega
  · rintro (rfl | rfl | rfl | rfl)
    · exact fkIsingSquare_adj_neighbor n x .east heast
    · exact fkIsingSquare_adj_neighbor n x .north hnorth
    · exact fkIsingSquare_adj_neighbor n x .west hwest
    · exact fkIsingSquare_adj_neighbor n x .south hsouth

private theorem vertex_difference_of_common_face
    (n : Nat) (hn : 0 < n)
    (e f : FKIsingSquareInteriorRadialIncidence n hn)
    (hface : fkIsingSquareFullFaceOfRadialIncidence n hn e =
      fkIsingSquareFullFaceOfRadialIncidence n hn f) :
    FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn
          (fkIsingSquareInteriorRadialEndpoint n hn f) -
        FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn
          (fkIsingSquareInteriorRadialEndpoint n hn e) =
      fkIsingSquareInteriorRadialIncrement n hn e -
        fkIsingSquareInteriorRadialIncrement n hn f := by
  have he := FKIsingSquareFullIntegratedPrimitive.face_sub_vertex n hn e
  have hf := FKIsingSquareFullIntegratedPrimitive.face_sub_vertex n hn f
  rw [hface] at he
  linarith

private def northCenterDart (n : Nat) (x : (fkSquareBoxPlanar n).V)
    (hnorth : fkIsingSquareDirectionAvailable n x .north)
    (hwest : fkIsingSquareDirectionAvailable n x .west) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(fullVertexNorthEdge n x hnorth, .west), by
    simp [fullVertexNorthEdge, fkIsingSquareWedgeFaceKey,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareSideCorner, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareInteriorFaceKey,
      fkIsingSquareDirectionAvailable] at hnorth hwest ⊢
    have hx0 := fkIsingSquareVertex_coordinate_bounds n x 0
    have hx1 := fkIsingSquareVertex_coordinate_bounds n x 1
    omega⟩

private def northNeighborDart (n : Nat) (x : (fkSquareBoxPlanar n).V)
    (hnorth : fkIsingSquareDirectionAvailable n x .north)
    (hwest : fkIsingSquareDirectionAvailable n x .west) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(fullVertexNorthEdge n x hnorth, .north), by
    rw [show fkIsingSquareWedgeFaceKey n
        (fullVertexNorthEdge n x hnorth, .north) =
      fkIsingSquareWedgeFaceKey n
        (fullVertexNorthEdge n x hnorth, .west) by
      simp [fullVertexNorthEdge, fkIsingSquareWedgeFaceKey,
        fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation,
        fkIsingSquareSideCorner, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite]
      constructor <;> rfl]
    exact (northCenterDart n x hnorth hwest).2⟩

private def eastCenterDart (n : Nat) (x : (fkSquareBoxPlanar n).V)
    (heast : fkIsingSquareDirectionAvailable n x .east)
    (hnorth : fkIsingSquareDirectionAvailable n x .north) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(fullVertexEastEdge n x heast, .west), by
    simp [fullVertexEastEdge, fkIsingSquareWedgeFaceKey,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareSideCorner, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareInteriorFaceKey,
      fkIsingSquareDirectionAvailable] at heast hnorth ⊢
    have hx0 := fkIsingSquareVertex_coordinate_bounds n x 0
    have hx1 := fkIsingSquareVertex_coordinate_bounds n x 1
    omega⟩

private def eastNeighborDart (n : Nat) (x : (fkSquareBoxPlanar n).V)
    (heast : fkIsingSquareDirectionAvailable n x .east)
    (hnorth : fkIsingSquareDirectionAvailable n x .north) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(fullVertexEastEdge n x heast, .north), by
    rw [show fkIsingSquareWedgeFaceKey n
        (fullVertexEastEdge n x heast, .north) =
      fkIsingSquareWedgeFaceKey n
        (fullVertexEastEdge n x heast, .west) by
      simp [fullVertexEastEdge, fkIsingSquareWedgeFaceKey,
        fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation,
        fkIsingSquareSideCorner, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite]
      constructor <;> rfl]
    exact (eastCenterDart n x heast hnorth).2⟩

private def southCenterDart (n : Nat) (x : (fkSquareBoxPlanar n).V)
    (hsouth : fkIsingSquareDirectionAvailable n x .south)
    (heast : fkIsingSquareDirectionAvailable n x .east) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(fullVertexSouthEdge n x hsouth, .east), by
    simp [fullVertexSouthEdge, fkIsingSquareWedgeFaceKey,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareSideCorner, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareInteriorFaceKey,
      fkIsingSquareDirectionAvailable] at hsouth heast ⊢
    have hx0 := fkIsingSquareVertex_coordinate_bounds n x 0
    have hx1 := fkIsingSquareVertex_coordinate_bounds n x 1
    omega⟩

private def southNeighborDart (n : Nat) (x : (fkSquareBoxPlanar n).V)
    (hsouth : fkIsingSquareDirectionAvailable n x .south)
    (heast : fkIsingSquareDirectionAvailable n x .east) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(fullVertexSouthEdge n x hsouth, .south), by
    rw [show fkIsingSquareWedgeFaceKey n
        (fullVertexSouthEdge n x hsouth, .south) =
      fkIsingSquareWedgeFaceKey n
        (fullVertexSouthEdge n x hsouth, .east) by
      simp [fullVertexSouthEdge, fkIsingSquareWedgeFaceKey,
        fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation,
        fkIsingSquareSideCorner, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite]
      constructor <;> rfl]
    exact (southCenterDart n x hsouth heast).2⟩

private def westCenterDart (n : Nat) (x : (fkSquareBoxPlanar n).V)
    (hwest : fkIsingSquareDirectionAvailable n x .west)
    (hsouth : fkIsingSquareDirectionAvailable n x .south) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(fullVertexWestEdge n x hwest, .east), by
    simp [fullVertexWestEdge, fkIsingSquareWedgeFaceKey,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareSideCorner, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareInteriorFaceKey,
      fkIsingSquareDirectionAvailable] at hwest hsouth ⊢
    have hx0 := fkIsingSquareVertex_coordinate_bounds n x 0
    have hx1 := fkIsingSquareVertex_coordinate_bounds n x 1
    omega⟩

private def westNeighborDart (n : Nat) (x : (fkSquareBoxPlanar n).V)
    (hwest : fkIsingSquareDirectionAvailable n x .west)
    (hsouth : fkIsingSquareDirectionAvailable n x .south) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(fullVertexWestEdge n x hwest, .south), by
    rw [show fkIsingSquareWedgeFaceKey n
        (fullVertexWestEdge n x hwest, .south) =
      fkIsingSquareWedgeFaceKey n
        (fullVertexWestEdge n x hwest, .east) by
      simp [fullVertexWestEdge, fkIsingSquareWedgeFaceKey,
        fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation,
        fkIsingSquareSideCorner, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite]
      constructor <;> rfl]
    exact (westCenterDart n x hwest hsouth).2⟩

private theorem vertex_difference_north (n : Nat) (hn : 0 < n)
    (x : (fkSquareBoxPlanar n).V)
    (hnorth : fkIsingSquareDirectionAvailable n x .north)
    (hwest : fkIsingSquareDirectionAvailable n x .west) :
    FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn
          (fkIsingSquareNeighbor n x .north hnorth) -
        FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn x =
      fkIsingSquareWiredPrimitiveIncrement n hn
          (.dart (fullVertexNorthEdge n x hnorth, .west)) -
        fkIsingSquareWiredPrimitiveIncrement n hn
          (.dart (fullVertexNorthEdge n x hnorth, .north)) := by
  let e : FKIsingSquareInteriorRadialIncidence n hn :=
    Quot.mk _ (northCenterDart n x hnorth hwest)
  let f : FKIsingSquareInteriorRadialIncidence n hn :=
    Quot.mk _ (northNeighborDart n x hnorth hwest)
  have hface : fkIsingSquareFullFaceOfRadialIncidence n hn e =
      fkIsingSquareFullFaceOfRadialIncidence n hn f := by
    apply fkIsingSquareInteriorCellKey_injective n
    simp only [fkIsingSquareFullFaceOfRadialIncidence_key]
    change fkIsingSquareWedgeFaceKey n
        (fullVertexNorthEdge n x hnorth, .west) =
      fkIsingSquareWedgeFaceKey n
        (fullVertexNorthEdge n x hnorth, .north)
    symm
    simp [fullVertexNorthEdge, fkIsingSquareWedgeFaceKey,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareSideCorner, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite]
    constructor <;> rfl
  have h := vertex_difference_of_common_face n hn e f hface
  simpa [e, f, northCenterDart, northNeighborDart,
    fullVertexNorthEdge] using h

private theorem vertex_difference_east (n : Nat) (hn : 0 < n)
    (x : (fkSquareBoxPlanar n).V)
    (heast : fkIsingSquareDirectionAvailable n x .east)
    (hnorth : fkIsingSquareDirectionAvailable n x .north) :
    FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn
          (fkIsingSquareNeighbor n x .east heast) -
        FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn x =
      fkIsingSquareWiredPrimitiveIncrement n hn
          (.dart (fullVertexEastEdge n x heast, .west)) -
        fkIsingSquareWiredPrimitiveIncrement n hn
          (.dart (fullVertexEastEdge n x heast, .north)) := by
  let e : FKIsingSquareInteriorRadialIncidence n hn :=
    Quot.mk _ (eastCenterDart n x heast hnorth)
  let f : FKIsingSquareInteriorRadialIncidence n hn :=
    Quot.mk _ (eastNeighborDart n x heast hnorth)
  have hface : fkIsingSquareFullFaceOfRadialIncidence n hn e =
      fkIsingSquareFullFaceOfRadialIncidence n hn f := by
    apply fkIsingSquareInteriorCellKey_injective n
    simp only [fkIsingSquareFullFaceOfRadialIncidence_key]
    change fkIsingSquareWedgeFaceKey n
        (fullVertexEastEdge n x heast, .west) =
      fkIsingSquareWedgeFaceKey n
        (fullVertexEastEdge n x heast, .north)
    symm
    simp [fullVertexEastEdge, fkIsingSquareWedgeFaceKey,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareSideCorner, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite]
    constructor <;> rfl
  have h := vertex_difference_of_common_face n hn e f hface
  simpa [e, f, eastCenterDart, eastNeighborDart,
    fullVertexEastEdge] using h

private theorem vertex_difference_south (n : Nat) (hn : 0 < n)
    (x : (fkSquareBoxPlanar n).V)
    (hsouth : fkIsingSquareDirectionAvailable n x .south)
    (heast : fkIsingSquareDirectionAvailable n x .east) :
    FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn
          (fkIsingSquareNeighbor n x .south hsouth) -
        FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn x =
      fkIsingSquareWiredPrimitiveIncrement n hn
          (.dart (fullVertexSouthEdge n x hsouth, .east)) -
        fkIsingSquareWiredPrimitiveIncrement n hn
          (.dart (fullVertexSouthEdge n x hsouth, .south)) := by
  let e : FKIsingSquareInteriorRadialIncidence n hn :=
    Quot.mk _ (southCenterDart n x hsouth heast)
  let f : FKIsingSquareInteriorRadialIncidence n hn :=
    Quot.mk _ (southNeighborDart n x hsouth heast)
  have hface : fkIsingSquareFullFaceOfRadialIncidence n hn e =
      fkIsingSquareFullFaceOfRadialIncidence n hn f := by
    apply fkIsingSquareInteriorCellKey_injective n
    simp only [fkIsingSquareFullFaceOfRadialIncidence_key]
    change fkIsingSquareWedgeFaceKey n
        (fullVertexSouthEdge n x hsouth, .east) =
      fkIsingSquareWedgeFaceKey n
        (fullVertexSouthEdge n x hsouth, .south)
    symm
    simp [fullVertexSouthEdge, fkIsingSquareWedgeFaceKey,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareSideCorner, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite]
    constructor <;> rfl
  have h := vertex_difference_of_common_face n hn e f hface
  simpa [e, f, southCenterDart, southNeighborDart,
    fullVertexSouthEdge] using h

private theorem vertex_difference_west (n : Nat) (hn : 0 < n)
    (x : (fkSquareBoxPlanar n).V)
    (hwest : fkIsingSquareDirectionAvailable n x .west)
    (hsouth : fkIsingSquareDirectionAvailable n x .south) :
    FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn
          (fkIsingSquareNeighbor n x .west hwest) -
        FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn x =
      fkIsingSquareWiredPrimitiveIncrement n hn
          (.dart (fullVertexWestEdge n x hwest, .east)) -
        fkIsingSquareWiredPrimitiveIncrement n hn
          (.dart (fullVertexWestEdge n x hwest, .south)) := by
  let e : FKIsingSquareInteriorRadialIncidence n hn :=
    Quot.mk _ (westCenterDart n x hwest hsouth)
  let f : FKIsingSquareInteriorRadialIncidence n hn :=
    Quot.mk _ (westNeighborDart n x hwest hsouth)
  have hface : fkIsingSquareFullFaceOfRadialIncidence n hn e =
      fkIsingSquareFullFaceOfRadialIncidence n hn f := by
    apply fkIsingSquareInteriorCellKey_injective n
    simp only [fkIsingSquareFullFaceOfRadialIncidence_key]
    change fkIsingSquareWedgeFaceKey n
        (fullVertexWestEdge n x hwest, .east) =
      fkIsingSquareWedgeFaceKey n
        (fullVertexWestEdge n x hwest, .south)
    symm
    simp [fullVertexWestEdge, fkIsingSquareWedgeFaceKey,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareSideCorner, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite]
    constructor <;> rfl
  have h := vertex_difference_of_common_face n hn e f hface
  have hcenter : fkIsingSquareDartEndpoint n
      (fullVertexWestEdge n x hwest, .east) = x := by
    unfold fkIsingSquareDartEndpoint fullVertexWestEdge
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have hneighbor : fkIsingSquareDartEndpoint n
      (fullVertexWestEdge n x hwest, .south) =
        fkIsingSquareNeighbor n x .west hwest := by
    unfold fkIsingSquareDartEndpoint fullVertexWestEdge
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  change FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn
        (fkIsingSquareDartEndpoint n
          (fullVertexWestEdge n x hwest, .south)) -
      FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn
        (fkIsingSquareDartEndpoint n
          (fullVertexWestEdge n x hwest, .east)) = _ at h
  rw [hcenter, hneighbor] at h
  simpa [e, f, westCenterDart, westNeighborDart,
    fullVertexWestEdge] using h

namespace FKIsingSquareFullIntegratedPrimitive

theorem vertex_laplacian_nonpos_of_interior (n : Nat) (hn : 0 < n)
    (x : (fkSquareBoxPlanar n).V)
    (heast : fkIsingSquareDirectionAvailable n x .east)
    (hnorth : fkIsingSquareDirectionAvailable n x .north)
    (hwest : fkIsingSquareDirectionAvailable n x .west)
    (hsouth : fkIsingSquareDirectionAvailable n x .south) :
    isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
      (FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn) x ≤ 0 := by
  let xE := fkIsingSquareNeighbor n x .east heast
  let xN := fkIsingSquareNeighbor n x .north hnorth
  let xW := fkIsingSquareNeighbor n x .west hwest
  let xS := fkIsingSquareNeighbor n x .south hsouth
  let eN := fullVertexNorthEdge n x hnorth
  let eE := fullVertexEastEdge n x heast
  let eS := fullVertexSouthEdge n x hsouth
  let eW := fullVertexWestEdge n x hwest
  let H := FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn
  let F := fkIsingSquareWiredFullMedialObservable n hn
  have hEN : xE ≠ xN := by
    intro h
    have h0 := congrArg (fun z : (fkSquareBoxPlanar n).V ↦ z.1 0) h
    simp [xE, xN, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h0
  have hEW : xE ≠ xW := by
    intro h
    have h0 := congrArg (fun z : (fkSquareBoxPlanar n).V ↦ z.1 0) h
    simp [xE, xW, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h0
  have hES : xE ≠ xS := by
    intro h
    have h0 := congrArg (fun z : (fkSquareBoxPlanar n).V ↦ z.1 0) h
    simp [xE, xS, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h0
  have hNW : xN ≠ xW := by
    intro h
    have h1 := congrArg (fun z : (fkSquareBoxPlanar n).V ↦ z.1 1) h
    simp [xN, xW, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h1
  have hNS : xN ≠ xS := by
    intro h
    have h1 := congrArg (fun z : (fkSquareBoxPlanar n).V ↦ z.1 1) h
    simp [xN, xS, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h1
  have hWS : xW ≠ xS := by
    intro h
    have h0 := congrArg (fun z : (fkSquareBoxPlanar n).V ↦ z.1 0) h
    simp [xW, xS, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h0
  have hLap : isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G H x =
      (H xE - H x) + (H xN - H x) +
        (H xW - H x) + (H xS - H x) := by
    unfold isingFiniteGraphLaplacian
    rw [fkIsingSquareFullVertex_neighborFinset n x heast hnorth hwest hsouth]
    simp [xE, xN, xW, xS, hEN, hEW, hES, hNW, hNS, hWS]
    ring
  have hdN := vertex_difference_north n hn x hnorth hwest
  have hdE := vertex_difference_east n hn x heast hnorth
  have hdS := vertex_difference_south n hn x hsouth heast
  have hdW := vertex_difference_west n hn x hwest hsouth
  change H xN - H x = _ at hdN
  change H xE - H x = _ at hdE
  change H xS - H x = _ at hdS
  change H xW - H x = _ at hdW
  have haxisN : (fkIsingSquareOrientedEdge n eN).axis = .vertical := by
    dsimp [eN, fullVertexNorthEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisE : (fkIsingSquareOrientedEdge n eE).axis = .horizontal := by
    dsimp [eE, fullVertexEastEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisS : (fkIsingSquareOrientedEdge n eS).axis = .vertical := by
    dsimp [eS, fullVertexSouthEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisW : (fkIsingSquareOrientedEdge n eW).axis = .horizontal := by
    dsimp [eW, fullVertexWestEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn eN haxisN with
    ⟨hNW, _, _, hNN⟩
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn eE haxisE with
    ⟨hEW, _, _, hEN⟩
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn eS haxisS with
    ⟨_, hSE, hSS, _⟩
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn eW haxisW with
    ⟨_, hWE, hWS, _⟩
  have hdiv : isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G H x =
      isingPrimalProjectionDivergence (F eN) (F eE) (F eS) (F eW) := by
    rw [hLap, hdE, hdN, hdW, hdS]
    simp_rw [fkIsingSquareWiredPrimitiveIncrement_eq_normSq_full_projection]
    unfold isingPrimalProjectionDivergence
    rw [hNW, hNN, hEW, hEN, hSE, hSS, hWE, hWS]
    ring
  rw [hdiv, ← isingPrimalPrimitiveLaplacian_eq_projectionDivergence]
  exact isingPrimalPrimitiveLaplacian_nonpos_of_rotated_quad _ _ _ _
    (fkIsingSquareFullVertexFullObservable_quad
      n hn x heast hnorth hwest hsouth)

end FKIsingSquareFullIntegratedPrimitive

end

end StatMech.Universality
