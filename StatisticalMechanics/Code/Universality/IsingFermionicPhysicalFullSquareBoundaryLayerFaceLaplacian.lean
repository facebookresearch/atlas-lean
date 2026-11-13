/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerLaplacian










namespace StatMech.Universality

open Complex SimpleGraph
open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

private theorem natAbs_le_of_bounds {n : Nat} {z : Int}
    (h0 : -(n : Int) ≤ z) (h1 : z ≤ (n : Int)) : z.natAbs ≤ n := by
  have h : |z| ≤ (n : Int) := abs_le.mpr ⟨h0, h1⟩
  rw [Int.abs_eq_natAbs] at h
  exact_mod_cast h

def faceSWVertex (n : Nat) (c : FKIsingSquareFullFaceNode n) :
    FKIsingSquareFullVertexNode n := by
  let p := fkIsingSquareInteriorCellKey n c
  have hp := fkIsingSquareInteriorCellKey_interior n c
  change -(n : Int) ≤ p.1 ∧ p.1 < (n : Int) ∧
    -(n : Int) ≤ p.2 ∧ p.2 < (n : Int) at hp
  refine ⟨![p.1, p.2], ?_⟩
  intro k
  fin_cases k
  · exact natAbs_le_of_bounds hp.1 hp.2.1.le
  · exact natAbs_le_of_bounds hp.2.2.1 hp.2.2.2.le

def faceSEVertex (n : Nat) (c : FKIsingSquareFullFaceNode n) :
    FKIsingSquareFullVertexNode n := by
  let p := fkIsingSquareInteriorCellKey n c
  have hp := fkIsingSquareInteriorCellKey_interior n c
  change -(n : Int) ≤ p.1 ∧ p.1 < (n : Int) ∧
    -(n : Int) ≤ p.2 ∧ p.2 < (n : Int) at hp
  refine ⟨![p.1 + 1, p.2], ?_⟩
  intro k
  fin_cases k
  · change (p.1 + 1).natAbs ≤ n
    exact natAbs_le_of_bounds (by omega) (by omega)
  · exact natAbs_le_of_bounds hp.2.2.1 hp.2.2.2.le

def faceNWVertex (n : Nat) (c : FKIsingSquareFullFaceNode n) :
    FKIsingSquareFullVertexNode n := by
  let p := fkIsingSquareInteriorCellKey n c
  have hp := fkIsingSquareInteriorCellKey_interior n c
  change -(n : Int) ≤ p.1 ∧ p.1 < (n : Int) ∧
    -(n : Int) ≤ p.2 ∧ p.2 < (n : Int) at hp
  refine ⟨![p.1, p.2 + 1], ?_⟩
  intro k
  fin_cases k
  · exact natAbs_le_of_bounds hp.1 hp.2.1.le
  · change (p.2 + 1).natAbs ≤ n
    exact natAbs_le_of_bounds (by omega) (by omega)

def faceNEVertex (n : Nat) (c : FKIsingSquareFullFaceNode n) :
    FKIsingSquareFullVertexNode n := by
  let p := fkIsingSquareInteriorCellKey n c
  have hp := fkIsingSquareInteriorCellKey_interior n c
  change -(n : Int) ≤ p.1 ∧ p.1 < (n : Int) ∧
    -(n : Int) ≤ p.2 ∧ p.2 < (n : Int) at hp
  refine ⟨![p.1 + 1, p.2 + 1], ?_⟩
  intro k
  fin_cases k
  · change (p.1 + 1).natAbs ≤ n
    exact natAbs_le_of_bounds (by omega) (by omega)
  · change (p.2 + 1).natAbs ≤ n
    exact natAbs_le_of_bounds (by omega) (by omega)

private theorem faceSW_east_available (n : Nat)
    (c : FKIsingSquareFullFaceNode n) :
    fkIsingSquareDirectionAvailable n (faceSWVertex n c) .east := by
  have hp := fkIsingSquareInteriorCellKey_interior n c
  change (fkIsingSquareInteriorCellKey n c).1 < (n : Int)
  exact hp.2.1

private theorem faceSW_north_available (n : Nat)
    (c : FKIsingSquareFullFaceNode n) :
    fkIsingSquareDirectionAvailable n (faceSWVertex n c) .north := by
  have hp := fkIsingSquareInteriorCellKey_interior n c
  change (fkIsingSquareInteriorCellKey n c).2 < (n : Int)
  exact hp.2.2.2

private theorem faceSE_north_available (n : Nat)
    (c : FKIsingSquareFullFaceNode n) :
    fkIsingSquareDirectionAvailable n (faceSEVertex n c) .north := by
  have hp := fkIsingSquareInteriorCellKey_interior n c
  change (fkIsingSquareInteriorCellKey n c).2 < (n : Int)
  exact hp.2.2.2

private theorem faceNW_east_available (n : Nat)
    (c : FKIsingSquareFullFaceNode n) :
    fkIsingSquareDirectionAvailable n (faceNWVertex n c) .east := by
  have hp := fkIsingSquareInteriorCellKey_interior n c
  change (fkIsingSquareInteriorCellKey n c).1 < (n : Int)
  exact hp.2.1

private theorem faceNW_south_available (n : Nat)
    (c : FKIsingSquareFullFaceNode n) :
    fkIsingSquareDirectionAvailable n (faceNWVertex n c) .south := by
  have hp := fkIsingSquareInteriorCellKey_interior n c
  simp [fkIsingSquareInteriorFaceKey] at hp
  change -(n : Int) < (fkIsingSquareInteriorCellKey n c).2 + 1
  omega

private theorem faceNE_west_available (n : Nat)
    (c : FKIsingSquareFullFaceNode n) :
    fkIsingSquareDirectionAvailable n (faceNEVertex n c) .west := by
  have hp := fkIsingSquareInteriorCellKey_interior n c
  simp [fkIsingSquareInteriorFaceKey] at hp
  change -(n : Int) < (fkIsingSquareInteriorCellKey n c).1 + 1
  omega

private theorem faceNE_south_available (n : Nat)
    (c : FKIsingSquareFullFaceNode n) :
    fkIsingSquareDirectionAvailable n (faceNEVertex n c) .south := by
  have hp := fkIsingSquareInteriorCellKey_interior n c
  simp [fkIsingSquareInteriorFaceKey] at hp
  change -(n : Int) < (fkIsingSquareInteriorCellKey n c).2 + 1
  omega

private theorem faceSE_west_available (n : Nat)
    (c : FKIsingSquareFullFaceNode n) :
    fkIsingSquareDirectionAvailable n (faceSEVertex n c) .west := by
  have hp := fkIsingSquareInteriorCellKey_interior n c
  simp [fkIsingSquareInteriorFaceKey] at hp
  change -(n : Int) < (fkIsingSquareInteriorCellKey n c).1 + 1
  omega

def faceNorthEdge (n : Nat) (c : FKIsingSquareFullFaceNode n) :=
  fkIsingSquareDirectionEdge n (faceNWVertex n c) .east
    (faceNW_east_available n c)

def faceEastEdge (n : Nat) (c : FKIsingSquareFullFaceNode n) :=
  fkIsingSquareDirectionEdge n (faceSEVertex n c) .north
    (faceSE_north_available n c)

def faceSouthEdge (n : Nat) (c : FKIsingSquareFullFaceNode n) :=
  fkIsingSquareDirectionEdge n (faceSWVertex n c) .east
    (faceSW_east_available n c)

def faceWestEdge (n : Nat) (c : FKIsingSquareFullFaceNode n) :=
  fkIsingSquareDirectionEdge n (faceSWVertex n c) .north
    (faceSW_north_available n c)

theorem faceWestEdge_eq_south (n : Nat)
    (c : FKIsingSquareFullFaceNode n) :
    faceWestEdge n c = fkIsingSquareDirectionEdge n (faceNWVertex n c)
      .south (faceNW_south_available n c) := by
  apply Subtype.ext
  change s(faceSWVertex n c,
      fkIsingSquareNeighbor n (faceSWVertex n c) .north
        (faceSW_north_available n c)) =
    s(faceNWVertex n c,
      fkIsingSquareNeighbor n (faceNWVertex n c) .south
        (faceNW_south_available n c))
  rw [Sym2.eq_iff]
  right
  constructor
  · apply Subtype.ext
    funext k
    fin_cases k <;>
      simp [faceSWVertex, faceNWVertex, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite]
  · apply Subtype.ext
    funext k
    fin_cases k <;>
      simp [faceSWVertex, faceNWVertex, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite]

theorem faceNorthEdge_eq_west (n : Nat)
    (c : FKIsingSquareFullFaceNode n) :
    faceNorthEdge n c = fkIsingSquareDirectionEdge n (faceNEVertex n c)
      .west (faceNE_west_available n c) := by
  apply Subtype.ext
  change s(faceNWVertex n c,
      fkIsingSquareNeighbor n (faceNWVertex n c) .east
        (faceNW_east_available n c)) =
    s(faceNEVertex n c,
      fkIsingSquareNeighbor n (faceNEVertex n c) .west
        (faceNE_west_available n c))
  rw [Sym2.eq_iff]
  right
  constructor
  · apply Subtype.ext
    funext k
    fin_cases k <;>
      simp [faceNWVertex, faceNEVertex, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite]
  · apply Subtype.ext
    funext k
    fin_cases k <;>
      simp [faceNWVertex, faceNEVertex, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite]

theorem faceEastEdge_eq_south (n : Nat)
    (c : FKIsingSquareFullFaceNode n) :
    faceEastEdge n c = fkIsingSquareDirectionEdge n (faceNEVertex n c)
      .south (faceNE_south_available n c) := by
  apply Subtype.ext
  change s(faceSEVertex n c,
      fkIsingSquareNeighbor n (faceSEVertex n c) .north
        (faceSE_north_available n c)) =
    s(faceNEVertex n c,
      fkIsingSquareNeighbor n (faceNEVertex n c) .south
        (faceNE_south_available n c))
  rw [Sym2.eq_iff]
  right
  constructor
  · apply Subtype.ext
    funext k
    fin_cases k <;>
      simp [faceSEVertex, faceNEVertex, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite]
  · apply Subtype.ext
    funext k
    fin_cases k <;>
      simp [faceSEVertex, faceNEVertex, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite]

theorem faceSouthEdge_eq_west (n : Nat)
    (c : FKIsingSquareFullFaceNode n) :
    faceSouthEdge n c = fkIsingSquareDirectionEdge n (faceSEVertex n c)
      .west (faceSE_west_available n c) := by
  apply Subtype.ext
  change s(faceSWVertex n c,
      fkIsingSquareNeighbor n (faceSWVertex n c) .east
        (faceSW_east_available n c)) =
    s(faceSEVertex n c,
      fkIsingSquareNeighbor n (faceSEVertex n c) .west
        (faceSE_west_available n c))
  rw [Sym2.eq_iff]
  right
  constructor
  · apply Subtype.ext
    funext k
    fin_cases k <;>
      simp [faceSWVertex, faceSEVertex, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite]
  · apply Subtype.ext
    funext k
    fin_cases k <;>
      simp [faceSWVertex, faceSEVertex, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite]

def faceSouthWestDart (n : Nat)
    (c : FKIsingSquareFullFaceNode n) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(faceSouthEdge n c, .west), by
    rw [show fkIsingSquareWedgeFaceKey n (faceSouthEdge n c, .west) =
        fkIsingSquareInteriorCellKey n c by
      simp [faceSouthEdge, faceSWVertex, fkIsingSquareWedgeFaceKey,
        fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation,
        fkIsingSquareSideCorner, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite]]
    exact fkIsingSquareInteriorCellKey_interior n c⟩

theorem faceSouthWest_bondMate (n : Nat) (hn : 0 < n)
    (c : FKIsingSquareFullFaceNode n) :
    fkIsingSquareWiredBondMate n hn (faceSouthWestDart n c).1 =
      (faceWestEdge n c, .south) := by
  rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn _
    (faceSouthWestDart n c).2]
  change fkIsingSquareBondMate n hn
    (fkIsingSquareDirectionDart n (faceSWVertex n c) .east
      (faceSW_east_available n c) .counterclockwise) = _
  simp only [fkIsingSquareBondMate,
    fkIsingSquareDirectionDart_endpoint,
    fkIsingSquareDirectionDart_direction,
    fkIsingSquareDirectionDart_turn]
  have hnav : (faceSWVertex n c).1 1 < (n : Int) :=
    faceSW_north_available n c
  have hdir : fkIsingSquareNextDirection n (faceSWVertex n c) .east = .north := by
    simp [fkIsingSquareNextDirection, fkIsingSquareDirectionAvailable,
      hnav]
  calc
    _ = fkIsingSquareDirectionDart n (faceSWVertex n c) .north
        (faceSW_north_available n c) .clockwise :=
      fkIsingSquareDirectionDart_congr n _ hdir _ _ _
    _ = (faceWestEdge n c, .south) := rfl

def faceWestEastDart (n : Nat)
    (c : FKIsingSquareFullFaceNode n) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(faceWestEdge n c, .east), by
    rw [show fkIsingSquareWedgeFaceKey n (faceWestEdge n c, .east) =
        fkIsingSquareInteriorCellKey n c by
      rw [faceWestEdge_eq_south]
      simp [faceNWVertex, fkIsingSquareWedgeFaceKey,
        fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation,
        fkIsingSquareSideCorner, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite]]
    exact fkIsingSquareInteriorCellKey_interior n c⟩

theorem faceWestEast_bondMate (n : Nat) (hn : 0 < n)
    (c : FKIsingSquareFullFaceNode n) :
    fkIsingSquareWiredBondMate n hn (faceWestEastDart n c).1 =
      (faceNorthEdge n c, .south) := by
  rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn _
    (faceWestEastDart n c).2]
  rw [show (faceWestEastDart n c).1 =
      (fkIsingSquareDirectionEdge n (faceNWVertex n c) .south
        (faceNW_south_available n c), .east) by
    apply Prod.ext
    · exact faceWestEdge_eq_south n c
    · rfl]
  change fkIsingSquareBondMate n hn
    (fkIsingSquareDirectionDart n (faceNWVertex n c) .south
      (faceNW_south_available n c) .counterclockwise) = _
  simp only [fkIsingSquareBondMate,
    fkIsingSquareDirectionDart_endpoint,
    fkIsingSquareDirectionDart_direction,
    fkIsingSquareDirectionDart_turn]
  have heast : (faceNWVertex n c).1 0 < (n : Int) :=
    faceNW_east_available n c
  have hdir : fkIsingSquareNextDirection n (faceNWVertex n c) .south = .east := by
    simp [fkIsingSquareNextDirection, fkIsingSquareDirectionAvailable, heast]
  calc
    _ = fkIsingSquareDirectionDart n (faceNWVertex n c) .east
        (faceNW_east_available n c) .clockwise :=
      fkIsingSquareDirectionDart_congr n _ hdir _ _ _
    _ = (faceNorthEdge n c, .south) := rfl

def faceNorthEastDart (n : Nat)
    (c : FKIsingSquareFullFaceNode n) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(faceNorthEdge n c, .east), by
    rw [show fkIsingSquareWedgeFaceKey n (faceNorthEdge n c, .east) =
        fkIsingSquareInteriorCellKey n c by
      rw [faceNorthEdge_eq_west]
      simp [faceNEVertex, fkIsingSquareWedgeFaceKey,
        fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation,
        fkIsingSquareSideCorner, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite]]
    exact fkIsingSquareInteriorCellKey_interior n c⟩

theorem faceNorthEast_bondMate (n : Nat) (hn : 0 < n)
    (c : FKIsingSquareFullFaceNode n) :
    fkIsingSquareWiredBondMate n hn (faceNorthEastDart n c).1 =
      (faceEastEdge n c, .north) := by
  rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn _
    (faceNorthEastDart n c).2]
  rw [show (faceNorthEastDart n c).1 =
      (fkIsingSquareDirectionEdge n (faceNEVertex n c) .west
        (faceNE_west_available n c), .east) by
    apply Prod.ext
    · exact faceNorthEdge_eq_west n c
    · rfl]
  change fkIsingSquareBondMate n hn
    (fkIsingSquareDirectionDart n (faceNEVertex n c) .west
      (faceNE_west_available n c) .counterclockwise) = _
  simp only [fkIsingSquareBondMate,
    fkIsingSquareDirectionDart_endpoint,
    fkIsingSquareDirectionDart_direction,
    fkIsingSquareDirectionDart_turn]
  have hsouth : -(n : Int) < (faceNEVertex n c).1 1 :=
    faceNE_south_available n c
  have hdir : fkIsingSquareNextDirection n (faceNEVertex n c) .west = .south := by
    simp [fkIsingSquareNextDirection, fkIsingSquareDirectionAvailable, hsouth]
  calc
    _ = fkIsingSquareDirectionDart n (faceNEVertex n c) .south
        (faceNE_south_available n c) .clockwise :=
      fkIsingSquareDirectionDart_congr n _ hdir _ _ _
    _ = (fkIsingSquareDirectionEdge n (faceNEVertex n c) .south
          (faceNE_south_available n c), .north) := rfl
    _ = (faceEastEdge n c, .north) := by rw [faceEastEdge_eq_south]

def faceEastWestDart (n : Nat)
    (c : FKIsingSquareFullFaceNode n) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(faceEastEdge n c, .west), by
    rw [show fkIsingSquareWedgeFaceKey n (faceEastEdge n c, .west) =
        fkIsingSquareInteriorCellKey n c by
      simp [faceEastEdge, faceSEVertex, fkIsingSquareWedgeFaceKey,
        fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation,
        fkIsingSquareSideCorner, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite]]
    exact fkIsingSquareInteriorCellKey_interior n c⟩

theorem faceEastWest_bondMate (n : Nat) (hn : 0 < n)
    (c : FKIsingSquareFullFaceNode n) :
    fkIsingSquareWiredBondMate n hn (faceEastWestDart n c).1 =
      (faceSouthEdge n c, .north) := by
  rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn _
    (faceEastWestDart n c).2]
  change fkIsingSquareBondMate n hn
    (fkIsingSquareDirectionDart n (faceSEVertex n c) .north
      (faceSE_north_available n c) .counterclockwise) = _
  simp only [fkIsingSquareBondMate,
    fkIsingSquareDirectionDart_endpoint,
    fkIsingSquareDirectionDart_direction,
    fkIsingSquareDirectionDart_turn]
  have hwest : -(n : Int) < (faceSEVertex n c).1 0 :=
    faceSE_west_available n c
  have hdir : fkIsingSquareNextDirection n (faceSEVertex n c) .north = .west := by
    simp [fkIsingSquareNextDirection, fkIsingSquareDirectionAvailable, hwest]
  calc
    _ = fkIsingSquareDirectionDart n (faceSEVertex n c) .west
        (faceSE_west_available n c) .clockwise :=
      fkIsingSquareDirectionDart_congr n _ hdir _ _ _
    _ = (fkIsingSquareDirectionEdge n (faceSEVertex n c) .west
          (faceSE_west_available n c), .north) := rfl
    _ = (faceSouthEdge n c, .north) := by rw [faceSouthEdge_eq_west]

theorem fkIsingSquareBoundaryFullFaceFullObservable_quad (n : Nat) (hn : 0 < n)
    (c : FKIsingSquareFullFaceNode n)
    (hN : (faceNorthEdge n c).1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n)
    (hE : (faceEastEdge n c).1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n)
    (hS : (faceSouthEdge n c).1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n)
    (hW : (faceWestEdge n c).1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n) :
    IsingSquareSHolomorphicQuad
      (fkIsingSquareBoundaryFullMedialObservable n hn (faceNorthEdge n c))
      (fkIsingSquareBoundaryFullMedialObservable n hn (faceEastEdge n c))
      (fkIsingSquareBoundaryFullMedialObservable n hn (faceSouthEdge n c))
      (fkIsingSquareBoundaryFullMedialObservable n hn (faceWestEdge n c)) := by
  let eN := faceNorthEdge n c
  let eE := faceEastEdge n c
  let eS := faceSouthEdge n c
  let eW := faceWestEdge n c
  have heN : eN.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
    simpa [eN] using hN
  have heE : eE.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
    simpa [eE] using hE
  have heS : eS.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
    simpa [eS] using hS
  have heW : eW.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
    simpa [eW] using hW
  have haxisN : (fkIsingSquareOrientedEdge n eN).axis = .horizontal := by
    dsimp [eN, faceNorthEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisE : (fkIsingSquareOrientedEdge n eE).axis = .vertical := by
    dsimp [eE, faceEastEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisS : (fkIsingSquareOrientedEdge n eS).axis = .horizontal := by
    dsimp [eS, faceSouthEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisW : (fkIsingSquareOrientedEdge n eW).axis = .vertical := by
    dsimp [eW, faceWestEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn eN haxisN with
    ⟨hNW, hNE, hNS, hNN⟩
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn eE haxisE with
    ⟨hEW, hEE, hES, hEN⟩
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn eS haxisS with
    ⟨hSW, hSE, hSS, hSN⟩
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn eW haxisW with
    ⟨hWW, hWE, hWS, hWN⟩
  have hSWobs :
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .west)) =
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .south)) := by
    let d := faceSouthWestDart n c
    have hmate : fkIsingSquareWiredBondMate n hn d.1 = (eW, .south) := by
      simpa [d, eW] using faceSouthWest_bondMate n hn c
    have hcode : fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareInteriorRadialBondMate n hn d)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8] := by
      change fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareWiredBondMate n hn d.1)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8]
      rw [hmate]
      have hcS := fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local
        n hn eS haxisS
      have hcW := fkIsingSquareWiredDirectedTangentCode_bond_vertical_local
        n hn eW haxisW
      simp [d, faceSouthWestDart, eS, hcS.1, hcW.2.2.1, Int.ModEq]
    have h :=
      fkIsingSquareBoundary_fermionicObservable_bondMate_eq_of_code_modEq
        n hn d hcode
    change (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareWiredBondMate n hn d.1)) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart d.1) at h
    rw [hmate] at h
    simpa [d, faceSouthWestDart, eS] using h.symm
  have hWNobs :
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .east)) =
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .south)) := by
    let d := faceWestEastDart n c
    have hmate : fkIsingSquareWiredBondMate n hn d.1 = (eN, .south) := by
      simpa [d, eN] using faceWestEast_bondMate n hn c
    have hcode : fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareInteriorRadialBondMate n hn d)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8] := by
      change fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareWiredBondMate n hn d.1)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8]
      rw [hmate]
      have hcW := fkIsingSquareWiredDirectedTangentCode_bond_vertical_local
        n hn eW haxisW
      have hcN := fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local
        n hn eN haxisN
      simp [d, faceWestEastDart, eW, hcW.2.1, hcN.2.2.1, Int.ModEq]
    have h :=
      fkIsingSquareBoundary_fermionicObservable_bondMate_eq_of_code_modEq
        n hn d hcode
    change (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareWiredBondMate n hn d.1)) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart d.1) at h
    rw [hmate] at h
    simpa [d, faceWestEastDart, eW] using h.symm
  have hNEobs :
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .east)) =
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eE, .north)) := by
    let d := faceNorthEastDart n c
    have hmate : fkIsingSquareWiredBondMate n hn d.1 = (eE, .north) := by
      simpa [d, eE] using faceNorthEast_bondMate n hn c
    have hcode : fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareInteriorRadialBondMate n hn d)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8] := by
      change fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareWiredBondMate n hn d.1)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8]
      rw [hmate]
      have hcN := fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local
        n hn eN haxisN
      have hcE := fkIsingSquareWiredDirectedTangentCode_bond_vertical_local
        n hn eE haxisE
      simp [d, faceNorthEastDart, eN, hcN.2.1, hcE.2.2.2, Int.ModEq]
    have h :=
      fkIsingSquareBoundary_fermionicObservable_bondMate_eq_of_code_modEq
        n hn d hcode
    change (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareWiredBondMate n hn d.1)) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart d.1) at h
    rw [hmate] at h
    simpa [d, faceNorthEastDart, eN] using h.symm
  have hESobs :
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eE, .west)) =
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .north)) := by
    let d := faceEastWestDart n c
    have hmate : fkIsingSquareWiredBondMate n hn d.1 = (eS, .north) := by
      simpa [d, eS] using faceEastWest_bondMate n hn c
    have hcode : fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareInteriorRadialBondMate n hn d)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8] := by
      change fkIsingSquareWiredDirectedTangentCode n hn
          (.bond (fkIsingSquareWiredBondMate n hn d.1)) ≡
        fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8]
      rw [hmate]
      have hcE := fkIsingSquareWiredDirectedTangentCode_bond_vertical_local
        n hn eE haxisE
      have hcS := fkIsingSquareWiredDirectedTangentCode_bond_horizontal_local
        n hn eS haxisS
      simp [d, faceEastWestDart, eE, hcE.1, hcS.2.2.2, Int.ModEq]
    have h :=
      fkIsingSquareBoundary_fermionicObservable_bondMate_eq_of_code_modEq
        n hn d hcode
    change (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquareWiredBondMate n hn d.1)) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart d.1) at h
    rw [hmate] at h
    simpa [d, faceEastWestDart, eE] using h.symm
  let north := fkIsingSquareBoundaryFullMedialObservable n hn eN
  let east := fkIsingSquareBoundaryFullMedialObservable n hn eE
  let south := fkIsingSquareBoundaryFullMedialObservable n hn eS
  let west := fkIsingSquareBoundaryFullMedialObservable n hn eW
  change IsingSquareSHolomorphicQuad north east south west
  apply isingSquareSHolomorphicQuad_of_projection_cycle south west north east
  · calc
      isingProj 1 south = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eS, .west))) south := by
        rw [hSW]
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .west)) := by
        simpa [south] using
          fkIsingSquareBoundaryFullMedialObservable_projection n hn eS heS .west
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .south)) := hSWobs
      _ = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eW, .south))) west := by
        symm
        simpa [west] using
          fkIsingSquareBoundaryFullMedialObservable_projection n hn eW heW .south
      _ = isingProj 1 west := by rw [hWS]
  · calc
      isingProj Complex.I west = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eW, .east))) west := by
        rw [hWE]
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eW, .east)) := by
        simpa [west] using
          fkIsingSquareBoundaryFullMedialObservable_projection n hn eW heW .east
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .south)) := hWNobs
      _ = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eN, .south))) north := by
        symm
        simpa [north] using
          fkIsingSquareBoundaryFullMedialObservable_projection n hn eN heN .south
      _ = isingProj Complex.I north := by rw [hNS]
  · calc
      isingProj (-1) north = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eN, .east))) north := by
        rw [hNE]
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eN, .east)) := by
        simpa [north] using
          fkIsingSquareBoundaryFullMedialObservable_projection n hn eN heN .east
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eE, .north)) := hNEobs
      _ = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eE, .north))) east := by
        symm
        simpa [east] using
          fkIsingSquareBoundaryFullMedialObservable_projection n hn eE heE .north
      _ = isingProj (-1) east := by rw [hEN]
  · calc
      isingProj (-Complex.I) east = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eE, .west))) east := by
        rw [hEW]
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eE, .west)) := by
        simpa [east] using
          fkIsingSquareBoundaryFullMedialObservable_projection n hn eE heE .west
      _ = (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (eS, .north)) := hESobs
      _ = isingProj
          (fkIsingSquareWiredDirectedTangent n hn (.dart (eS, .north))) south := by
        symm
        simpa [south] using
          fkIsingSquareBoundaryFullMedialObservable_projection n hn eS heS .north
      _ = isingProj (-Complex.I) south := by rw [hSN]

def faceNorthNeighbor (n : Nat) (c : FKIsingSquareFullFaceNode n)
    (h : c.2.1 + 1 < 2 * n) : FKIsingSquareFullFaceNode n :=
  (c.1, ⟨c.2.1 + 1, h⟩)

def faceEastNeighbor (n : Nat) (c : FKIsingSquareFullFaceNode n)
    (h : c.1.1 + 1 < 2 * n) : FKIsingSquareFullFaceNode n :=
  (⟨c.1.1 + 1, h⟩, c.2)

def faceSouthNeighbor (n : Nat) (c : FKIsingSquareFullFaceNode n)
    (h : 0 < c.2.1) : FKIsingSquareFullFaceNode n :=
  (c.1, ⟨c.2.1 - 1, by omega⟩)

def faceWestNeighbor (n : Nat) (c : FKIsingSquareFullFaceNode n)
    (h : 0 < c.1.1) : FKIsingSquareFullFaceNode n :=
  (⟨c.1.1 - 1, by omega⟩, c.2)

theorem fkIsingSquareBoundaryFullFace_neighborFinset (n : Nat)
    (c : FKIsingSquareFullFaceNode n)
    (heast : c.1.1 + 1 < 2 * n)
    (hnorth : c.2.1 + 1 < 2 * n)
    (hwest : 0 < c.1.1) (hsouth : 0 < c.2.1)
    [Fintype ↑((fkIsingSquareFullFaceGraph n).neighborSet c)] :
    (fkIsingSquareFullFaceGraph n).neighborFinset c =
      {faceEastNeighbor n c heast, faceNorthNeighbor n c hnorth,
        faceWestNeighbor n c hwest, faceSouthNeighbor n c hsouth} := by
  ext q
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert,
    Finset.mem_singleton]
  change ((c.1 = q.1 ∧ (c.2.1 + 1 = q.2.1 ∨ q.2.1 + 1 = c.2.1)) ∨
      (c.2 = q.2 ∧ (c.1.1 + 1 = q.1.1 ∨ q.1.1 + 1 = c.1.1))) ↔ _
  constructor
  · rintro (⟨hx, hy | hy⟩ | ⟨hy, hx | hx⟩)
    · right; left
      apply Prod.ext
      · exact hx.symm
      · apply Fin.ext
        exact hy.symm
    · right; right; right
      apply Prod.ext
      · exact hx.symm
      · apply Fin.ext
        simp [faceSouthNeighbor]
        omega
    · left
      apply Prod.ext
      · apply Fin.ext
        exact hx.symm
      · exact hy.symm
    · right; right; left
      apply Prod.ext
      · apply Fin.ext
        simp [faceWestNeighbor]
        omega
      · exact hy.symm
  · rintro (rfl | rfl | rfl | rfl)
    · exact Or.inr ⟨rfl, Or.inl rfl⟩
    · exact Or.inl ⟨rfl, Or.inl rfl⟩
    · exact Or.inr ⟨rfl, Or.inr (by simp [faceWestNeighbor]; omega)⟩
    · exact Or.inl ⟨rfl, Or.inr (by simp [faceSouthNeighbor]; omega)⟩

private def faceNorthNeighborDart (n : Nat)
    (c : FKIsingSquareFullFaceNode n) (hnorth : c.2.1 + 1 < 2 * n) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(faceNorthEdge n c, .north), by
    simp [faceNorthEdge, faceNWVertex, fkIsingSquareWedgeFaceKey,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
      fkIsingSquareInteriorFaceKey, fkIsingSquareInteriorCellKey] at hnorth ⊢
    have hx := c.1.isLt
    have hy := c.2.isLt
    omega⟩

private def faceEastNeighborDart (n : Nat)
    (c : FKIsingSquareFullFaceNode n) (heast : c.1.1 + 1 < 2 * n) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(faceEastEdge n c, .south), by
    simp [faceEastEdge, faceSEVertex, fkIsingSquareWedgeFaceKey,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
      fkIsingSquareInteriorFaceKey, fkIsingSquareInteriorCellKey] at heast ⊢
    have hx := c.1.isLt
    have hy := c.2.isLt
    omega⟩

private def faceSouthNeighborDart (n : Nat)
    (c : FKIsingSquareFullFaceNode n) (hsouth : 0 < c.2.1) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(faceSouthEdge n c, .south), by
    simp [faceSouthEdge, faceSWVertex, fkIsingSquareWedgeFaceKey,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
      fkIsingSquareInteriorFaceKey, fkIsingSquareInteriorCellKey] at hsouth ⊢
    have hx := c.1.isLt
    have hy := c.2.isLt
    omega⟩

private def faceWestNeighborDart (n : Nat)
    (c : FKIsingSquareFullFaceNode n) (hwest : 0 < c.1.1) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(faceWestEdge n c, .north), by
    simp [faceWestEdge, faceSWVertex, fkIsingSquareWedgeFaceKey,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
      fkIsingSquareInteriorFaceKey, fkIsingSquareInteriorCellKey] at hwest ⊢
    have hx := c.1.isLt
    have hy := c.2.isLt
    omega⟩

private theorem face_difference_of_common_vertex
    (n : Nat) (hn : 0 < n)
    (e f : FKIsingSquareInteriorRadialIncidence n hn)
    (hendpoint : fkIsingSquareInteriorRadialEndpoint n hn e =
      fkIsingSquareInteriorRadialEndpoint n hn f) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (fkIsingSquareFullFaceOfRadialIncidence n hn f) -
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (fkIsingSquareFullFaceOfRadialIncidence n hn e) =
      fkIsingSquareBoundaryLayerRadialIncrement n hn f -
        fkIsingSquareBoundaryLayerRadialIncrement n hn e := by
  have he := fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex n hn e
  have hf := fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex n hn f
  rw [hendpoint] at he
  linarith

theorem face_difference_north (n : Nat) (hn : 0 < n)
    (c : FKIsingSquareFullFaceNode n) (hnorth : c.2.1 + 1 < 2 * n) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (faceNorthNeighbor n c hnorth) -
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive c =
      fkIsingSquareBoundaryPrimitiveIncrement n hn
          (.dart (faceNorthEdge n c, .north)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn
          (.dart (faceNorthEdge n c, .east)) := by
  let e : FKIsingSquareInteriorRadialIncidence n hn :=
    Quot.mk _ (faceNorthEastDart n c)
  let f : FKIsingSquareInteriorRadialIncidence n hn :=
    Quot.mk _ (faceNorthNeighborDart n c hnorth)
  have hendpoint : fkIsingSquareInteriorRadialEndpoint n hn e =
      fkIsingSquareInteriorRadialEndpoint n hn f := by
    apply Subtype.ext
    funext k
    fin_cases k <;>
      simp [e, f, faceNorthEastDart, faceNorthNeighborDart, faceNorthEdge,
        faceNWVertex, fkIsingSquareDartEndpoint,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite]
  have h := face_difference_of_common_vertex n hn e f hendpoint
  have heface : fkIsingSquareFullFaceOfRadialIncidence n hn e = c := by
    apply fkIsingSquareInteriorCellKey_injective n
    simp only [fkIsingSquareFullFaceOfRadialIncidence_key]
    simp [e, faceNorthEastDart, faceNorthEdge, faceNWVertex,
      fkIsingSquareWedgeFaceKey, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite]
  have hfface : fkIsingSquareFullFaceOfRadialIncidence n hn f =
      faceNorthNeighbor n c hnorth := by
    apply fkIsingSquareInteriorCellKey_injective n
    simp only [fkIsingSquareFullFaceOfRadialIncidence_key]
    simp [f, faceNorthNeighborDart, faceNorthNeighbor, faceNorthEdge,
      faceNWVertex, fkIsingSquareWedgeFaceKey, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
      fkIsingSquareInteriorCellKey]
    ring
  rw [heface, hfface] at h
  simpa [e, f, faceNorthEastDart, faceNorthNeighborDart] using h

theorem face_difference_east (n : Nat) (hn : 0 < n)
    (c : FKIsingSquareFullFaceNode n) (heast : c.1.1 + 1 < 2 * n) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (faceEastNeighbor n c heast) -
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive c =
      fkIsingSquareBoundaryPrimitiveIncrement n hn
          (.dart (faceEastEdge n c, .south)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn
          (.dart (faceEastEdge n c, .west)) := by
  let e : FKIsingSquareInteriorRadialIncidence n hn :=
    Quot.mk _ (faceEastWestDart n c)
  let f : FKIsingSquareInteriorRadialIncidence n hn :=
    Quot.mk _ (faceEastNeighborDart n c heast)
  have hendpoint : fkIsingSquareInteriorRadialEndpoint n hn e =
      fkIsingSquareInteriorRadialEndpoint n hn f := by
    apply Subtype.ext
    funext k
    fin_cases k <;>
      simp [e, f, faceEastWestDart, faceEastNeighborDart, faceEastEdge,
        faceSEVertex, fkIsingSquareDartEndpoint,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite]
  have h := face_difference_of_common_vertex n hn e f hendpoint
  have heface : fkIsingSquareFullFaceOfRadialIncidence n hn e = c := by
    apply fkIsingSquareInteriorCellKey_injective n
    simp only [fkIsingSquareFullFaceOfRadialIncidence_key]
    simp [e, faceEastWestDart, faceEastEdge, faceSEVertex,
      fkIsingSquareWedgeFaceKey, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite]
  have hfface : fkIsingSquareFullFaceOfRadialIncidence n hn f =
      faceEastNeighbor n c heast := by
    apply fkIsingSquareInteriorCellKey_injective n
    simp only [fkIsingSquareFullFaceOfRadialIncidence_key]
    simp [f, faceEastNeighborDart, faceEastNeighbor, faceEastEdge,
      faceSEVertex, fkIsingSquareWedgeFaceKey, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
      fkIsingSquareInteriorCellKey]
    ring
  rw [heface, hfface] at h
  simpa [e, f, faceEastWestDart, faceEastNeighborDart] using h

theorem face_difference_south (n : Nat) (hn : 0 < n)
    (c : FKIsingSquareFullFaceNode n) (hsouth : 0 < c.2.1) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (faceSouthNeighbor n c hsouth) -
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive c =
      fkIsingSquareBoundaryPrimitiveIncrement n hn
          (.dart (faceSouthEdge n c, .south)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn
          (.dart (faceSouthEdge n c, .west)) := by
  let e : FKIsingSquareInteriorRadialIncidence n hn :=
    Quot.mk _ (faceSouthWestDart n c)
  let f : FKIsingSquareInteriorRadialIncidence n hn :=
    Quot.mk _ (faceSouthNeighborDart n c hsouth)
  have hendpoint : fkIsingSquareInteriorRadialEndpoint n hn e =
      fkIsingSquareInteriorRadialEndpoint n hn f := by
    apply Subtype.ext
    funext k
    fin_cases k <;>
      simp [e, f, faceSouthWestDart, faceSouthNeighborDart, faceSouthEdge,
        faceSWVertex, fkIsingSquareDartEndpoint,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite]
  have h := face_difference_of_common_vertex n hn e f hendpoint
  have heface : fkIsingSquareFullFaceOfRadialIncidence n hn e = c := by
    apply fkIsingSquareInteriorCellKey_injective n
    simp only [fkIsingSquareFullFaceOfRadialIncidence_key]
    simp [e, faceSouthWestDart, faceSouthEdge, faceSWVertex,
      fkIsingSquareWedgeFaceKey, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite]
  have hfface : fkIsingSquareFullFaceOfRadialIncidence n hn f =
      faceSouthNeighbor n c hsouth := by
    apply fkIsingSquareInteriorCellKey_injective n
    simp only [fkIsingSquareFullFaceOfRadialIncidence_key]
    simp [f, faceSouthNeighborDart, faceSouthNeighbor, faceSouthEdge,
      faceSWVertex, fkIsingSquareWedgeFaceKey, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
      fkIsingSquareInteriorCellKey]
    have hy := c.2.isLt
    omega
  rw [heface, hfface] at h
  simpa [e, f, faceSouthWestDart, faceSouthNeighborDart] using h

theorem face_difference_west (n : Nat) (hn : 0 < n)
    (c : FKIsingSquareFullFaceNode n) (hwest : 0 < c.1.1) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (faceWestNeighbor n c hwest) -
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive c =
      fkIsingSquareBoundaryPrimitiveIncrement n hn
          (.dart (faceWestEdge n c, .north)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn
          (.dart (faceWestEdge n c, .east)) := by
  let e : FKIsingSquareInteriorRadialIncidence n hn :=
    Quot.mk _ (faceWestEastDart n c)
  let f : FKIsingSquareInteriorRadialIncidence n hn :=
    Quot.mk _ (faceWestNeighborDart n c hwest)
  have hendpoint : fkIsingSquareInteriorRadialEndpoint n hn e =
      fkIsingSquareInteriorRadialEndpoint n hn f := by
    apply Subtype.ext
    funext k
    fin_cases k <;>
      simp [e, f, faceWestEastDart, faceWestNeighborDart, faceWestEdge,
        faceSWVertex, fkIsingSquareDartEndpoint,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite]
  have h := face_difference_of_common_vertex n hn e f hendpoint
  have heface : fkIsingSquareFullFaceOfRadialIncidence n hn e = c := by
    apply fkIsingSquareInteriorCellKey_injective n
    simp only [fkIsingSquareFullFaceOfRadialIncidence_key]
    simp [e, faceWestEastDart, faceWestEdge, faceSWVertex,
      fkIsingSquareWedgeFaceKey, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite]
  have hfface : fkIsingSquareFullFaceOfRadialIncidence n hn f =
      faceWestNeighbor n c hwest := by
    apply fkIsingSquareInteriorCellKey_injective n
    simp only [fkIsingSquareFullFaceOfRadialIncidence_key]
    simp [f, faceWestNeighborDart, faceWestNeighbor, faceWestEdge,
      faceSWVertex, fkIsingSquareWedgeFaceKey, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
      fkIsingSquareInteriorCellKey]
    have hx := c.1.isLt
    omega
  rw [heface, hfface] at h
  simpa [e, f, faceWestEastDart, faceWestNeighborDart] using h

namespace FKIsingSquareBoundaryLayerIntegratedPrimitive

theorem face_laplacian_nonneg_of_interior (n : Nat) (hn : 0 < n)
    (c : FKIsingSquareFullFaceNode n)
    (heast : c.1.1 + 1 < 2 * n)
    (hnorth : c.2.1 + 1 < 2 * n)
    (hwest : 0 < c.1.1) (hsouth : 0 < c.2.1) :
    0 ≤ isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
      ((fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive) c := by
  classical
  let cE := faceEastNeighbor n c heast
  let cN := faceNorthNeighbor n c hnorth
  let cW := faceWestNeighbor n c hwest
  let cS := faceSouthNeighbor n c hsouth
  let eN := faceNorthEdge n c
  let eE := faceEastEdge n c
  let eS := faceSouthEdge n c
  let eW := faceWestEdge n c
  let H := (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
  let F := fkIsingSquareBoundaryFullMedialObservable n hn
  have hSWwest : fkIsingSquareDirectionAvailable n (faceSWVertex n c) .west := by
    change -(n : Int) < (fkIsingSquareInteriorCellKey n c).1
    simp [fkIsingSquareInteriorCellKey] at hwest ⊢
    omega
  have hSWsouth : fkIsingSquareDirectionAvailable n (faceSWVertex n c) .south := by
    change -(n : Int) < (fkIsingSquareInteriorCellKey n c).2
    simp [fkIsingSquareInteriorCellKey] at hsouth ⊢
    omega
  have hNWwest : fkIsingSquareDirectionAvailable n (faceNWVertex n c) .west := by
    change -(n : Int) < (fkIsingSquareInteriorCellKey n c).1
    simp [fkIsingSquareInteriorCellKey] at hwest ⊢
    omega
  have hNWnorth : fkIsingSquareDirectionAvailable n (faceNWVertex n c) .north := by
    change (fkIsingSquareInteriorCellKey n c).2 + 1 < (n : Int)
    simp [fkIsingSquareInteriorCellKey] at hnorth ⊢
    omega
  have hSEeast : fkIsingSquareDirectionAvailable n (faceSEVertex n c) .east := by
    change (fkIsingSquareInteriorCellKey n c).1 + 1 < (n : Int)
    simp [fkIsingSquareInteriorCellKey] at heast ⊢
    omega
  have hSEsouth : fkIsingSquareDirectionAvailable n (faceSEVertex n c) .south := by
    change -(n : Int) < (fkIsingSquareInteriorCellKey n c).2
    simp [fkIsingSquareInteriorCellKey] at hsouth ⊢
    omega
  have heN : eN.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
    simpa [eN, faceNorthEdge] using
      fkIsingSquareDirectionEdge_not_mem_perimeter_of_interior n
        (faceNWVertex n c) .east (faceNW_east_available n c)
        (faceNW_east_available n c) hNWnorth hNWwest
        (faceNW_south_available n c)
  have heE : eE.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
    simpa [eE, faceEastEdge] using
      fkIsingSquareDirectionEdge_not_mem_perimeter_of_interior n
        (faceSEVertex n c) .north (faceSE_north_available n c)
        hSEeast (faceSE_north_available n c) (faceSE_west_available n c)
        hSEsouth
  have heS : eS.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
    simpa [eS, faceSouthEdge] using
      fkIsingSquareDirectionEdge_not_mem_perimeter_of_interior n
        (faceSWVertex n c) .east (faceSW_east_available n c)
        (faceSW_east_available n c) (faceSW_north_available n c) hSWwest
        hSWsouth
  have heW : eW.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
    simpa [eW, faceWestEdge] using
      fkIsingSquareDirectionEdge_not_mem_perimeter_of_interior n
        (faceSWVertex n c) .north (faceSW_north_available n c)
        (faceSW_east_available n c) (faceSW_north_available n c) hSWwest
        hSWsouth
  have hEN : cE ≠ cN := by
    intro h
    have h0 := congrArg (fun z : FKIsingSquareFullFaceNode n ↦ z.1.1) h
    simp [cE, cN, faceEastNeighbor, faceNorthNeighbor] at h0
  have hEW : cE ≠ cW := by
    intro h
    have h0 := congrArg (fun z : FKIsingSquareFullFaceNode n ↦ z.1.1) h
    simp [cE, cW, faceEastNeighbor, faceWestNeighbor] at h0
    omega
  have hES : cE ≠ cS := by
    intro h
    have h0 := congrArg (fun z : FKIsingSquareFullFaceNode n ↦ z.1.1) h
    simp [cE, cS, faceEastNeighbor, faceSouthNeighbor] at h0
  have hNW : cN ≠ cW := by
    intro h
    have h1 := congrArg (fun z : FKIsingSquareFullFaceNode n ↦ z.2.1) h
    simp [cN, cW, faceNorthNeighbor, faceWestNeighbor] at h1
  have hNS : cN ≠ cS := by
    intro h
    have h1 := congrArg (fun z : FKIsingSquareFullFaceNode n ↦ z.2.1) h
    simp [cN, cS, faceNorthNeighbor, faceSouthNeighbor] at h1
    omega
  have hWS : cW ≠ cS := by
    intro h
    have h0 := congrArg (fun z : FKIsingSquareFullFaceNode n ↦ z.1.1) h
    simp [cW, cS, faceWestNeighbor, faceSouthNeighbor] at h0
    omega
  have hLap : isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) H c =
      (H cE - H c) + (H cN - H c) +
        (H cW - H c) + (H cS - H c) := by
    unfold isingFiniteGraphLaplacian
    simp only [fkIsingSquareBoundaryFullFace_neighborFinset n c heast hnorth hwest hsouth]
    change ∑ y ∈ {cE, cN, cW, cS}, (H y - H c) = _
    simp [hEN, hEW, hES, hNW, hNS, hWS]
    ring
  have hdN := face_difference_north n hn c hnorth
  have hdE := face_difference_east n hn c heast
  have hdS := face_difference_south n hn c hsouth
  have hdW := face_difference_west n hn c hwest
  change H cN - H c = _ at hdN
  change H cE - H c = _ at hdE
  change H cS - H c = _ at hdS
  change H cW - H c = _ at hdW
  have haxisN : (fkIsingSquareOrientedEdge n eN).axis = .horizontal := by
    dsimp [eN, faceNorthEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisE : (fkIsingSquareOrientedEdge n eE).axis = .vertical := by
    dsimp [eE, faceEastEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisS : (fkIsingSquareOrientedEdge n eS).axis = .horizontal := by
    dsimp [eS, faceSouthEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisW : (fkIsingSquareOrientedEdge n eW).axis = .vertical := by
    dsimp [eW, faceWestEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn eN haxisN with
    ⟨_, hNE, _, hNN⟩
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn eE haxisE with
    ⟨hEW, _, hES, _⟩
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn eS haxisS with
    ⟨hSW, _, hSS, _⟩
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn eW haxisW with
    ⟨_, hWE, _, hWN⟩
  have hdiv : isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) H c =
      isingPrimalProjectionDivergence (F eN) (F eE) (F eS) (F eW) := by
    rw [hLap, hdE, hdN, hdW, hdS]
    rw [fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
          n hn eE heE .south,
        fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
          n hn eE heE .west,
        fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
          n hn eN heN .north,
        fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
          n hn eN heN .east,
        fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
          n hn eW heW .north,
        fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
          n hn eW heW .east,
        fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
          n hn eS heS .south,
        fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
          n hn eS heS .west]
    unfold isingPrimalProjectionDivergence
    rw [hNE, hNN, hEW, hES, hSW, hSS, hWE, hWN]
    ring
  rw [hdiv, ← isingPrimalPrimitiveLaplacian_eq_projectionDivergence]
  exact isingPrimalPrimitiveLaplacian_nonneg _ _ _ _
    (fkIsingSquareBoundaryFullFaceFullObservable_quad n hn c heN heE heS heW)

end FKIsingSquareBoundaryLayerIntegratedPrimitive

end

end StatMech.Universality
