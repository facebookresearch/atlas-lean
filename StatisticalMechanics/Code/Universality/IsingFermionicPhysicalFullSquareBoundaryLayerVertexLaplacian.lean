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

def fullVertexNorthEdge (n : Nat)
    (x : (fkSquareBoxPlanar n).V)
    (h : fkIsingSquareDirectionAvailable n x .north) :=
  fkIsingSquareDirectionEdge n x .north h

def fullVertexEastEdge (n : Nat)
    (x : (fkSquareBoxPlanar n).V)
    (h : fkIsingSquareDirectionAvailable n x .east) :=
  fkIsingSquareDirectionEdge n x .east h

def fullVertexSouthEdge (n : Nat)
    (x : (fkSquareBoxPlanar n).V)
    (h : fkIsingSquareDirectionAvailable n x .south) :=
  fkIsingSquareDirectionEdge n x .south h

def fullVertexWestEdge (n : Nat)
    (x : (fkSquareBoxPlanar n).V)
    (h : fkIsingSquareDirectionAvailable n x .west) :=
  fkIsingSquareDirectionEdge n x .west h

private theorem vertex_difference_of_common_face
    (n : Nat) (hn : 0 < n)
    (e f : FKIsingSquareInteriorRadialIncidence n hn)
    (hface : fkIsingSquareFullFaceOfRadialIncidence n hn e =
      fkIsingSquareFullFaceOfRadialIncidence n hn f) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
          (fkIsingSquareInteriorRadialEndpoint n hn f) -
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
          (fkIsingSquareInteriorRadialEndpoint n hn e) =
      fkIsingSquareBoundaryLayerRadialIncrement n hn e -
        fkIsingSquareBoundaryLayerRadialIncrement n hn f := by
  have he := fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex n hn e
  have hf := fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex n hn f
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

theorem vertex_difference_north (n : Nat) (hn : 0 < n)
    (x : (fkSquareBoxPlanar n).V)
    (hnorth : fkIsingSquareDirectionAvailable n x .north)
    (hwest : fkIsingSquareDirectionAvailable n x .west) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
          (fkIsingSquareNeighbor n x .north hnorth) -
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x =
      fkIsingSquareBoundaryPrimitiveIncrement n hn
          (.dart (fullVertexNorthEdge n x hnorth, .west)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn
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

theorem vertex_difference_east (n : Nat) (hn : 0 < n)
    (x : (fkSquareBoxPlanar n).V)
    (heast : fkIsingSquareDirectionAvailable n x .east)
    (hnorth : fkIsingSquareDirectionAvailable n x .north) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
          (fkIsingSquareNeighbor n x .east heast) -
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x =
      fkIsingSquareBoundaryPrimitiveIncrement n hn
          (.dart (fullVertexEastEdge n x heast, .west)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn
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

theorem vertex_difference_south (n : Nat) (hn : 0 < n)
    (x : (fkSquareBoxPlanar n).V)
    (hsouth : fkIsingSquareDirectionAvailable n x .south)
    (heast : fkIsingSquareDirectionAvailable n x .east) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
          (fkIsingSquareNeighbor n x .south hsouth) -
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x =
      fkIsingSquareBoundaryPrimitiveIncrement n hn
          (.dart (fullVertexSouthEdge n x hsouth, .east)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn
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

theorem vertex_difference_west (n : Nat) (hn : 0 < n)
    (x : (fkSquareBoxPlanar n).V)
    (hwest : fkIsingSquareDirectionAvailable n x .west)
    (hsouth : fkIsingSquareDirectionAvailable n x .south) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
          (fkIsingSquareNeighbor n x .west hwest) -
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x =
      fkIsingSquareBoundaryPrimitiveIncrement n hn
          (.dart (fullVertexWestEdge n x hwest, .east)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn
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
  change (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
        (fkIsingSquareDartEndpoint n
          (fullVertexWestEdge n x hwest, .south)) -
      (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
        (fkIsingSquareDartEndpoint n
          (fullVertexWestEdge n x hwest, .east)) = _ at h
  rw [hcenter, hneighbor] at h
  simpa [e, f, westCenterDart, westNeighborDart,
    fullVertexWestEdge] using h

namespace FKIsingSquareBoundaryLayerVertexIntegratedPrimitive

theorem vertex_laplacian_nonpos_of_interior (n : Nat) (hn : 0 < n)
    (x : (fkSquareBoxPlanar n).V)
    (heast : fkIsingSquareDirectionAvailable n x .east)
    (hnorth : fkIsingSquareDirectionAvailable n x .north)
    (hwest : fkIsingSquareDirectionAvailable n x .west)
    (hsouth : fkIsingSquareDirectionAvailable n x .south) :
    isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
      ((fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive) x ≤ 0 := by
  let xE := fkIsingSquareNeighbor n x .east heast
  let xN := fkIsingSquareNeighbor n x .north hnorth
  let xW := fkIsingSquareNeighbor n x .west hwest
  let xS := fkIsingSquareNeighbor n x .south hsouth
  let eN := fullVertexNorthEdge n x hnorth
  let eE := fullVertexEastEdge n x heast
  let eS := fullVertexSouthEdge n x hsouth
  let eW := fullVertexWestEdge n x hwest
  let H := (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
  let F := fkIsingSquareBoundaryFullMedialObservable n hn
  have heN : eN.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
    simpa [eN, fullVertexNorthEdge] using
      fkIsingSquareDirectionEdge_not_mem_perimeter_of_interior n x .north hnorth
        heast hnorth hwest hsouth
  have heE : eE.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
    simpa [eE, fullVertexEastEdge] using
      fkIsingSquareDirectionEdge_not_mem_perimeter_of_interior n x .east heast
        heast hnorth hwest hsouth
  have heS : eS.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
    simpa [eS, fullVertexSouthEdge] using
      fkIsingSquareDirectionEdge_not_mem_perimeter_of_interior n x .south hsouth
        heast hnorth hwest hsouth
  have heW : eW.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
    simpa [eW, fullVertexWestEdge] using
      fkIsingSquareDirectionEdge_not_mem_perimeter_of_interior n x .west hwest
        heast hnorth hwest hsouth
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
    rw [fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
          n hn eE heE .west,
        fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
          n hn eE heE .north,
        fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
          n hn eN heN .west,
        fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
          n hn eN heN .north,
        fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
          n hn eW heW .east,
        fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
          n hn eW heW .south,
        fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
          n hn eS heS .east,
        fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
          n hn eS heS .south]
    unfold isingPrimalProjectionDivergence
    rw [hNW, hNN, hEW, hEN, hSE, hSS, hWE, hWS]
    ring
  rw [hdiv, ← isingPrimalPrimitiveLaplacian_eq_projectionDivergence]
  exact isingPrimalPrimitiveLaplacian_nonpos_of_rotated_quad _ _ _ _
    (fkIsingSquareBoundaryFullVertexFullObservable_quad
      n hn x heast hnorth hwest hsouth)

end FKIsingSquareBoundaryLayerVertexIntegratedPrimitive

end

end StatMech.Universality
