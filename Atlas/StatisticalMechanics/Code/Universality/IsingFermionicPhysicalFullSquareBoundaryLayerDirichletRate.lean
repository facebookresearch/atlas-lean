/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichletResidual
import Code.Universality.IsingFermionicCaratheodoryApproximation
import Code.Universality.IsingFermionicSquareGridConsistency









namespace StatMech.Universality

open Filter Finset Set Topology
open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem isingFiniteWeightedBoundaryError_le
    {V : Type*} [Fintype V] [Nonempty V]
    (boundary : V → Prop) (data target : V → Real) (bound : Real)
    (hbound : 0 ≤ bound)
    (hboundary : ∀ x, boundary x → |data x - target x| ≤ bound) :
    isingFiniteWeightedBoundaryError boundary data target ≤ bound := by
  classical
  unfold isingFiniteWeightedBoundaryError
  rw [Finset.max'_le_iff]
  intro z hz
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hz
  by_cases hx : boundary x
  · simpa [hx] using hboundary x hx
  · simp [hx, hbound]

theorem isingFiniteWeightedTargetResidual_le
    {V : Type*} [Fintype V] [Nonempty V]
    (conductance : V → V → Real) (boundary : V → Prop)
    (target : V → Real) (bound : Real) (hbound : 0 ≤ bound)
    (hresidual : ∀ x, ¬ boundary x →
      |isingFiniteWeightedLaplacian conductance target x| ≤ bound) :
    isingFiniteWeightedTargetResidual conductance boundary target ≤ bound := by
  classical
  unfold isingFiniteWeightedTargetResidual
  rw [Finset.max'_le_iff]
  intro z hz
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hz
  by_cases hx : boundary x
  · simp [hx, hbound]
  · simpa [hx] using hresidual x hx

def vertexSampledImaginaryTarget
    (n : Nat) (embedding : FKIsingSquareFullVertexNode n → Complex)
    (Phi : Complex → Complex) :
    Option (FKIsingSquareFullVertexNode n) → Real
  | none => 1
  | some x => (Phi (embedding x)).im

def faceSampledImaginaryTarget
    (n : Nat) (embedding : FKIsingSquareFullFaceNode n → Complex)
    (Phi : Complex → Complex) :
    Option (FKIsingSquareFullFaceNode n) → Real
  | none => 0
  | some c => (Phi (embedding c)).im




structure FullSquareCoordinateEmbeddingCompatibility
    (N : Nat → Nat)
    (vertexEmbedding : ∀ k,
      FKIsingSquareFullVertexNode (N k) → Complex)
    (faceEmbedding : ∀ k,
      FKIsingSquareFullFaceNode (N k) → Complex)
    (mesh : Nat → Real) where
  coordinateEmbedding : Nat → Int × Int → Complex
  vertex_eq_coordinate : ∀ k x,
    vertexEmbedding k x =
      coordinateEmbedding k (fkIsingSquareFullVertexCoordinate (N k) x)
  face_eq_coordinate : ∀ k c,
    faceEmbedding k c =
      coordinateEmbedding k (fkIsingSquareFullFaceCoordinate (N k) c)
  unitAxial_dist_le_mesh : ∀ k u v,
    (v = (u.1 + 1, u.2) ∨
      v = (u.1, u.2 + 1) ∨
      v = (u.1 - 1, u.2) ∨
      v = (u.1, u.2 - 1)) →
    dist (coordinateEmbedding k v) (coordinateEmbedding k u) ≤ mesh k



def fullSquareScaledCoordinateEmbedding
    (scale : Real) (q : Int × Int) : Complex :=
  scale • fkIsingSquareWiredIntPoint q

def fullSquareScaledVertexEmbedding
    (n : Nat) (scale : Real) :
    FKIsingSquareFullVertexNode n → Complex := fun x ↦
  fullSquareScaledCoordinateEmbedding scale
    (fkIsingSquareFullVertexCoordinate n x)

def fullSquareScaledFaceEmbedding
    (n : Nat) (scale : Real) :
    FKIsingSquareFullFaceNode n → Complex := fun c ↦
  fullSquareScaledCoordinateEmbedding scale
    (fkIsingSquareFullFaceCoordinate n c)

theorem fullSquareScaledVertexEmbedding_east
    (n : Nat) (scale : Real) (x : FKIsingSquareFullVertexNode n)
    (h : fkIsingSquareDirectionAvailable n x .east) :
    fullSquareScaledVertexEmbedding n scale
        (fkIsingSquareNeighbor n x .east h) =
      fullSquareScaledVertexEmbedding n scale x +
        (scale : Complex) * (1 + Complex.I) := by
  apply Complex.ext <;>
    simp [fullSquareScaledVertexEmbedding,
      fullSquareScaledCoordinateEmbedding, fkIsingSquareWiredIntPoint,
      fkIsingSquareFullVertexCoordinate, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, Matrix.vecHead, Matrix.vecTail] <;>
    ring

theorem fullSquareScaledVertexEmbedding_north
    (n : Nat) (scale : Real) (x : FKIsingSquareFullVertexNode n)
    (h : fkIsingSquareDirectionAvailable n x .north) :
    fullSquareScaledVertexEmbedding n scale
        (fkIsingSquareNeighbor n x .north h) =
      fullSquareScaledVertexEmbedding n scale x +
        (scale : Complex) * (1 - Complex.I) := by
  apply Complex.ext <;>
    simp [fullSquareScaledVertexEmbedding,
      fullSquareScaledCoordinateEmbedding, fkIsingSquareWiredIntPoint,
      fkIsingSquareFullVertexCoordinate, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, Matrix.vecHead, Matrix.vecTail] <;>
    ring

theorem fullSquareScaledVertexEmbedding_west
    (n : Nat) (scale : Real) (x : FKIsingSquareFullVertexNode n)
    (h : fkIsingSquareDirectionAvailable n x .west) :
    fullSquareScaledVertexEmbedding n scale
        (fkIsingSquareNeighbor n x .west h) =
      fullSquareScaledVertexEmbedding n scale x -
        (scale : Complex) * (1 + Complex.I) := by
  apply Complex.ext <;>
    simp [fullSquareScaledVertexEmbedding,
      fullSquareScaledCoordinateEmbedding, fkIsingSquareWiredIntPoint,
      fkIsingSquareFullVertexCoordinate, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, Matrix.vecHead, Matrix.vecTail] <;>
    ring

theorem fullSquareScaledVertexEmbedding_south
    (n : Nat) (scale : Real) (x : FKIsingSquareFullVertexNode n)
    (h : fkIsingSquareDirectionAvailable n x .south) :
    fullSquareScaledVertexEmbedding n scale
        (fkIsingSquareNeighbor n x .south h) =
      fullSquareScaledVertexEmbedding n scale x -
        (scale : Complex) * (1 - Complex.I) := by
  apply Complex.ext <;>
    simp [fullSquareScaledVertexEmbedding,
      fullSquareScaledCoordinateEmbedding, fkIsingSquareWiredIntPoint,
      fkIsingSquareFullVertexCoordinate, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, Matrix.vecHead, Matrix.vecTail] <;>
    ring

theorem fullSquareScaledFaceEmbedding_east
    (n : Nat) (scale : Real) (c : FKIsingSquareFullFaceNode n)
    (h : c.1.1 + 1 < 2 * n) :
    fullSquareScaledFaceEmbedding n scale (faceEastNeighbor n c h) =
      fullSquareScaledFaceEmbedding n scale c +
        (scale : Complex) * (1 + Complex.I) := by
  apply Complex.ext <;>
    simp [fullSquareScaledFaceEmbedding,
      fullSquareScaledCoordinateEmbedding, fkIsingSquareWiredIntPoint,
      fkIsingSquareFullFaceCoordinate, fkIsingSquareInteriorCellKey,
      faceEastNeighbor] <;>
    ring

theorem fullSquareScaledFaceEmbedding_north
    (n : Nat) (scale : Real) (c : FKIsingSquareFullFaceNode n)
    (h : c.2.1 + 1 < 2 * n) :
    fullSquareScaledFaceEmbedding n scale (faceNorthNeighbor n c h) =
      fullSquareScaledFaceEmbedding n scale c +
        (scale : Complex) * (1 - Complex.I) := by
  apply Complex.ext <;>
    simp [fullSquareScaledFaceEmbedding,
      fullSquareScaledCoordinateEmbedding, fkIsingSquareWiredIntPoint,
      fkIsingSquareFullFaceCoordinate, fkIsingSquareInteriorCellKey,
      faceNorthNeighbor] <;>
    ring

theorem fullSquareScaledFaceEmbedding_west
    (n : Nat) (scale : Real) (c : FKIsingSquareFullFaceNode n)
    (h : 0 < c.1.1) :
    fullSquareScaledFaceEmbedding n scale (faceWestNeighbor n c h) =
      fullSquareScaledFaceEmbedding n scale c -
        (scale : Complex) * (1 + Complex.I) := by
  have hc : 1 ≤ c.1.1 := h
  apply Complex.ext <;>
    simp [fullSquareScaledFaceEmbedding,
      fullSquareScaledCoordinateEmbedding, fkIsingSquareWiredIntPoint,
      fkIsingSquareFullFaceCoordinate, fkIsingSquareInteriorCellKey,
      faceWestNeighbor, Nat.cast_sub hc] <;>
    ring

theorem fullSquareScaledFaceEmbedding_south
    (n : Nat) (scale : Real) (c : FKIsingSquareFullFaceNode n)
    (h : 0 < c.2.1) :
    fullSquareScaledFaceEmbedding n scale (faceSouthNeighbor n c h) =
      fullSquareScaledFaceEmbedding n scale c -
        (scale : Complex) * (1 - Complex.I) := by
  have hc : 1 ≤ c.2.1 := h
  apply Complex.ext <;>
    simp [fullSquareScaledFaceEmbedding,
      fullSquareScaledCoordinateEmbedding, fkIsingSquareWiredIntPoint,
      fkIsingSquareFullFaceCoordinate, fkIsingSquareInteriorCellKey,
      faceSouthNeighbor, Nat.cast_sub hc] <;>
    ring

theorem fullSquareScaledVertex_sampledLaplacian_eq_stencil
    (n : Nat) (scale : Real) (f : Complex → Real)
    (x : FKIsingSquareFullVertexNode n)
    (heast : fkIsingSquareDirectionAvailable n x .east)
    (hnorth : fkIsingSquareDirectionAvailable n x .north)
    (hwest : fkIsingSquareDirectionAvailable n x .west)
    (hsouth : fkIsingSquareDirectionAvailable n x .south) :
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fun y ↦ f (fullSquareScaledVertexEmbedding n scale y)) x =
      complexDirectionalFourNeighborStencil f
        (fullSquareScaledVertexEmbedding n scale x)
        (1 + Complex.I) (1 - Complex.I) scale := by
  let xE := fkIsingSquareNeighbor n x .east heast
  let xN := fkIsingSquareNeighbor n x .north hnorth
  let xW := fkIsingSquareNeighbor n x .west hwest
  let xS := fkIsingSquareNeighbor n x .south hsouth
  have hEN : xE ≠ xN := by
    intro h
    have h0 := congrArg (fun z : FKIsingSquareFullVertexNode n ↦ z.1 0) h
    simp [xE, xN, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h0
  have hEW : xE ≠ xW := by
    intro h
    have h0 := congrArg (fun z : FKIsingSquareFullVertexNode n ↦ z.1 0) h
    simp [xE, xW, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h0
  have hES : xE ≠ xS := by
    intro h
    have h0 := congrArg (fun z : FKIsingSquareFullVertexNode n ↦ z.1 0) h
    simp [xE, xS, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h0
  have hNW : xN ≠ xW := by
    intro h
    have h1 := congrArg (fun z : FKIsingSquareFullVertexNode n ↦ z.1 1) h
    simp [xN, xW, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h1
  have hNS : xN ≠ xS := by
    intro h
    have h1 := congrArg (fun z : FKIsingSquareFullVertexNode n ↦ z.1 1) h
    simp [xN, xS, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h1
  have hWS : xW ≠ xS := by
    intro h
    have h0 := congrArg (fun z : FKIsingSquareFullVertexNode n ↦ z.1 0) h
    simp [xW, xS, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h0
  unfold isingFiniteGraphLaplacian fkIsingSquareFullVertexGraph
  rw [fkIsingSquareFullVertex_neighborFinset n x heast hnorth hwest hsouth]
  simp [xE, xN, xW, xS, hEN, hEW, hES, hNW, hNS, hWS]
  unfold complexDirectionalFourNeighborStencil
  rw [fullSquareScaledVertexEmbedding_east,
    fullSquareScaledVertexEmbedding_north,
    fullSquareScaledVertexEmbedding_west,
    fullSquareScaledVertexEmbedding_south]
  ring

theorem fullSquareScaledFace_sampledLaplacian_eq_stencil
    (n : Nat) (scale : Real) (f : Complex → Real)
    (c : FKIsingSquareFullFaceNode n)
    (heast : c.1.1 + 1 < 2 * n)
    (hnorth : c.2.1 + 1 < 2 * n)
    (hwest : 0 < c.1.1) (hsouth : 0 < c.2.1) :
    isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
        (fun d ↦ f (fullSquareScaledFaceEmbedding n scale d)) c =
      complexDirectionalFourNeighborStencil f
        (fullSquareScaledFaceEmbedding n scale c)
        (1 + Complex.I) (1 - Complex.I) scale := by
  classical
  let cE := faceEastNeighbor n c heast
  let cN := faceNorthNeighbor n c hnorth
  let cW := faceWestNeighbor n c hwest
  let cS := faceSouthNeighbor n c hsouth
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
  unfold isingFiniteGraphLaplacian
  rw [fkIsingSquareBoundaryFullFace_neighborFinset
    n c heast hnorth hwest hsouth]
  change ∑ d ∈ {cE, cN, cW, cS},
    (f (fullSquareScaledFaceEmbedding n scale d) -
      f (fullSquareScaledFaceEmbedding n scale c)) = _
  simp [hEN, hEW, hES, hNW, hNS, hWS]
  unfold complexDirectionalFourNeighborStencil
  rw [fullSquareScaledFaceEmbedding_east,
    fullSquareScaledFaceEmbedding_north,
    fullSquareScaledFaceEmbedding_west,
    fullSquareScaledFaceEmbedding_south]
  ring

theorem fullSquareScaledVertex_sampledLaplacian_le_fourthOrder
    (n : Nat) (scale : Real) (f : Complex → Real)
    (x : FKIsingSquareFullVertexNode n)
    (heast : fkIsingSquareDirectionAvailable n x .east)
    (hnorth : fkIsingSquareDirectionAvailable n x .north)
    (hwest : fkIsingSquareDirectionAvailable n x .west)
    (hsouth : fkIsingSquareDirectionAvailable n x .south)
    (M₁ M₂ : Real)
    (hg₁ : ContDiff Real 4 (fun t : Real ↦ f
      (fullSquareScaledVertexEmbedding n scale x +
        (t : Complex) * (1 + Complex.I))))
    (hg₂ : ContDiff Real 4 (fun t : Real ↦ f
      (fullSquareScaledVertexEmbedding n scale x +
        (t : Complex) * (1 - Complex.I))))
    (hfourth₁ : ∀ t, |iteratedDeriv 4 (fun s : Real ↦ f
      (fullSquareScaledVertexEmbedding n scale x +
        (s : Complex) * (1 + Complex.I))) t| ≤ M₁)
    (hfourth₂ : ∀ t, |iteratedDeriv 4 (fun s : Real ↦ f
      (fullSquareScaledVertexEmbedding n scale x +
        (s : Complex) * (1 - Complex.I))) t| ≤ M₂)
    (hharmonic : iteratedDeriv 2 (fun t : Real ↦ f
        (fullSquareScaledVertexEmbedding n scale x +
          (t : Complex) * (1 + Complex.I))) 0 +
      iteratedDeriv 2 (fun t : Real ↦ f
        (fullSquareScaledVertexEmbedding n scale x +
          (t : Complex) * (1 - Complex.I))) 0 = 0) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
      (fun y ↦ f (fullSquareScaledVertexEmbedding n scale y)) x| ≤
        (M₁ + M₂) * |scale| ^ 4 / 12 := by
  rw [fullSquareScaledVertex_sampledLaplacian_eq_stencil
    n scale f x heast hnorth hwest hsouth]
  exact complexDirectionalFourNeighborStencil_le f
    (fullSquareScaledVertexEmbedding n scale x)
    (1 + Complex.I) (1 - Complex.I) scale M₁ M₂
    hg₁ hg₂ hfourth₁ hfourth₂ hharmonic

theorem fullSquareScaledFace_sampledLaplacian_le_fourthOrder
    (n : Nat) (scale : Real) (f : Complex → Real)
    (c : FKIsingSquareFullFaceNode n)
    (heast : c.1.1 + 1 < 2 * n)
    (hnorth : c.2.1 + 1 < 2 * n)
    (hwest : 0 < c.1.1) (hsouth : 0 < c.2.1)
    (M₁ M₂ : Real)
    (hg₁ : ContDiff Real 4 (fun t : Real ↦ f
      (fullSquareScaledFaceEmbedding n scale c +
        (t : Complex) * (1 + Complex.I))))
    (hg₂ : ContDiff Real 4 (fun t : Real ↦ f
      (fullSquareScaledFaceEmbedding n scale c +
        (t : Complex) * (1 - Complex.I))))
    (hfourth₁ : ∀ t, |iteratedDeriv 4 (fun s : Real ↦ f
      (fullSquareScaledFaceEmbedding n scale c +
        (s : Complex) * (1 + Complex.I))) t| ≤ M₁)
    (hfourth₂ : ∀ t, |iteratedDeriv 4 (fun s : Real ↦ f
      (fullSquareScaledFaceEmbedding n scale c +
        (s : Complex) * (1 - Complex.I))) t| ≤ M₂)
    (hharmonic : iteratedDeriv 2 (fun t : Real ↦ f
        (fullSquareScaledFaceEmbedding n scale c +
          (t : Complex) * (1 + Complex.I))) 0 +
      iteratedDeriv 2 (fun t : Real ↦ f
        (fullSquareScaledFaceEmbedding n scale c +
          (t : Complex) * (1 - Complex.I))) 0 = 0) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
      (fun d ↦ f (fullSquareScaledFaceEmbedding n scale d)) c| ≤
        (M₁ + M₂) * |scale| ^ 4 / 12 := by
  rw [fullSquareScaledFace_sampledLaplacian_eq_stencil
    n scale f c heast hnorth hwest hsouth]
  exact complexDirectionalFourNeighborStencil_le f
    (fullSquareScaledFaceEmbedding n scale c)
    (1 + Complex.I) (1 - Complex.I) scale M₁ M₂
    hg₁ hg₂ hfourth₁ hfourth₂ hharmonic

theorem fullSquareScaledCoordinateEmbedding_unitAxial_dist
    (scale : Real) (hscale : 0 ≤ scale) (u v : Int × Int)
    (hunit : v = (u.1 + 1, u.2) ∨
      v = (u.1, u.2 + 1) ∨
      v = (u.1 - 1, u.2) ∨
      v = (u.1, u.2 - 1)) :
    dist (fullSquareScaledCoordinateEmbedding scale v)
      (fullSquareScaledCoordinateEmbedding scale u) ≤ scale := by
  rcases hunit with rfl | rfl | rfl | rfl <;>
    simp only [fullSquareScaledCoordinateEmbedding] <;>
    rw [dist_smul₀] <;>
    simp [fkIsingSquareWiredIntPoint, Complex.dist_eq_re_im,
      abs_of_nonneg hscale]



theorem FullSquareCoordinateEmbeddingCompatibility.incidenceDistance
    {N : Nat → Nat} {hN : ∀ k, 0 < N k}
    {vertexEmbedding : ∀ k,
      FKIsingSquareFullVertexNode (N k) → Complex}
    {faceEmbedding : ∀ k,
      FKIsingSquareFullFaceNode (N k) → Complex}
    {mesh : Nat → Real}
    (C : FullSquareCoordinateEmbeddingCompatibility
      N vertexEmbedding faceEmbedding mesh) (k : Nat)
    (e : FKIsingSquareInteriorRadialIncidence (N k) (hN k)) :
    dist
        (faceEmbedding k
          (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e))
        (vertexEmbedding k
          (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e)) ≤ mesh k := by
  rw [C.face_eq_coordinate, C.vertex_eq_coordinate]
  exact C.unitAxial_dist_le_mesh k _ _
    (fkIsingSquareFull_radiallyAdjacent_of_incidence (N k) (hN k) e)



def fullSquareScaledEmbeddingCompatibility
    (N : Nat → Nat) (mesh : Nat → Real)
    (hmesh : ∀ k, 0 ≤ mesh k) :
    FullSquareCoordinateEmbeddingCompatibility N
      (fun k ↦ fullSquareScaledVertexEmbedding (N k) (mesh k))
      (fun k ↦ fullSquareScaledFaceEmbedding (N k) (mesh k)) mesh where
  coordinateEmbedding k := fullSquareScaledCoordinateEmbedding (mesh k)
  vertex_eq_coordinate _ _ := rfl
  face_eq_coordinate _ _ := rfl
  unitAxial_dist_le_mesh k u v hunit :=
    fullSquareScaledCoordinateEmbedding_unitAxial_dist
      (mesh k) (hmesh k) u v hunit

theorem fullSquareScaledEmbedding_incidenceDistance
    (N : Nat → Nat) (hN : ∀ k, 0 < N k)
    (mesh : Nat → Real) (hmesh : ∀ k, 0 ≤ mesh k)
    (k : Nat)
    (e : FKIsingSquareInteriorRadialIncidence (N k) (hN k)) :
    dist
        (fullSquareScaledFaceEmbedding (N k) (mesh k)
          (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e))
        (fullSquareScaledVertexEmbedding (N k) (mesh k)
          (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e)) ≤ mesh k :=
  (fullSquareScaledEmbeddingCompatibility N mesh hmesh).incidenceDistance
    (hN := hN) k e

theorem vertexSampled_boundaryConsistencyError_le
    (n : Nat) (hn : 0 < n)
    (embedding : FKIsingSquareFullVertexNode n → Complex)
    (Phi : Complex → Complex) (bound : Real) (hbound : 0 ≤ bound)
    (hfixed : ∀ x, fkIsingSquareFullVertexFixedBoundary n x →
      |0 - (Phi (embedding x)).im| ≤ bound) :
    vertexBoundaryConsistencyError n hn
      (vertexSampledImaginaryTarget n embedding Phi) ≤ bound := by
  apply isingFiniteWeightedBoundaryError_le
    (vertexDirichletBoundary n) (vertexGhostPrimitive n hn)
    (vertexSampledImaginaryTarget n embedding Phi) bound hbound
  intro x hx
  cases x with
  | none => simpa [vertexGhostPrimitive, vertexSampledImaginaryTarget,
      isingFiniteGhostExtension] using hbound
  | some x =>
      change fkIsingSquareFullVertexFixedBoundary n x at hx
      simpa [vertexGhostPrimitive, vertexSampledImaginaryTarget,
        isingFiniteGhostExtension, vertex_fixedBoundary_eq_zero n hn x hx]
        using hfixed x hx

theorem faceSampled_boundaryConsistencyError_le
    (n : Nat) (hn : 0 < n)
    (embedding : FKIsingSquareFullFaceNode n → Complex)
    (Phi : Complex → Complex) (bound : Real) (hbound : 0 ≤ bound)
    (hfixed : ∀ c, fkIsingSquareFullFaceFixedBoundary n c →
      |1 - (Phi (embedding c)).im| ≤ bound) :
    faceBoundaryConsistencyError n hn
      (faceSampledImaginaryTarget n embedding Phi) ≤ bound := by
  apply isingFiniteWeightedBoundaryError_le
    (faceDirichletBoundary n) (faceGhostPrimitive n hn)
    (faceSampledImaginaryTarget n embedding Phi) bound hbound
  intro c hc
  cases c with
  | none => simpa [faceGhostPrimitive, faceSampledImaginaryTarget,
      isingFiniteGhostExtension] using hbound
  | some c =>
      change fkIsingSquareFullFaceFixedBoundary n c at hc
      simpa [faceGhostPrimitive, faceSampledImaginaryTarget,
        isingFiniteGhostExtension, face_fixedBoundary_eq_one n hn c hc]
        using hfixed c hc

theorem vertexSampled_boundaryConsistencyError_eq_zero
    (n : Nat) (hn : 0 < n)
    (embedding : FKIsingSquareFullVertexNode n → Complex)
    (Phi : Complex → Complex)
    (hfixed : ∀ x, fkIsingSquareFullVertexFixedBoundary n x →
      (Phi (embedding x)).im = 0) :
    vertexBoundaryConsistencyError n hn
      (vertexSampledImaginaryTarget n embedding Phi) = 0 := by
  apply le_antisymm
  · apply vertexSampled_boundaryConsistencyError_le
      n hn embedding Phi 0 (le_refl 0)
    intro x hx
    simp [hfixed x hx]
  · exact isingFiniteWeightedBoundaryError_nonneg
      (vertexDirichletBoundary n) (vertexGhostPrimitive n hn)
      (vertexSampledImaginaryTarget n embedding Phi)

theorem faceSampled_boundaryConsistencyError_eq_zero
    (n : Nat) (hn : 0 < n)
    (embedding : FKIsingSquareFullFaceNode n → Complex)
    (Phi : Complex → Complex)
    (hfixed : ∀ c, fkIsingSquareFullFaceFixedBoundary n c →
      (Phi (embedding c)).im = 1) :
    faceBoundaryConsistencyError n hn
      (faceSampledImaginaryTarget n embedding Phi) = 0 := by
  apply le_antisymm
  · apply faceSampled_boundaryConsistencyError_le
      n hn embedding Phi 0 (le_refl 0)
    intro c hc
    simp [hfixed c hc]
  · exact isingFiniteWeightedBoundaryError_nonneg
      (faceDirichletBoundary n) (faceGhostPrimitive n hn)
      (faceSampledImaginaryTarget n embedding Phi)

theorem vertexSampled_targetResidual_le
    (n : Nat)
    (embedding : FKIsingSquareFullVertexNode n → Complex)
    (Phi : Complex → Complex) (bound : Real) (hbound : 0 ≤ bound)
    (hrobin : ∀ x, ¬ fkIsingSquareFullVertexFixedBoundary n x →
      |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
          (fun y ↦ (Phi (embedding y)).im) x +
        isingFermionicGhostRate
          (fkIsingSquareFullVertexGhostMultiplicity n) x *
            (1 - (Phi (embedding x)).im)| ≤ bound) :
    vertexTargetResidual n
      (vertexSampledImaginaryTarget n embedding Phi) ≤ bound := by
  apply isingFiniteWeightedTargetResidual_le
    (vertexGhostConductance n) (vertexDirichletBoundary n)
    (vertexSampledImaginaryTarget n embedding Phi) bound hbound
  intro x hx
  cases x with
  | none => exact False.elim (hx trivial)
  | some x =>
      change ¬ fkIsingSquareFullVertexFixedBoundary n x at hx
      have h := hrobin x hx
      have htarget : vertexSampledImaginaryTarget n embedding Phi =
          isingFiniteGhostExtension 1
            (fun y ↦ (Phi (embedding y)).im) := by
        funext z
        cases z <;> rfl
      rw [htarget]
      unfold vertexGhostConductance
      rw [isingFiniteGhostLaplacian_some]
      exact h

theorem faceSampled_targetResidual_le
    (n : Nat)
    (embedding : FKIsingSquareFullFaceNode n → Complex)
    (Phi : Complex → Complex) (bound : Real) (hbound : 0 ≤ bound)
    (hrobin : ∀ c, ¬ fkIsingSquareFullFaceFixedBoundary n c →
      |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
          (fun d ↦ (Phi (embedding d)).im) c +
        isingFermionicGhostRate
          (fkIsingSquareFullFaceGhostMultiplicity n) c *
            (0 - (Phi (embedding c)).im)| ≤ bound) :
    faceTargetResidual n
      (faceSampledImaginaryTarget n embedding Phi) ≤ bound := by
  apply isingFiniteWeightedTargetResidual_le
    (faceGhostConductance n) (faceDirichletBoundary n)
    (faceSampledImaginaryTarget n embedding Phi) bound hbound
  intro c hc
  cases c with
  | none => exact False.elim (hc trivial)
  | some c =>
      change ¬ fkIsingSquareFullFaceFixedBoundary n c at hc
      have h := hrobin c hc
      have htarget : faceSampledImaginaryTarget n embedding Phi =
          isingFiniteGhostExtension 0
            (fun d ↦ (Phi (embedding d)).im) := by
        funext z
        cases z <;> rfl
      rw [htarget]
      unfold faceGhostConductance
      rw [isingFiniteGhostLaplacian_some]
      exact h

theorem fullVertexGhostMultiplicity_le_three
    (n : Nat) (x : FKIsingSquareFullVertexNode n) :
    fkIsingSquareFullVertexGhostMultiplicity n x ≤ 3 := by
  unfold fkIsingSquareFullVertexGhostMultiplicity
  split_ifs <;> omega

theorem fullFaceGhostMultiplicity_le_one
    (n : Nat) (c : FKIsingSquareFullFaceNode n) :
    fkIsingSquareFullFaceGhostMultiplicity n c ≤ 1 := by
  unfold fkIsingSquareFullFaceGhostMultiplicity
  split_ifs <;> omega

theorem vertexGhostRate_le_threeCoefficient
    (n : Nat) (x : FKIsingSquareFullVertexNode n) :
    isingFermionicGhostRate
        (fkIsingSquareFullVertexGhostMultiplicity n) x ≤
      3 * isingFermionicGhostCoefficient := by
  unfold isingFermionicGhostRate
  have h : (fkIsingSquareFullVertexGhostMultiplicity n x : Real) ≤ 3 := by
    exact_mod_cast fullVertexGhostMultiplicity_le_three n x
  nlinarith [isingFermionicGhostCoefficient_pos.le]

theorem faceGhostRate_le_coefficient
    (n : Nat) (c : FKIsingSquareFullFaceNode n) :
    isingFermionicGhostRate
        (fkIsingSquareFullFaceGhostMultiplicity n) c ≤
      isingFermionicGhostCoefficient := by
  unfold isingFermionicGhostRate
  have h : (fkIsingSquareFullFaceGhostMultiplicity n c : Real) ≤ 1 := by
    exact_mod_cast fullFaceGhostMultiplicity_le_one n c
  nlinarith [isingFermionicGhostCoefficient_pos.le]



theorem vertexSampled_robinResidual_le_of_laplacian_and_trace
    (n : Nat)
    (embedding : FKIsingSquareFullVertexNode n → Complex)
    (Phi : Complex → Complex) (laplacianBound traceBound : Real)
    (htrace_nonneg : 0 ≤ traceBound)
    (hlaplacian : ∀ x, ¬ fkIsingSquareFullVertexFixedBoundary n x →
      |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fun y ↦ (Phi (embedding y)).im) x| ≤ laplacianBound)
    (htrace : ∀ x,
      ¬ fkIsingSquareFullVertexFixedBoundary n x →
      0 < fkIsingSquareFullVertexGhostMultiplicity n x →
        |1 - (Phi (embedding x)).im| ≤ traceBound) :
    ∀ x, ¬ fkIsingSquareFullVertexFixedBoundary n x →
      |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
          (fun y ↦ (Phi (embedding y)).im) x +
        isingFermionicGhostRate
            (fkIsingSquareFullVertexGhostMultiplicity n) x *
          (1 - (Phi (embedding x)).im)| ≤
        laplacianBound +
          (3 * isingFermionicGhostCoefficient) * traceBound := by
  intro x hx
  let rate := isingFermionicGhostRate
    (fkIsingSquareFullVertexGhostMultiplicity n) x
  let jump := 1 - (Phi (embedding x)).im
  calc
    |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
          (fun y ↦ (Phi (embedding y)).im) x + rate * jump| ≤
        |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
          (fun y ↦ (Phi (embedding y)).im) x| + |rate * jump| :=
      abs_add_le _ _
    _ = |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
          (fun y ↦ (Phi (embedding y)).im) x| + rate * |jump| := by
      have hrate : 0 ≤ rate := isingFermionicGhostRate_nonneg _ x
      rw [abs_mul, abs_of_nonneg hrate]
    _ ≤ laplacianBound +
        (3 * isingFermionicGhostCoefficient) * traceBound := by
      apply add_le_add (hlaplacian x hx)
      by_cases hpositive :
          0 < fkIsingSquareFullVertexGhostMultiplicity n x
      · exact mul_le_mul (vertexGhostRate_le_threeCoefficient n x)
          (htrace x hx hpositive) (abs_nonneg _)
          (mul_nonneg (by norm_num) isingFermionicGhostCoefficient_pos.le)
      · have hzero : fkIsingSquareFullVertexGhostMultiplicity n x = 0 :=
          Nat.eq_zero_of_not_pos hpositive
        simp [rate, isingFermionicGhostRate, hzero,
          mul_nonneg
            (mul_nonneg (by norm_num : (0 : Real) ≤ 3)
              isingFermionicGhostCoefficient_pos.le)
            htrace_nonneg]


theorem faceSampled_robinResidual_le_of_laplacian_and_trace
    (n : Nat)
    (embedding : FKIsingSquareFullFaceNode n → Complex)
    (Phi : Complex → Complex) (laplacianBound traceBound : Real)
    (htrace_nonneg : 0 ≤ traceBound)
    (hlaplacian : ∀ c, ¬ fkIsingSquareFullFaceFixedBoundary n c →
      |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
        (fun d ↦ (Phi (embedding d)).im) c| ≤ laplacianBound)
    (htrace : ∀ c,
      ¬ fkIsingSquareFullFaceFixedBoundary n c →
      0 < fkIsingSquareFullFaceGhostMultiplicity n c →
        |0 - (Phi (embedding c)).im| ≤ traceBound) :
    ∀ c, ¬ fkIsingSquareFullFaceFixedBoundary n c →
      |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
          (fun d ↦ (Phi (embedding d)).im) c +
        isingFermionicGhostRate
            (fkIsingSquareFullFaceGhostMultiplicity n) c *
          (0 - (Phi (embedding c)).im)| ≤
        laplacianBound + isingFermionicGhostCoefficient * traceBound := by
  intro c hc
  let rate := isingFermionicGhostRate
    (fkIsingSquareFullFaceGhostMultiplicity n) c
  let jump := 0 - (Phi (embedding c)).im
  calc
    |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
          (fun d ↦ (Phi (embedding d)).im) c + rate * jump| ≤
        |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
          (fun d ↦ (Phi (embedding d)).im) c| + |rate * jump| :=
      abs_add_le _ _
    _ = |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
          (fun d ↦ (Phi (embedding d)).im) c| + rate * |jump| := by
      have hrate : 0 ≤ rate := isingFermionicGhostRate_nonneg _ c
      rw [abs_mul, abs_of_nonneg hrate]
    _ ≤ laplacianBound + isingFermionicGhostCoefficient * traceBound := by
      apply add_le_add (hlaplacian c hc)
      by_cases hpositive : 0 < fkIsingSquareFullFaceGhostMultiplicity n c
      · exact mul_le_mul (faceGhostRate_le_coefficient n c)
          (htrace c hc hpositive) (abs_nonneg _)
          isingFermionicGhostCoefficient_pos.le
      · have hzero : fkIsingSquareFullFaceGhostMultiplicity n c = 0 :=
          Nat.eq_zero_of_not_pos hpositive
        simp [rate, isingFermionicGhostRate, hzero,
          mul_nonneg isingFermionicGhostCoefficient_pos.le htrace_nonneg]

theorem vertexSampled_targetResidual_le_of_laplacian_and_trace
    (n : Nat)
    (embedding : FKIsingSquareFullVertexNode n → Complex)
    (Phi : Complex → Complex) (laplacianBound traceBound : Real)
    (hlaplacian_nonneg : 0 ≤ laplacianBound)
    (htrace_nonneg : 0 ≤ traceBound)
    (hlaplacian : ∀ x, ¬ fkIsingSquareFullVertexFixedBoundary n x →
      |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fun y ↦ (Phi (embedding y)).im) x| ≤ laplacianBound)
    (htrace : ∀ x,
      ¬ fkIsingSquareFullVertexFixedBoundary n x →
      0 < fkIsingSquareFullVertexGhostMultiplicity n x →
        |1 - (Phi (embedding x)).im| ≤ traceBound) :
    vertexTargetResidual n
        (vertexSampledImaginaryTarget n embedding Phi) ≤
      laplacianBound +
        (3 * isingFermionicGhostCoefficient) * traceBound := by
  apply vertexSampled_targetResidual_le n embedding Phi
  · exact add_nonneg hlaplacian_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) isingFermionicGhostCoefficient_pos.le)
        htrace_nonneg)
  · exact vertexSampled_robinResidual_le_of_laplacian_and_trace
      n embedding Phi laplacianBound traceBound htrace_nonneg
      hlaplacian htrace

theorem faceSampled_targetResidual_le_of_laplacian_and_trace
    (n : Nat)
    (embedding : FKIsingSquareFullFaceNode n → Complex)
    (Phi : Complex → Complex) (laplacianBound traceBound : Real)
    (hlaplacian_nonneg : 0 ≤ laplacianBound)
    (htrace_nonneg : 0 ≤ traceBound)
    (hlaplacian : ∀ c, ¬ fkIsingSquareFullFaceFixedBoundary n c →
      |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
        (fun d ↦ (Phi (embedding d)).im) c| ≤ laplacianBound)
    (htrace : ∀ c,
      ¬ fkIsingSquareFullFaceFixedBoundary n c →
      0 < fkIsingSquareFullFaceGhostMultiplicity n c →
        |0 - (Phi (embedding c)).im| ≤ traceBound) :
    faceTargetResidual n
        (faceSampledImaginaryTarget n embedding Phi) ≤
      laplacianBound + isingFermionicGhostCoefficient * traceBound := by
  apply faceSampled_targetResidual_le n embedding Phi
  · exact add_nonneg hlaplacian_nonneg
      (mul_nonneg isingFermionicGhostCoefficient_pos.le htrace_nonneg)
  · exact faceSampled_robinResidual_le_of_laplacian_and_trace
      n embedding Phi laplacianBound traceBound htrace_nonneg
      hlaplacian htrace

theorem vertexSampled_targetResidual_le_of_exact_free_trace
    (n : Nat)
    (embedding : FKIsingSquareFullVertexNode n → Complex)
    (Phi : Complex → Complex) (laplacianBound : Real)
    (hlaplacian_nonneg : 0 ≤ laplacianBound)
    (hlaplacian : ∀ x, ¬ fkIsingSquareFullVertexFixedBoundary n x →
      |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fun y ↦ (Phi (embedding y)).im) x| ≤ laplacianBound)
    (hfree : ∀ x,
      ¬ fkIsingSquareFullVertexFixedBoundary n x →
      0 < fkIsingSquareFullVertexGhostMultiplicity n x →
        (Phi (embedding x)).im = 1) :
    vertexTargetResidual n
        (vertexSampledImaginaryTarget n embedding Phi) ≤ laplacianBound := by
  simpa using vertexSampled_targetResidual_le_of_laplacian_and_trace
    n embedding Phi laplacianBound 0 hlaplacian_nonneg (le_refl 0)
    hlaplacian (fun x hfixed hx ↦ by simp [hfree x hfixed hx])

theorem faceSampled_targetResidual_le_of_exact_free_trace
    (n : Nat)
    (embedding : FKIsingSquareFullFaceNode n → Complex)
    (Phi : Complex → Complex) (laplacianBound : Real)
    (hlaplacian_nonneg : 0 ≤ laplacianBound)
    (hlaplacian : ∀ c, ¬ fkIsingSquareFullFaceFixedBoundary n c →
      |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
        (fun d ↦ (Phi (embedding d)).im) c| ≤ laplacianBound)
    (hfree : ∀ c,
      ¬ fkIsingSquareFullFaceFixedBoundary n c →
      0 < fkIsingSquareFullFaceGhostMultiplicity n c →
        (Phi (embedding c)).im = 0) :
    faceTargetResidual n
        (faceSampledImaginaryTarget n embedding Phi) ≤ laplacianBound := by
  simpa using faceSampled_targetResidual_le_of_laplacian_and_trace
    n embedding Phi laplacianBound 0 hlaplacian_nonneg (le_refl 0)
    hlaplacian (fun c hfixed hc ↦ by simp [hfree c hfixed hc])

theorem fullVertex_neighbor_card_le_four
    (n : Nat) (x : FKIsingSquareFullVertexNode n) :
    Nat.card ↑((fkIsingSquareFullVertexGraph n).neighborSet x) ≤ 4 := by
  classical
  let f : (fkIsingSquareFullVertexGraph n).neighborSet x →
      (hypercubicLattice 2).neighborSet x.1 := fun y ↦ ⟨y.1.1, y.2⟩
  have hf : Function.Injective f := by
    intro y z hyz
    dsimp [f] at hyz
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg
      (fun w : (hypercubicLattice 2).neighborSet x.1 ↦ w.1) hyz
  calc
    Nat.card ((fkIsingSquareFullVertexGraph n).neighborSet x) ≤
        Nat.card ((hypercubicLattice 2).neighborSet x.1) :=
      Nat.card_le_card_of_injective f hf
    _ = (hypercubicLattice 2).degree x.1 :=
      (Nat.card_eq_fintype_card).trans
        (SimpleGraph.card_neighborSet_eq_degree _ _)
    _ = 4 := by simpa using degree_eq 2 x.1

theorem vertexQuadraticBarrier_laplacian_le
    (n : Nat) (x : FKIsingSquareFullVertexNode n) :
    isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
      (fkIsingSquareBoxQuadraticBarrier n) x ≤ 2 * (n : Real) ^ 2 := by
  classical
  have hcardNat :
      ((fkIsingSquareFullVertexGraph n).neighborFinset x).card ≤ 4 := by
    have hncard : Nat.card
        ↑((fkIsingSquareFullVertexGraph n).neighborSet x) =
        (fkIsingSquareFullVertexGraph n).degree x :=
      (Nat.card_eq_fintype_card).trans
        (SimpleGraph.card_neighborSet_eq_degree _ _)
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    rw [← hncard]
    exact fullVertex_neighbor_card_le_four n x
  have hcard :
      (((fkIsingSquareFullVertexGraph n).neighborFinset x).card : Real) ≤ 4 := by
    exact_mod_cast hcardNat
  unfold isingFiniteGraphLaplacian
  calc
    (∑ y ∈ (fkIsingSquareFullVertexGraph n).neighborFinset x,
        (fkIsingSquareBoxQuadraticBarrier n y -
          fkIsingSquareBoxQuadraticBarrier n x)) ≤
        ∑ _y ∈ (fkIsingSquareFullVertexGraph n).neighborFinset x,
          ((n : Real) ^ 2 / 2) := by
      apply Finset.sum_le_sum
      intro y hy
      have hyBound := fkIsingSquareBoxQuadraticBarrier_le n y
      have hxNonneg := fkIsingSquareBoxQuadraticBarrier_nonneg n x
      linarith
    _ = (((fkIsingSquareFullVertexGraph n).neighborFinset x).card : Real) *
        ((n : Real) ^ 2 / 2) := by simp
    _ ≤ 4 * ((n : Real) ^ 2 / 2) := by gcongr
    _ = 2 * (n : Real) ^ 2 := by ring

noncomputable def vertexBarrierOffset (n : Nat) : Real :=
  (2 * (n : Real) ^ 2 + 1) / isingFermionicGhostCoefficient

def vertexExplicitPoissonBarrier
    (n : Nat) : Option (FKIsingSquareFullVertexNode n) → Real
  | none => 0
  | some x => fkIsingSquareBoxQuadraticBarrier n x + vertexBarrierOffset n

noncomputable def vertexExplicitPoissonBarrierBound (n : Nat) : Real :=
  (n : Real) ^ 2 / 2 + vertexBarrierOffset n

theorem vertexBarrierOffset_nonneg (n : Nat) :
    0 ≤ vertexBarrierOffset n := by
  unfold vertexBarrierOffset
  exact div_nonneg (by positivity) isingFermionicGhostCoefficient_pos.le

theorem vertexExplicitPoissonBarrier_nonneg (n : Nat) :
    ∀ x, 0 ≤ vertexExplicitPoissonBarrier n x := by
  intro x
  cases x with
  | none => simp [vertexExplicitPoissonBarrier]
  | some x =>
      simp only [vertexExplicitPoissonBarrier]
      exact add_nonneg (fkIsingSquareBoxQuadraticBarrier_nonneg n x)
        (vertexBarrierOffset_nonneg n)

theorem vertexExplicitPoissonBarrier_le_bound (n : Nat) :
    ∀ x, vertexExplicitPoissonBarrier n x ≤
      vertexExplicitPoissonBarrierBound n := by
  intro x
  cases x with
  | none =>
      simp only [vertexExplicitPoissonBarrier]
      exact add_nonneg (by positivity) (vertexBarrierOffset_nonneg n)
  | some x =>
      simpa [vertexExplicitPoissonBarrier,
        vertexExplicitPoissonBarrierBound, add_comm] using
          add_le_add_right (fkIsingSquareBoxQuadraticBarrier_le n x)
            (vertexBarrierOffset n)

theorem vertexExplicitPoissonBarrier_laplacian
    (n : Nat) (hn : 0 < n)
    (x : Option (FKIsingSquareFullVertexNode n))
    (hx : ¬ vertexDirichletBoundary n x) :
    isingFiniteWeightedLaplacian (vertexGhostConductance n)
      (vertexExplicitPoissonBarrier n) x ≤ -1 := by
  cases x with
  | none => exact False.elim (hx trivial)
  | some x =>
      change ¬ fkIsingSquareFullVertexFixedBoundary n x at hx
      let Q := fkIsingSquareBoxQuadraticBarrier n
      let C := vertexBarrierOffset n
      let f : FKIsingSquareFullVertexNode n → Real := fun y ↦ Q y + C
      have hbarrier : vertexExplicitPoissonBarrier n =
          isingFiniteGhostExtension 0 f := by
        funext z
        cases z <;> rfl
      change isingFiniteWeightedLaplacian
        (isingFiniteGhostConductance (fkIsingSquareFullVertexGraph n)
          (isingFermionicGhostRate
            (fkIsingSquareFullVertexGhostMultiplicity n)))
        (vertexExplicitPoissonBarrier n) (some x) ≤ -1
      rw [hbarrier, isingFiniteGhostLaplacian_some]
      by_cases hghost : 0 < fkIsingSquareFullVertexGhostMultiplicity n x
      · have hgraph := vertexQuadraticBarrier_laplacian_le n x
        have hgraphf : isingFiniteGraphLaplacian
            (fkIsingSquareFullVertexGraph n) f x =
            isingFiniteGraphLaplacian
              (fkIsingSquareFullVertexGraph n) Q x := by
          exact isingFiniteGraphLaplacian_add_const
            (fkIsingSquareFullVertexGraph n) Q C x
        have hQ : 0 ≤ Q x := fkIsingSquareBoxQuadraticBarrier_nonneg n x
        have hcoef : 0 < isingFermionicGhostCoefficient :=
          isingFermionicGhostCoefficient_pos
        have hm : (1 : Real) ≤
            (fkIsingSquareFullVertexGhostMultiplicity n x : Real) := by
          exact_mod_cast hghost
        have hrateC : 2 * (n : Real) ^ 2 + 1 ≤
            isingFermionicGhostRate
                (fkIsingSquareFullVertexGhostMultiplicity n) x * C := by
          unfold isingFermionicGhostRate C vertexBarrierOffset
          field_simp
          nlinarith
        have hrate : 0 ≤ isingFermionicGhostRate
            (fkIsingSquareFullVertexGhostMultiplicity n) x :=
          isingFermionicGhostRate_nonneg
            (fkIsingSquareFullVertexGhostMultiplicity n) x
        rw [hgraphf]
        dsimp only [f]
        nlinarith
      · have hmult : fkIsingSquareFullVertexGhostMultiplicity n x = 0 :=
          Nat.eq_zero_of_not_pos hghost
        have hinterior : ¬ fkIsingSquareBoxBoundary n x := by
          intro hboundary
          rcases fkIsingSquareFullVertex_boundary_fixed_or_ghost
              n x hboundary with hfixed | hpos
          · exact hx hfixed
          · exact hghost hpos
        have hQlap := fkIsingSquareBoxQuadraticBarrier_laplacian
          n x hinterior
        have hQlap' : isingFiniteGraphLaplacian
            (fkIsingSquareFullVertexGraph n) Q x = -1 := by
          simpa [fkIsingSquareFullVertexGraph, Q] using hQlap
        rw [show isingFiniteGraphLaplacian
            (fkIsingSquareFullVertexGraph n) f x =
            isingFiniteGraphLaplacian
              (fkIsingSquareFullVertexGraph n) Q x by
          exact isingFiniteGraphLaplacian_add_const
            (fkIsingSquareFullVertexGraph n) Q C x]
        simp [isingFermionicGhostRate, hmult, hQlap']

theorem vertexPoissonBarrier_le_explicit
    (n : Nat) (hn : 0 < n) : ∀ x,
    isingFiniteWeightedPoissonBarrier
        (vertexGhostGraph n) (vertexGhostConductance n)
        (vertexDirichletBoundary n) (vertexGhostConductance_nonneg n)
        (vertexGhostConductance_pos_of_adj n)
        (vertexGhost_reaches_boundary n) x ≤
      vertexExplicitPoissonBarrier n x := by
  apply isingFiniteWeighted_laplacian_comparison
    (vertexGhostGraph n) (vertexGhostConductance n)
    (vertexDirichletBoundary n)
    (isingFiniteWeightedPoissonBarrier
      (vertexGhostGraph n) (vertexGhostConductance n)
      (vertexDirichletBoundary n) (vertexGhostConductance_nonneg n)
      (vertexGhostConductance_pos_of_adj n)
      (vertexGhost_reaches_boundary n))
    (vertexExplicitPoissonBarrier n)
    (vertexGhostConductance_nonneg n)
    (vertexGhostConductance_pos_of_adj n)
    (vertexGhost_reaches_boundary n)
  · intro x hx
    rw [isingFiniteWeightedPoissonBarrier_boundary
      (vertexGhostGraph n) (vertexGhostConductance n)
      (vertexDirichletBoundary n) (vertexGhostConductance_nonneg n)
      (vertexGhostConductance_pos_of_adj n)
      (vertexGhost_reaches_boundary n) x hx]
    exact vertexExplicitPoissonBarrier_nonneg n x
  · intro x hx
    rw [isingFiniteWeightedPoissonBarrier_laplacian
      (vertexGhostGraph n) (vertexGhostConductance n)
      (vertexDirichletBoundary n) (vertexGhostConductance_nonneg n)
      (vertexGhostConductance_pos_of_adj n)
      (vertexGhost_reaches_boundary n) x hx]
    exact vertexExplicitPoissonBarrier_laplacian n hn x hx

theorem vertexPoissonBarrierBound_le_explicit
    (n : Nat) (hn : 0 < n) :
    vertexPoissonBarrierBound n ≤ vertexExplicitPoissonBarrierBound n := by
  unfold vertexPoissonBarrierBound isingFiniteWeightedPoissonBarrierBound
  rw [Finset.max'_le_iff]
  intro z hz
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hz
  exact (vertexPoissonBarrier_le_explicit n hn x).trans
    (vertexExplicitPoissonBarrier_le_bound n x)

def faceRowPoissonBarrier
    (n : Nat) (c : FKIsingSquareFullFaceNode n) : Real :=
  (c.2.1 : Real) * (2 * (n : Real) - c.2.1) / 2

def faceExplicitPoissonBarrier
    (n : Nat) : Option (FKIsingSquareFullFaceNode n) → Real
  | none => 0
  | some c => faceRowPoissonBarrier n c

def faceExplicitPoissonBarrierBound (n : Nat) : Real :=
  (n : Real) ^ 2 / 2

theorem faceRowPoissonBarrier_nonneg
    (n : Nat) (c : FKIsingSquareFullFaceNode n) :
    0 ≤ faceRowPoissonBarrier n c := by
  have hc : (c.2.1 : Real) ≤ 2 * (n : Real) := by
    exact_mod_cast (Nat.le_of_lt c.2.isLt)
  unfold faceRowPoissonBarrier
  positivity

theorem faceRowPoissonBarrier_le
    (n : Nat) (c : FKIsingSquareFullFaceNode n) :
    faceRowPoissonBarrier n c ≤ faceExplicitPoissonBarrierBound n := by
  unfold faceRowPoissonBarrier faceExplicitPoissonBarrierBound
  nlinarith [sq_nonneg ((c.2.1 : Real) - (n : Real))]

theorem faceExplicitPoissonBarrier_nonneg (n : Nat) :
    ∀ c, 0 ≤ faceExplicitPoissonBarrier n c := by
  intro c
  cases c with
  | none => simp [faceExplicitPoissonBarrier]
  | some c => exact faceRowPoissonBarrier_nonneg n c

theorem faceExplicitPoissonBarrier_le_bound (n : Nat) :
    ∀ c, faceExplicitPoissonBarrier n c ≤
      faceExplicitPoissonBarrierBound n := by
  intro c
  cases c with
  | none =>
      simp [faceExplicitPoissonBarrier]
      exact div_nonneg (sq_nonneg (n : Real)) (by norm_num)
  | some c => exact faceRowPoissonBarrier_le n c


theorem face_neighborFinset_left
    (n : Nat) (c : FKIsingSquareFullFaceNode n)
    (hleft : c.1.1 = 0)
    (heast : c.1.1 + 1 < 2 * n)
    (hnorth : c.2.1 + 1 < 2 * n)
    (hsouth : 0 < c.2.1)
    [Fintype ↑((fkIsingSquareFullFaceGraph n).neighborSet c)] :
    (fkIsingSquareFullFaceGraph n).neighborFinset c =
      {faceEastNeighbor n c heast, faceNorthNeighbor n c hnorth,
        faceSouthNeighbor n c hsouth} := by
  ext y
  rw [SimpleGraph.mem_neighborFinset]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (⟨hcol, hup | hdown⟩ | ⟨hrow, hright | hwest⟩)
    · right; left
      apply Prod.ext
      · exact hcol.symm
      · apply Fin.ext
        simp [faceNorthNeighbor]
        omega
    · right; right
      apply Prod.ext
      · exact hcol.symm
      · apply Fin.ext
        simp [faceSouthNeighbor]
        omega
    · left
      apply Prod.ext
      · apply Fin.ext
        simp [faceEastNeighbor]
        omega
      · exact hrow.symm
    · have hy := y.1.2
      omega
  · rintro (rfl | rfl | rfl)
    · exact Or.inr ⟨rfl, Or.inl (by simp [faceEastNeighbor])⟩
    · exact Or.inl ⟨rfl, Or.inl (by simp [faceNorthNeighbor])⟩
    · exact Or.inl ⟨rfl, Or.inr (by simp [faceSouthNeighbor]; omega)⟩



theorem faceColumnFunction_laplacian_of_not_fixed
    (n : Nat) (F : Nat -> Real) (c : FKIsingSquareFullFaceNode n)
    (hc : ¬ fkIsingSquareFullFaceFixedBoundary n c) :
    isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
        (fun d => F d.1.1) c =
      if c.1.1 = 0 then F 1 - F 0
      else F (c.1.1 + 1) + F (c.1.1 - 1) - 2 * F c.1.1 := by
  classical
  have hsouth : 0 < c.2.1 := by
    by_contra h
    apply hc
    left
    omega
  have heast : c.1.1 + 1 < 2 * n := by
    by_contra h
    apply hc
    right
    left
    omega
  have hnorth : c.2.1 + 1 < 2 * n := by
    by_contra h
    apply hc
    right
    right
    omega
  let cE := faceEastNeighbor n c heast
  let cN := faceNorthNeighbor n c hnorth
  let cS := faceSouthNeighbor n c hsouth
  have hEN : cE ≠ cN := by
    intro h
    have h0 := congrArg (fun z : FKIsingSquareFullFaceNode n => z.1.1) h
    simp [cE, cN, faceEastNeighbor, faceNorthNeighbor] at h0
  have hES : cE ≠ cS := by
    intro h
    have h0 := congrArg (fun z : FKIsingSquareFullFaceNode n => z.1.1) h
    simp [cE, cS, faceEastNeighbor, faceSouthNeighbor] at h0
  have hNS : cN ≠ cS := by
    intro h
    have h1 := congrArg (fun z : FKIsingSquareFullFaceNode n => z.2.1) h
    simp [cN, cS, faceNorthNeighbor, faceSouthNeighbor] at h1
    omega
  by_cases hleft : c.1.1 = 0
  · unfold isingFiniteGraphLaplacian
    rw [show (fkIsingSquareFullFaceGraph n).neighborFinset c =
        {cE, cN, cS} by
      exact face_neighborFinset_left n c hleft heast hnorth hsouth]
    have he_not : cE ∉ ({cN, cS} : Finset _) := by simp [hEN, hES]
    have hn_not : cN ∉ ({cS} : Finset _) := by simp [hNS]
    rw [Finset.sum_insert he_not, Finset.sum_insert hn_not,
      Finset.sum_singleton]
    simp [cE, cN, cS, faceEastNeighbor, faceNorthNeighbor,
      faceSouthNeighbor, hleft]
  · let cW := faceWestNeighbor n c (by omega)
    have hEW : cE ≠ cW := by
      intro h
      have h0 := congrArg (fun z : FKIsingSquareFullFaceNode n => z.1.1) h
      simp [cE, cW, faceEastNeighbor, faceWestNeighbor] at h0
      omega
    have hNW : cN ≠ cW := by
      intro h
      have h1 := congrArg (fun z : FKIsingSquareFullFaceNode n => z.2.1) h
      simp [cN, cW, faceNorthNeighbor, faceWestNeighbor] at h1
    have hWS : cW ≠ cS := by
      intro h
      have h1 := congrArg (fun z : FKIsingSquareFullFaceNode n => z.2.1) h
      simp [cW, cS, faceWestNeighbor, faceSouthNeighbor] at h1
      omega
    unfold isingFiniteGraphLaplacian
    rw [show (fkIsingSquareFullFaceGraph n).neighborFinset c =
        {cE, cN, cW, cS} by
      exact fkIsingSquareBoundaryFullFace_neighborFinset n c heast hnorth
        (by omega) hsouth]
    have he_not : cE ∉ ({cN, cW, cS} : Finset _) := by
      simp [hEN, hEW, hES]
    have hn_not : cN ∉ ({cW, cS} : Finset _) := by simp [hNW, hNS]
    have hw_not : cW ∉ ({cS} : Finset _) := by simp [hWS]
    rw [Finset.sum_insert he_not, Finset.sum_insert hn_not,
      Finset.sum_insert hw_not, Finset.sum_singleton]
    simp [cE, cN, cW, cS, faceEastNeighbor, faceNorthNeighbor,
      faceWestNeighbor, faceSouthNeighbor, hleft]
    ring


theorem faceRowFunction_laplacian_of_not_fixed
    (n : Nat) (F : Nat -> Real) (c : FKIsingSquareFullFaceNode n)
    (hc : ¬ fkIsingSquareFullFaceFixedBoundary n c) :
    isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
        (fun d => F d.2.1) c =
      F (c.2.1 + 1) + F (c.2.1 - 1) - 2 * F c.2.1 := by
  classical
  have hsouth : 0 < c.2.1 := by
    by_contra h
    apply hc
    left
    omega
  have heast : c.1.1 + 1 < 2 * n := by
    by_contra h
    apply hc
    right
    left
    omega
  have hnorth : c.2.1 + 1 < 2 * n := by
    by_contra h
    apply hc
    right
    right
    omega
  let cE := faceEastNeighbor n c heast
  let cN := faceNorthNeighbor n c hnorth
  let cS := faceSouthNeighbor n c hsouth
  have hEN : cE ≠ cN := by
    intro h
    have h0 := congrArg (fun z : FKIsingSquareFullFaceNode n => z.1.1) h
    simp [cE, cN, faceEastNeighbor, faceNorthNeighbor] at h0
  have hES : cE ≠ cS := by
    intro h
    have h0 := congrArg (fun z : FKIsingSquareFullFaceNode n => z.1.1) h
    simp [cE, cS, faceEastNeighbor, faceSouthNeighbor] at h0
  have hNS : cN ≠ cS := by
    intro h
    have h1 := congrArg (fun z : FKIsingSquareFullFaceNode n => z.2.1) h
    simp [cN, cS, faceNorthNeighbor, faceSouthNeighbor] at h1
    omega
  by_cases hleft : c.1.1 = 0
  · unfold isingFiniteGraphLaplacian
    rw [show (fkIsingSquareFullFaceGraph n).neighborFinset c =
        {cE, cN, cS} by
      exact face_neighborFinset_left n c hleft heast hnorth hsouth]
    have he_not : cE ∉ ({cN, cS} : Finset _) := by simp [hEN, hES]
    have hn_not : cN ∉ ({cS} : Finset _) := by simp [hNS]
    rw [Finset.sum_insert he_not, Finset.sum_insert hn_not,
      Finset.sum_singleton]
    simp [cE, cN, cS, faceEastNeighbor, faceNorthNeighbor,
      faceSouthNeighbor]
    ring
  · let cW := faceWestNeighbor n c (by omega)
    have hEW : cE ≠ cW := by
      intro h
      have h0 := congrArg (fun z : FKIsingSquareFullFaceNode n => z.1.1) h
      simp [cE, cW, faceEastNeighbor, faceWestNeighbor] at h0
      omega
    have hNW : cN ≠ cW := by
      intro h
      have h1 := congrArg (fun z : FKIsingSquareFullFaceNode n => z.2.1) h
      simp [cN, cW, faceNorthNeighbor, faceWestNeighbor] at h1
    have hWS : cW ≠ cS := by
      intro h
      have h1 := congrArg (fun z : FKIsingSquareFullFaceNode n => z.2.1) h
      simp [cW, cS, faceWestNeighbor, faceSouthNeighbor] at h1
      omega
    unfold isingFiniteGraphLaplacian
    rw [show (fkIsingSquareFullFaceGraph n).neighborFinset c =
        {cE, cN, cW, cS} by
      exact fkIsingSquareBoundaryFullFace_neighborFinset n c heast hnorth
        (by omega) hsouth]
    have he_not : cE ∉ ({cN, cW, cS} : Finset _) := by
      simp [hEN, hEW, hES]
    have hn_not : cN ∉ ({cW, cS} : Finset _) := by simp [hNW, hNS]
    have hw_not : cW ∉ ({cS} : Finset _) := by simp [hWS]
    rw [Finset.sum_insert he_not, Finset.sum_insert hn_not,
      Finset.sum_insert hw_not, Finset.sum_singleton]
    simp [cE, cN, cW, cS, faceEastNeighbor, faceNorthNeighbor,
      faceWestNeighbor, faceSouthNeighbor]
    ring

theorem faceRowPoissonBarrier_laplacian
    (n : Nat) (c : FKIsingSquareFullFaceNode n)
    (hc : ¬ fkIsingSquareFullFaceFixedBoundary n c) :
    isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
      (faceRowPoissonBarrier n) c = -1 := by
  classical
  have hsouth : 0 < c.2.1 := by
    by_contra h
    apply hc
    left
    omega
  have heast : c.1.1 + 1 < 2 * n := by
    have hcBound := c.1.isLt
    by_contra h
    apply hc
    right
    left
    omega
  have hnorth : c.2.1 + 1 < 2 * n := by
    have hcBound := c.2.isLt
    by_contra h
    apply hc
    right
    right
    omega
  let cE := faceEastNeighbor n c heast
  let cN := faceNorthNeighbor n c hnorth
  let cS := faceSouthNeighbor n c hsouth
  have hEN : cE ≠ cN := by
    intro h
    have h0 := congrArg (fun z : FKIsingSquareFullFaceNode n ↦ z.1.1) h
    simp [cE, cN, faceEastNeighbor, faceNorthNeighbor] at h0
  have hES : cE ≠ cS := by
    intro h
    have h0 := congrArg (fun z : FKIsingSquareFullFaceNode n ↦ z.1.1) h
    simp [cE, cS, faceEastNeighbor, faceSouthNeighbor] at h0
  have hNS : cN ≠ cS := by
    intro h
    have h1 := congrArg (fun z : FKIsingSquareFullFaceNode n ↦ z.2.1) h
    simp [cN, cS, faceNorthNeighbor, faceSouthNeighbor] at h1
    omega
  have hcast : ((c.2.1 - 1 : Nat) : Real) = (c.2.1 : Real) - 1 := by
    rw [Nat.cast_sub (R := Real) (by omega : 1 ≤ c.2.1)]
    norm_num
  by_cases hleft : c.1.1 = 0
  · unfold isingFiniteGraphLaplacian
    rw [show (fkIsingSquareFullFaceGraph n).neighborFinset c =
        {cE, cN, cS} by
      exact face_neighborFinset_left n c hleft heast hnorth hsouth]
    have he_not : cE ∉ ({cN, cS} : Finset _) := by simp [hEN, hES]
    have hn_not : cN ∉ ({cS} : Finset _) := by simp [hNS]
    rw [Finset.sum_insert he_not, Finset.sum_insert hn_not,
      Finset.sum_singleton]
    simp [cE, cN, cS, faceRowPoissonBarrier,
      faceEastNeighbor, faceNorthNeighbor, faceSouthNeighbor]
    rw [hcast]
    ring
  · let cW := faceWestNeighbor n c (by omega)
    have hEW : cE ≠ cW := by
      intro h
      have h0 := congrArg (fun z : FKIsingSquareFullFaceNode n ↦ z.1.1) h
      simp [cE, cW, faceEastNeighbor, faceWestNeighbor] at h0
      omega
    have hNW : cN ≠ cW := by
      intro h
      have h1 := congrArg (fun z : FKIsingSquareFullFaceNode n ↦ z.2.1) h
      simp [cN, cW, faceNorthNeighbor, faceWestNeighbor] at h1
    have hWS : cW ≠ cS := by
      intro h
      have h1 := congrArg (fun z : FKIsingSquareFullFaceNode n ↦ z.2.1) h
      simp [cW, cS, faceWestNeighbor, faceSouthNeighbor] at h1
      omega
    unfold isingFiniteGraphLaplacian
    rw [show (fkIsingSquareFullFaceGraph n).neighborFinset c =
        {cE, cN, cW, cS} by
      exact fkIsingSquareBoundaryFullFace_neighborFinset n c heast hnorth
        (by omega) hsouth]
    have he_not : cE ∉ ({cN, cW, cS} : Finset _) := by
      simp [hEN, hEW, hES]
    have hn_not : cN ∉ ({cW, cS} : Finset _) := by simp [hNW, hNS]
    have hw_not : cW ∉ ({cS} : Finset _) := by simp [hWS]
    rw [Finset.sum_insert he_not, Finset.sum_insert hn_not,
      Finset.sum_insert hw_not, Finset.sum_singleton]
    simp [cE, cN, cW, cS,
      faceRowPoissonBarrier, faceEastNeighbor, faceNorthNeighbor,
      faceWestNeighbor, faceSouthNeighbor]
    rw [hcast]
    ring

theorem faceExplicitPoissonBarrier_laplacian
    (n : Nat) (c : Option (FKIsingSquareFullFaceNode n))
    (hc : ¬ faceDirichletBoundary n c) :
    isingFiniteWeightedLaplacian (faceGhostConductance n)
      (faceExplicitPoissonBarrier n) c ≤ -1 := by
  cases c with
  | none => exact False.elim (hc trivial)
  | some c =>
      change ¬ fkIsingSquareFullFaceFixedBoundary n c at hc
      have hbarrier : faceExplicitPoissonBarrier n =
          isingFiniteGhostExtension 0 (faceRowPoissonBarrier n) := by
        funext z
        cases z <;> rfl
      change isingFiniteWeightedLaplacian
        (isingFiniteGhostConductance (fkIsingSquareFullFaceGraph n)
          (isingFermionicGhostRate
            (fkIsingSquareFullFaceGhostMultiplicity n)))
        (faceExplicitPoissonBarrier n) (some c) ≤ -1
      rw [hbarrier, isingFiniteGhostLaplacian_some,
        faceRowPoissonBarrier_laplacian n c hc]
      have hrate : 0 ≤ isingFermionicGhostRate
          (fkIsingSquareFullFaceGhostMultiplicity n) c :=
        isingFermionicGhostRate_nonneg
          (fkIsingSquareFullFaceGhostMultiplicity n) c
      have hrow := faceRowPoissonBarrier_nonneg n c
      nlinarith

theorem facePoissonBarrier_le_explicit (n : Nat) : ∀ c,
    isingFiniteWeightedPoissonBarrier
        (faceGhostGraph n) (faceGhostConductance n)
        (faceDirichletBoundary n) (faceGhostConductance_nonneg n)
        (faceGhostConductance_pos_of_adj n)
        (faceGhost_reaches_boundary n) c ≤
      faceExplicitPoissonBarrier n c := by
  apply isingFiniteWeighted_laplacian_comparison
    (faceGhostGraph n) (faceGhostConductance n)
    (faceDirichletBoundary n)
    (isingFiniteWeightedPoissonBarrier
      (faceGhostGraph n) (faceGhostConductance n)
      (faceDirichletBoundary n) (faceGhostConductance_nonneg n)
      (faceGhostConductance_pos_of_adj n)
      (faceGhost_reaches_boundary n))
    (faceExplicitPoissonBarrier n)
    (faceGhostConductance_nonneg n)
    (faceGhostConductance_pos_of_adj n)
    (faceGhost_reaches_boundary n)
  · intro c hc
    rw [isingFiniteWeightedPoissonBarrier_boundary
      (faceGhostGraph n) (faceGhostConductance n)
      (faceDirichletBoundary n) (faceGhostConductance_nonneg n)
      (faceGhostConductance_pos_of_adj n)
      (faceGhost_reaches_boundary n) c hc]
    exact faceExplicitPoissonBarrier_nonneg n c
  · intro c hc
    rw [isingFiniteWeightedPoissonBarrier_laplacian
      (faceGhostGraph n) (faceGhostConductance n)
      (faceDirichletBoundary n) (faceGhostConductance_nonneg n)
      (faceGhostConductance_pos_of_adj n)
      (faceGhost_reaches_boundary n) c hc]
    exact faceExplicitPoissonBarrier_laplacian n c hc

theorem facePoissonBarrierBound_le_explicit (n : Nat) :
    facePoissonBarrierBound n ≤ faceExplicitPoissonBarrierBound n := by
  unfold facePoissonBarrierBound isingFiniteWeightedPoissonBarrierBound
  rw [Finset.max'_le_iff]
  intro z hz
  obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hz
  exact (facePoissonBarrier_le_explicit n c).trans
    (faceExplicitPoissonBarrier_le_bound n c)

noncomputable def vertexBarrierGrowthConstant : Real :=
  1 / 2 + 3 / isingFermionicGhostCoefficient

theorem vertexBarrierGrowthConstant_nonneg :
    0 ≤ vertexBarrierGrowthConstant := by
  unfold vertexBarrierGrowthConstant
  exact add_nonneg (by norm_num)
    (div_nonneg (by norm_num) isingFermionicGhostCoefficient_pos.le)

theorem half_le_vertexBarrierGrowthConstant :
    (1 / 2 : Real) ≤ vertexBarrierGrowthConstant := by
  unfold vertexBarrierGrowthConstant
  have h : 0 ≤ 3 / isingFermionicGhostCoefficient :=
    div_nonneg (by norm_num) isingFermionicGhostCoefficient_pos.le
  linarith

theorem vertexExplicitPoissonBarrierBound_le_growth
    (n : Nat) (hn : 0 < n) :
    vertexExplicitPoissonBarrierBound n ≤
      vertexBarrierGrowthConstant * (n : Real) ^ 2 := by
  have hn1 : (1 : Real) ≤ (n : Real) := by exact_mod_cast hn
  have hsquare : (1 : Real) ≤ (n : Real) ^ 2 := by nlinarith
  have hnum : 2 * (n : Real) ^ 2 + 1 ≤ 3 * (n : Real) ^ 2 := by
    linarith
  unfold vertexExplicitPoissonBarrierBound vertexBarrierOffset
    vertexBarrierGrowthConstant
  calc
    (n : Real) ^ 2 / 2 +
        (2 * (n : Real) ^ 2 + 1) / isingFermionicGhostCoefficient ≤
      (n : Real) ^ 2 / 2 +
        (3 * (n : Real) ^ 2) / isingFermionicGhostCoefficient := by
      simpa [add_comm] using
        (add_le_add_left
          (div_le_div_of_nonneg_right hnum
            isingFermionicGhostCoefficient_pos.le)
          ((n : Real) ^ 2 / 2))
    _ = (1 / 2 + 3 / isingFermionicGhostCoefficient) *
        (n : Real) ^ 2 := by ring

theorem vertexPoissonBarrierBound_le_growth
    (n : Nat) (hn : 0 < n) :
    vertexPoissonBarrierBound n ≤
      vertexBarrierGrowthConstant * (n : Real) ^ 2 :=
  (vertexPoissonBarrierBound_le_explicit n hn).trans
    (vertexExplicitPoissonBarrierBound_le_growth n hn)

theorem facePoissonBarrierBound_le_growth (n : Nat) :
    facePoissonBarrierBound n ≤
      vertexBarrierGrowthConstant * (n : Real) ^ 2 := by
  calc
    facePoissonBarrierBound n ≤ faceExplicitPoissonBarrierBound n :=
      facePoissonBarrierBound_le_explicit n
    _ = (1 / 2 : Real) * (n : Real) ^ 2 := by
      unfold faceExplicitPoissonBarrierBound
      ring
    _ ≤ vertexBarrierGrowthConstant * (n : Real) ^ 2 :=
      mul_le_mul_of_nonneg_right half_le_vertexBarrierGrowthConstant
        (sq_nonneg _)

theorem vertexTargetConsistencyError_nonneg
    (n : Nat) (hn : 0 < n)
    (target : Option (FKIsingSquareFullVertexNode n) → Real) :
    0 ≤ vertexTargetConsistencyError n hn target := by
  unfold vertexTargetConsistencyError
  exact add_nonneg
    (isingFiniteWeightedBoundaryError_nonneg
      (vertexDirichletBoundary n) (vertexGhostPrimitive n hn) target)
    (mul_nonneg
      (isingFiniteWeightedTargetResidual_nonneg
        (vertexGhostConductance n) (vertexDirichletBoundary n) target)
      (isingFiniteWeightedPoissonBarrierBound_nonneg
        (vertexGhostGraph n) (vertexGhostConductance n)
        (vertexDirichletBoundary n) (vertexGhostConductance_nonneg n)
        (vertexGhostConductance_pos_of_adj n)
        (vertexGhost_reaches_boundary n)))

theorem faceTargetConsistencyError_nonneg
    (n : Nat) (hn : 0 < n)
    (target : Option (FKIsingSquareFullFaceNode n) → Real) :
    0 ≤ faceTargetConsistencyError n hn target := by
  unfold faceTargetConsistencyError
  exact add_nonneg
    (isingFiniteWeightedBoundaryError_nonneg
      (faceDirichletBoundary n) (faceGhostPrimitive n hn) target)
    (mul_nonneg
      (isingFiniteWeightedTargetResidual_nonneg
        (faceGhostConductance n) (faceDirichletBoundary n) target)
      (isingFiniteWeightedPoissonBarrierBound_nonneg
        (faceGhostGraph n) (faceGhostConductance n)
        (faceDirichletBoundary n) (faceGhostConductance_nonneg n)
        (faceGhostConductance_pos_of_adj n)
        (faceGhost_reaches_boundary n)))




theorem sampledWeightedConsistency_tendsto_of_quadraticRates
    (N : Nat → Nat) (hN : ∀ k, 0 < N k)
    (vertexEmbedding : ∀ k,
      FKIsingSquareFullVertexNode (N k) → Complex)
    (faceEmbedding : ∀ k,
      FKIsingSquareFullFaceNode (N k) → Complex)
    (Phi : Complex → Complex)
    (boundaryRate residualRate : Nat → Real)
    (hboundary_nonneg : ∀ k, 0 ≤ boundaryRate k)
    (hresidual_nonneg : ∀ k, 0 ≤ residualRate k)
    (hvertexFixed : ∀ k x,
      fkIsingSquareFullVertexFixedBoundary (N k) x →
        |0 - (Phi (vertexEmbedding k x)).im| ≤ boundaryRate k)
    (hfaceFixed : ∀ k c,
      fkIsingSquareFullFaceFixedBoundary (N k) c →
        |1 - (Phi (faceEmbedding k c)).im| ≤ boundaryRate k)
    (hvertexRobin : ∀ k x,
      ¬ fkIsingSquareFullVertexFixedBoundary (N k) x →
        |isingFiniteGraphLaplacian
            (fkIsingSquareFullVertexGraph (N k))
            (fun y ↦ (Phi (vertexEmbedding k y)).im) x +
          isingFermionicGhostRate
              (fkIsingSquareFullVertexGhostMultiplicity (N k)) x *
            (1 - (Phi (vertexEmbedding k x)).im)| ≤ residualRate k)
    (hfaceRobin : ∀ k c,
      ¬ fkIsingSquareFullFaceFixedBoundary (N k) c →
        |isingFiniteGraphLaplacian
            (fkIsingSquareFullFaceGraph (N k))
            (fun d ↦ (Phi (faceEmbedding k d)).im) c +
          isingFermionicGhostRate
              (fkIsingSquareFullFaceGhostMultiplicity (N k)) c *
            (0 - (Phi (faceEmbedding k c)).im)| ≤ residualRate k)
    (hboundary_tendsto : Tendsto boundaryRate atTop (nhds 0))
    (hscaledResidual_tendsto : Tendsto
      (fun k ↦ residualRate k * (N k : Real) ^ 2) atTop (nhds 0)) :
    Tendsto (fun k ↦
      max
        (vertexTargetConsistencyError (N k) (hN k)
          (vertexSampledImaginaryTarget (N k) (vertexEmbedding k) Phi))
        (faceTargetConsistencyError (N k) (hN k)
          (faceSampledImaginaryTarget (N k) (faceEmbedding k) Phi)))
      atTop (nhds 0) := by
  let upper : Nat → Real := fun k ↦
    boundaryRate k + vertexBarrierGrowthConstant *
      (residualRate k * (N k : Real) ^ 2)
  have hvertex (k : Nat) :
      vertexTargetConsistencyError (N k) (hN k)
          (vertexSampledImaginaryTarget (N k) (vertexEmbedding k) Phi) ≤
        upper k := by
    unfold vertexTargetConsistencyError upper
    calc
      vertexBoundaryConsistencyError (N k) (hN k)
            (vertexSampledImaginaryTarget (N k) (vertexEmbedding k) Phi) +
          vertexTargetResidual (N k)
              (vertexSampledImaginaryTarget (N k) (vertexEmbedding k) Phi) *
            vertexPoissonBarrierBound (N k) ≤
        boundaryRate k + residualRate k *
            (vertexBarrierGrowthConstant * (N k : Real) ^ 2) := by
          apply add_le_add
          · exact vertexSampled_boundaryConsistencyError_le
              (N k) (hN k) (vertexEmbedding k) Phi (boundaryRate k)
              (hboundary_nonneg k) (hvertexFixed k)
          · exact mul_le_mul
              (vertexSampled_targetResidual_le
                (N k) (vertexEmbedding k) Phi (residualRate k)
                (hresidual_nonneg k) (hvertexRobin k))
              (vertexPoissonBarrierBound_le_growth (N k) (hN k))
              (isingFiniteWeightedPoissonBarrierBound_nonneg
                (vertexGhostGraph (N k)) (vertexGhostConductance (N k))
                (vertexDirichletBoundary (N k))
                (vertexGhostConductance_nonneg (N k))
                (vertexGhostConductance_pos_of_adj (N k))
                (vertexGhost_reaches_boundary (N k)))
              (hresidual_nonneg k)
      _ = boundaryRate k + vertexBarrierGrowthConstant *
          (residualRate k * (N k : Real) ^ 2) := by ring
  have hface (k : Nat) :
      faceTargetConsistencyError (N k) (hN k)
          (faceSampledImaginaryTarget (N k) (faceEmbedding k) Phi) ≤
        upper k := by
    unfold faceTargetConsistencyError upper
    calc
      faceBoundaryConsistencyError (N k) (hN k)
            (faceSampledImaginaryTarget (N k) (faceEmbedding k) Phi) +
          faceTargetResidual (N k)
              (faceSampledImaginaryTarget (N k) (faceEmbedding k) Phi) *
            facePoissonBarrierBound (N k) ≤
        boundaryRate k + residualRate k *
            (vertexBarrierGrowthConstant * (N k : Real) ^ 2) := by
          apply add_le_add
          · exact faceSampled_boundaryConsistencyError_le
              (N k) (hN k) (faceEmbedding k) Phi (boundaryRate k)
              (hboundary_nonneg k) (hfaceFixed k)
          · exact mul_le_mul
              (faceSampled_targetResidual_le
                (N k) (faceEmbedding k) Phi (residualRate k)
                (hresidual_nonneg k) (hfaceRobin k))
              (facePoissonBarrierBound_le_growth (N k))
              (isingFiniteWeightedPoissonBarrierBound_nonneg
                (faceGhostGraph (N k)) (faceGhostConductance (N k))
                (faceDirichletBoundary (N k))
                (faceGhostConductance_nonneg (N k))
                (faceGhostConductance_pos_of_adj (N k))
                (faceGhost_reaches_boundary (N k)))
              (hresidual_nonneg k)
      _ = boundaryRate k + vertexBarrierGrowthConstant *
          (residualRate k * (N k : Real) ^ 2) := by ring
  have hnonneg (k : Nat) : 0 ≤
      max
        (vertexTargetConsistencyError (N k) (hN k)
          (vertexSampledImaginaryTarget (N k) (vertexEmbedding k) Phi))
        (faceTargetConsistencyError (N k) (hN k)
          (faceSampledImaginaryTarget (N k) (faceEmbedding k) Phi)) :=
    (vertexTargetConsistencyError_nonneg (N k) (hN k)
      (vertexSampledImaginaryTarget (N k) (vertexEmbedding k) Phi)).trans
        (le_max_left _ _)
  have hupper (k : Nat) :
      max
        (vertexTargetConsistencyError (N k) (hN k)
          (vertexSampledImaginaryTarget (N k) (vertexEmbedding k) Phi))
        (faceTargetConsistencyError (N k) (hN k)
          (faceSampledImaginaryTarget (N k) (faceEmbedding k) Phi)) ≤
      upper k := max_le (hvertex k) (hface k)
  have hupper_tendsto : Tendsto upper atTop (nhds 0) := by
    have hscaled : Tendsto (fun k ↦ vertexBarrierGrowthConstant *
        (residualRate k * (N k : Real) ^ 2)) atTop (nhds 0) := by
      simpa using
        (tendsto_const_nhds.mul hscaledResidual_tendsto)
    simpa [upper] using hboundary_tendsto.add hscaled
  exact squeeze_zero hnonneg hupper hupper_tendsto



theorem sampledWeightedConsistency_tendsto_of_meshAndQuadraticResidual
    (N : Nat → Nat) (hN : ∀ k, 0 < N k)
    (vertexEmbedding : ∀ k,
      FKIsingSquareFullVertexNode (N k) → Complex)
    (faceEmbedding : ∀ k,
      FKIsingSquareFullFaceNode (N k) → Complex)
    (Phi : Complex → Complex)
    (mesh residualRate : Nat → Real) (L : Real)
    (hmesh_nonneg : ∀ k, 0 ≤ mesh k) (hL : 0 ≤ L)
    (hresidual_nonneg : ∀ k, 0 ≤ residualRate k)
    (hvertexFixed : ∀ k x,
      fkIsingSquareFullVertexFixedBoundary (N k) x →
        |0 - (Phi (vertexEmbedding k x)).im| ≤ L * mesh k)
    (hfaceFixed : ∀ k c,
      fkIsingSquareFullFaceFixedBoundary (N k) c →
        |1 - (Phi (faceEmbedding k c)).im| ≤ L * mesh k)
    (hvertexRobin : ∀ k x,
      ¬ fkIsingSquareFullVertexFixedBoundary (N k) x →
        |isingFiniteGraphLaplacian
            (fkIsingSquareFullVertexGraph (N k))
            (fun y ↦ (Phi (vertexEmbedding k y)).im) x +
          isingFermionicGhostRate
              (fkIsingSquareFullVertexGhostMultiplicity (N k)) x *
            (1 - (Phi (vertexEmbedding k x)).im)| ≤ residualRate k)
    (hfaceRobin : ∀ k c,
      ¬ fkIsingSquareFullFaceFixedBoundary (N k) c →
        |isingFiniteGraphLaplacian
            (fkIsingSquareFullFaceGraph (N k))
            (fun d ↦ (Phi (faceEmbedding k d)).im) c +
          isingFermionicGhostRate
              (fkIsingSquareFullFaceGhostMultiplicity (N k)) c *
            (0 - (Phi (faceEmbedding k c)).im)| ≤ residualRate k)
    (hmesh_tendsto : Tendsto mesh atTop (nhds 0))
    (hscaledResidual_tendsto : Tendsto
      (fun k ↦ residualRate k * (N k : Real) ^ 2) atTop (nhds 0)) :
    Tendsto (fun k ↦
      max
        (vertexTargetConsistencyError (N k) (hN k)
          (vertexSampledImaginaryTarget (N k) (vertexEmbedding k) Phi))
        (faceTargetConsistencyError (N k) (hN k)
          (faceSampledImaginaryTarget (N k) (faceEmbedding k) Phi)))
      atTop (nhds 0) := by
  apply sampledWeightedConsistency_tendsto_of_quadraticRates
    N hN vertexEmbedding faceEmbedding Phi (fun k ↦ L * mesh k)
      residualRate
  · intro k
    exact mul_nonneg hL (hmesh_nonneg k)
  · exact hresidual_nonneg
  · exact hvertexFixed
  · exact hfaceFixed
  · exact hvertexRobin
  · exact hfaceRobin
  · simpa using tendsto_const_nhds.mul hmesh_tendsto
  · exact hscaledResidual_tendsto





theorem physicalIncidence_sampledTarget_error_le
    (n : Nat) (hn : 0 < n)
    (vertexEmbedding : FKIsingSquareFullVertexNode n → Complex)
    (faceEmbedding : FKIsingSquareFullFaceNode n → Complex)
    (Phi : Complex → Complex)
    (e : FKIsingSquareInteriorRadialIncidence n hn) (target : Real) :
    |(fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive
          (fkIsingSquareInteriorRadialEndpoint n hn e) - target| ≤
        max
          (vertexTargetConsistencyError n hn
            (vertexSampledImaginaryTarget n vertexEmbedding Phi))
          (faceTargetConsistencyError n hn
            (faceSampledImaginaryTarget n faceEmbedding Phi)) +
          max
            |(Phi (vertexEmbedding
              (fkIsingSquareInteriorRadialEndpoint n hn e))).im - target|
            |(Phi (faceEmbedding
              (fkIsingSquareFullFaceOfRadialIncidence n hn e))).im - target| ∧
      |(fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (fkIsingSquareFullFaceOfRadialIncidence n hn e) - target| ≤
        max
          (vertexTargetConsistencyError n hn
            (vertexSampledImaginaryTarget n vertexEmbedding Phi))
          (faceTargetConsistencyError n hn
            (faceSampledImaginaryTarget n faceEmbedding Phi)) +
          max
            |(Phi (vertexEmbedding
              (fkIsingSquareInteriorRadialEndpoint n hn e))).im - target|
            |(Phi (faceEmbedding
              (fkIsingSquareFullFaceOfRadialIncidence n hn e))).im - target| := by
  let vertexValue : Real := (Phi (vertexEmbedding
    (fkIsingSquareInteriorRadialEndpoint n hn e))).im
  let faceValue : Real := (Phi (faceEmbedding
    (fkIsingSquareFullFaceOfRadialIncidence n hn e))).im
  let consistency : Real := max
    (vertexTargetConsistencyError n hn
      (vertexSampledImaginaryTarget n vertexEmbedding Phi))
    (faceTargetConsistencyError n hn
      (faceSampledImaginaryTarget n faceEmbedding Phi))
  let mismatch : Real := max |vertexValue - target| |faceValue - target|
  have hvertexSample :
      |vertexDirichlet n hn
          (some (fkIsingSquareInteriorRadialEndpoint n hn e)) - vertexValue| ≤
        vertexTargetConsistencyError n hn
          (vertexSampledImaginaryTarget n vertexEmbedding Phi) := by
    simpa [vertexValue, vertexSampledImaginaryTarget] using
      (vertexDirichlet_target_error_le n hn
        (vertexSampledImaginaryTarget n vertexEmbedding Phi)
        (some (fkIsingSquareInteriorRadialEndpoint n hn e)))
  have hfaceSample :
      |faceDirichlet n hn
          (some (fkIsingSquareFullFaceOfRadialIncidence n hn e)) - faceValue| ≤
        faceTargetConsistencyError n hn
          (faceSampledImaginaryTarget n faceEmbedding Phi) := by
    simpa [faceValue, faceSampledImaginaryTarget] using
      (faceDirichlet_target_error_le n hn
        (faceSampledImaginaryTarget n faceEmbedding Phi)
        (some (fkIsingSquareFullFaceOfRadialIncidence n hn e)))
  have hvertexTarget :
      |vertexDirichlet n hn
          (some (fkIsingSquareInteriorRadialEndpoint n hn e)) - target| ≤
        consistency + mismatch := by
    calc
      |vertexDirichlet n hn
          (some (fkIsingSquareInteriorRadialEndpoint n hn e)) - target| =
        |(vertexDirichlet n hn
            (some (fkIsingSquareInteriorRadialEndpoint n hn e)) -
              vertexValue) + (vertexValue - target)| := by ring_nf
      _ ≤ |vertexDirichlet n hn
              (some (fkIsingSquareInteriorRadialEndpoint n hn e)) -
            vertexValue| + |vertexValue - target| := abs_add_le _ _
      _ ≤ consistency + mismatch := add_le_add
        (hvertexSample.trans (le_max_left _ _)) (le_max_left _ _)
  have hfaceTarget :
      |faceDirichlet n hn
          (some (fkIsingSquareFullFaceOfRadialIncidence n hn e)) - target| ≤
        consistency + mismatch := by
    calc
      |faceDirichlet n hn
          (some (fkIsingSquareFullFaceOfRadialIncidence n hn e)) - target| =
        |(faceDirichlet n hn
            (some (fkIsingSquareFullFaceOfRadialIncidence n hn e)) -
              faceValue) + (faceValue - target)| := by ring_nf
      _ ≤ |faceDirichlet n hn
              (some (fkIsingSquareFullFaceOfRadialIncidence n hn e)) -
            faceValue| + |faceValue - target| := abs_add_le _ _
      _ ≤ consistency + mismatch := add_le_add
        (hfaceSample.trans (le_max_right _ _)) (le_max_right _ _)
  simpa [consistency, mismatch, vertexValue, faceValue] using
    (physicalIncidence_close_of_dirichlet_close n hn e target
      (consistency + mismatch) hvertexTarget hfaceTarget)



theorem physicalIncidence_uniform_convergence_of_sampledConsistency
    (N : Nat → Nat) (hN : ∀ k, 0 < N k)
    (vertexEmbedding : ∀ k,
      FKIsingSquareFullVertexNode (N k) → Complex)
    (faceEmbedding : ∀ k,
      FKIsingSquareFullFaceNode (N k) → Complex)
    (Phi : Complex → Complex)
    (incidenceTarget : ∀ k,
      FKIsingSquareInteriorRadialIncidence (N k) (hN k) → Real)
    (vertexMismatch faceMismatch : Nat → Real)
    (hvertexMismatch : ∀ k e,
      |(Phi (vertexEmbedding k
        (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e))).im -
          incidenceTarget k e| ≤ vertexMismatch k)
    (hfaceMismatch : ∀ k e,
      |(Phi (faceEmbedding k
        (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e))).im -
          incidenceTarget k e| ≤ faceMismatch k)
    (hconsistency : Tendsto (fun k ↦
      max
        (vertexTargetConsistencyError (N k) (hN k)
          (vertexSampledImaginaryTarget (N k) (vertexEmbedding k) Phi))
        (faceTargetConsistencyError (N k) (hN k)
          (faceSampledImaginaryTarget (N k) (faceEmbedding k) Phi)))
      atTop (nhds 0))
    (hvertexMismatch_tendsto : Tendsto vertexMismatch atTop (nhds 0))
    (hfaceMismatch_tendsto : Tendsto faceMismatch atTop (nhds 0)) :
    ∀ eta : Real, 0 < eta → ∀ᶠ k in atTop,
      ∀ e : FKIsingSquareInteriorRadialIncidence (N k) (hN k),
        |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (N k) (hN k)).vertexPrimitive
            (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e) -
              incidenceTarget k e| < eta ∧
          |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (N k) (hN k)).facePrimitive
            (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e) -
              incidenceTarget k e| < eta := by
  intro eta heta
  have hmismatch : Tendsto (fun k ↦
      max (vertexMismatch k) (faceMismatch k)) atTop (nhds 0) := by
    simpa using hvertexMismatch_tendsto.max hfaceMismatch_tendsto
  have htotal : Tendsto (fun k ↦
      max
        (vertexTargetConsistencyError (N k) (hN k)
          (vertexSampledImaginaryTarget (N k) (vertexEmbedding k) Phi))
        (faceTargetConsistencyError (N k) (hN k)
          (faceSampledImaginaryTarget (N k) (faceEmbedding k) Phi)) +
        max (vertexMismatch k) (faceMismatch k)) atTop (nhds 0) := by
    simpa using hconsistency.add hmismatch
  have hevent := htotal (Iio_mem_nhds heta)
  filter_upwards [hevent] with k hk
  intro e
  have h := physicalIncidence_sampledTarget_error_le
    (N k) (hN k) (vertexEmbedding k) (faceEmbedding k) Phi e
    (incidenceTarget k e)
  have hmismatchBound :
      max
          |(Phi (vertexEmbedding k
            (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e))).im -
              incidenceTarget k e|
          |(Phi (faceEmbedding k
            (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e))).im -
              incidenceTarget k e| ≤
        max (vertexMismatch k) (faceMismatch k) :=
    max_le
      ((hvertexMismatch k e).trans (le_max_left _ _))
      ((hfaceMismatch k e).trans (le_max_right _ _))
  constructor
  · refine lt_of_le_of_lt (h.1.trans ?_) hk
    exact add_le_add (le_refl _) hmismatchBound
  · refine lt_of_le_of_lt (h.2.trans ?_) hk
    exact add_le_add (le_refl _) hmismatchBound




theorem physicalIncidence_uniform_convergence_of_lipschitzSamples
    (N : Nat → Nat) (hN : ∀ k, 0 < N k)
    (vertexEmbedding : ∀ k,
      FKIsingSquareFullVertexNode (N k) → Complex)
    (faceEmbedding : ∀ k,
      FKIsingSquareFullFaceNode (N k) → Complex)
    (Phi : Complex → Complex) (lipschitzConstant : NNReal)
    (hPhi : LipschitzWith lipschitzConstant (fun z ↦ (Phi z).im))
    (mesh : Nat → Real)
    (embeddingCompatibility : FullSquareCoordinateEmbeddingCompatibility
      N vertexEmbedding faceEmbedding mesh)
    (hconsistency : Tendsto (fun k ↦
      max
        (vertexTargetConsistencyError (N k) (hN k)
          (vertexSampledImaginaryTarget (N k) (vertexEmbedding k) Phi))
        (faceTargetConsistencyError (N k) (hN k)
          (faceSampledImaginaryTarget (N k) (faceEmbedding k) Phi)))
      atTop (nhds 0))
    (hmesh_tendsto : Tendsto mesh atTop (nhds 0)) :
    ∀ eta : Real, 0 < eta → ∀ᶠ k in atTop,
      ∀ e : FKIsingSquareInteriorRadialIncidence (N k) (hN k),
        |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (N k) (hN k)).vertexPrimitive
            (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e) -
              (Phi (vertexEmbedding k
                (fkIsingSquareInteriorRadialEndpoint
                  (N k) (hN k) e))).im| < eta ∧
          |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (N k) (hN k)).facePrimitive
            (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e) -
              (Phi (vertexEmbedding k
                (fkIsingSquareInteriorRadialEndpoint
                  (N k) (hN k) e))).im| < eta := by
  apply physicalIncidence_uniform_convergence_of_sampledConsistency
    N hN vertexEmbedding faceEmbedding Phi
    (fun k e ↦ (Phi (vertexEmbedding k
      (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e))).im)
    (fun _ ↦ 0) (fun k ↦ (lipschitzConstant : Real) * mesh k)
  · intro k e
    simp
  · intro k e
    rw [← Real.dist_eq]
    calc
      dist
          (Phi (faceEmbedding k
            (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e))).im
          (Phi (vertexEmbedding k
            (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e))).im ≤
        lipschitzConstant *
          dist
            (faceEmbedding k
              (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e))
            (vertexEmbedding k
              (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e)) :=
        hPhi.dist_le_mul _ _
      _ ≤ lipschitzConstant * mesh k :=
        mul_le_mul_of_nonneg_left
          (embeddingCompatibility.incidenceDistance (hN := hN) k e)
          lipschitzConstant.2
  · exact hconsistency
  · exact tendsto_const_nhds
  · simpa using tendsto_const_nhds.mul hmesh_tendsto





theorem physicalIncidence_uniform_convergence_of_meshAndQuadraticResidual
    (N : Nat → Nat) (hN : ∀ k, 0 < N k)
    (vertexEmbedding : ∀ k,
      FKIsingSquareFullVertexNode (N k) → Complex)
    (faceEmbedding : ∀ k,
      FKIsingSquareFullFaceNode (N k) → Complex)
    (Phi : Complex → Complex)
    (mesh residualRate : Nat → Real) (boundaryL : Real)
    (lipschitzConstant : NNReal)
    (hmesh_nonneg : ∀ k, 0 ≤ mesh k) (hboundaryL : 0 ≤ boundaryL)
    (hresidual_nonneg : ∀ k, 0 ≤ residualRate k)
    (hvertexFixed : ∀ k x,
      fkIsingSquareFullVertexFixedBoundary (N k) x →
        |0 - (Phi (vertexEmbedding k x)).im| ≤ boundaryL * mesh k)
    (hfaceFixed : ∀ k c,
      fkIsingSquareFullFaceFixedBoundary (N k) c →
        |1 - (Phi (faceEmbedding k c)).im| ≤ boundaryL * mesh k)
    (hvertexRobin : ∀ k x,
      ¬ fkIsingSquareFullVertexFixedBoundary (N k) x →
        |isingFiniteGraphLaplacian
            (fkIsingSquareFullVertexGraph (N k))
            (fun y ↦ (Phi (vertexEmbedding k y)).im) x +
          isingFermionicGhostRate
              (fkIsingSquareFullVertexGhostMultiplicity (N k)) x *
            (1 - (Phi (vertexEmbedding k x)).im)| ≤ residualRate k)
    (hfaceRobin : ∀ k c,
      ¬ fkIsingSquareFullFaceFixedBoundary (N k) c →
        |isingFiniteGraphLaplacian
            (fkIsingSquareFullFaceGraph (N k))
            (fun d ↦ (Phi (faceEmbedding k d)).im) c +
          isingFermionicGhostRate
              (fkIsingSquareFullFaceGhostMultiplicity (N k)) c *
            (0 - (Phi (faceEmbedding k c)).im)| ≤ residualRate k)
    (hPhi : LipschitzWith lipschitzConstant (fun z ↦ (Phi z).im))
    (embeddingCompatibility : FullSquareCoordinateEmbeddingCompatibility
      N vertexEmbedding faceEmbedding mesh)
    (hmesh_tendsto : Tendsto mesh atTop (nhds 0))
    (hscaledResidual_tendsto : Tendsto
      (fun k ↦ residualRate k * (N k : Real) ^ 2) atTop (nhds 0)) :
    ∀ eta : Real, 0 < eta → ∀ᶠ k in atTop,
      ∀ e : FKIsingSquareInteriorRadialIncidence (N k) (hN k),
        |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (N k) (hN k)).vertexPrimitive
            (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e) -
              (Phi (vertexEmbedding k
                (fkIsingSquareInteriorRadialEndpoint
                  (N k) (hN k) e))).im| < eta ∧
          |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (N k) (hN k)).facePrimitive
            (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e) -
              (Phi (vertexEmbedding k
                (fkIsingSquareInteriorRadialEndpoint
                  (N k) (hN k) e))).im| < eta := by
  apply physicalIncidence_uniform_convergence_of_lipschitzSamples
    N hN vertexEmbedding faceEmbedding Phi lipschitzConstant hPhi mesh
      embeddingCompatibility
  · exact sampledWeightedConsistency_tendsto_of_meshAndQuadraticResidual
      N hN vertexEmbedding faceEmbedding Phi mesh residualRate boundaryL
      hmesh_nonneg hboundaryL hresidual_nonneg hvertexFixed hfaceFixed
      hvertexRobin hfaceRobin hmesh_tendsto hscaledResidual_tendsto
  · exact hmesh_tendsto




theorem physicalIncidence_uniform_convergence_of_scaledMeshAndQuadraticResidual
    (N : Nat → Nat) (hN : ∀ k, 0 < N k)
    (Phi : Complex → Complex)
    (mesh residualRate : Nat → Real) (boundaryL : Real)
    (lipschitzConstant : NNReal)
    (hmesh_nonneg : ∀ k, 0 ≤ mesh k) (hboundaryL : 0 ≤ boundaryL)
    (hresidual_nonneg : ∀ k, 0 ≤ residualRate k)
    (hvertexFixed : ∀ k x,
      fkIsingSquareFullVertexFixedBoundary (N k) x →
        |0 - (Phi (fullSquareScaledVertexEmbedding
          (N k) (mesh k) x)).im| ≤ boundaryL * mesh k)
    (hfaceFixed : ∀ k c,
      fkIsingSquareFullFaceFixedBoundary (N k) c →
        |1 - (Phi (fullSquareScaledFaceEmbedding
          (N k) (mesh k) c)).im| ≤ boundaryL * mesh k)
    (hvertexRobin : ∀ k x,
      ¬ fkIsingSquareFullVertexFixedBoundary (N k) x →
        |isingFiniteGraphLaplacian
            (fkIsingSquareFullVertexGraph (N k))
            (fun y ↦ (Phi (fullSquareScaledVertexEmbedding
              (N k) (mesh k) y)).im) x +
          isingFermionicGhostRate
              (fkIsingSquareFullVertexGhostMultiplicity (N k)) x *
            (1 - (Phi (fullSquareScaledVertexEmbedding
              (N k) (mesh k) x)).im)| ≤ residualRate k)
    (hfaceRobin : ∀ k c,
      ¬ fkIsingSquareFullFaceFixedBoundary (N k) c →
        |isingFiniteGraphLaplacian
            (fkIsingSquareFullFaceGraph (N k))
            (fun d ↦ (Phi (fullSquareScaledFaceEmbedding
              (N k) (mesh k) d)).im) c +
          isingFermionicGhostRate
              (fkIsingSquareFullFaceGhostMultiplicity (N k)) c *
            (0 - (Phi (fullSquareScaledFaceEmbedding
              (N k) (mesh k) c)).im)| ≤ residualRate k)
    (hPhi : LipschitzWith lipschitzConstant (fun z ↦ (Phi z).im))
    (hmesh_tendsto : Tendsto mesh atTop (nhds 0))
    (hscaledResidual_tendsto : Tendsto
      (fun k ↦ residualRate k * (N k : Real) ^ 2) atTop (nhds 0)) :
    ∀ eta : Real, 0 < eta → ∀ᶠ k in atTop,
      ∀ e : FKIsingSquareInteriorRadialIncidence (N k) (hN k),
        |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (N k) (hN k)).vertexPrimitive
            (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e) -
              (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k)
                (fkIsingSquareInteriorRadialEndpoint
                  (N k) (hN k) e))).im| < eta ∧
          |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (N k) (hN k)).facePrimitive
            (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e) -
              (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k)
                (fkIsingSquareInteriorRadialEndpoint
                  (N k) (hN k) e))).im| < eta := by
  exact physicalIncidence_uniform_convergence_of_meshAndQuadraticResidual
    N hN
    (fun k ↦ fullSquareScaledVertexEmbedding (N k) (mesh k))
    (fun k ↦ fullSquareScaledFaceEmbedding (N k) (mesh k))
    Phi mesh residualRate boundaryL lipschitzConstant hmesh_nonneg
    hboundaryL hresidual_nonneg hvertexFixed hfaceFixed hvertexRobin
    hfaceRobin hPhi (fullSquareScaledEmbeddingCompatibility N mesh hmesh_nonneg)
    hmesh_tendsto hscaledResidual_tendsto




theorem physicalIncidence_uniform_convergence_of_scaledExactBoundaryAndLaplacian
    (N : Nat → Nat) (hN : ∀ k, 0 < N k)
    (Phi : Complex → Complex) (mesh laplacianRate : Nat → Real)
    (lipschitzConstant : NNReal)
    (hmesh_nonneg : ∀ k, 0 ≤ mesh k)
    (hlaplacian_nonneg : ∀ k, 0 ≤ laplacianRate k)
    (hvertexFixed : ∀ k x,
      fkIsingSquareFullVertexFixedBoundary (N k) x →
        (Phi (fullSquareScaledVertexEmbedding
          (N k) (mesh k) x)).im = 0)
    (hfaceFixed : ∀ k c,
      fkIsingSquareFullFaceFixedBoundary (N k) c →
        (Phi (fullSquareScaledFaceEmbedding
          (N k) (mesh k) c)).im = 1)
    (hvertexFree : ∀ k x,
      ¬ fkIsingSquareFullVertexFixedBoundary (N k) x →
      0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x →
        (Phi (fullSquareScaledVertexEmbedding
          (N k) (mesh k) x)).im = 1)
    (hfaceFree : ∀ k c,
      ¬ fkIsingSquareFullFaceFixedBoundary (N k) c →
      0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c →
        (Phi (fullSquareScaledFaceEmbedding
          (N k) (mesh k) c)).im = 0)
    (hvertexLaplacian : ∀ k x,
      ¬ fkIsingSquareFullVertexFixedBoundary (N k) x →
        |isingFiniteGraphLaplacian
          (fkIsingSquareFullVertexGraph (N k))
          (fun y ↦ (Phi (fullSquareScaledVertexEmbedding
            (N k) (mesh k) y)).im) x| ≤ laplacianRate k)
    (hfaceLaplacian : ∀ k c,
      ¬ fkIsingSquareFullFaceFixedBoundary (N k) c →
        |isingFiniteGraphLaplacian
          (fkIsingSquareFullFaceGraph (N k))
          (fun d ↦ (Phi (fullSquareScaledFaceEmbedding
            (N k) (mesh k) d)).im) c| ≤ laplacianRate k)
    (hPhi : LipschitzWith lipschitzConstant (fun z ↦ (Phi z).im))
    (hmesh_tendsto : Tendsto mesh atTop (nhds 0))
    (hscaledLaplacian_tendsto : Tendsto
      (fun k ↦ laplacianRate k * (N k : Real) ^ 2) atTop (nhds 0)) :
    ∀ eta : Real, 0 < eta → ∀ᶠ k in atTop,
      ∀ e : FKIsingSquareInteriorRadialIncidence (N k) (hN k),
        |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (N k) (hN k)).vertexPrimitive
            (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e) -
              (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k)
                (fkIsingSquareInteriorRadialEndpoint
                  (N k) (hN k) e))).im| < eta ∧
          |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (N k) (hN k)).facePrimitive
            (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e) -
              (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k)
                (fkIsingSquareInteriorRadialEndpoint
                  (N k) (hN k) e))).im| < eta := by
  apply physicalIncidence_uniform_convergence_of_scaledMeshAndQuadraticResidual
    N hN Phi mesh laplacianRate 0 lipschitzConstant hmesh_nonneg
      (le_refl 0) hlaplacian_nonneg
  · intro k x hx
    simp [hvertexFixed k x hx]
  · intro k c hc
    simp [hfaceFixed k c hc]
  · intro k x hx
    simpa using
      (vertexSampled_robinResidual_le_of_laplacian_and_trace
        (N k) (fullSquareScaledVertexEmbedding (N k) (mesh k)) Phi
        (laplacianRate k) 0 (le_refl 0) (hvertexLaplacian k)
        (fun y hyFixed hy ↦ by simp [hvertexFree k y hyFixed hy]) x hx)
  · intro k c hc
    simpa using
      (faceSampled_robinResidual_le_of_laplacian_and_trace
        (N k) (fullSquareScaledFaceEmbedding (N k) (mesh k)) Phi
        (laplacianRate k) 0 (le_refl 0) (hfaceLaplacian k)
        (fun d hdFixed hd ↦ by simp [hfaceFree k d hdFixed hd]) c hc)
  · exact hPhi
  · exact hmesh_tendsto
  · exact hscaledLaplacian_tendsto

end FKIsingSquareBoundaryLayerCoordinateOneForm

end

end StatMech.Universality
