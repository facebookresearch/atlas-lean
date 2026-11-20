/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicBoundaryProjectedPrimitiveConvergence









namespace StatMech.Universality

open Filter
open Finset SimpleGraph
open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem isingFiniteGraphLaplacian_eq_of_eq_on_neighbors
    {V : Type*} [Fintype V] (G : SimpleGraph V) (f g : V -> Real) (x : V)
    (hx : f x = g x) (hneighbor : forall y, G.Adj x y -> f y = g y) :
    isingFiniteGraphLaplacian G f x = isingFiniteGraphLaplacian G g x := by
  classical
  unfold isingFiniteGraphLaplacian
  apply Finset.sum_congr rfl
  intro y hy
  rw [hx, hneighbor y ((mem_neighborFinset G x y).mp hy)]

def vertexMarkedBoundaryEndpoint (n : Nat)
    (x : FKIsingSquareFullVertexNode n) : Prop :=
  fkIsingSquareFullVertexFixedBoundary n x /\
    0 < fkIsingSquareFullVertexGhostMultiplicity n x

def faceMarkedBoundaryEndpoint (n : Nat)
    (c : FKIsingSquareFullFaceNode n) : Prop :=
  fkIsingSquareFullFaceFixedBoundary n c /\
    0 < fkIsingSquareFullFaceGhostMultiplicity n c



noncomputable def vertexMarkedEndpointClampedSampledTarget
    (n : Nat) (embedding : FKIsingSquareFullVertexNode n -> Complex)
    (Phi : Complex -> Complex) :
    Option (FKIsingSquareFullVertexNode n) -> Real :=
  isingFiniteGhostExtension 1
    (isingBoundaryClamp (vertexMarkedBoundaryEndpoint n) 0
      (fun x => (Phi (embedding x)).im))


noncomputable def faceMarkedEndpointClampedSampledTarget
    (n : Nat) (embedding : FKIsingSquareFullFaceNode n -> Complex)
    (Phi : Complex -> Complex) :
    Option (FKIsingSquareFullFaceNode n) -> Real :=
  isingFiniteGhostExtension 0
    (isingBoundaryClamp (faceMarkedBoundaryEndpoint n) 1
      (fun c => (Phi (embedding c)).im))

@[simp] theorem vertexMarkedEndpointClampedSampledTarget_of_not_fixed
    (n : Nat) (embedding : FKIsingSquareFullVertexNode n -> Complex)
    (Phi : Complex -> Complex) (x : FKIsingSquareFullVertexNode n)
    (hx : Not (fkIsingSquareFullVertexFixedBoundary n x)) :
    vertexMarkedEndpointClampedSampledTarget n embedding Phi (some x) =
      (Phi (embedding x)).im := by
  simp [vertexMarkedEndpointClampedSampledTarget, isingBoundaryClamp,
    vertexMarkedBoundaryEndpoint, hx, isingFiniteGhostExtension]

@[simp] theorem faceMarkedEndpointClampedSampledTarget_of_not_fixed
    (n : Nat) (embedding : FKIsingSquareFullFaceNode n -> Complex)
    (Phi : Complex -> Complex) (c : FKIsingSquareFullFaceNode n)
    (hc : Not (fkIsingSquareFullFaceFixedBoundary n c)) :
    faceMarkedEndpointClampedSampledTarget n embedding Phi (some c) =
      (Phi (embedding c)).im := by
  simp [faceMarkedEndpointClampedSampledTarget, isingBoundaryClamp,
    faceMarkedBoundaryEndpoint, hc, isingFiniteGhostExtension]



theorem vertexMarkedEndpointClamped_boundaryConsistencyError_le
    (n : Nat) (hn : 0 < n)
    (embedding : FKIsingSquareFullVertexNode n -> Complex)
    (Phi : Complex -> Complex) (traceBound : Real)
    (htrace_nonneg : 0 <= traceBound)
    (htrace : forall x, fkIsingSquareFullVertexFixedBoundary n x ->
      Not (0 < fkIsingSquareFullVertexGhostMultiplicity n x) ->
        |0 - (Phi (embedding x)).im| <= traceBound) :
    vertexBoundaryConsistencyError n hn
      (vertexMarkedEndpointClampedSampledTarget n embedding Phi) <=
        traceBound := by
  apply isingFiniteWeightedBoundaryError_le
    (vertexDirichletBoundary n) (vertexGhostPrimitive n hn)
    (vertexMarkedEndpointClampedSampledTarget n embedding Phi)
    traceBound htrace_nonneg
  intro z hz
  cases z with
  | none =>
      simpa [vertexGhostPrimitive, vertexMarkedEndpointClampedSampledTarget,
        isingFiniteGhostExtension] using htrace_nonneg
  | some x =>
      change fkIsingSquareFullVertexFixedBoundary n x at hz
      by_cases hghost : 0 < fkIsingSquareFullVertexGhostMultiplicity n x
      · simp [vertexGhostPrimitive, vertexMarkedEndpointClampedSampledTarget,
          isingFiniteGhostExtension, isingBoundaryClamp,
          vertexMarkedBoundaryEndpoint, hz, hghost,
          vertex_fixedBoundary_eq_zero n hn x hz, htrace_nonneg]
      · simpa [vertexGhostPrimitive, vertexMarkedEndpointClampedSampledTarget,
          isingFiniteGhostExtension, isingBoundaryClamp,
          vertexMarkedBoundaryEndpoint, hz, hghost,
          vertex_fixedBoundary_eq_zero n hn x hz] using htrace x hz hghost


theorem faceMarkedEndpointClamped_boundaryConsistencyError_le
    (n : Nat) (hn : 0 < n)
    (embedding : FKIsingSquareFullFaceNode n -> Complex)
    (Phi : Complex -> Complex) (traceBound : Real)
    (htrace_nonneg : 0 <= traceBound)
    (htrace : forall c, fkIsingSquareFullFaceFixedBoundary n c ->
      Not (0 < fkIsingSquareFullFaceGhostMultiplicity n c) ->
        |1 - (Phi (embedding c)).im| <= traceBound) :
    faceBoundaryConsistencyError n hn
      (faceMarkedEndpointClampedSampledTarget n embedding Phi) <=
        traceBound := by
  apply isingFiniteWeightedBoundaryError_le
    (faceDirichletBoundary n) (faceGhostPrimitive n hn)
    (faceMarkedEndpointClampedSampledTarget n embedding Phi)
    traceBound htrace_nonneg
  intro z hz
  cases z with
  | none =>
      simpa [faceGhostPrimitive, faceMarkedEndpointClampedSampledTarget,
        isingFiniteGhostExtension] using htrace_nonneg
  | some c =>
      change fkIsingSquareFullFaceFixedBoundary n c at hz
      by_cases hghost : 0 < fkIsingSquareFullFaceGhostMultiplicity n c
      · simp [faceGhostPrimitive, faceMarkedEndpointClampedSampledTarget,
          isingFiniteGhostExtension, isingBoundaryClamp,
          faceMarkedBoundaryEndpoint, hz, hghost,
          face_fixedBoundary_eq_one n hn c hz, htrace_nonneg]
      · simpa [faceGhostPrimitive, faceMarkedEndpointClampedSampledTarget,
          isingFiniteGhostExtension, isingBoundaryClamp,
          faceMarkedBoundaryEndpoint, hz, hghost,
          face_fixedBoundary_eq_one n hn c hz] using htrace c hz hghost



theorem vertexMarkedEndpointClamped_weightedLaplacian_eq_sampled
    (n radius : Nat) (hradius : 0 < radius)
    (embedding : FKIsingSquareFullVertexNode n -> Complex)
    (Phi : Complex -> Complex) (x : FKIsingSquareFullVertexNode n)
    (hx : Not (fkIsingSquareFullVertexFixedBoundary n x))
    (hendpoint : Not (vertexMarkedEndpointLayer n radius (some x))) :
    isingFiniteWeightedLaplacian (vertexGhostConductance n)
        (vertexMarkedEndpointClampedSampledTarget n embedding Phi) (some x) =
      isingFiniteWeightedLaplacian (vertexGhostConductance n)
        (vertexSampledImaginaryTarget n embedding Phi) (some x) := by
  have hsampled : vertexSampledImaginaryTarget n embedding Phi =
      isingFiniteGhostExtension 1 (fun y => (Phi (embedding y)).im) := by
    funext z
    cases z <;> rfl
  rw [hsampled]
  unfold vertexGhostConductance vertexMarkedEndpointClampedSampledTarget
  rw [isingFiniteGhostLaplacian_some, isingFiniteGhostLaplacian_some]
  have hxvalue : isingBoundaryClamp (vertexMarkedBoundaryEndpoint n) 0
      (fun y => (Phi (embedding y)).im) x = (Phi (embedding x)).im := by
    simp [isingBoundaryClamp, vertexMarkedBoundaryEndpoint, hx]
  have hlap := isingFiniteGraphLaplacian_eq_of_eq_on_neighbors
    (fkIsingSquareFullVertexGraph n)
    (isingBoundaryClamp (vertexMarkedBoundaryEndpoint n) 0
      (fun y => (Phi (embedding y)).im))
    (fun y => (Phi (embedding y)).im) x hxvalue
  rw [hlap]
  · rw [hxvalue]
  · intro y hxy
    have hnot : Not (vertexMarkedBoundaryEndpoint n y) := by
      intro hy
      exact hendpoint (vertex_adj_fixed_ghost_mem_markedEndpointLayer
        n radius hradius x y hxy hy.1 hy.2)
    simp [isingBoundaryClamp, hnot]



theorem faceMarkedEndpointClamped_weightedLaplacian_eq_sampled
    (n radius : Nat) (hradius : 2 <= radius)
    (embedding : FKIsingSquareFullFaceNode n -> Complex)
    (Phi : Complex -> Complex) (c : FKIsingSquareFullFaceNode n)
    (hc : Not (fkIsingSquareFullFaceFixedBoundary n c))
    (hendpoint : Not (faceMarkedEndpointLayer n radius (some c))) :
    isingFiniteWeightedLaplacian (faceGhostConductance n)
        (faceMarkedEndpointClampedSampledTarget n embedding Phi) (some c) =
      isingFiniteWeightedLaplacian (faceGhostConductance n)
        (faceSampledImaginaryTarget n embedding Phi) (some c) := by
  have hsampled : faceSampledImaginaryTarget n embedding Phi =
      isingFiniteGhostExtension 0 (fun d => (Phi (embedding d)).im) := by
    funext z
    cases z <;> rfl
  rw [hsampled]
  unfold faceGhostConductance faceMarkedEndpointClampedSampledTarget
  rw [isingFiniteGhostLaplacian_some, isingFiniteGhostLaplacian_some]
  have hcvalue : isingBoundaryClamp (faceMarkedBoundaryEndpoint n) 1
      (fun d => (Phi (embedding d)).im) c = (Phi (embedding c)).im := by
    simp [isingBoundaryClamp, faceMarkedBoundaryEndpoint, hc]
  have hlap := isingFiniteGraphLaplacian_eq_of_eq_on_neighbors
    (fkIsingSquareFullFaceGraph n)
    (isingBoundaryClamp (faceMarkedBoundaryEndpoint n) 1
      (fun d => (Phi (embedding d)).im))
    (fun d => (Phi (embedding d)).im) c hcvalue
  rw [hlap]
  · rw [hcvalue]
  · intro d hcd
    have hnot : Not (faceMarkedBoundaryEndpoint n d) := by
      intro hd
      exact hendpoint (face_adj_fixed_ghost_mem_markedEndpointLayer
        n radius hradius c d hcd hd.1 hd.2)
    simp [isingBoundaryClamp, hnot]



theorem vertexMarkedEndpointClamped_weightedLaplacian_le_of_unitRange
    (n : Nat) (embedding : FKIsingSquareFullVertexNode n -> Complex)
    (Phi : Complex -> Complex)
    (hrange : forall x,
      0 <= (Phi (embedding x)).im /\ (Phi (embedding x)).im <= 1)
    (x : FKIsingSquareFullVertexNode n) :
    |isingFiniteWeightedLaplacian (vertexGhostConductance n)
      (vertexMarkedEndpointClampedSampledTarget n embedding Phi) (some x)| <=
        4 + 3 * isingFermionicGhostCoefficient := by
  let f := isingBoundaryClamp (vertexMarkedBoundaryEndpoint n) 0
    (fun y => (Phi (embedding y)).im)
  have hfrange : forall y, 0 <= f y /\ f y <= 1 := by
    intro y
    by_cases hy : vertexMarkedBoundaryEndpoint n y
    · simp [f, isingBoundaryClamp, hy]
    · simpa [f, isingBoundaryClamp, hy] using hrange y
  have hgraph : |isingFiniteGraphLaplacian
      (fkIsingSquareFullVertexGraph n) f x| <= 4 :=
    isingFiniteGraphLaplacian_abs_le_four_of_unitRange
      (fkIsingSquareFullVertexGraph n) f x
      (fullVertex_neighbor_card_le_four n x) hfrange
  have hjump : |1 - f x| <= 1 := by
    rw [abs_le]
    constructor <;> linarith [(hfrange x).1, (hfrange x).2]
  have hrate0 : 0 <= isingFermionicGhostRate
      (fkIsingSquareFullVertexGhostMultiplicity n) x :=
    isingFermionicGhostRate_nonneg _ x
  have hrate := vertexGhostRate_le_threeCoefficient n x
  unfold vertexGhostConductance vertexMarkedEndpointClampedSampledTarget
  rw [isingFiniteGhostLaplacian_some]
  change |isingFiniteGraphLaplacian
      (fkIsingSquareFullVertexGraph n) f x +
        isingFermionicGhostRate
          (fkIsingSquareFullVertexGhostMultiplicity n) x * (1 - f x)| <= _
  calc
    |_ + _| <= |isingFiniteGraphLaplacian
        (fkIsingSquareFullVertexGraph n) f x| +
      |isingFermionicGhostRate
        (fkIsingSquareFullVertexGhostMultiplicity n) x * (1 - f x)| :=
          abs_add_le _ _
    _ <= 4 + (3 * isingFermionicGhostCoefficient) * 1 := by
      rw [abs_mul, abs_of_nonneg hrate0]
      exact add_le_add hgraph
        (mul_le_mul hrate hjump (abs_nonneg _)
          (mul_nonneg (by norm_num) isingFermionicGhostCoefficient_pos.le))
    _ = _ := by ring


theorem faceMarkedEndpointClamped_weightedLaplacian_le_of_unitRange
    (n : Nat) (embedding : FKIsingSquareFullFaceNode n -> Complex)
    (Phi : Complex -> Complex)
    (hrange : forall c,
      0 <= (Phi (embedding c)).im /\ (Phi (embedding c)).im <= 1)
    (c : FKIsingSquareFullFaceNode n) :
    |isingFiniteWeightedLaplacian (faceGhostConductance n)
      (faceMarkedEndpointClampedSampledTarget n embedding Phi) (some c)| <=
        4 + 3 * isingFermionicGhostCoefficient := by
  let f := isingBoundaryClamp (faceMarkedBoundaryEndpoint n) 1
    (fun d => (Phi (embedding d)).im)
  have hfrange : forall d, 0 <= f d /\ f d <= 1 := by
    intro d
    by_cases hd : faceMarkedBoundaryEndpoint n d
    · simp [f, isingBoundaryClamp, hd]
    · simpa [f, isingBoundaryClamp, hd] using hrange d
  have hgraph : |isingFiniteGraphLaplacian
      (fkIsingSquareFullFaceGraph n) f c| <= 4 :=
    isingFiniteGraphLaplacian_abs_le_four_of_unitRange
      (fkIsingSquareFullFaceGraph n) f c
      (fullFace_neighbor_card_le_four n c) hfrange
  have hjump : |0 - f c| <= 1 := by
    rw [abs_le]
    constructor <;> linarith [(hfrange c).1, (hfrange c).2]
  have hrate0 : 0 <= isingFermionicGhostRate
      (fkIsingSquareFullFaceGhostMultiplicity n) c :=
    isingFermionicGhostRate_nonneg _ c
  have hrate : isingFermionicGhostRate
      (fkIsingSquareFullFaceGhostMultiplicity n) c <=
        3 * isingFermionicGhostCoefficient := by
    have h := faceGhostRate_le_coefficient n c
    nlinarith [isingFermionicGhostCoefficient_pos.le]
  unfold faceGhostConductance faceMarkedEndpointClampedSampledTarget
  rw [isingFiniteGhostLaplacian_some]
  change |isingFiniteGraphLaplacian
      (fkIsingSquareFullFaceGraph n) f c +
        isingFermionicGhostRate
          (fkIsingSquareFullFaceGhostMultiplicity n) c * (0 - f c)| <= _
  calc
    |_ + _| <= |isingFiniteGraphLaplacian
        (fkIsingSquareFullFaceGraph n) f c| +
      |isingFermionicGhostRate
        (fkIsingSquareFullFaceGhostMultiplicity n) c * (0 - f c)| :=
          abs_add_le _ _
    _ <= 4 + (3 * isingFermionicGhostCoefficient) * 1 := by
      rw [abs_mul, abs_of_nonneg hrate0]
      exact add_le_add hgraph
        (mul_le_mul hrate hjump (abs_nonneg _)
          (mul_nonneg (by norm_num) isingFermionicGhostCoefficient_pos.le))
    _ = _ := by ring



theorem vertexMarkedEndpointClamped_target_error_le_endpointLocalized
    (n : Nat) (hn : 0 < n) (radius : Nat)
    (embedding : FKIsingSquareFullVertexNode n -> Complex)
    (Phi : Complex -> Complex)
    (traceBound bulkResidual layerResidual endpointResidual : Real)
    (htraceBound : 0 <= traceBound)
    (hbulkResidual : 0 <= bulkResidual)
    (hlayerResidual : 0 <= layerResidual)
    (hendpointResidual : 0 <= endpointResidual)
    (htrace : forall x, fkIsingSquareFullVertexFixedBoundary n x ->
      Not (0 < fkIsingSquareFullVertexGhostMultiplicity n x) ->
        |0 - (Phi (embedding x)).im| <= traceBound)
    (hbulk : forall x,
      Not (fkIsingSquareFullVertexFixedBoundary n x) ->
      fkIsingSquareFullVertexGhostMultiplicity n x = 0 ->
      Not (vertexMarkedEndpointLayer n radius (some x)) ->
      |isingFiniteWeightedLaplacian (vertexGhostConductance n)
        (vertexMarkedEndpointClampedSampledTarget n embedding Phi)
        (some x)| <= bulkResidual)
    (hlayer : forall x,
      Not (fkIsingSquareFullVertexFixedBoundary n x) ->
      0 < fkIsingSquareFullVertexGhostMultiplicity n x ->
      Not (vertexMarkedEndpointLayer n radius (some x)) ->
      |isingFiniteWeightedLaplacian (vertexGhostConductance n)
        (vertexMarkedEndpointClampedSampledTarget n embedding Phi)
        (some x)| <= layerResidual)
    (hendpoint : forall x,
      Not (fkIsingSquareFullVertexFixedBoundary n x) ->
      vertexMarkedEndpointLayer n radius (some x) ->
      |isingFiniteWeightedLaplacian (vertexGhostConductance n)
        (vertexMarkedEndpointClampedSampledTarget n embedding Phi)
        (some x)| <= endpointResidual) :
    forall z, |vertexDirichlet n hn z -
        vertexMarkedEndpointClampedSampledTarget n embedding Phi z| <=
      traceBound + bulkResidual * vertexExplicitPoissonBarrier n z +
        layerResidual * vertexGhostLayerBarrier n z +
        endpointResidual * vertexMarkedEndpointBarrier n radius z := by
  intro z
  have h := vertexDirichlet_target_error_le_endpointLocalized
    n hn radius (vertexMarkedEndpointClampedSampledTarget n embedding Phi)
    bulkResidual layerResidual endpointResidual hbulkResidual
    hlayerResidual hendpointResidual hbulk hlayer hendpoint z
  have hb := vertexMarkedEndpointClamped_boundaryConsistencyError_le
    n hn embedding Phi traceBound htraceBound htrace
  linarith


theorem faceMarkedEndpointClamped_target_error_le_endpointLocalized
    (n : Nat) (hn : 0 < n) (radius : Nat)
    (embedding : FKIsingSquareFullFaceNode n -> Complex)
    (Phi : Complex -> Complex)
    (traceBound bulkResidual layerResidual endpointResidual : Real)
    (htraceBound : 0 <= traceBound)
    (hbulkResidual : 0 <= bulkResidual)
    (hlayerResidual : 0 <= layerResidual)
    (hendpointResidual : 0 <= endpointResidual)
    (htrace : forall c, fkIsingSquareFullFaceFixedBoundary n c ->
      Not (0 < fkIsingSquareFullFaceGhostMultiplicity n c) ->
        |1 - (Phi (embedding c)).im| <= traceBound)
    (hbulk : forall c,
      Not (fkIsingSquareFullFaceFixedBoundary n c) ->
      fkIsingSquareFullFaceGhostMultiplicity n c = 0 ->
      Not (faceMarkedEndpointLayer n radius (some c)) ->
      |isingFiniteWeightedLaplacian (faceGhostConductance n)
        (faceMarkedEndpointClampedSampledTarget n embedding Phi)
        (some c)| <= bulkResidual)
    (hlayer : forall c,
      Not (fkIsingSquareFullFaceFixedBoundary n c) ->
      0 < fkIsingSquareFullFaceGhostMultiplicity n c ->
      Not (faceMarkedEndpointLayer n radius (some c)) ->
      |isingFiniteWeightedLaplacian (faceGhostConductance n)
        (faceMarkedEndpointClampedSampledTarget n embedding Phi)
        (some c)| <= layerResidual)
    (hendpoint : forall c,
      Not (fkIsingSquareFullFaceFixedBoundary n c) ->
      faceMarkedEndpointLayer n radius (some c) ->
      |isingFiniteWeightedLaplacian (faceGhostConductance n)
        (faceMarkedEndpointClampedSampledTarget n embedding Phi)
        (some c)| <= endpointResidual) :
    forall z, |faceDirichlet n hn z -
        faceMarkedEndpointClampedSampledTarget n embedding Phi z| <=
      traceBound + bulkResidual * faceExplicitPoissonBarrier n z +
        layerResidual * faceGhostLayerBarrier n z +
        endpointResidual * faceMarkedEndpointBarrier n radius z := by
  intro z
  have h := faceDirichlet_target_error_le_endpointLocalized
    n hn radius (faceMarkedEndpointClampedSampledTarget n embedding Phi)
    bulkResidual layerResidual endpointResidual hbulkResidual
    hlayerResidual hendpointResidual hbulk hlayer hendpoint z
  have hb := faceMarkedEndpointClamped_boundaryConsistencyError_le
    n hn embedding Phi traceBound htraceBound htrace
  linarith


structure PhysicalEndpointLocalizedMarkedClampedRobinInputs
    (N : Nat -> Nat) (hN : forall k, 0 < N k)
    (Phi : Complex -> Complex) (mesh : Nat -> Real) (radius : Nat -> Nat)
    (boundaryRate bulkRate layerRate endpointRate : Nat -> Real) where
  boundary_nonneg : forall k, 0 <= boundaryRate k
  bulk_nonneg : forall k, 0 <= bulkRate k
  layer_nonneg : forall k, 0 <= layerRate k
  endpoint_nonneg : forall k, 0 <= endpointRate k
  vertexTrace : forall k x,
    fkIsingSquareFullVertexFixedBoundary (N k) x ->
    Not (0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x) ->
      |0 - (Phi (fullSquareScaledVertexEmbedding
        (N k) (mesh k) x)).im| <= boundaryRate k
  faceTrace : forall k c,
    fkIsingSquareFullFaceFixedBoundary (N k) c ->
    Not (0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c) ->
      |1 - (Phi (fullSquareScaledFaceEmbedding
        (N k) (mesh k) c)).im| <= boundaryRate k
  vertexBulk : forall k x,
    Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
    fkIsingSquareFullVertexGhostMultiplicity (N k) x = 0 ->
    Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
      |isingFiniteWeightedLaplacian (vertexGhostConductance (N k))
        (vertexMarkedEndpointClampedSampledTarget (N k)
          (fullSquareScaledVertexEmbedding (N k) (mesh k)) Phi)
        (some x)| <= bulkRate k
  faceBulk : forall k c,
    Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
    fkIsingSquareFullFaceGhostMultiplicity (N k) c = 0 ->
    Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
      |isingFiniteWeightedLaplacian (faceGhostConductance (N k))
        (faceMarkedEndpointClampedSampledTarget (N k)
          (fullSquareScaledFaceEmbedding (N k) (mesh k)) Phi)
        (some c)| <= bulkRate k
  vertexLayer : forall k x,
    Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
    0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x ->
    Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
      |isingFiniteWeightedLaplacian (vertexGhostConductance (N k))
        (vertexMarkedEndpointClampedSampledTarget (N k)
          (fullSquareScaledVertexEmbedding (N k) (mesh k)) Phi)
        (some x)| <= layerRate k
  faceLayer : forall k c,
    Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
    0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c ->
    Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
      |isingFiniteWeightedLaplacian (faceGhostConductance (N k))
        (faceMarkedEndpointClampedSampledTarget (N k)
          (fullSquareScaledFaceEmbedding (N k) (mesh k)) Phi)
        (some c)| <= layerRate k
  vertexEndpoint : forall k x,
    Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
    vertexMarkedEndpointLayer (N k) (radius k) (some x) ->
      |isingFiniteWeightedLaplacian (vertexGhostConductance (N k))
        (vertexMarkedEndpointClampedSampledTarget (N k)
          (fullSquareScaledVertexEmbedding (N k) (mesh k)) Phi)
        (some x)| <= endpointRate k
  faceEndpoint : forall k c,
    Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
    faceMarkedEndpointLayer (N k) (radius k) (some c) ->
      |isingFiniteWeightedLaplacian (faceGhostConductance (N k))
        (faceMarkedEndpointClampedSampledTarget (N k)
          (fullSquareScaledFaceEmbedding (N k) (mesh k)) Phi)
        (some c)| <= endpointRate k
  boundary_tendsto : Tendsto boundaryRate atTop (nhds 0)
  scaledBulk_tendsto : Tendsto
    (fun k => bulkRate k * (N k : Real) ^ 2) atTop (nhds 0)
  layer_tendsto : Tendsto layerRate atTop (nhds 0)




theorem PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofSampledResiduals
    {N : Nat -> Nat} {hN : forall k, 0 < N k}
    {Phi : Complex -> Complex} {mesh : Nat -> Real} {radius : Nat -> Nat}
    {boundaryRate bulkRate layerRate endpointRate : Nat -> Real}
    (hvertexRadius : forall k, 0 < radius k)
    (hfaceRadius : forall k, 2 <= radius k)
    (hboundary_nonneg : forall k, 0 <= boundaryRate k)
    (hbulk_nonneg : forall k, 0 <= bulkRate k)
    (hlayer_nonneg : forall k, 0 <= layerRate k)
    (hendpoint_nonneg : forall k, 0 <= endpointRate k)
    (hvertexTrace : forall k x,
      fkIsingSquareFullVertexFixedBoundary (N k) x ->
      Not (0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x) ->
        |0 - (Phi (fullSquareScaledVertexEmbedding
          (N k) (mesh k) x)).im| <= boundaryRate k)
    (hfaceTrace : forall k c,
      fkIsingSquareFullFaceFixedBoundary (N k) c ->
      Not (0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c) ->
        |1 - (Phi (fullSquareScaledFaceEmbedding
          (N k) (mesh k) c)).im| <= boundaryRate k)
    (hvertexBulk : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      fkIsingSquareFullVertexGhostMultiplicity (N k) x = 0 ->
      Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
        |isingFiniteWeightedLaplacian (vertexGhostConductance (N k))
          (vertexSampledImaginaryTarget (N k)
            (fullSquareScaledVertexEmbedding (N k) (mesh k)) Phi)
          (some x)| <= bulkRate k)
    (hfaceBulk : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      fkIsingSquareFullFaceGhostMultiplicity (N k) c = 0 ->
      Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
        |isingFiniteWeightedLaplacian (faceGhostConductance (N k))
          (faceSampledImaginaryTarget (N k)
            (fullSquareScaledFaceEmbedding (N k) (mesh k)) Phi)
          (some c)| <= bulkRate k)
    (hvertexLayer : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      0 < fkIsingSquareFullVertexGhostMultiplicity (N k) x ->
      Not (vertexMarkedEndpointLayer (N k) (radius k) (some x)) ->
        |isingFiniteWeightedLaplacian (vertexGhostConductance (N k))
          (vertexSampledImaginaryTarget (N k)
            (fullSquareScaledVertexEmbedding (N k) (mesh k)) Phi)
          (some x)| <= layerRate k)
    (hfaceLayer : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      0 < fkIsingSquareFullFaceGhostMultiplicity (N k) c ->
      Not (faceMarkedEndpointLayer (N k) (radius k) (some c)) ->
        |isingFiniteWeightedLaplacian (faceGhostConductance (N k))
          (faceSampledImaginaryTarget (N k)
            (fullSquareScaledFaceEmbedding (N k) (mesh k)) Phi)
          (some c)| <= layerRate k)
    (hvertexEndpoint : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary (N k) x) ->
      vertexMarkedEndpointLayer (N k) (radius k) (some x) ->
        |isingFiniteWeightedLaplacian (vertexGhostConductance (N k))
          (vertexMarkedEndpointClampedSampledTarget (N k)
            (fullSquareScaledVertexEmbedding (N k) (mesh k)) Phi)
          (some x)| <= endpointRate k)
    (hfaceEndpoint : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary (N k) c) ->
      faceMarkedEndpointLayer (N k) (radius k) (some c) ->
        |isingFiniteWeightedLaplacian (faceGhostConductance (N k))
          (faceMarkedEndpointClampedSampledTarget (N k)
            (fullSquareScaledFaceEmbedding (N k) (mesh k)) Phi)
          (some c)| <= endpointRate k)
    (hboundary_tendsto : Tendsto boundaryRate atTop (nhds 0))
    (hscaledBulk_tendsto : Tendsto
      (fun k => bulkRate k * (N k : Real) ^ 2) atTop (nhds 0))
    (hlayer_tendsto : Tendsto layerRate atTop (nhds 0)) :
    PhysicalEndpointLocalizedMarkedClampedRobinInputs N hN Phi mesh radius
      boundaryRate bulkRate layerRate endpointRate := by
  refine
    { boundary_nonneg := hboundary_nonneg
      bulk_nonneg := hbulk_nonneg
      layer_nonneg := hlayer_nonneg
      endpoint_nonneg := hendpoint_nonneg
      vertexTrace := hvertexTrace
      faceTrace := hfaceTrace
      vertexBulk := ?_
      faceBulk := ?_
      vertexLayer := ?_
      faceLayer := ?_
      vertexEndpoint := hvertexEndpoint
      faceEndpoint := hfaceEndpoint
      boundary_tendsto := hboundary_tendsto
      scaledBulk_tendsto := hscaledBulk_tendsto
      layer_tendsto := hlayer_tendsto }
  · intro k x hx hghost hendpoint
    rw [vertexMarkedEndpointClamped_weightedLaplacian_eq_sampled
      (N k) (radius k) (hvertexRadius k)
      (fullSquareScaledVertexEmbedding (N k) (mesh k)) Phi x hx hendpoint]
    exact hvertexBulk k x hx hghost hendpoint
  · intro k c hc hghost hendpoint
    rw [faceMarkedEndpointClamped_weightedLaplacian_eq_sampled
      (N k) (radius k) (hfaceRadius k)
      (fullSquareScaledFaceEmbedding (N k) (mesh k)) Phi c hc hendpoint]
    exact hfaceBulk k c hc hghost hendpoint
  · intro k x hx hghost hendpoint
    rw [vertexMarkedEndpointClamped_weightedLaplacian_eq_sampled
      (N k) (radius k) (hvertexRadius k)
      (fullSquareScaledVertexEmbedding (N k) (mesh k)) Phi x hx hendpoint]
    exact hvertexLayer k x hx hghost hendpoint
  · intro k c hc hghost hendpoint
    rw [faceMarkedEndpointClamped_weightedLaplacian_eq_sampled
      (N k) (radius k) (hfaceRadius k)
      (fullSquareScaledFaceEmbedding (N k) (mesh k)) Phi c hc hendpoint]
    exact hfaceLayer k c hc hghost hendpoint

theorem PhysicalEndpointLocalizedMarkedClampedRobinInputs.vertex_error_le
    {N : Nat -> Nat} {hN : forall k, 0 < N k}
    {Phi : Complex -> Complex} {mesh : Nat -> Real} {radius : Nat -> Nat}
    {boundaryRate bulkRate layerRate endpointRate : Nat -> Real}
    (H : PhysicalEndpointLocalizedMarkedClampedRobinInputs N hN Phi mesh
      radius boundaryRate bulkRate layerRate endpointRate)
    (k : Nat) (x : FKIsingSquareFullVertexNode (N k))
    (hx : Not (fkIsingSquareFullVertexFixedBoundary (N k) x)) :
    |vertexDirichlet (N k) (hN k) (some x) -
        (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im| <=
      boundaryRate k + bulkRate k * vertexExplicitPoissonBarrier (N k) (some x) +
        layerRate k * vertexGhostLayerBarrier (N k) (some x) +
        endpointRate k * vertexMarkedEndpointBarrier
          (N k) (radius k) (some x) := by
  have h := vertexMarkedEndpointClamped_target_error_le_endpointLocalized
    (N k) (hN k) (radius k)
    (fullSquareScaledVertexEmbedding (N k) (mesh k)) Phi
    (boundaryRate k) (bulkRate k) (layerRate k) (endpointRate k)
    (H.boundary_nonneg k) (H.bulk_nonneg k) (H.layer_nonneg k)
    (H.endpoint_nonneg k) (H.vertexTrace k) (H.vertexBulk k)
    (H.vertexLayer k) (H.vertexEndpoint k) (some x)
  simpa [vertexMarkedEndpointClampedSampledTarget_of_not_fixed _ _ _ x hx]
    using h

theorem PhysicalEndpointLocalizedMarkedClampedRobinInputs.face_error_le
    {N : Nat -> Nat} {hN : forall k, 0 < N k}
    {Phi : Complex -> Complex} {mesh : Nat -> Real} {radius : Nat -> Nat}
    {boundaryRate bulkRate layerRate endpointRate : Nat -> Real}
    (H : PhysicalEndpointLocalizedMarkedClampedRobinInputs N hN Phi mesh
      radius boundaryRate bulkRate layerRate endpointRate)
    (k : Nat) (c : FKIsingSquareFullFaceNode (N k))
    (hc : Not (fkIsingSquareFullFaceFixedBoundary (N k) c)) :
    |faceDirichlet (N k) (hN k) (some c) -
        (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im| <=
      boundaryRate k + bulkRate k * faceExplicitPoissonBarrier (N k) (some c) +
        layerRate k * faceGhostLayerBarrier (N k) (some c) +
        endpointRate k * faceMarkedEndpointBarrier
          (N k) (radius k) (some c) := by
  have h := faceMarkedEndpointClamped_target_error_le_endpointLocalized
    (N k) (hN k) (radius k)
    (fullSquareScaledFaceEmbedding (N k) (mesh k)) Phi
    (boundaryRate k) (bulkRate k) (layerRate k) (endpointRate k)
    (H.boundary_nonneg k) (H.bulk_nonneg k) (H.layer_nonneg k)
    (H.endpoint_nonneg k) (H.faceTrace k) (H.faceBulk k)
    (H.faceLayer k) (H.faceEndpoint k) (some c)
  simpa [faceMarkedEndpointClampedSampledTarget_of_not_fixed _ _ _ c hc]
    using h



theorem PhysicalEndpointLocalizedMarkedClampedRobinInputs.primitive_convergence_away
    {N : Nat -> Nat} {hN : forall k, 0 < N k}
    {Phi : Complex -> Complex} {mesh : Nat -> Real} {radius : Nat -> Nat}
    {boundaryRate bulkRate layerRate endpointRate : Nat -> Real}
    (H : PhysicalEndpointLocalizedMarkedClampedRobinInputs N hN Phi mesh
      radius boundaryRate bulkRate layerRate endpointRate)
    (safe : forall k,
      FKIsingSquareInteriorRadialIncidence (N k) (hN k) -> Prop)
    (vertexEndpointWeight faceEndpointWeight mismatchRate : Nat -> Real)
    (hvertexWeight_nonneg : forall k, 0 <= vertexEndpointWeight k)
    (hfaceWeight_nonneg : forall k, 0 <= faceEndpointWeight k)
    (hmismatch_nonneg : forall k, 0 <= mismatchRate k)
    (hsafeVertex : forall k e, safe k e ->
      Not (fkIsingSquareFullVertexFixedBoundary (N k)
        (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e)))
    (hsafeFace : forall k e, safe k e ->
      Not (fkIsingSquareFullFaceFixedBoundary (N k)
        (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e)))
    (hvertexWeight : forall k e, safe k e ->
      vertexMarkedEndpointBarrier (N k) (radius k)
        (some (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e)) <=
          vertexEndpointWeight k)
    (hfaceWeight : forall k e, safe k e ->
      faceMarkedEndpointBarrier (N k) (radius k)
        (some (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e)) <=
          faceEndpointWeight k)
    (hmismatch : forall k e, safe k e ->
      |(Phi (fullSquareScaledFaceEmbedding (N k) (mesh k)
          (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e))).im -
        (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k)
          (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e))).im| <=
        mismatchRate k)
    (hvertexEndpoint_tendsto : Tendsto
      (fun k => endpointRate k * vertexEndpointWeight k)
      atTop (nhds 0))
    (hfaceEndpoint_tendsto : Tendsto
      (fun k => endpointRate k * faceEndpointWeight k)
      atTop (nhds 0))
    (hmismatch_tendsto : Tendsto mismatchRate atTop (nhds 0)) :
    forall eta : Real, 0 < eta -> ∀ᶠ k in atTop,
      forall e : FKIsingSquareInteriorRadialIncidence (N k) (hN k),
        safe k e ->
        |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (N k) (hN k)).vertexPrimitive
            (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e) -
              (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k)
                (fkIsingSquareInteriorRadialEndpoint
                  (N k) (hN k) e))).im| < eta /\
          |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (N k) (hN k)).facePrimitive
            (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e) -
              (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k)
                (fkIsingSquareInteriorRadialEndpoint
                  (N k) (hN k) e))).im| < eta := by
  let common : Nat -> Real := fun k =>
    boundaryRate k +
      vertexBarrierGrowthConstant * (bulkRate k * (N k : Real) ^ 2) +
      (1 / isingFermionicGhostCoefficient) * layerRate k
  let upper : Nat -> Real := fun k =>
    common k + endpointRate k * vertexEndpointWeight k +
      endpointRate k * faceEndpointWeight k + mismatchRate k
  have hbulk : Tendsto
      (fun k => vertexBarrierGrowthConstant *
        (bulkRate k * (N k : Real) ^ 2)) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul H.scaledBulk_tendsto
  have hlayer : Tendsto
      (fun k => (1 / isingFermionicGhostCoefficient) * layerRate k)
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul H.layer_tendsto
  have hcommon : Tendsto common atTop (nhds 0) := by
    simpa [common, add_assoc] using (H.boundary_tendsto.add hbulk).add hlayer
  have hupper : Tendsto upper atTop (nhds 0) := by
    simpa [upper] using
      ((hcommon.add hvertexEndpoint_tendsto).add
        hfaceEndpoint_tendsto).add hmismatch_tendsto
  intro eta heta
  have heventually : ∀ᶠ k in atTop, dist (upper k) 0 < eta :=
    (Metric.tendsto_nhds.1 hupper) eta heta
  filter_upwards [heventually] with k hk
  intro e hsafe
  have hcommon_nonneg : 0 <= common k := by
    dsimp only [common]
    exact add_nonneg
      (add_nonneg (H.boundary_nonneg k)
        (mul_nonneg vertexBarrierGrowthConstant_nonneg
          (mul_nonneg (H.bulk_nonneg k) (sq_nonneg _))))
      (mul_nonneg
        (div_nonneg (by norm_num) isingFermionicGhostCoefficient_pos.le)
        (H.layer_nonneg k))
  have hupper_nonneg : 0 <= upper k := by
    dsimp only [upper]
    exact add_nonneg
      (add_nonneg
        (add_nonneg hcommon_nonneg
          (mul_nonneg (H.endpoint_nonneg k) (hvertexWeight_nonneg k)))
        (mul_nonneg (H.endpoint_nonneg k) (hfaceWeight_nonneg k)))
      (hmismatch_nonneg k)
  have hk' : upper k < eta := by
    simpa [Real.dist_eq, abs_of_nonneg hupper_nonneg] using hk
  let x := fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e
  let c := fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e
  have hv := H.vertex_error_le k x (hsafeVertex k e hsafe)
  have hvBarrier := vertexExplicitPoissonBarrierBound_le_growth
    (N k) (hN k)
  have hv' : |vertexDirichlet (N k) (hN k) (some x) -
      (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im| <=
        upper k := by
    calc
      _ <= boundaryRate k +
          bulkRate k * vertexExplicitPoissonBarrier (N k) (some x) +
          layerRate k * vertexGhostLayerBarrier (N k) (some x) +
          endpointRate k *
            vertexMarkedEndpointBarrier (N k) (radius k) (some x) := hv
      _ <= boundaryRate k +
          bulkRate k *
            (vertexBarrierGrowthConstant * (N k : Real) ^ 2) +
          layerRate k * (1 / isingFermionicGhostCoefficient) +
          endpointRate k * vertexEndpointWeight k := by
        gcongr
        · exact H.bulk_nonneg k
        · exact (vertexExplicitPoissonBarrier_le_bound (N k) (some x)).trans
            hvBarrier
        · exact H.layer_nonneg k
        · exact vertexGhostLayerBarrier_le (N k) (some x)
        · exact H.endpoint_nonneg k
        · exact hvertexWeight k e hsafe
      _ <= upper k := by
        dsimp only [upper, common]
        have hf : 0 <= endpointRate k * faceEndpointWeight k :=
          mul_nonneg (H.endpoint_nonneg k) (hfaceWeight_nonneg k)
        have hm : 0 <= mismatchRate k := hmismatch_nonneg k
        nlinarith
  have hf := H.face_error_le k c (hsafeFace k e hsafe)
  have hfBarrier : faceExplicitPoissonBarrierBound (N k) <=
      vertexBarrierGrowthConstant * (N k : Real) ^ 2 := by
    calc
      faceExplicitPoissonBarrierBound (N k) =
          (1 / 2 : Real) * (N k : Real) ^ 2 := by
        unfold faceExplicitPoissonBarrierBound
        ring
      _ <= vertexBarrierGrowthConstant * (N k : Real) ^ 2 :=
        mul_le_mul_of_nonneg_right half_le_vertexBarrierGrowthConstant
          (sq_nonneg _)
  have hfOwn : |faceDirichlet (N k) (hN k) (some c) -
      (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im| <=
        common k + endpointRate k * faceEndpointWeight k := by
    calc
      _ <= boundaryRate k +
          bulkRate k * faceExplicitPoissonBarrier (N k) (some c) +
          layerRate k * faceGhostLayerBarrier (N k) (some c) +
          endpointRate k *
            faceMarkedEndpointBarrier (N k) (radius k) (some c) := hf
      _ <= boundaryRate k +
          bulkRate k *
            (vertexBarrierGrowthConstant * (N k : Real) ^ 2) +
          layerRate k * (1 / isingFermionicGhostCoefficient) +
          endpointRate k * faceEndpointWeight k := by
        gcongr
        · exact H.bulk_nonneg k
        · exact (faceExplicitPoissonBarrier_le_bound (N k) (some c)).trans
            hfBarrier
        · exact H.layer_nonneg k
        · exact faceGhostLayerBarrier_le (N k) (some c)
        · exact H.endpoint_nonneg k
        · exact hfaceWeight k e hsafe
      _ = _ := by
        dsimp only [common]
        ring
  have hmis := hmismatch k e hsafe
  have hf' : |faceDirichlet (N k) (hN k) (some c) -
      (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im| <=
        upper k := by
    rw [show faceDirichlet (N k) (hN k) (some c) -
        (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im =
      (faceDirichlet (N k) (hN k) (some c) -
        (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im) +
      ((Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im -
        (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im) by ring]
    calc
      |_ + _| <= |faceDirichlet (N k) (hN k) (some c) -
          (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im| +
        |(Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im -
          (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im| :=
            abs_add_le _ _
      _ <= (common k + endpointRate k * faceEndpointWeight k) +
          mismatchRate k := add_le_add hfOwn hmis
      _ <= upper k := by
        dsimp only [upper]
        have hvw : 0 <= endpointRate k * vertexEndpointWeight k :=
          mul_nonneg (H.endpoint_nonneg k) (hvertexWeight_nonneg k)
        nlinarith
  have hphysical := physicalIncidence_close_of_dirichlet_close
    (N k) (hN k) e
    (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im
    (upper k) hv' hf'
  exact ⟨hphysical.1.trans_lt hk', hphysical.2.trans_lt hk'⟩




theorem PhysicalEndpointLocalizedMarkedClampedRobinInputs.primitive_convergence_away_polynomial
    {Phi : Complex -> Complex}
    {mesh boundaryRate bulkRate layerRate : Nat -> Real}
    (H : PhysicalEndpointLocalizedMarkedClampedRobinInputs
      isingFermionicPolynomialSide isingFermionicPolynomialSide_pos
      Phi mesh isingFermionicPolynomialRadius boundaryRate bulkRate layerRate
      (fun _ => 4 + 3 * isingFermionicGhostCoefficient))
    (mismatchRate : Nat -> Real)
    (hmismatch_nonneg : forall k, 0 <= mismatchRate k)
    (hmismatch : forall k e, PhysicalPolynomialEndpointSafe k e ->
      |(Phi (fullSquareScaledFaceEmbedding
          (isingFermionicPolynomialSide k) (mesh k)
          (fkIsingSquareFullFaceOfRadialIncidence
            (isingFermionicPolynomialSide k)
            (isingFermionicPolynomialSide_pos k) e))).im -
        (Phi (fullSquareScaledVertexEmbedding
          (isingFermionicPolynomialSide k) (mesh k)
          (fkIsingSquareInteriorRadialEndpoint
            (isingFermionicPolynomialSide k)
            (isingFermionicPolynomialSide_pos k) e))).im| <=
          mismatchRate k)
    (hmismatch_tendsto : Tendsto mismatchRate atTop (nhds 0)) :
    forall eta : Real, 0 < eta -> ∀ᶠ k in atTop,
      forall e : FKIsingSquareInteriorRadialIncidence
        (isingFermionicPolynomialSide k)
        (isingFermionicPolynomialSide_pos k),
        PhysicalPolynomialEndpointSafe k e ->
        |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (isingFermionicPolynomialSide k)
              (isingFermionicPolynomialSide_pos k)).vertexPrimitive
            (fkIsingSquareInteriorRadialEndpoint
              (isingFermionicPolynomialSide k)
              (isingFermionicPolynomialSide_pos k) e) -
              (Phi (fullSquareScaledVertexEmbedding
                (isingFermionicPolynomialSide k) (mesh k)
                (fkIsingSquareInteriorRadialEndpoint
                  (isingFermionicPolynomialSide k)
                  (isingFermionicPolynomialSide_pos k) e))).im| < eta /\
          |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (isingFermionicPolynomialSide k)
              (isingFermionicPolynomialSide_pos k)).facePrimitive
            (fkIsingSquareFullFaceOfRadialIncidence
              (isingFermionicPolynomialSide k)
              (isingFermionicPolynomialSide_pos k) e) -
              (Phi (fullSquareScaledVertexEmbedding
                (isingFermionicPolynomialSide k) (mesh k)
                (fkIsingSquareInteriorRadialEndpoint
                  (isingFermionicPolynomialSide k)
                  (isingFermionicPolynomialSide_pos k) e))).im| < eta := by
  apply H.primitive_convergence_away PhysicalPolynomialEndpointSafe
    vertexEndpointPolynomialBound faceEndpointPolynomialBound mismatchRate
  · exact vertexEndpointPolynomialBound_nonneg
  · exact faceEndpointPolynomialBound_nonneg
  · exact hmismatch_nonneg
  · intro k e hsafe
    exact hsafe.vertexNotFixed
  · intro k e hsafe
    exact hsafe.faceNotFixed
  · intro k e hsafe
    simpa [isingFermionicPolynomialSide,
      isingFermionicPolynomialRadius] using
      vertexMarkedEndpointBarrier_le_polynomialBound_of_halfColumn
        k (fkIsingSquareInteriorRadialEndpoint
          (isingFermionicPolynomialSide k)
          (isingFermionicPolynomialSide_pos k) e)
        hsafe.vertexNotFixed hsafe.vertexRight hsafe.vertexBottom
        hsafe.vertexTop hsafe.vertexHalf
  · intro k e hsafe
    simpa [isingFermionicPolynomialSide,
      isingFermionicPolynomialRadius] using
      faceMarkedEndpointBarrier_le_polynomialBound_of_halfColumn
        k (fkIsingSquareFullFaceOfRadialIncidence
          (isingFermionicPolynomialSide k)
          (isingFermionicPolynomialSide_pos k) e)
        hsafe.faceNotFixed hsafe.faceHalf
  · exact hmismatch
  · simpa using tendsto_const_nhds.mul tendsto_vertexEndpointPolynomialBound
  · simpa using tendsto_const_nhds.mul tendsto_faceEndpointPolynomialBound
  · exact hmismatch_tendsto

end FKIsingSquareBoundaryLayerCoordinateOneForm

end

end StatMech.Universality
