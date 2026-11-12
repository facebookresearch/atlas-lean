/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalCompactPlacement












namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm



theorem boundaryTrace_abs_sub_le_of_lipschitz
    (Phi : Complex -> Complex) (L : NNReal)
    (hPhi : LipschitzWith L (fun z => (Phi z).im))
    (sample boundaryPoint : Complex) (value mesh : Real)
    (htrace : (Phi boundaryPoint).im = value)
    (hdist : dist sample boundaryPoint <= mesh) :
    |value - (Phi sample).im| <= L * mesh := by
  calc
    |value - (Phi sample).im| =
        dist (Phi sample).im (Phi boundaryPoint).im := by
      rw [Real.dist_eq, htrace, abs_sub_comm]
    _ <= L * dist sample boundaryPoint := hPhi.dist_le_mul sample boundaryPoint
    _ <= L * mesh := mul_le_mul_of_nonneg_left hdist L.2



noncomputable def isingBoundaryClamp
    {V : Type*} (boundary : V -> Prop) (value : Real) (f : V -> Real) :
    V -> Real := by
  classical
  exact fun x => if boundary x then value else f x



theorem isingFiniteGraphLaplacian_boundaryClamp_sub_le_four
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (boundary : V -> Prop) (value : Real) (f : V -> Real) (x : V)
    (hx : Not (boundary x)) (traceBound : Real)
    (htrace_nonneg : 0 <= traceBound)
    (hcard : Nat.card (G.neighborSet x) <= 4)
    (htrace : forall y, boundary y -> |value - f y| <= traceBound) :
    |isingFiniteGraphLaplacian G
          (isingBoundaryClamp boundary value f) x -
        isingFiniteGraphLaplacian G f x| <= 4 * traceBound := by
  classical
  have hcardFinset : (G.neighborFinset x).card <= 4 := by
    have hncard : Nat.card (G.neighborSet x) = G.degree x :=
      (Nat.card_eq_fintype_card).trans
        (SimpleGraph.card_neighborSet_eq_degree G x)
    rw [SimpleGraph.card_neighborFinset_eq_degree, <- hncard]
    exact hcard
  unfold isingFiniteGraphLaplacian
  rw [<- Finset.sum_sub_distrib]
  calc
    |∑ y ∈ G.neighborFinset x,
        ((isingBoundaryClamp boundary value f y -
            isingBoundaryClamp boundary value f x) - (f y - f x))| <=
        ∑ y ∈ G.neighborFinset x,
          |(isingBoundaryClamp boundary value f y -
            isingBoundaryClamp boundary value f x) - (f y - f x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ _y ∈ G.neighborFinset x, traceBound := by
      apply Finset.sum_le_sum
      intro y _hy
      by_cases hy : boundary y
      · simpa [isingBoundaryClamp, hx, hy] using htrace y hy
      · simpa [isingBoundaryClamp, hx, hy] using htrace_nonneg
    _ = ((G.neighborFinset x).card : Real) * traceBound := by simp
    _ <= 4 * traceBound := by
      gcongr
      exact_mod_cast hcardFinset




theorem isingFiniteGhostLaplacian_boundaryClamp_sub_le_four
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (ghostRate : V -> Real) (boundary : V -> Prop)
    (value ghostValue : Real) (f : V -> Real) (x : V)
    (hx : Not (boundary x)) (traceBound : Real)
    (htrace_nonneg : 0 <= traceBound)
    (hcard : Nat.card (G.neighborSet x) <= 4)
    (htrace : forall y, boundary y -> |value - f y| <= traceBound) :
    |isingFiniteWeightedLaplacian
          (isingFiniteGhostConductance G ghostRate)
          (isingFiniteGhostExtension ghostValue
            (isingBoundaryClamp boundary value f)) (some x) -
        isingFiniteWeightedLaplacian
          (isingFiniteGhostConductance G ghostRate)
          (isingFiniteGhostExtension ghostValue f) (some x)| <=
      4 * traceBound := by
  rw [isingFiniteGhostLaplacian_some, isingFiniteGhostLaplacian_some]
  have hgraph := isingFiniteGraphLaplacian_boundaryClamp_sub_le_four
    G boundary value f x hx traceBound htrace_nonneg hcard htrace
  simpa [isingBoundaryClamp, hx] using hgraph



noncomputable def vertexBoundaryClampedSampledTarget
    (n : Nat) (embedding : FKIsingSquareFullVertexNode n -> Complex)
    (Phi : Complex -> Complex) :
    Option (FKIsingSquareFullVertexNode n) -> Real := by
  classical
  exact fun
    | none => 1
    | some x =>
        if fkIsingSquareFullVertexFixedBoundary n x then 0
        else (Phi (embedding x)).im



noncomputable def faceBoundaryClampedSampledTarget
    (n : Nat) (embedding : FKIsingSquareFullFaceNode n -> Complex)
    (Phi : Complex -> Complex) :
    Option (FKIsingSquareFullFaceNode n) -> Real := by
  classical
  exact fun
    | none => 0
    | some c =>
        if fkIsingSquareFullFaceFixedBoundary n c then 1
        else (Phi (embedding c)).im

@[simp] theorem vertexBoundaryClampedSampledTarget_none
    (n : Nat) (embedding : FKIsingSquareFullVertexNode n -> Complex)
    (Phi : Complex -> Complex) :
    vertexBoundaryClampedSampledTarget n embedding Phi none = 1 := rfl

@[simp] theorem faceBoundaryClampedSampledTarget_none
    (n : Nat) (embedding : FKIsingSquareFullFaceNode n -> Complex)
    (Phi : Complex -> Complex) :
    faceBoundaryClampedSampledTarget n embedding Phi none = 0 := rfl

@[simp] theorem vertexBoundaryClampedSampledTarget_of_fixed
    (n : Nat) (embedding : FKIsingSquareFullVertexNode n -> Complex)
    (Phi : Complex -> Complex) (x : FKIsingSquareFullVertexNode n)
    (hx : fkIsingSquareFullVertexFixedBoundary n x) :
    vertexBoundaryClampedSampledTarget n embedding Phi (some x) = 0 := by
  simp [vertexBoundaryClampedSampledTarget, hx]

@[simp] theorem faceBoundaryClampedSampledTarget_of_fixed
    (n : Nat) (embedding : FKIsingSquareFullFaceNode n -> Complex)
    (Phi : Complex -> Complex) (c : FKIsingSquareFullFaceNode n)
    (hc : fkIsingSquareFullFaceFixedBoundary n c) :
    faceBoundaryClampedSampledTarget n embedding Phi (some c) = 1 := by
  simp [faceBoundaryClampedSampledTarget, hc]

@[simp] theorem vertexBoundaryClampedSampledTarget_of_not_fixed
    (n : Nat) (embedding : FKIsingSquareFullVertexNode n -> Complex)
    (Phi : Complex -> Complex) (x : FKIsingSquareFullVertexNode n)
    (hx : Not (fkIsingSquareFullVertexFixedBoundary n x)) :
    vertexBoundaryClampedSampledTarget n embedding Phi (some x) =
      (Phi (embedding x)).im := by
  simp [vertexBoundaryClampedSampledTarget, hx]

@[simp] theorem faceBoundaryClampedSampledTarget_of_not_fixed
    (n : Nat) (embedding : FKIsingSquareFullFaceNode n -> Complex)
    (Phi : Complex -> Complex) (c : FKIsingSquareFullFaceNode n)
    (hc : Not (fkIsingSquareFullFaceFixedBoundary n c)) :
    faceBoundaryClampedSampledTarget n embedding Phi (some c) =
      (Phi (embedding c)).im := by
  simp [faceBoundaryClampedSampledTarget, hc]



theorem vertexBoundaryClampedSampledTarget_boundaryConsistencyError_eq_zero
    (n : Nat) (hn : 0 < n)
    (embedding : FKIsingSquareFullVertexNode n -> Complex)
    (Phi : Complex -> Complex) :
    vertexBoundaryConsistencyError n hn
      (vertexBoundaryClampedSampledTarget n embedding Phi) = 0 := by
  apply le_antisymm
  · apply isingFiniteWeightedBoundaryError_le
      (vertexDirichletBoundary n) (vertexGhostPrimitive n hn)
      (vertexBoundaryClampedSampledTarget n embedding Phi) 0 (le_refl 0)
    intro x hx
    cases x with
    | none => simp [vertexGhostPrimitive, isingFiniteGhostExtension]
    | some x =>
        change fkIsingSquareFullVertexFixedBoundary n x at hx
        simp [vertexGhostPrimitive, isingFiniteGhostExtension, hx,
          vertex_fixedBoundary_eq_zero n hn x hx]
  · exact isingFiniteWeightedBoundaryError_nonneg
      (vertexDirichletBoundary n) (vertexGhostPrimitive n hn)
      (vertexBoundaryClampedSampledTarget n embedding Phi)



theorem faceBoundaryClampedSampledTarget_boundaryConsistencyError_eq_zero
    (n : Nat) (hn : 0 < n)
    (embedding : FKIsingSquareFullFaceNode n -> Complex)
    (Phi : Complex -> Complex) :
    faceBoundaryConsistencyError n hn
      (faceBoundaryClampedSampledTarget n embedding Phi) = 0 := by
  apply le_antisymm
  · apply isingFiniteWeightedBoundaryError_le
      (faceDirichletBoundary n) (faceGhostPrimitive n hn)
      (faceBoundaryClampedSampledTarget n embedding Phi) 0 (le_refl 0)
    intro c hc
    cases c with
    | none => simp [faceGhostPrimitive, isingFiniteGhostExtension]
    | some c =>
        change fkIsingSquareFullFaceFixedBoundary n c at hc
        simp [faceGhostPrimitive, isingFiniteGhostExtension, hc,
          face_fixedBoundary_eq_one n hn c hc]
  · exact isingFiniteWeightedBoundaryError_nonneg
      (faceDirichletBoundary n) (faceGhostPrimitive n hn)
      (faceBoundaryClampedSampledTarget n embedding Phi)



theorem vertexBoundaryClampedSampledTarget_laplacian_sub_le_four
    (n : Nat) (embedding : FKIsingSquareFullVertexNode n -> Complex)
    (Phi : Complex -> Complex) (traceBound : Real)
    (htrace_nonneg : 0 <= traceBound)
    (htrace : forall y, fkIsingSquareFullVertexFixedBoundary n y ->
      |0 - (Phi (embedding y)).im| <= traceBound)
    (x : FKIsingSquareFullVertexNode n)
    (hx : Not (fkIsingSquareFullVertexFixedBoundary n x)) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
          (fun y => vertexBoundaryClampedSampledTarget
            n embedding Phi (some y)) x -
        isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
          (fun y => (Phi (embedding y)).im) x| <= 4 * traceBound := by
  simpa only [vertexBoundaryClampedSampledTarget,
      isingBoundaryClamp] using
    isingFiniteGraphLaplacian_boundaryClamp_sub_le_four
      (fkIsingSquareFullVertexGraph n)
      (fkIsingSquareFullVertexFixedBoundary n) 0
      (fun y => (Phi (embedding y)).im) x hx traceBound htrace_nonneg
      (fullVertex_neighbor_card_le_four n x) htrace



theorem faceBoundaryClampedSampledTarget_laplacian_sub_le_four
    (n : Nat) (embedding : FKIsingSquareFullFaceNode n -> Complex)
    (Phi : Complex -> Complex) (traceBound : Real)
    (htrace_nonneg : 0 <= traceBound)
    (htrace : forall d, fkIsingSquareFullFaceFixedBoundary n d ->
      |1 - (Phi (embedding d)).im| <= traceBound)
    (c : FKIsingSquareFullFaceNode n)
    (hc : Not (fkIsingSquareFullFaceFixedBoundary n c)) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
          (fun d => faceBoundaryClampedSampledTarget
            n embedding Phi (some d)) c -
        isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
          (fun d => (Phi (embedding d)).im) c| <= 4 * traceBound := by
  simpa only [faceBoundaryClampedSampledTarget,
      isingBoundaryClamp] using
    isingFiniteGraphLaplacian_boundaryClamp_sub_le_four
      (fkIsingSquareFullFaceGraph n)
      (fkIsingSquareFullFaceFixedBoundary n) 1
      (fun d => (Phi (embedding d)).im) c hc traceBound htrace_nonneg
      (fullFace_neighbor_card_le_four n c) htrace


theorem vertexBoundaryClampedSampledTarget_weightedLaplacian_sub_le_four
    (n : Nat) (embedding : FKIsingSquareFullVertexNode n -> Complex)
    (Phi : Complex -> Complex) (traceBound : Real)
    (htrace_nonneg : 0 <= traceBound)
    (htrace : forall y, fkIsingSquareFullVertexFixedBoundary n y ->
      |0 - (Phi (embedding y)).im| <= traceBound)
    (x : FKIsingSquareFullVertexNode n)
    (hx : Not (fkIsingSquareFullVertexFixedBoundary n x)) :
    |isingFiniteWeightedLaplacian (vertexGhostConductance n)
          (vertexBoundaryClampedSampledTarget n embedding Phi) (some x) -
        isingFiniteWeightedLaplacian (vertexGhostConductance n)
          (vertexSampledImaginaryTarget n embedding Phi) (some x)| <=
      4 * traceBound := by
  have hclamped : vertexBoundaryClampedSampledTarget n embedding Phi =
      isingFiniteGhostExtension 1
        (isingBoundaryClamp (fkIsingSquareFullVertexFixedBoundary n) 0
          (fun y => (Phi (embedding y)).im)) := by
    funext z
    cases z <;> rfl
  have hsampled : vertexSampledImaginaryTarget n embedding Phi =
      isingFiniteGhostExtension 1 (fun y => (Phi (embedding y)).im) := by
    funext z
    cases z <;> rfl
  rw [hclamped, hsampled, vertexGhostConductance]
  exact isingFiniteGhostLaplacian_boundaryClamp_sub_le_four
    (fkIsingSquareFullVertexGraph n)
    (isingFermionicGhostRate
      (fkIsingSquareFullVertexGhostMultiplicity n))
    (fkIsingSquareFullVertexFixedBoundary n) 0 1
    (fun y => (Phi (embedding y)).im) x hx traceBound htrace_nonneg
    (fullVertex_neighbor_card_le_four n x) htrace


theorem faceBoundaryClampedSampledTarget_weightedLaplacian_sub_le_four
    (n : Nat) (embedding : FKIsingSquareFullFaceNode n -> Complex)
    (Phi : Complex -> Complex) (traceBound : Real)
    (htrace_nonneg : 0 <= traceBound)
    (htrace : forall d, fkIsingSquareFullFaceFixedBoundary n d ->
      |1 - (Phi (embedding d)).im| <= traceBound)
    (c : FKIsingSquareFullFaceNode n)
    (hc : Not (fkIsingSquareFullFaceFixedBoundary n c)) :
    |isingFiniteWeightedLaplacian (faceGhostConductance n)
          (faceBoundaryClampedSampledTarget n embedding Phi) (some c) -
        isingFiniteWeightedLaplacian (faceGhostConductance n)
          (faceSampledImaginaryTarget n embedding Phi) (some c)| <=
      4 * traceBound := by
  have hclamped : faceBoundaryClampedSampledTarget n embedding Phi =
      isingFiniteGhostExtension 0
        (isingBoundaryClamp (fkIsingSquareFullFaceFixedBoundary n) 1
          (fun d => (Phi (embedding d)).im)) := by
    funext z
    cases z <;> rfl
  have hsampled : faceSampledImaginaryTarget n embedding Phi =
      isingFiniteGhostExtension 0 (fun d => (Phi (embedding d)).im) := by
    funext z
    cases z <;> rfl
  rw [hclamped, hsampled, faceGhostConductance]
  exact isingFiniteGhostLaplacian_boundaryClamp_sub_le_four
    (fkIsingSquareFullFaceGraph n)
    (isingFermionicGhostRate
      (fkIsingSquareFullFaceGhostMultiplicity n))
    (fkIsingSquareFullFaceFixedBoundary n) 1 0
    (fun d => (Phi (embedding d)).im) c hc traceBound htrace_nonneg
    (fullFace_neighbor_card_le_four n c) htrace



theorem vertexBoundaryClampedSampledTarget_laplacian_le
    (n : Nat) (embedding : FKIsingSquareFullVertexNode n -> Complex)
    (Phi : Complex -> Complex) (sampleBound traceBound : Real)
    (htrace_nonneg : 0 <= traceBound)
    (htrace : forall y, fkIsingSquareFullVertexFixedBoundary n y ->
      |0 - (Phi (embedding y)).im| <= traceBound)
    (x : FKIsingSquareFullVertexNode n)
    (hx : Not (fkIsingSquareFullVertexFixedBoundary n x))
    (hsample :
      |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
        (fun y => (Phi (embedding y)).im) x| <= sampleBound) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n)
      (fun y => vertexBoundaryClampedSampledTarget
        n embedding Phi (some y)) x| <= sampleBound + 4 * traceBound := by
  let clamped := isingFiniteGraphLaplacian
    (fkIsingSquareFullVertexGraph n)
    (fun y => vertexBoundaryClampedSampledTarget n embedding Phi (some y)) x
  let sampled := isingFiniteGraphLaplacian
    (fkIsingSquareFullVertexGraph n)
    (fun y => (Phi (embedding y)).im) x
  have hdiff : |clamped - sampled| <= 4 * traceBound :=
    vertexBoundaryClampedSampledTarget_laplacian_sub_le_four
      n embedding Phi traceBound htrace_nonneg htrace x hx
  calc
    |clamped| = |(clamped - sampled) + sampled| := by ring_nf
    _ <= |clamped - sampled| + |sampled| := abs_add_le _ _
    _ <= 4 * traceBound + sampleBound := add_le_add hdiff hsample
    _ = sampleBound + 4 * traceBound := by ring



theorem faceBoundaryClampedSampledTarget_laplacian_le
    (n : Nat) (embedding : FKIsingSquareFullFaceNode n -> Complex)
    (Phi : Complex -> Complex) (sampleBound traceBound : Real)
    (htrace_nonneg : 0 <= traceBound)
    (htrace : forall d, fkIsingSquareFullFaceFixedBoundary n d ->
      |1 - (Phi (embedding d)).im| <= traceBound)
    (c : FKIsingSquareFullFaceNode n)
    (hc : Not (fkIsingSquareFullFaceFixedBoundary n c))
    (hsample :
      |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
        (fun d => (Phi (embedding d)).im) c| <= sampleBound) :
    |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
      (fun d => faceBoundaryClampedSampledTarget
        n embedding Phi (some d)) c| <= sampleBound + 4 * traceBound := by
  let clamped := isingFiniteGraphLaplacian
    (fkIsingSquareFullFaceGraph n)
    (fun d => faceBoundaryClampedSampledTarget n embedding Phi (some d)) c
  let sampled := isingFiniteGraphLaplacian
    (fkIsingSquareFullFaceGraph n)
    (fun d => (Phi (embedding d)).im) c
  have hdiff : |clamped - sampled| <= 4 * traceBound :=
    faceBoundaryClampedSampledTarget_laplacian_sub_le_four
      n embedding Phi traceBound htrace_nonneg htrace c hc
  calc
    |clamped| = |(clamped - sampled) + sampled| := by ring_nf
    _ <= |clamped - sampled| + |sampled| := abs_add_le _ _
    _ <= 4 * traceBound + sampleBound := add_le_add hdiff hsample
    _ = sampleBound + 4 * traceBound := by ring



theorem vertexBoundaryClampedSampledTarget_error_le_endpointLocalized
    (n : Nat) (hn : 0 < n) (radius : Nat)
    (embedding : FKIsingSquareFullVertexNode n -> Complex)
    (Phi : Complex -> Complex)
    (bulkResidual layerResidual endpointResidual : Real)
    (hbulkResidual : 0 <= bulkResidual)
    (hlayerResidual : 0 <= layerResidual)
    (hendpointResidual : 0 <= endpointResidual)
    (hbulk : forall x,
      Not (fkIsingSquareFullVertexFixedBoundary n x) ->
      fkIsingSquareFullVertexGhostMultiplicity n x = 0 ->
      Not (vertexMarkedEndpointLayer n radius (some x)) ->
      |isingFiniteWeightedLaplacian (vertexGhostConductance n)
        (vertexBoundaryClampedSampledTarget n embedding Phi) (some x)| <=
          bulkResidual)
    (hlayer : forall x,
      Not (fkIsingSquareFullVertexFixedBoundary n x) ->
      0 < fkIsingSquareFullVertexGhostMultiplicity n x ->
      Not (vertexMarkedEndpointLayer n radius (some x)) ->
      |isingFiniteWeightedLaplacian (vertexGhostConductance n)
        (vertexBoundaryClampedSampledTarget n embedding Phi) (some x)| <=
          layerResidual)
    (hendpoint : forall x,
      Not (fkIsingSquareFullVertexFixedBoundary n x) ->
      vertexMarkedEndpointLayer n radius (some x) ->
      |isingFiniteWeightedLaplacian (vertexGhostConductance n)
        (vertexBoundaryClampedSampledTarget n embedding Phi) (some x)| <=
          endpointResidual) :
    forall z,
      |vertexDirichlet n hn z -
          vertexBoundaryClampedSampledTarget n embedding Phi z| <=
        bulkResidual * vertexExplicitPoissonBarrier n z +
          layerResidual * vertexGhostLayerBarrier n z +
          endpointResidual * vertexMarkedEndpointBarrier n radius z := by
  intro z
  have h := vertexDirichlet_target_error_le_endpointLocalized
    n hn radius (vertexBoundaryClampedSampledTarget n embedding Phi)
    bulkResidual layerResidual endpointResidual hbulkResidual
    hlayerResidual hendpointResidual hbulk hlayer hendpoint z
  rw [vertexBoundaryClampedSampledTarget_boundaryConsistencyError_eq_zero]
    at h
  simpa using h



theorem faceBoundaryClampedSampledTarget_error_le_endpointLocalized
    (n : Nat) (hn : 0 < n) (radius : Nat)
    (embedding : FKIsingSquareFullFaceNode n -> Complex)
    (Phi : Complex -> Complex)
    (bulkResidual layerResidual endpointResidual : Real)
    (hbulkResidual : 0 <= bulkResidual)
    (hlayerResidual : 0 <= layerResidual)
    (hendpointResidual : 0 <= endpointResidual)
    (hbulk : forall c,
      Not (fkIsingSquareFullFaceFixedBoundary n c) ->
      fkIsingSquareFullFaceGhostMultiplicity n c = 0 ->
      Not (faceMarkedEndpointLayer n radius (some c)) ->
      |isingFiniteWeightedLaplacian (faceGhostConductance n)
        (faceBoundaryClampedSampledTarget n embedding Phi) (some c)| <=
          bulkResidual)
    (hlayer : forall c,
      Not (fkIsingSquareFullFaceFixedBoundary n c) ->
      0 < fkIsingSquareFullFaceGhostMultiplicity n c ->
      Not (faceMarkedEndpointLayer n radius (some c)) ->
      |isingFiniteWeightedLaplacian (faceGhostConductance n)
        (faceBoundaryClampedSampledTarget n embedding Phi) (some c)| <=
          layerResidual)
    (hendpoint : forall c,
      Not (fkIsingSquareFullFaceFixedBoundary n c) ->
      faceMarkedEndpointLayer n radius (some c) ->
      |isingFiniteWeightedLaplacian (faceGhostConductance n)
        (faceBoundaryClampedSampledTarget n embedding Phi) (some c)| <=
          endpointResidual) :
    forall z,
      |faceDirichlet n hn z -
          faceBoundaryClampedSampledTarget n embedding Phi z| <=
        bulkResidual * faceExplicitPoissonBarrier n z +
          layerResidual * faceGhostLayerBarrier n z +
          endpointResidual * faceMarkedEndpointBarrier n radius z := by
  intro z
  have h := faceDirichlet_target_error_le_endpointLocalized
    n hn radius (faceBoundaryClampedSampledTarget n embedding Phi)
    bulkResidual layerResidual endpointResidual hbulkResidual
    hlayerResidual hendpointResidual hbulk hlayer hendpoint z
  rw [faceBoundaryClampedSampledTarget_boundaryConsistencyError_eq_zero]
    at h
  simpa using h

end FKIsingSquareBoundaryLayerCoordinateOneForm

end

end StatMech.Universality
