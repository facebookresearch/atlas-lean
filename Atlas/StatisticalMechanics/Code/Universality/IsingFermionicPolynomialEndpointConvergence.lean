/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicVertexCornerCardinality
import Code.Universality.IsingFermionicFaceCornerCardinality
import Code.Universality.IsingFermionicEndpointInputAssembly








namespace StatMech.Universality

open Filter

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

def isingFermionicPolynomialSide (k : Nat) : Nat := (k + 1) ^ 5

def isingFermionicPolynomialRadius (k : Nat) : Nat := k + 1



noncomputable def isingFermionicPolynomialMesh (k : Nat) : Real :=
  1 / (((k + 1 : Nat) : Real) ^ 3)

theorem isingFermionicPolynomialSide_pos (k : Nat) :
    0 < isingFermionicPolynomialSide k := by
  unfold isingFermionicPolynomialSide
  positivity

theorem isingFermionicPolynomialMesh_nonneg (k : Nat) :
    0 <= isingFermionicPolynomialMesh k := by
  unfold isingFermionicPolynomialMesh
  positivity

theorem tendsto_isingFermionicPolynomialMesh :
    Tendsto isingFermionicPolynomialMesh atTop (nhds 0) := by
  let u : Nat -> Real := fun k => 1 / ((k : Real) + 1)
  have hu : Tendsto u atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hu3 : Tendsto (fun k => u k ^ 3) atTop (nhds 0) := by
    simpa using hu.pow 3
  convert hu3 using 1
  funext k
  unfold isingFermionicPolynomialMesh u
  have hk : (0 : Real) < (k : Real) + 1 := by positivity
  push_cast
  field_simp [hk.ne']

theorem tendsto_isingFermionicPolynomialMesh_fourthOrder :
    Tendsto (fun k =>
      |isingFermionicPolynomialMesh k| ^ 4 *
        (isingFermionicPolynomialSide k : Real) ^ 2)
      atTop (nhds 0) := by
  let u : Nat -> Real := fun k => 1 / ((k : Real) + 1)
  have hu : Tendsto u atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hu2 : Tendsto (fun k => u k ^ 2) atTop (nhds 0) := by
    simpa using hu.pow 2
  convert hu2 using 1
  funext k
  unfold isingFermionicPolynomialMesh isingFermionicPolynomialSide u
  have hk : (0 : Real) < (k : Real) + 1 := by positivity
  rw [abs_of_nonneg (by positivity :
    0 <= 1 / ((((k + 1 : Nat) : Real)) ^ 3))]
  push_cast
  field_simp [hk.ne']




structure PhysicalPolynomialEndpointSafe (k : Nat)
    (e : FKIsingSquareInteriorRadialIncidence
      (isingFermionicPolynomialSide k)
      (isingFermionicPolynomialSide_pos k)) : Prop where
  vertexNotFixed : Not (fkIsingSquareFullVertexFixedBoundary
    (isingFermionicPolynomialSide k)
    (fkIsingSquareInteriorRadialEndpoint
      (isingFermionicPolynomialSide k)
      (isingFermionicPolynomialSide_pos k) e))
  vertexRight :
    (fkIsingSquareInteriorRadialEndpoint
      (isingFermionicPolynomialSide k)
      (isingFermionicPolynomialSide_pos k) e).1 0 <
        (isingFermionicPolynomialSide k : Int)
  vertexBottom :
    -(isingFermionicPolynomialSide k : Int) <
      (fkIsingSquareInteriorRadialEndpoint
        (isingFermionicPolynomialSide k)
        (isingFermionicPolynomialSide_pos k) e).1 1
  vertexTop :
    (fkIsingSquareInteriorRadialEndpoint
      (isingFermionicPolynomialSide k)
      (isingFermionicPolynomialSide_pos k) e).1 1 <
        (isingFermionicPolynomialSide k : Int)
  vertexHalf :
    ((isingFermionicPolynomialSide k : Real) / 2) <=
      fullVertexColumnIndex (isingFermionicPolynomialSide k)
        (fkIsingSquareInteriorRadialEndpoint
          (isingFermionicPolynomialSide k)
          (isingFermionicPolynomialSide_pos k) e)
  faceNotFixed : Not (fkIsingSquareFullFaceFixedBoundary
    (isingFermionicPolynomialSide k)
    (fkIsingSquareFullFaceOfRadialIncidence
      (isingFermionicPolynomialSide k)
      (isingFermionicPolynomialSide_pos k) e))
  faceHalf :
    ((isingFermionicPolynomialSide k : Real) / 2) <=
      (fkIsingSquareFullFaceOfRadialIncidence
        (isingFermionicPolynomialSide k)
        (isingFermionicPolynomialSide_pos k) e).1.1

theorem vertexEndpointPolynomialBound_nonneg (k : Nat) :
    0 <= vertexEndpointPolynomialBound k := by
  have hcoefficient : 0 < isingFermionicGhostCoefficient :=
    isingFermionicGhostCoefficient_pos
  unfold vertexEndpointPolynomialBound
  positivity

theorem faceEndpointPolynomialBound_nonneg (k : Nat) :
    0 <= faceEndpointPolynomialBound k := by
  have hcoefficient : 0 < isingFermionicGhostCoefficient :=
    isingFermionicGhostCoefficient_pos
  unfold faceEndpointPolynomialBound
  positivity



theorem PhysicalEndpointLocalizedRobinInputs.ofPolynomialData
    {Phi : Complex -> Complex}
    (Hfourth : PhysicalEndpointFourthOrderBulkData
      isingFermionicPolynomialSide Phi isingFermionicPolynomialMesh
      isingFermionicPolynomialRadius)
    (Hlayer : PhysicalEndpointLayerIncrementData
      isingFermionicPolynomialSide Phi isingFermionicPolynomialMesh
      isingFermionicPolynomialRadius)
    (hvertexFixed : forall k x,
      fkIsingSquareFullVertexFixedBoundary
        (isingFermionicPolynomialSide k) x ->
        (Phi (fullSquareScaledVertexEmbedding
          (isingFermionicPolynomialSide k)
          (isingFermionicPolynomialMesh k) x)).im = 0)
    (hfaceFixed : forall k c,
      fkIsingSquareFullFaceFixedBoundary
        (isingFermionicPolynomialSide k) c ->
        (Phi (fullSquareScaledFaceEmbedding
          (isingFermionicPolynomialSide k)
          (isingFermionicPolynomialMesh k) c)).im = 1)
    (hvertexFree : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary
        (isingFermionicPolynomialSide k) x) ->
      0 < fkIsingSquareFullVertexGhostMultiplicity
        (isingFermionicPolynomialSide k) x ->
        (Phi (fullSquareScaledVertexEmbedding
          (isingFermionicPolynomialSide k)
          (isingFermionicPolynomialMesh k) x)).im = 1)
    (hfaceFree : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary
        (isingFermionicPolynomialSide k) c) ->
      0 < fkIsingSquareFullFaceGhostMultiplicity
        (isingFermionicPolynomialSide k) c ->
        (Phi (fullSquareScaledFaceEmbedding
          (isingFermionicPolynomialSide k)
          (isingFermionicPolynomialMesh k) c)).im = 0)
    (hvertexRange : forall k x,
      0 <= (Phi (fullSquareScaledVertexEmbedding
        (isingFermionicPolynomialSide k)
        (isingFermionicPolynomialMesh k) x)).im /\
      (Phi (fullSquareScaledVertexEmbedding
        (isingFermionicPolynomialSide k)
        (isingFermionicPolynomialMesh k) x)).im <= 1)
    (hfaceRange : forall k c,
      0 <= (Phi (fullSquareScaledFaceEmbedding
        (isingFermionicPolynomialSide k)
        (isingFermionicPolynomialMesh k) c)).im /\
      (Phi (fullSquareScaledFaceEmbedding
        (isingFermionicPolynomialSide k)
        (isingFermionicPolynomialMesh k) c)).im <= 1) :
    PhysicalEndpointLocalizedRobinInputs
      isingFermionicPolynomialSide isingFermionicPolynomialSide_pos
      Phi isingFermionicPolynomialMesh isingFermionicPolynomialRadius
      (fun k =>
        (Hfourth.boundOne + Hfourth.boundTwo) *
          |isingFermionicPolynomialMesh k| ^ 4 / 12)
      (fun k => 4 * Hlayer.constant * isingFermionicPolynomialMesh k)
      (fun _ => 4) := by
  exact PhysicalEndpointLocalizedRobinInputs.ofLocalizedFourthOrderLayerAndRange
    Hfourth Hlayer isingFermionicPolynomialMesh_nonneg
    hvertexFixed hfaceFixed hvertexFree hfaceFree hvertexRange hfaceRange
    tendsto_isingFermionicPolynomialMesh_fourthOrder
    tendsto_isingFermionicPolynomialMesh



theorem PhysicalEndpointLocalizedRobinInputs.primitive_convergence_away_polynomial
    {Phi : Complex -> Complex} {mesh bulkRate layerRate : Nat -> Real}
    (H : PhysicalEndpointLocalizedRobinInputs
      isingFermionicPolynomialSide isingFermionicPolynomialSide_pos
      Phi mesh isingFermionicPolynomialRadius bulkRate layerRate
      (fun _ => 4))
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
  · exact tendsto_four_mul_vertexEndpointPolynomialBound
  · exact tendsto_four_mul_faceEndpointPolynomialBound
  · exact hmismatch_tendsto



theorem PhysicalEndpointLocalizedRobinInputs.primitive_convergence_away_polynomial_of_lipschitz
    {Phi : Complex -> Complex} {mesh bulkRate layerRate : Nat -> Real}
    (H : PhysicalEndpointLocalizedRobinInputs
      isingFermionicPolynomialSide isingFermionicPolynomialSide_pos
      Phi mesh isingFermionicPolynomialRadius bulkRate layerRate
      (fun _ => 4))
    (L : NNReal) (hPhi : LipschitzWith L (fun z => (Phi z).im)) :
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
  apply H.primitive_convergence_away_polynomial
    (fun k => (L : Real) * mesh k)
  · intro k
    exact mul_nonneg L.2 (H.mesh_nonneg k)
  · intro k e _hsafe
    rw [← Real.dist_eq]
    calc
      dist
          (Phi (fullSquareScaledFaceEmbedding
            (isingFermionicPolynomialSide k) (mesh k)
            (fkIsingSquareFullFaceOfRadialIncidence
              (isingFermionicPolynomialSide k)
              (isingFermionicPolynomialSide_pos k) e))).im
          (Phi (fullSquareScaledVertexEmbedding
            (isingFermionicPolynomialSide k) (mesh k)
            (fkIsingSquareInteriorRadialEndpoint
              (isingFermionicPolynomialSide k)
              (isingFermionicPolynomialSide_pos k) e))).im <=
          L * dist
            (fullSquareScaledFaceEmbedding
              (isingFermionicPolynomialSide k) (mesh k)
              (fkIsingSquareFullFaceOfRadialIncidence
                (isingFermionicPolynomialSide k)
                (isingFermionicPolynomialSide_pos k) e))
            (fullSquareScaledVertexEmbedding
              (isingFermionicPolynomialSide k) (mesh k)
              (fkIsingSquareInteriorRadialEndpoint
                (isingFermionicPolynomialSide k)
                (isingFermionicPolynomialSide_pos k) e)) :=
        hPhi.dist_le_mul _ _
      _ <= L * mesh k := by
        apply mul_le_mul_of_nonneg_left _ L.2
        exact fullSquareScaledEmbedding_incidenceDistance
          isingFermionicPolynomialSide isingFermionicPolynomialSide_pos
          mesh H.mesh_nonneg k e
  · simpa using tendsto_const_nhds.mul H.mesh_tendsto

end FKIsingSquareBoundaryLayerCoordinateOneForm

end

end StatMech.Universality
