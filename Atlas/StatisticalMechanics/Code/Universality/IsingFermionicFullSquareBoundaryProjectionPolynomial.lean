/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicFullSquareBoundaryProjectionGeometry









namespace StatMech.Universality

open Filter Metric Set
open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

def isingFermionicProjectionPolynomialSide (k : Nat) : Nat :=
  isingFermionicPolynomialSide (k + 1)

noncomputable def isingFermionicProjectionPolynomialMesh (k : Nat) : Real :=
  isingFermionicPolynomialMesh (k + 1)

def isingFermionicProjectionPolynomialRadius (k : Nat) : Nat :=
  isingFermionicPolynomialRadius (k + 1)

theorem isingFermionicProjectionPolynomialSide_pos (k : Nat) :
    0 < isingFermionicProjectionPolynomialSide k := by
  exact isingFermionicPolynomialSide_pos (k + 1)

theorem isingFermionicProjectionPolynomialRadius_pos (k : Nat) :
    0 < isingFermionicProjectionPolynomialRadius k := by
  simp [isingFermionicProjectionPolynomialRadius,
    isingFermionicPolynomialRadius]

theorem isingFermionicProjectionPolynomialRadius_two_le (k : Nat) :
    2 <= isingFermionicProjectionPolynomialRadius k := by
  simp [isingFermionicProjectionPolynomialRadius,
    isingFermionicPolynomialRadius]

theorem isingFermionicProjectionPolynomialMesh_nonneg (k : Nat) :
    0 <= isingFermionicProjectionPolynomialMesh k := by
  exact isingFermionicPolynomialMesh_nonneg (k + 1)

theorem tendsto_isingFermionicProjectionPolynomialMesh :
    Tendsto isingFermionicProjectionPolynomialMesh atTop (nhds 0) := by
  exact tendsto_isingFermionicPolynomialMesh.comp (tendsto_add_atTop_nat 1)

theorem tendsto_isingFermionicProjectionPolynomialMesh_fourthOrder :
    Tendsto (fun k =>
      |isingFermionicProjectionPolynomialMesh k| ^ 4 *
        (isingFermionicProjectionPolynomialSide k : Real) ^ 2)
      atTop (nhds 0) := by
  simpa [isingFermionicProjectionPolynomialMesh,
    isingFermionicProjectionPolynomialSide] using
    tendsto_isingFermionicPolynomialMesh_fourthOrder.comp
      (tendsto_add_atTop_nat 1)

theorem
    tendsto_isingFermionicProjectionQuadraticLipschitz_mul_polynomialMesh
    (C : NNReal) :
    Tendsto (fun k =>
      (isingFermionicQuadraticLipschitzConstant C (k + 1) : Real) *
        isingFermionicProjectionPolynomialMesh k) atTop (nhds 0) := by
  simpa [isingFermionicProjectionPolynomialMesh] using
    (tendsto_isingFermionicQuadraticLipschitz_mul_polynomialMesh C).comp
      (tendsto_add_atTop_nat 1)




theorem
    PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofPolynomialTailCarrierSideTracesAndRange
    {Phi : Complex -> Complex}
    (Hfourth : PhysicalEndpointFourthOrderBulkData
      isingFermionicProjectionPolynomialSide Phi
      isingFermionicProjectionPolynomialMesh
      isingFermionicProjectionPolynomialRadius)
    (Hlayer : PhysicalEndpointLayerIncrementData
      isingFermionicProjectionPolynomialSide Phi
      isingFermionicProjectionPolynomialMesh
      isingFermionicProjectionPolynomialRadius)
    (C : NNReal)
    (hPhi : forall k,
      LipschitzOnWith (isingFermionicQuadraticLipschitzConstant C (k + 1))
        (fun z => (Phi z).im)
        (fullSquareOrdinaryBoundaryProjectionCarrier
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicProjectionPolynomialMesh k)
          (isingFermionicProjectionPolynomialRadius k)))
    (hleftTrace : forall k,
      Set.EqOn (fun z => (Phi z).im) (fun _ => 0)
        (fullSquareScaledLeftSide
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicProjectionPolynomialMesh k)))
    (hfreeTrace : forall k,
      Set.EqOn (fun z => (Phi z).im) (fun _ => 1)
        (fullSquareScaledFreeSides
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicProjectionPolynomialMesh k)))
    (hvertexRange : forall k x,
      0 <= (Phi (fullSquareScaledVertexEmbedding
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicProjectionPolynomialMesh k) x)).im /\
      (Phi (fullSquareScaledVertexEmbedding
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicProjectionPolynomialMesh k) x)).im <= 1)
    (hfaceRange : forall k c,
      0 <= (Phi (fullSquareScaledFaceEmbedding
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicProjectionPolynomialMesh k) c)).im /\
      (Phi (fullSquareScaledFaceEmbedding
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicProjectionPolynomialMesh k) c)).im <= 1) :
    PhysicalEndpointLocalizedMarkedClampedRobinInputs
      isingFermionicProjectionPolynomialSide
      isingFermionicProjectionPolynomialSide_pos Phi
      isingFermionicProjectionPolynomialMesh
      isingFermionicProjectionPolynomialRadius
      (fun k =>
        (isingFermionicQuadraticLipschitzConstant C (k + 1) : Real) *
          isingFermionicProjectionPolynomialMesh k)
      (fun k => (Hfourth.boundOne + Hfourth.boundTwo) *
        |isingFermionicProjectionPolynomialMesh k| ^ 4 / 12)
      (fun k => (4 * Hlayer.constant) *
          isingFermionicProjectionPolynomialMesh k +
        (3 * isingFermionicGhostCoefficient) *
          ((isingFermionicQuadraticLipschitzConstant C (k + 1) : Real) *
            isingFermionicProjectionPolynomialMesh k))
      (fun _ => 4 + 3 * isingFermionicGhostCoefficient) := by
  exact
    PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofCarrierSideTracesAndRange
      Hfourth Hlayer
      (fun k => isingFermionicQuadraticLipschitzConstant C (k + 1))
      hPhi hleftTrace hfreeTrace
      isingFermionicProjectionPolynomialRadius_pos
      isingFermionicProjectionPolynomialRadius_two_le
      isingFermionicProjectionPolynomialMesh_nonneg
      hvertexRange hfaceRange
      tendsto_isingFermionicProjectionPolynomialMesh_fourthOrder
      (tendsto_isingFermionicProjectionQuadraticLipschitz_mul_polynomialMesh C)
      tendsto_isingFermionicProjectionPolynomialMesh



def PhysicalProjectionPolynomialEndpointSafe (k : Nat)
    (e : FKIsingSquareInteriorRadialIncidence
      (isingFermionicProjectionPolynomialSide k)
      (isingFermionicProjectionPolynomialSide_pos k)) : Prop :=
  PhysicalPolynomialEndpointSafe (k + 1) e




theorem
    PhysicalEndpointLocalizedMarkedClampedRobinInputs.primitive_convergence_away_projectionPolynomial
    {Phi : Complex -> Complex}
    {mesh boundaryRate bulkRate layerRate : Nat -> Real}
    (H : PhysicalEndpointLocalizedMarkedClampedRobinInputs
      isingFermionicProjectionPolynomialSide
      isingFermionicProjectionPolynomialSide_pos Phi mesh
      isingFermionicProjectionPolynomialRadius boundaryRate bulkRate layerRate
      (fun _ => 4 + 3 * isingFermionicGhostCoefficient))
    (mismatchRate : Nat -> Real)
    (hmismatch_nonneg : forall k, 0 <= mismatchRate k)
    (hmismatch : forall k e, PhysicalProjectionPolynomialEndpointSafe k e ->
      |(Phi (fullSquareScaledFaceEmbedding
          (isingFermionicProjectionPolynomialSide k) (mesh k)
          (fkIsingSquareFullFaceOfRadialIncidence
            (isingFermionicProjectionPolynomialSide k)
            (isingFermionicProjectionPolynomialSide_pos k) e))).im -
        (Phi (fullSquareScaledVertexEmbedding
          (isingFermionicProjectionPolynomialSide k) (mesh k)
          (fkIsingSquareInteriorRadialEndpoint
            (isingFermionicProjectionPolynomialSide k)
            (isingFermionicProjectionPolynomialSide_pos k) e))).im| <=
          mismatchRate k)
    (hmismatch_tendsto : Tendsto mismatchRate atTop (nhds 0)) :
    forall eta : Real, 0 < eta -> Filter.Eventually (fun k =>
      forall e : FKIsingSquareInteriorRadialIncidence
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicProjectionPolynomialSide_pos k),
        PhysicalProjectionPolynomialEndpointSafe k e ->
        |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (isingFermionicProjectionPolynomialSide k)
              (isingFermionicProjectionPolynomialSide_pos k)).vertexPrimitive
            (fkIsingSquareInteriorRadialEndpoint
              (isingFermionicProjectionPolynomialSide k)
              (isingFermionicProjectionPolynomialSide_pos k) e) -
              (Phi (fullSquareScaledVertexEmbedding
                (isingFermionicProjectionPolynomialSide k) (mesh k)
                (fkIsingSquareInteriorRadialEndpoint
                  (isingFermionicProjectionPolynomialSide k)
                  (isingFermionicProjectionPolynomialSide_pos k) e))).im| < eta /\
          |(fkIsingSquareBoundaryLayerCoordinateOneForm
              (isingFermionicProjectionPolynomialSide k)
              (isingFermionicProjectionPolynomialSide_pos k)).facePrimitive
            (fkIsingSquareFullFaceOfRadialIncidence
              (isingFermionicProjectionPolynomialSide k)
              (isingFermionicProjectionPolynomialSide_pos k) e) -
              (Phi (fullSquareScaledVertexEmbedding
                (isingFermionicProjectionPolynomialSide k) (mesh k)
                (fkIsingSquareInteriorRadialEndpoint
                  (isingFermionicProjectionPolynomialSide k)
                  (isingFermionicProjectionPolynomialSide_pos k) e))).im| < eta)
      atTop := by
  apply H.primitive_convergence_away
    PhysicalProjectionPolynomialEndpointSafe
    (fun k => vertexEndpointPolynomialBound (k + 1))
    (fun k => faceEndpointPolynomialBound (k + 1)) mismatchRate
  · exact fun k => vertexEndpointPolynomialBound_nonneg (k + 1)
  · exact fun k => faceEndpointPolynomialBound_nonneg (k + 1)
  · exact hmismatch_nonneg
  · intro k e hsafe
    exact hsafe.vertexNotFixed
  · intro k e hsafe
    exact hsafe.faceNotFixed
  · intro k e hsafe
    simpa [isingFermionicProjectionPolynomialSide,
      isingFermionicProjectionPolynomialRadius,
      isingFermionicPolynomialSide, isingFermionicPolynomialRadius] using
      vertexMarkedEndpointBarrier_le_polynomialBound_of_halfColumn
        (k + 1) (fkIsingSquareInteriorRadialEndpoint
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicProjectionPolynomialSide_pos k) e)
        hsafe.vertexNotFixed hsafe.vertexRight hsafe.vertexBottom
        hsafe.vertexTop hsafe.vertexHalf
  · intro k e hsafe
    simpa [isingFermionicProjectionPolynomialSide,
      isingFermionicProjectionPolynomialRadius,
      isingFermionicPolynomialSide, isingFermionicPolynomialRadius] using
      faceMarkedEndpointBarrier_le_polynomialBound_of_halfColumn
        (k + 1) (fkIsingSquareFullFaceOfRadialIncidence
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicProjectionPolynomialSide_pos k) e)
        hsafe.faceNotFixed hsafe.faceHalf
  · exact hmismatch
  · simpa using
      (tendsto_const_nhds.mul tendsto_vertexEndpointPolynomialBound).comp
        (tendsto_add_atTop_nat 1)
  · simpa using
      (tendsto_const_nhds.mul tendsto_faceEndpointPolynomialBound).comp
        (tendsto_add_atTop_nat 1)
  · exact hmismatch_tendsto

end FKIsingSquareBoundaryLayerCoordinateOneForm

end

end StatMech.Universality
