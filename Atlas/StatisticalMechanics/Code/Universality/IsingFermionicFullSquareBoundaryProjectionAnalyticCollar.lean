/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicFullSquareBoundaryProjectionFixedDomain
import Code.Universality.IsingFermionicStripCauchyFirstOrder










namespace StatMech.Universality

open Filter Metric Set
open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm



noncomputable def isingFermionicFixedDiamondEndpointCollar (k : Nat) : Real :=
  (1 / ((k : Real) + 2)) ^ 4

theorem isingFermionicFixedDiamondEndpointCollar_pos (k : Nat) :
    0 < isingFermionicFixedDiamondEndpointCollar k := by
  unfold isingFermionicFixedDiamondEndpointCollar
  positivity

theorem isingFermionicFixedDiamondEndpointLipschitzConstant_eight_eq
    (k : Nat) :
    (isingFermionicFixedDiamondEndpointLipschitzConstant 8 k : Real) =
      8 / isingFermionicFixedDiamondEndpointCollar k := by
  unfold isingFermionicFixedDiamondEndpointLipschitzConstant
    isingFermionicFixedDiamondEndpointCollar
  change 8 * (((k + 2 : Nat) : Real) ^ 4) =
    8 / (1 / ((k : Real) + 2)) ^ 4
  push_cast
  have hk : (0 : Real) < (k : Real) + 2 := by positivity
  field_simp [hk.ne']




theorem
    PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFixedDiamondAnalyticCollarMap
    {Phi : Complex -> Complex}
    (Hfourth : PhysicalEndpointFourthOrderBulkData
      isingFermionicProjectionPolynomialSide Phi
      isingFermionicFixedDiamondMesh
      isingFermionicProjectionPolynomialRadius)
    (Hlayer : PhysicalEndpointLayerIncrementData
      isingFermionicProjectionPolynomialSide Phi
      isingFermionicFixedDiamondMesh
      isingFermionicProjectionPolynomialRadius)
    (hPhi : forall k c,
      c ∈ fullSquareOrdinaryBoundaryProjectionCarrier
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicFixedDiamondMesh k)
          (isingFermionicProjectionPolynomialRadius k) ->
        DifferentiableOn Complex Phi
          (ball c (isingFermionicFixedDiamondEndpointCollar k)))
    (hrangeBall : forall k c,
      c ∈ fullSquareOrdinaryBoundaryProjectionCarrier
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicFixedDiamondMesh k)
          (isingFermionicProjectionPolynomialRadius k) ->
        forall z, z ∈ ball c (isingFermionicFixedDiamondEndpointCollar k) ->
          0 <= (Phi z).im /\ (Phi z).im <= 1)
    (hleftTrace : Set.EqOn (fun z => (Phi z).im) (fun _ => 0)
      isingFermionicFixedDiamondLeftSide)
    (hfreeTrace : Set.EqOn (fun z => (Phi z).im) (fun _ => 1)
      isingFermionicFixedDiamondFreeSides)
    (hrange : Set.MapsTo Phi isingFermionicFixedClosedDiamond
      isingFermionicClosedUnitStrip) :
    PhysicalEndpointLocalizedMarkedClampedRobinInputs
      isingFermionicProjectionPolynomialSide
      isingFermionicProjectionPolynomialSide_pos Phi
      isingFermionicFixedDiamondMesh
      isingFermionicProjectionPolynomialRadius
      (fun k =>
        (isingFermionicFixedDiamondEndpointLipschitzConstant 8 k : Real) *
          isingFermionicFixedDiamondMesh k)
      (fun k => (Hfourth.boundOne + Hfourth.boundTwo) *
        |isingFermionicFixedDiamondMesh k| ^ 4 / 12)
      (fun k => (4 * Hlayer.constant) * isingFermionicFixedDiamondMesh k +
        (3 * isingFermionicGhostCoefficient) *
          ((isingFermionicFixedDiamondEndpointLipschitzConstant 8 k : Real) *
            isingFermionicFixedDiamondMesh k))
      (fun _ => 4 + 3 * isingFermionicGhostCoefficient) := by
  apply
    PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFixedDiamondEndpointLipschitzMap
      Hfourth Hlayer 8
  · intro k
    let K := fullSquareOrdinaryBoundaryProjectionCarrier
      (isingFermionicProjectionPolynomialSide k)
      (isingFermionicFixedDiamondMesh k)
      (isingFermionicProjectionPolynomialRadius k)
    have hLip := isingFermionic_unitStrip_lipschitzOn_carrier_of_balls
      Phi K (isingFermionicFixedDiamondEndpointCollar k)
      (isingFermionicFixedDiamondEndpointCollar_pos k)
      (hPhi k) (hrangeBall k)
      (fun z hz => hrangeBall k z hz z
        (Metric.mem_ball_self
          (isingFermionicFixedDiamondEndpointCollar_pos k)))
    have hconstant :
        isingFermionicFixedDiamondEndpointLipschitzConstant 8 k =
          (⟨8 / isingFermionicFixedDiamondEndpointCollar k,
            (div_pos (by norm_num)
              (isingFermionicFixedDiamondEndpointCollar_pos k)).le⟩ : NNReal) := by
      ext
      exact
        isingFermionicFixedDiamondEndpointLipschitzConstant_eight_eq k
    rw [hconstant]
    exact hLip
  · exact hleftTrace
  · exact hfreeTrace
  · exact hrange




theorem
    PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFixedDiamondOpenAnalyticCollarMap
    {Phi : Complex -> Complex}
    (Hfourth : PhysicalEndpointFourthOrderBulkData
      isingFermionicProjectionPolynomialSide Phi
      isingFermionicFixedDiamondMesh
      isingFermionicProjectionPolynomialRadius)
    (Hlayer : PhysicalEndpointLayerIncrementData
      isingFermionicProjectionPolynomialSide Phi
      isingFermionicFixedDiamondMesh
      isingFermionicProjectionPolynomialRadius)
    (U : Set Complex)
    (hPhi : AnalyticOnNhd Complex Phi U)
    (hrangeU : Set.MapsTo Phi U isingFermionicClosedUnitStrip)
    (hcollar : forall k c,
      c ∈ fullSquareOrdinaryBoundaryProjectionCarrier
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicFixedDiamondMesh k)
          (isingFermionicProjectionPolynomialRadius k) ->
        ball c (isingFermionicFixedDiamondEndpointCollar k) ⊆ U)
    (hleftTrace : Set.EqOn (fun z => (Phi z).im) (fun _ => 0)
      isingFermionicFixedDiamondLeftSide)
    (hfreeTrace : Set.EqOn (fun z => (Phi z).im) (fun _ => 1)
      isingFermionicFixedDiamondFreeSides)
    (hrange : Set.MapsTo Phi isingFermionicFixedClosedDiamond
      isingFermionicClosedUnitStrip) :
    PhysicalEndpointLocalizedMarkedClampedRobinInputs
      isingFermionicProjectionPolynomialSide
      isingFermionicProjectionPolynomialSide_pos Phi
      isingFermionicFixedDiamondMesh
      isingFermionicProjectionPolynomialRadius
      (fun k =>
        (isingFermionicFixedDiamondEndpointLipschitzConstant 8 k : Real) *
          isingFermionicFixedDiamondMesh k)
      (fun k => (Hfourth.boundOne + Hfourth.boundTwo) *
        |isingFermionicFixedDiamondMesh k| ^ 4 / 12)
      (fun k => (4 * Hlayer.constant) * isingFermionicFixedDiamondMesh k +
        (3 * isingFermionicGhostCoefficient) *
          ((isingFermionicFixedDiamondEndpointLipschitzConstant 8 k : Real) *
            isingFermionicFixedDiamondMesh k))
      (fun _ => 4 + 3 * isingFermionicGhostCoefficient) := by
  apply
    PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFixedDiamondAnalyticCollarMap
      Hfourth Hlayer
  · intro k c hc
    exact hPhi.differentiableOn.mono (hcollar k c hc)
  · intro k c hc z hz
    exact hrangeU (hcollar k c hc hz)
  · exact hleftTrace
  · exact hfreeTrace
  · exact hrange

end FKIsingSquareBoundaryLayerCoordinateOneForm

end

end StatMech.Universality
