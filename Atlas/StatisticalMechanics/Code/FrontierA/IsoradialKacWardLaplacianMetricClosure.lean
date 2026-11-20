/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.IsoradialKacWardMetricClosure
import Code.FrontierA.IsoradialKacWardLaplacianAtlas












open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false

namespace StatMech.FrontierA

universe u

variable {V E D Component : Type*}
  [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]
  [Fintype D] [DecidableEq D]
  [Fintype Component] [DecidableEq Component]




structure IsoradialMetricComponentOrientationData
    (Component : Type*) [Fintype Component] [DecidableEq Component]
    (R : RibbonPermutationSystem E D)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (weight : E -> Complex) (conductance transport : V -> V -> Complex) where
  outgoingEdgeSet : (V -> V) -> Finset E
  conductanceMonomial : forall next : V -> V,
    finiteCRSFOutgoingConductance conductance next =
      ∏ edge ∈ outgoingEdgeSet next, weight edge
  supported : Finset E -> Prop
  components : Finset E -> Finset Component
  componentHolonomy : Finset E -> Component -> Complex
  boundaryCoefficient_supported : forall (F : Finset E), supported F ->
    ribbonBoundaryCharacterCoefficient R character F =
      ∏ component : {component // component ∈ components F},
        formanCycleCoefficient (componentHolonomy F component)
  boundaryCoefficient_unsupported : forall (F : Finset E), ¬ supported F ->
    ribbonBoundaryCharacterCoefficient R character F = 0
  fiberEmpty_unsupported : forall (F : Finset E), ¬ supported F ->
    IsEmpty (finiteMapFiber outgoingEdgeSet F)
  orientationOf : forall (F : Finset E) (_hF : supported F),
    finiteMapFiber outgoingEdgeSet F ->
      ({component // component ∈ components F} -> Bool)
  outgoingOfOrientation : forall (F : Finset E) (_hF : supported F),
    ({component // component ∈ components F} -> Bool) ->
      finiteMapFiber outgoingEdgeSet F
  outgoingOf_orientationOf : forall (F : Finset E) (hF : supported F)
      (next : finiteMapFiber outgoingEdgeSet F),
    outgoingOfOrientation F hF (orientationOf F hF next) = next
  orientationOf_outgoingOf : forall (F : Finset E) (hF : supported F)
      (orientation : {component // component ∈ components F} -> Bool),
    orientationOf F hF (outgoingOfOrientation F hF orientation) = orientation
  formanFactor_orientation : forall (F : Finset E) (hF : supported F)
      (next : finiteMapFiber outgoingEdgeSet F),
    (∏ cycle : finiteCRSFAtomicCycle next.1,
      (1 - finiteCRSFAmbientAtomicCycleHolonomy transport cycle)) =
      ∏ component : {component // component ∈ components F},
        if orientationOf F hF next component then
          1 - componentHolonomy F component
        else 1 - (componentHolonomy F component)⁻¹

namespace IsoradialMetricComponentOrientationData



noncomputable def toComponentIdentification
    (R : RibbonPermutationSystem E D)
    (C : CellularRibbonDualData R)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (weight : E -> Complex) (conductance transport : V -> V -> Complex)
    (genus_le_one : C.genus ≤ 1)
    (data : IsoradialMetricComponentOrientationData Component
      R character weight conductance transport) :
    GenusZeroOneRibbonComponentIdentification Component
      R C character weight conductance transport where
  genus_le_one := genus_le_one
  outgoingEdgeSet := data.outgoingEdgeSet
  conductanceMonomial := data.conductanceMonomial
  supported := data.supported
  components := data.components
  componentHolonomy := data.componentHolonomy
  boundaryCoefficient_supported := data.boundaryCoefficient_supported
  boundaryCoefficient_unsupported := data.boundaryCoefficient_unsupported
  fiberEmpty_unsupported := data.fiberEmpty_unsupported
  fiberEquivOrientations := fun F hF =>
    { toFun := data.orientationOf F hF
      invFun := data.outgoingOfOrientation F hF
      left_inv := data.outgoingOf_orientationOf F hF
      right_inv := data.orientationOf_outgoingOf F hF }
  formanFactor_orientation := data.formanFactor_orientation

end IsoradialMetricComponentOrientationData



structure MetricCriticalIsoradialGenusZeroOneEmbedding
    (g : Nat) {GraphVertex : Type u}
    [Fintype GraphVertex] [DecidableEq GraphVertex]
    (G : SimpleGraph GraphVertex) [DecidableRel G.Adj]
    (DualVertex Qprimal Qdual Component : Type u)
    [Fintype DualVertex] [DecidableEq DualVertex]
    [Fintype Qprimal] [DecidableEq Qprimal]
    [Fintype Qdual] [DecidableEq Qdual]
    [Fintype Component] [DecidableEq Component] where
  isoradial : MetricCriticalIsoradialClosedFlatSurfaceEmbedding
    g G DualVertex Qprimal Qdual
  genus_le_one : g ≤ 1
  thetaVertex : GraphVertex -> GraphVertex -> Real
  transport : GraphVertex -> GraphVertex -> Complex
  componentOrientation : IsoradialMetricComponentOrientationData Component
    isoradial.polygonalAtlas.cellular.ribbonSystem isoradial.character
    (fun edge => isoradialCriticalMu (isoradial.theta edge))
    (isoradialMuConductance thetaVertex) transport

namespace MetricCriticalIsoradialGenusZeroOneEmbedding

variable {g : Nat} {GraphVertex : Type u}
  [Fintype GraphVertex] [DecidableEq GraphVertex]
  {G : SimpleGraph GraphVertex} [DecidableRel G.Adj]
  {DualVertex Qprimal Qdual Component : Type u}
  [Fintype DualVertex] [DecidableEq DualVertex]
  [Fintype Qprimal] [DecidableEq Qprimal]
  [Fintype Qdual] [DecidableEq Qdual]
  [Fintype Component] [DecidableEq Component]



noncomputable def toCriticalIsoradialGenusZeroOneEmbedding
    (embedding : MetricCriticalIsoradialGenusZeroOneEmbedding
      g G DualVertex Qprimal Qdual Component) :
    CriticalIsoradialGenusZeroOneEmbedding
      g G DualVertex Qprimal Qdual Component where
  isoradial :=
    embedding.isoradial.toCriticalIsoradialClosedFlatSurfaceEmbedding
  thetaVertex := embedding.thetaVertex
  transport := embedding.transport
  componentIdentification :=
    embedding.componentOrientation.toComponentIdentification
      embedding.isoradial.polygonalAtlas.cellular.ribbonSystem
      embedding.isoradial.polygonalAtlas.cellular.cellularDualData
      embedding.isoradial.character
      (fun edge => isoradialCriticalMu (embedding.isoradial.theta edge))
      (isoradialMuConductance embedding.thetaVertex) embedding.transport
      (by
        change embedding.isoradial.polygonalAtlas.cellular.genus ≤ 1
        rw [embedding.isoradial.polygonalAtlas.genus_eq]
        exact embedding.genus_le_one)



theorem det_eq_laplacian
    (embedding : MetricCriticalIsoradialGenusZeroOneEmbedding
      g G DualVertex Qprimal Qdual Component) :
    (1 - embedding.isoradial.primalKacWard).det =
      (-1 : Complex) ^
          coneExceptionCount embedding.isoradial.primalExceptional *
        kwEulerPowerPrefactor (Fintype.card GraphVertex)
          (Fintype.card (finiteGraphEdge G)) *
        kwLaplacianEdgePrefactor embedding.isoradial.theta *
        (finiteTwistedLaplacian
          (isoradialLaplacianConductance embedding.thetaVertex)
          embedding.transport).det := by
  exact embedding.toCriticalIsoradialGenusZeroOneEmbedding
    |>.det_eq_laplacian

end MetricCriticalIsoradialGenusZeroOneEmbedding

end StatMech.FrontierA
