/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsoradialKacWardAtlas
import Code.FrontierA.IsoradialKacWardRibbonIdentification














open SimpleGraph

set_option linter.unusedDecidableInType false

namespace StatMech.FrontierA

universe u



structure CriticalIsoradialGenusZeroOneEmbedding
    (g : Nat) {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (DualVertex Q Qstar Component : Type u)
    [Fintype DualVertex]
    [Fintype Q] [DecidableEq Q]
    [Fintype Qstar] [DecidableEq Qstar]
    [Fintype Component] [DecidableEq Component] where
  isoradial : CriticalIsoradialClosedFlatSurfaceEmbedding
    g G DualVertex Q Qstar
  thetaVertex : V -> V -> Real
  transport : V -> V -> Complex
  componentIdentification : GenusZeroOneRibbonComponentIdentification
    Component isoradial.atlas.cellular.ribbonSystem
    isoradial.atlas.cellular.cellularDualData isoradial.character
    (fun edge => isoradialCriticalMu (isoradial.theta edge))
    (isoradialMuConductance thetaVertex) transport

namespace CriticalIsoradialGenusZeroOneEmbedding



noncomputable def toRibbonCertificate
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {DualVertex Q Qstar Component : Type u}
    [Fintype DualVertex]
    [Fintype Q] [DecidableEq Q]
    [Fintype Qstar] [DecidableEq Qstar]
    [Fintype Component] [DecidableEq Component]
    (embedding : CriticalIsoradialGenusZeroOneEmbedding
      g G DualVertex Q Qstar Component) :
    CriticalIsoradialEmbeddingRibbonCertificate Component
      embedding.isoradial.atlas.cellular.ribbonSystem
      embedding.isoradial.atlas.cellular.cellularDualData
      embedding.isoradial.character embedding.isoradial.primalKacWard
      embedding.thetaVertex embedding.isoradial.theta embedding.transport
      embedding.isoradial.primalExceptional where
  componentIdentification := embedding.componentIdentification
  coefficientIdentification := embedding.isoradial.primalCoefficient




theorem det_eq_laplacian
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {DualVertex Q Qstar Component : Type u}
    [Fintype DualVertex]
    [Fintype Q] [DecidableEq Q]
    [Fintype Qstar] [DecidableEq Qstar]
    [Fintype Component] [DecidableEq Component]
    (embedding : CriticalIsoradialGenusZeroOneEmbedding
      g G DualVertex Q Qstar Component) :
    (1 - embedding.isoradial.primalKacWard).det =
      (-1 : Complex) ^
          coneExceptionCount embedding.isoradial.primalExceptional *
        kwEulerPowerPrefactor (Fintype.card V)
          (Fintype.card (finiteGraphEdge G)) *
        kwLaplacianEdgePrefactor embedding.isoradial.theta *
        (finiteTwistedLaplacian
          (isoradialLaplacianConductance embedding.thetaVertex)
          embedding.transport).det :=
  embedding.toRibbonCertificate.det_eq_laplacian
    embedding.isoradial.atlas.cellular.ribbonSystem
    embedding.isoradial.atlas.cellular.cellularDualData
    embedding.isoradial.character embedding.isoradial.primalKacWard
    embedding.thetaVertex embedding.isoradial.theta embedding.transport
    embedding.isoradial.primalExceptional

end CriticalIsoradialGenusZeroOneEmbedding

end StatMech.FrontierA
