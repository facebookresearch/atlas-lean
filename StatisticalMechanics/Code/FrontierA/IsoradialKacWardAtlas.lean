/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.SurfaceKacWardAtlas
import Code.FrontierA.IsoradialDualPrefactor
















open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false

namespace StatMech.FrontierA

universe u







structure CriticalIsoradialClosedFlatSurfaceEmbedding
    (g : Nat) {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (DualVertex Q Qstar : Type u)
    [Fintype DualVertex]
    [Fintype Q] [DecidableEq Q]
    [Fintype Qstar] [DecidableEq Qstar] where
  atlas : ClosedFlatSurfaceGraphAtlas g G
  admissibleConeAngles : atlas.AdmissibleConeAngles
  dualVertexCount_eq : atlas.cellular.faceCount = Fintype.card DualVertex
  theta : finiteGraphEdge G -> Real
  theta_pos : forall edge, 0 < theta edge
  theta_lt : forall edge, theta edge < Real.pi / 2
  primalExceptional : V -> Bool
  dualExceptional : DualVertex -> Bool
  primalConeIndex : V -> Nat
  dualConeIndex : DualVertex -> Nat
  primalExceptional_iff : forall vertex,
    primalExceptional vertex = true ↔ primalConeIndex vertex % 2 = 1
  dualExceptional_iff : forall vertex,
    dualExceptional vertex = true ↔ dualConeIndex vertex % 2 = 1
  coneIndexGaussBonnet :
    (∑ vertex : V, primalConeIndex vertex) +
      (∑ vertex : DualVertex, dualConeIndex vertex) + 1 =
        atlas.cellular.genus
  character : forall F : Finset (finiteGraphEdge G),
    Fin (atlas.cellular.ribbonSystem.boundaryComponents F) -> Complex
  character_ne : forall (F : Finset (finiteGraphEdge G))
    (boundary : Fin (atlas.cellular.ribbonSystem.boundaryComponents F)),
      character F boundary ≠ 0
  character_total : forall F : Finset (finiteGraphEdge G),
    ∏ boundary, character F boundary = 1
  primalKacWard : Matrix Q Q Complex
  dualKacWard : Matrix Qstar Qstar Complex
  primalCoefficient : CriticalKacWardRibbonCoefficientIdentification
    atlas.cellular.ribbonSystem character primalKacWard theta
      primalExceptional
  dualCoefficient : CriticalKacWardRibbonCoefficientIdentification
    atlas.cellular.ribbonSystem.dualRibbonSystem
    (atlas.cellular.ribbonSystem.dualBoundaryCharacter character)
    dualKacWard (fun edge => Real.pi / 2 - theta edge) dualExceptional

namespace CriticalIsoradialClosedFlatSurfaceEmbedding



noncomputable def toAdmissibleClosedFlatSurfaceEmbedding
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {DualVertex Q Qstar : Type u}
    [Fintype DualVertex]
    [Fintype Q] [DecidableEq Q]
    [Fintype Qstar] [DecidableEq Qstar]
    (embedding : CriticalIsoradialClosedFlatSurfaceEmbedding
      g G DualVertex Q Qstar) :
    AdmissibleClosedFlatSurfaceEmbedding g G :=
  embedding.atlas.toAdmissibleEmbedding embedding.admissibleConeAngles



noncomputable def toOddConeGaussBonnetData
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {DualVertex Q Qstar : Type u}
    [Fintype DualVertex]
    [Fintype Q] [DecidableEq Q]
    [Fintype Qstar] [DecidableEq Qstar]
    (embedding : CriticalIsoradialClosedFlatSurfaceEmbedding
      g G DualVertex Q Qstar) :
    IsoradialOddConeGaussBonnetData V DualVertex
      embedding.atlas.cellular.ribbonSystem
      embedding.atlas.cellular.cellularDualData
      embedding.primalExceptional embedding.dualExceptional where
  primalVertexCount_eq := rfl
  dualVertexCount_eq := embedding.dualVertexCount_eq
  primalConeIndex := embedding.primalConeIndex
  dualConeIndex := embedding.dualConeIndex
  primalExceptional_iff := embedding.primalExceptional_iff
  dualExceptional_iff := embedding.dualExceptional_iff
  coneIndexGaussBonnet := embedding.coneIndexGaussBonnet



noncomputable def toDualityCertificate
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {DualVertex Q Qstar : Type u}
    [Fintype DualVertex]
    [Fintype Q] [DecidableEq Q]
    [Fintype Qstar] [DecidableEq Qstar]
    (embedding : CriticalIsoradialClosedFlatSurfaceEmbedding
      g G DualVertex Q Qstar) :
    CriticalIsoradialDualityCertificate
      V DualVertex G.Dart Q Qstar
      embedding.atlas.cellular.ribbonSystem
      embedding.atlas.cellular.cellularDualData
      embedding.character embedding.theta
      embedding.primalExceptional embedding.dualExceptional
      embedding.primalKacWard embedding.dualKacWard where
  theta_pos := embedding.theta_pos
  theta_lt := embedding.theta_lt
  character_ne := embedding.character_ne
  character_total := embedding.character_total
  primalCoefficient := embedding.primalCoefficient
  dualCoefficient := embedding.dualCoefficient
  oddConeGaussBonnet := embedding.toOddConeGaussBonnetData



theorem surface_kacWard_arf_formula
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {DualVertex Q Qstar : Type u}
    [Fintype DualVertex]
    [Fintype Q] [DecidableEq Q]
    [Fintype Qstar] [DecidableEq Qstar]
    (embedding : CriticalIsoradialClosedFlatSurfaceEmbedding
      g G DualVertex Q Qstar)
    (weight : Sym2 V -> Real) :
    (forall lambda : SurfaceSpinStructure g,
      (1 - surfaceTwistedKacWardMatrix G embedding.atlas.phase
          embedding.atlas.edgeClass lambda
          (fun edge => (weight edge : Complex))).det =
        (surfaceTwistedSectorSquare
          (surfaceGraphSectorWeight G embedding.atlas.edgeClass weight)
          lambda : Complex)) /\
    surfaceUnsignedSectorSum
        (surfaceGraphSectorWeight G embedding.atlas.edgeClass weight) =
      ((2 : Real) ^ g)⁻¹ *
        ∑ lambda : SurfaceSpinStructure g,
          surfaceParitySign (surfaceArfParity lambda) *
            surfaceTwistedSectorRoot
              (surfaceGraphSectorWeight G embedding.atlas.edgeClass weight)
              lambda :=
  closedFlatSurfaceAtlas_kacWard_arf_formula G embedding.atlas
    embedding.admissibleConeAngles weight



theorem normalized_kacWard_duality
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {DualVertex Q Qstar : Type u}
    [Fintype DualVertex]
    [Fintype Q] [DecidableEq Q]
    [Fintype Qstar] [DecidableEq Qstar]
    (embedding : CriticalIsoradialClosedFlatSurfaceEmbedding
      g G DualVertex Q Qstar) :
    kwIsoradialDualityNormalization DualVertex
        (fun edge => Real.pi / 2 - embedding.theta edge) *
        (1 - embedding.dualKacWard).det =
      kwIsoradialDualityNormalization V embedding.theta *
        (1 - embedding.primalKacWard).det :=
  embedding.toDualityCertificate.normalized_det_eq
    embedding.atlas.cellular.ribbonSystem
    embedding.atlas.cellular.cellularDualData embedding.character
    embedding.theta embedding.primalExceptional embedding.dualExceptional
    embedding.primalKacWard embedding.dualKacWard

end CriticalIsoradialClosedFlatSurfaceEmbedding

end StatMech.FrontierA
