/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.SurfaceKacWardPolygonalDevelopment
import Code.FrontierA.IsoradialKacWardAtlas














open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false

namespace StatMech.FrontierA

universe u

variable {E D Q : Type*} [Fintype E] [DecidableEq E]
  [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q]





structure IsoradialMetricPermutationExpansion
    {Vertex : Type*} [Fintype Vertex]
    (R : RibbonPermutationSystem E D)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (kacWard : Matrix Q Q Complex) (theta : E -> Real)
    (exceptional : Vertex -> Bool) where
  permutationEdgeSet : Equiv.Perm Q -> Finset E
  normalizedTerm : Equiv.Perm Q -> Complex
  permutationTerm_eq : forall sigma,
    matrixDetPermutationTerm (1 - kacWard) sigma =
      criticalKacWardRibbonPrefactor theta exceptional * normalizedTerm sigma
  normalizedFiber : forall F : Finset E,
    (∑ sigma : finiteMapFiber permutationEdgeSet F,
      normalizedTerm sigma.1) =
        ribbonBoundaryCharacterCoefficient R character F *
          ∏ edge ∈ F, isoradialCriticalMu (theta edge)

namespace IsoradialMetricPermutationExpansion



def toCoefficientIdentification
    {Vertex : Type*} [Fintype Vertex]
    (R : RibbonPermutationSystem E D)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (kacWard : Matrix Q Q Complex) (theta : E -> Real)
    (exceptional : Vertex -> Bool)
    (data : IsoradialMetricPermutationExpansion
      R character kacWard theta exceptional) :
    CriticalKacWardRibbonCoefficientIdentification
      R character kacWard theta exceptional where
  permutationEdgeSet := data.permutationEdgeSet
  coefficientFiber := by
    intro F
    calc
      (∑ sigma : finiteMapFiber data.permutationEdgeSet F,
          matrixDetPermutationTerm (1 - kacWard) sigma.1) =
          ∑ sigma : finiteMapFiber data.permutationEdgeSet F,
            criticalKacWardRibbonPrefactor theta exceptional *
              data.normalizedTerm sigma.1 := by
        apply Finset.sum_congr rfl
        intro sigma _
        exact data.permutationTerm_eq sigma.1
      _ = criticalKacWardRibbonPrefactor theta exceptional *
          ∑ sigma : finiteMapFiber data.permutationEdgeSet F,
            data.normalizedTerm sigma.1 := by
        rw [Finset.mul_sum]
      _ = _ := by rw [data.normalizedFiber F]

end IsoradialMetricPermutationExpansion




structure MetricCriticalIsoradialClosedFlatSurfaceEmbedding
    (g : Nat) {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (DualVertex Qprimal Qdual : Type u)
    [Fintype DualVertex] [DecidableEq DualVertex]
    [Fintype Qprimal] [DecidableEq Qprimal]
    [Fintype Qdual] [DecidableEq Qdual] where
  polygonalAtlas :
    ClosedPolygonalFlatSurfaceGraphAtlas g (Sum V DualVertex) G
  dualVertexCount_eq :
    polygonalAtlas.cellular.faceCount = Fintype.card DualVertex
  theta : finiteGraphEdge G -> Real
  theta_pos : forall edge, 0 < theta edge
  theta_lt : forall edge, theta edge < Real.pi / 2
  primalConeIndex : V -> Nat
  dualConeIndex : DualVertex -> Nat
  primalRhombusIncidence : V -> finiteGraphEdge G -> Nat
  dualRhombusIncidence : DualVertex -> finiteGraphEdge G -> Nat
  primalRhombusIncidence_total : forall edge,
    ∑ vertex : V, primalRhombusIncidence vertex edge = 2
  dualRhombusIncidence_total : forall edge,
    ∑ vertex : DualVertex, dualRhombusIncidence vertex edge = 2
  primalConeAngle : forall vertex,
    (∑ edge : finiteGraphEdge G,
      (primalRhombusIncidence vertex edge : Real) * theta edge) =
        Real.pi * (2 * (primalConeIndex vertex : Real) + 1)
  dualConeAngle : forall vertex,
    (∑ edge : finiteGraphEdge G,
      (dualRhombusIncidence vertex edge : Real) *
        (Real.pi / 2 - theta edge)) =
      Real.pi * (2 * (dualConeIndex vertex : Real) + 1)
  boundaryAngle : forall F : Finset (finiteGraphEdge G),
    Fin (polygonalAtlas.cellular.ribbonSystem.boundaryComponents F) -> Real
  boundaryAngle_sum_zero : forall F : Finset (finiteGraphEdge G),
    ∑ boundary, boundaryAngle F boundary = 0
  primalKacWard : Matrix Qprimal Qprimal Complex
  dualKacWard : Matrix Qdual Qdual Complex
  primalPermutationExpansion : IsoradialMetricPermutationExpansion
    polygonalAtlas.cellular.ribbonSystem
    (fun F boundary => Complex.exp
      ((boundaryAngle F boundary : Complex) * Complex.I))
    primalKacWard theta
    (fun vertex => decide (primalConeIndex vertex % 2 = 1))
  dualPermutationExpansion : IsoradialMetricPermutationExpansion
    polygonalAtlas.cellular.ribbonSystem.dualRibbonSystem
    (polygonalAtlas.cellular.ribbonSystem.dualBoundaryCharacter
      (fun F boundary => Complex.exp
        ((boundaryAngle F boundary : Complex) * Complex.I)))
    dualKacWard (fun edge => Real.pi / 2 - theta edge)
    (fun vertex => decide (dualConeIndex vertex % 2 = 1))

namespace MetricCriticalIsoradialClosedFlatSurfaceEmbedding

variable {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {DualVertex Qprimal Qdual : Type u}
  [Fintype DualVertex] [DecidableEq DualVertex]
  [Fintype Qprimal] [DecidableEq Qprimal]
  [Fintype Qdual] [DecidableEq Qdual]


noncomputable def character
    (embedding : MetricCriticalIsoradialClosedFlatSurfaceEmbedding
      g G DualVertex Qprimal Qdual)
    (F : Finset (finiteGraphEdge G))
    (boundary : Fin
      (embedding.polygonalAtlas.cellular.ribbonSystem.boundaryComponents F)) :
    Complex :=
  Complex.exp ((embedding.boundaryAngle F boundary : Complex) * Complex.I)

theorem character_ne
    (embedding : MetricCriticalIsoradialClosedFlatSurfaceEmbedding
      g G DualVertex Qprimal Qdual)
    (F : Finset (finiteGraphEdge G))
    (boundary : Fin
      (embedding.polygonalAtlas.cellular.ribbonSystem.boundaryComponents F)) :
    embedding.character F boundary ≠ 0 :=
  by
    exact Complex.exp_ne_zero _


theorem character_total
    (embedding : MetricCriticalIsoradialClosedFlatSurfaceEmbedding
      g G DualVertex Qprimal Qdual)
    (F : Finset (finiteGraphEdge G)) :
    ∏ boundary, embedding.character F boundary = 1 := by
  rw [show (∏ boundary, embedding.character F boundary) =
      Complex.exp (∑ boundary,
        ((embedding.boundaryAngle F boundary : Complex) * Complex.I)) by
    simp only [character, Complex.exp_sum]]
  rw [← Finset.sum_mul]
  rw [show (∑ boundary,
      (embedding.boundaryAngle F boundary : Complex)) = 0 by
    exact_mod_cast embedding.boundaryAngle_sum_zero F]
  simp


def primalExceptional
    (embedding : MetricCriticalIsoradialClosedFlatSurfaceEmbedding
      g G DualVertex Qprimal Qdual) (vertex : V) : Bool :=
  decide (embedding.primalConeIndex vertex % 2 = 1)


def dualExceptional
    (embedding : MetricCriticalIsoradialClosedFlatSurfaceEmbedding
      g G DualVertex Qprimal Qdual) (vertex : DualVertex) : Bool :=
  decide (embedding.dualConeIndex vertex % 2 = 1)

@[simp] theorem primalExceptional_iff
    (embedding : MetricCriticalIsoradialClosedFlatSurfaceEmbedding
      g G DualVertex Qprimal Qdual) (vertex : V) :
    embedding.primalExceptional vertex = true ↔
      embedding.primalConeIndex vertex % 2 = 1 := by
  simp [primalExceptional]

@[simp] theorem dualExceptional_iff
    (embedding : MetricCriticalIsoradialClosedFlatSurfaceEmbedding
      g G DualVertex Qprimal Qdual) (vertex : DualVertex) :
    embedding.dualExceptional vertex = true ↔
      embedding.dualConeIndex vertex % 2 = 1 := by
  simp [dualExceptional]




theorem coneIndexGaussBonnet
    (embedding : MetricCriticalIsoradialClosedFlatSurfaceEmbedding
      g G DualVertex Qprimal Qdual) :
    (∑ vertex : V, embedding.primalConeIndex vertex) +
      (∑ vertex : DualVertex, embedding.dualConeIndex vertex) + 1 = g := by
  have hprimal :
      (∑ vertex : V, ∑ edge : finiteGraphEdge G,
        (embedding.primalRhombusIncidence vertex edge : Real) *
          embedding.theta edge) =
      ∑ vertex : V,
        Real.pi *
          (2 * (embedding.primalConeIndex vertex : Real) + 1) := by
    apply Finset.sum_congr rfl
    intro vertex _
    exact embedding.primalConeAngle vertex
  have hdual :
      (∑ vertex : DualVertex, ∑ edge : finiteGraphEdge G,
        (embedding.dualRhombusIncidence vertex edge : Real) *
          (Real.pi / 2 - embedding.theta edge)) =
      ∑ vertex : DualVertex,
        Real.pi *
          (2 * (embedding.dualConeIndex vertex : Real) + 1) := by
    apply Finset.sum_congr rfl
    intro vertex _
    exact embedding.dualConeAngle vertex
  have hprimalTotal :
      (∑ vertex : V, ∑ edge : finiteGraphEdge G,
        (embedding.primalRhombusIncidence vertex edge : Real) *
          embedding.theta edge) =
      2 * ∑ edge : finiteGraphEdge G, embedding.theta edge := by
    rw [Finset.sum_comm]
    calc
      (∑ edge : finiteGraphEdge G, ∑ vertex : V,
          (embedding.primalRhombusIncidence vertex edge : Real) *
            embedding.theta edge) =
          ∑ edge : finiteGraphEdge G,
            ((∑ vertex : V,
              embedding.primalRhombusIncidence vertex edge : Nat) : Real) *
              embedding.theta edge := by
        apply Finset.sum_congr rfl
        intro edge _
        push_cast
        rw [Finset.sum_mul]
      _ = ∑ edge : finiteGraphEdge G, 2 * embedding.theta edge := by
        apply Finset.sum_congr rfl
        intro edge _
        rw [embedding.primalRhombusIncidence_total edge]
        norm_num
      _ = _ := by rw [Finset.mul_sum]
  have hdualTotal :
      (∑ vertex : DualVertex, ∑ edge : finiteGraphEdge G,
        (embedding.dualRhombusIncidence vertex edge : Real) *
          (Real.pi / 2 - embedding.theta edge)) =
      2 * ∑ edge : finiteGraphEdge G,
        (Real.pi / 2 - embedding.theta edge) := by
    rw [Finset.sum_comm]
    calc
      (∑ edge : finiteGraphEdge G, ∑ vertex : DualVertex,
          (embedding.dualRhombusIncidence vertex edge : Real) *
            (Real.pi / 2 - embedding.theta edge)) =
          ∑ edge : finiteGraphEdge G,
            ((∑ vertex : DualVertex,
              embedding.dualRhombusIncidence vertex edge : Nat) : Real) *
              (Real.pi / 2 - embedding.theta edge) := by
        apply Finset.sum_congr rfl
        intro edge _
        push_cast
        rw [Finset.sum_mul]
      _ = ∑ edge : finiteGraphEdge G,
          2 * (Real.pi / 2 - embedding.theta edge) := by
        apply Finset.sum_congr rfl
        intro edge _
        rw [embedding.dualRhombusIncidence_total edge]
        norm_num
      _ = _ := by rw [Finset.mul_sum]
  have hedgeAngles :
      (2 * ∑ edge : finiteGraphEdge G, embedding.theta edge) +
        (2 * ∑ edge : finiteGraphEdge G,
          (Real.pi / 2 - embedding.theta edge)) =
        (Fintype.card (finiteGraphEdge G) : Real) * Real.pi := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  have hconeAngles :
      (∑ vertex : V,
          Real.pi *
            (2 * (embedding.primalConeIndex vertex : Real) + 1)) +
        (∑ vertex : DualVertex,
          Real.pi *
            (2 * (embedding.dualConeIndex vertex : Real) + 1)) =
        (Fintype.card (finiteGraphEdge G) : Real) * Real.pi := by
    rw [← hprimal, ← hdual, hprimalTotal, hdualTotal]
    exact hedgeAngles
  have heuler := embedding.polygonalAtlas.cellular.cellularEuler
  rw [embedding.dualVertexCount_eq,
    embedding.polygonalAtlas.genus_eq] at heuler
  have hedgeCard :
      Fintype.card (finiteGraphEdge G) = G.edgeFinset.card := by
    exact Fintype.card_coe G.edgeFinset
  rw [hedgeCard] at hconeAngles
  simp only [mul_add, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hconeAngles
  have hfactor (x : Real) : Real.pi * (2 * x) =
      (2 * Real.pi) * x := by ring
  simp_rw [hfactor] at hconeAngles
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hconeAngles
  have heulerReal :
      (Fintype.card V : Real) + (Fintype.card DualVertex : Real) +
          2 * (g : Real) =
        (G.edgeFinset.card : Real) + 2 := by
    exact_mod_cast heuler
  have hreal :
      ((∑ vertex : V, embedding.primalConeIndex vertex) : Real) +
        ((∑ vertex : DualVertex,
          embedding.dualConeIndex vertex) : Real) + 1 = (g : Real) := by
    nlinarith [Real.pi_pos, heulerReal]
  exact_mod_cast hreal



noncomputable def toCriticalIsoradialClosedFlatSurfaceEmbedding
    (embedding : MetricCriticalIsoradialClosedFlatSurfaceEmbedding
      g G DualVertex Qprimal Qdual) :
    CriticalIsoradialClosedFlatSurfaceEmbedding
      g G DualVertex Qprimal Qdual where
  atlas := embedding.polygonalAtlas.toClosedMetricFlatSurfaceGraphAtlas
    |>.toClosedFlatSurfaceGraphAtlas
  admissibleConeAngles :=
    embedding.polygonalAtlas.toClosedMetricFlatSurfaceGraphAtlas
      |>.toClosedFlatSurfaceGraphAtlas_admissible
  dualVertexCount_eq := embedding.dualVertexCount_eq
  theta := embedding.theta
  theta_pos := embedding.theta_pos
  theta_lt := embedding.theta_lt
  primalExceptional := embedding.primalExceptional
  dualExceptional := embedding.dualExceptional
  primalConeIndex := embedding.primalConeIndex
  dualConeIndex := embedding.dualConeIndex
  primalExceptional_iff := embedding.primalExceptional_iff
  dualExceptional_iff := embedding.dualExceptional_iff
  coneIndexGaussBonnet := by
    change (∑ vertex : V, embedding.primalConeIndex vertex) +
      (∑ vertex : DualVertex, embedding.dualConeIndex vertex) + 1 =
        embedding.polygonalAtlas.cellular.genus
    rw [embedding.polygonalAtlas.genus_eq]
    exact embedding.coneIndexGaussBonnet
  character := embedding.character
  character_ne := embedding.character_ne
  character_total := embedding.character_total
  primalKacWard := embedding.primalKacWard
  dualKacWard := embedding.dualKacWard
  primalCoefficient :=
    embedding.primalPermutationExpansion.toCoefficientIdentification
      embedding.polygonalAtlas.cellular.ribbonSystem embedding.character
      embedding.primalKacWard embedding.theta embedding.primalExceptional
  dualCoefficient :=
    embedding.dualPermutationExpansion.toCoefficientIdentification
      embedding.polygonalAtlas.cellular.ribbonSystem.dualRibbonSystem
      (embedding.polygonalAtlas.cellular.ribbonSystem.dualBoundaryCharacter
        embedding.character)
      embedding.dualKacWard (fun edge => Real.pi / 2 - embedding.theta edge)
      embedding.dualExceptional



theorem surface_kacWard_arf_formula
    (embedding : MetricCriticalIsoradialClosedFlatSurfaceEmbedding
      g G DualVertex Qprimal Qdual)
    (weight : Sym2 V -> Real) :
    (forall lambda : SurfaceSpinStructure g,
      (1 - surfaceTwistedKacWardMatrix G
          embedding.toCriticalIsoradialClosedFlatSurfaceEmbedding.atlas.phase
          embedding.polygonalAtlas.edgeClass lambda
          (fun edge => (weight edge : Complex))).det =
        (surfaceTwistedSectorSquare
          (surfaceGraphSectorWeight G embedding.polygonalAtlas.edgeClass weight)
          lambda : Complex)) /\
    surfaceUnsignedSectorSum
        (surfaceGraphSectorWeight G embedding.polygonalAtlas.edgeClass weight) =
      ((2 : Real) ^ g)⁻¹ *
        ∑ lambda : SurfaceSpinStructure g,
          surfaceParitySign (surfaceArfParity lambda) *
            surfaceTwistedSectorRoot
              (surfaceGraphSectorWeight G
                embedding.polygonalAtlas.edgeClass weight) lambda := by
  exact embedding.toCriticalIsoradialClosedFlatSurfaceEmbedding
    |>.surface_kacWard_arf_formula weight


theorem normalized_kacWard_duality
    (embedding : MetricCriticalIsoradialClosedFlatSurfaceEmbedding
      g G DualVertex Qprimal Qdual) :
    kwIsoradialDualityNormalization DualVertex
        (fun edge => Real.pi / 2 - embedding.theta edge) *
        (1 - embedding.dualKacWard).det =
      kwIsoradialDualityNormalization V embedding.theta *
        (1 - embedding.primalKacWard).det :=
  embedding.toCriticalIsoradialClosedFlatSurfaceEmbedding
    |>.normalized_kacWard_duality

end MetricCriticalIsoradialClosedFlatSurfaceEmbedding

end StatMech.FrontierA
