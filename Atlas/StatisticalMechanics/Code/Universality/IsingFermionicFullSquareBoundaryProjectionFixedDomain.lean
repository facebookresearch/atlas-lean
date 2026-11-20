/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicFullSquareBoundaryProjectionPolynomial
import Code.Universality.IsingFermionicVariableFourthOrderBulk









namespace StatMech.Universality

open Filter Set
open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm


noncomputable def isingFermionicFixedDiamondMesh (k : Nat) : Real :=
  1 / (isingFermionicProjectionPolynomialSide k : Real)

theorem isingFermionicFixedDiamondMesh_nonneg (k : Nat) :
    0 <= isingFermionicFixedDiamondMesh k := by
  unfold isingFermionicFixedDiamondMesh
  positivity

theorem isingFermionicProjectionPolynomialSide_mul_fixedDiamondMesh
    (k : Nat) :
    (isingFermionicProjectionPolynomialSide k : Real) *
        isingFermionicFixedDiamondMesh k = 1 := by
  unfold isingFermionicFixedDiamondMesh
  field_simp [ne_of_gt (isingFermionicProjectionPolynomialSide_pos k)]

theorem isingFermionicFixedDiamondMesh_eq_inv_pow (k : Nat) :
    isingFermionicFixedDiamondMesh k =
      (1 / ((k : Real) + 2)) ^ 5 := by
  unfold isingFermionicFixedDiamondMesh
    isingFermionicProjectionPolynomialSide
    isingFermionicPolynomialSide
  push_cast
  rw [one_div_pow]
  congr 2
  ring

theorem tendsto_isingFermionicFixedDiamondMesh :
    Tendsto isingFermionicFixedDiamondMesh atTop (nhds 0) := by
  let u : Nat -> Real := fun k => 1 / ((k : Real) + 2)
  have hu : Tendsto u atTop (nhds 0) := by
    let v : Nat -> Real := fun k => 1 / ((k : Real) + 1)
    have hv : Tendsto v atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hcomp := hv.comp (tendsto_add_atTop_nat 1)
    convert hcomp using 1
    funext k
    dsimp [u, v, Function.comp_def]
    push_cast
    ring
  have hu5 : Tendsto (fun k => u k ^ 5) atTop (nhds 0) := by
    simpa using hu.pow 5
  convert hu5 using 1
  funext k
  exact isingFermionicFixedDiamondMesh_eq_inv_pow k

theorem tendsto_isingFermionicFixedDiamondMesh_fourthOrder :
    Tendsto (fun k =>
      |isingFermionicFixedDiamondMesh k| ^ 4 *
        (isingFermionicProjectionPolynomialSide k : Real) ^ 2)
      atTop (nhds 0) := by
  have hsq : Tendsto (fun k => isingFermionicFixedDiamondMesh k ^ 2)
      atTop (nhds 0) := by
    simpa using tendsto_isingFermionicFixedDiamondMesh.pow 2
  convert hsq using 1
  funext k
  have hnonneg := isingFermionicFixedDiamondMesh_nonneg k
  have hmul :=
    isingFermionicProjectionPolynomialSide_mul_fixedDiamondMesh k
  rw [abs_of_nonneg hnonneg]
  calc
    isingFermionicFixedDiamondMesh k ^ 4 *
          (isingFermionicProjectionPolynomialSide k : Real) ^ 2 =
        ((isingFermionicProjectionPolynomialSide k : Real) *
          isingFermionicFixedDiamondMesh k) ^ 2 *
            isingFermionicFixedDiamondMesh k ^ 2 := by ring
    _ = isingFermionicFixedDiamondMesh k ^ 2 := by rw [hmul]; norm_num

theorem
    tendsto_isingFermionicProjectionQuadraticLipschitz_mul_fixedDiamondMesh
    (C : NNReal) :
    Tendsto (fun k =>
      (isingFermionicQuadraticLipschitzConstant C (k + 1) : Real) *
        isingFermionicFixedDiamondMesh k) atTop (nhds 0) := by
  let u : Nat -> Real := fun k => 1 / ((k : Real) + 2)
  have hu : Tendsto u atTop (nhds 0) := by
    let v : Nat -> Real := fun k => 1 / ((k : Real) + 1)
    have hv : Tendsto v atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hcomp := hv.comp (tendsto_add_atTop_nat 1)
    convert hcomp using 1
    funext k
    dsimp [u, v, Function.comp_def]
    push_cast
    ring
  have hCu3 : Tendsto (fun k => (C : Real) * u k ^ 3)
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul (hu.pow 3)
  convert hCu3 using 1
  funext k
  have hL :
      (isingFermionicQuadraticLipschitzConstant C (k + 1) : Real) =
        (C : Real) * ((k : Real) + 2) ^ 2 := by
    change (C : Real) * ((((k + 1 + 1 : Nat) : Real) ^ 2)) = _
    push_cast
    ring
  rw [hL, isingFermionicFixedDiamondMesh_eq_inv_pow]
  dsimp [u]
  have hk : (0 : Real) < (k : Real) + 2 := by positivity
  field_simp [hk.ne']




noncomputable def isingFermionicFixedDiamondEndpointLipschitzConstant
    (C : NNReal) (k : Nat) : NNReal :=
  C * ⟨(((k + 2 : Nat) : Real) ^ 4), by positivity⟩

theorem tendsto_isingFermionicFixedDiamondEndpointLipschitz_mul_mesh
    (C : NNReal) :
    Tendsto (fun k =>
      (isingFermionicFixedDiamondEndpointLipschitzConstant C k : Real) *
        isingFermionicFixedDiamondMesh k) atTop (nhds 0) := by
  let u : Nat -> Real := fun k => 1 / ((k : Real) + 2)
  have hu : Tendsto u atTop (nhds 0) := by
    let v : Nat -> Real := fun k => 1 / ((k : Real) + 1)
    have hv : Tendsto v atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hcomp := hv.comp (tendsto_add_atTop_nat 1)
    convert hcomp using 1
    funext k
    dsimp [u, v, Function.comp_def]
    push_cast
    ring
  have hCu : Tendsto (fun k => (C : Real) * u k) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hu
  convert hCu using 1
  funext k
  have hL :
      (isingFermionicFixedDiamondEndpointLipschitzConstant C k : Real) =
        (C : Real) * ((k : Real) + 2) ^ 4 := by
    change (C : Real) * ((((k + 2 : Nat) : Real) ^ 4)) = _
    push_cast
    ring
  rw [hL, isingFermionicFixedDiamondMesh_eq_inv_pow]
  dsimp [u]
  have hk : (0 : Real) < (k : Real) + 2 := by positivity
  field_simp [hk.ne']


def isingFermionicFixedDiamondLeftSide : Set Complex :=
  {z | z.re + z.im = -2}


def isingFermionicFixedDiamondFreeSides : Set Complex :=
  {z | z.re - z.im = -2} ∪
    {z | z.re + z.im = 2} ∪ {z | z.re - z.im = 2}


def isingFermionicFixedClosedDiamond : Set Complex :=
  {z | -2 <= z.re + z.im ∧ z.re + z.im <= 2 ∧
    -2 <= z.re - z.im ∧ z.re - z.im <= 2}

theorem fullSquareScaledVertexEmbedding_mem_fixedClosedDiamond
    (k : Nat)
    (x : FKIsingSquareFullVertexNode
      (isingFermionicProjectionPolynomialSide k)) :
    fullSquareScaledVertexEmbedding
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicFixedDiamondMesh k) x ∈
      isingFermionicFixedClosedDiamond := by
  have hx0 := x.2 0
  have hx1 := x.2 1
  have hmul :=
    isingFermionicProjectionPolynomialSide_mul_fixedDiamondMesh k
  have hmesh := isingFermionicFixedDiamondMesh_nonneg k
  have hmul' : isingFermionicFixedDiamondMesh k *
      (isingFermionicProjectionPolynomialSide k : Real) = 1 := by
    nlinarith
  simp [isingFermionicFixedClosedDiamond,
    fullSquareScaledVertexEmbedding, fullSquareScaledCoordinateEmbedding,
    fkIsingSquareFullVertexCoordinate, fkIsingSquareWiredIntPoint]
  have habs0 : |x.1 0| <=
      (isingFermionicProjectionPolynomialSide k : Int) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hx0
  have habs1 : |x.1 1| <=
      (isingFermionicProjectionPolynomialSide k : Int) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hx1
  have h0lo := (abs_le.mp habs0).1
  have h0hi := (abs_le.mp habs0).2
  have h1lo := (abs_le.mp habs1).1
  have h1hi := (abs_le.mp habs1).2
  have h0loR : -(isingFermionicProjectionPolynomialSide k : Real) <=
      (x.1 0 : Real) := by exact_mod_cast h0lo
  have h0hiR : (x.1 0 : Real) <=
      (isingFermionicProjectionPolynomialSide k : Real) := by
    exact_mod_cast h0hi
  have h1loR : -(isingFermionicProjectionPolynomialSide k : Real) <=
      (x.1 1 : Real) := by exact_mod_cast h1lo
  have h1hiR : (x.1 1 : Real) <=
      (isingFermionicProjectionPolynomialSide k : Real) := by
    exact_mod_cast h1hi
  have h0lo' := mul_le_mul_of_nonneg_left h0loR hmesh
  have h0hi' := mul_le_mul_of_nonneg_left h0hiR hmesh
  have h1lo' := mul_le_mul_of_nonneg_left h1loR hmesh
  have h1hi' := mul_le_mul_of_nonneg_left h1hiR hmesh
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem fullSquareScaledFaceEmbedding_mem_fixedClosedDiamond
    (k : Nat)
    (c : FKIsingSquareFullFaceNode
      (isingFermionicProjectionPolynomialSide k)) :
    fullSquareScaledFaceEmbedding
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicFixedDiamondMesh k) c ∈
      isingFermionicFixedClosedDiamond := by
  have hc0 := c.1.isLt
  have hc1 := c.2.isLt
  have hside : 0 < isingFermionicProjectionPolynomialSide k :=
    isingFermionicProjectionPolynomialSide_pos k
  have hmul :=
    isingFermionicProjectionPolynomialSide_mul_fixedDiamondMesh k
  have hmesh := isingFermionicFixedDiamondMesh_nonneg k
  have hmul' : isingFermionicFixedDiamondMesh k *
      (isingFermionicProjectionPolynomialSide k : Real) = 1 := by
    nlinarith
  have hc0lo : (0 : Real) <= c.1 := by positivity
  have hc1lo : (0 : Real) <= c.2 := by positivity
  have hc0plus : (c.1 : Real) + 1 <=
      2 * (isingFermionicProjectionPolynomialSide k : Real) := by
    exact_mod_cast (Nat.lt_iff_add_one_le.mp hc0)
  have hc1plus : (c.2 : Real) + 1 <=
      2 * (isingFermionicProjectionPolynomialSide k : Real) := by
    exact_mod_cast (Nat.lt_iff_add_one_le.mp hc1)
  have hc0hi : (c.1 : Real) <=
      2 * (isingFermionicProjectionPolynomialSide k : Real) - 1 := by
    linarith
  have hc1hi : (c.2 : Real) <=
      2 * (isingFermionicProjectionPolynomialSide k : Real) - 1 := by
    linarith
  have hc0lo' := mul_nonneg hmesh hc0lo
  have hc1lo' := mul_nonneg hmesh hc1lo
  have hc0hi' := mul_le_mul_of_nonneg_left hc0hi hmesh
  have hc1hi' := mul_le_mul_of_nonneg_left hc1hi hmesh
  simp [isingFermionicFixedClosedDiamond,
    fullSquareScaledFaceEmbedding, fullSquareScaledCoordinateEmbedding,
    fkIsingSquareFullFaceCoordinate, fkIsingSquareInteriorCellKey,
    fkIsingSquareWiredIntPoint]
  push_cast at hc0 hc1
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith



theorem PhysicalEndpointLocalizedMarkedClampedRobinInputs.fixedDiamondRanges
    {Phi : Complex -> Complex}
    (hrange : Set.MapsTo Phi isingFermionicFixedClosedDiamond
      isingFermionicClosedUnitStrip) :
    (forall k x,
      0 <= (Phi (fullSquareScaledVertexEmbedding
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicFixedDiamondMesh k) x)).im /\
      (Phi (fullSquareScaledVertexEmbedding
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicFixedDiamondMesh k) x)).im <= 1) /\
    (forall k c,
      0 <= (Phi (fullSquareScaledFaceEmbedding
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicFixedDiamondMesh k) c)).im /\
      (Phi (fullSquareScaledFaceEmbedding
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicFixedDiamondMesh k) c)).im <= 1) := by
  constructor
  · intro k x
    exact hrange (fullSquareScaledVertexEmbedding_mem_fixedClosedDiamond k x)
  · intro k c
    exact hrange (fullSquareScaledFaceEmbedding_mem_fixedClosedDiamond k c)



theorem
    PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFixedDiamondVariableFourthOrderTraceDataAndMap
    {Phi : Complex -> Complex}
    (Hfourth : PhysicalEndpointVariableFourthOrderBulkData
      isingFermionicProjectionPolynomialSide Phi
      isingFermionicFixedDiamondMesh
      isingFermionicProjectionPolynomialRadius)
    (Hlayer : PhysicalEndpointVariableLayerIncrementData
      isingFermionicProjectionPolynomialSide Phi
      isingFermionicFixedDiamondMesh
      isingFermionicProjectionPolynomialRadius)
    (Htrace : FullSquareOrdinaryBoundaryProjectionTraceData
      isingFermionicProjectionPolynomialSide Phi
      isingFermionicFixedDiamondMesh
      isingFermionicProjectionPolynomialRadius)
    (hrange : Set.MapsTo Phi isingFermionicFixedClosedDiamond
      isingFermionicClosedUnitStrip)
    (hscaledFourth_tendsto : Tendsto (fun k =>
      ((Hfourth.boundOne k + Hfourth.boundTwo k) *
          |isingFermionicFixedDiamondMesh k| ^ 4 / 12) *
        (isingFermionicProjectionPolynomialSide k : Real) ^ 2)
      atTop (nhds 0))
    (htrace_tendsto : Tendsto (fun k =>
      (Htrace.lipschitzConstant k : Real) *
        isingFermionicFixedDiamondMesh k) atTop (nhds 0))
    (hlayer_tendsto : Tendsto (fun k =>
      (Hlayer.constant k : Real) * isingFermionicFixedDiamondMesh k)
      atTop (nhds 0)) :
    PhysicalEndpointLocalizedMarkedClampedRobinInputs
      isingFermionicProjectionPolynomialSide
      isingFermionicProjectionPolynomialSide_pos Phi
      isingFermionicFixedDiamondMesh
      isingFermionicProjectionPolynomialRadius
      (fun k => (Htrace.lipschitzConstant k : Real) *
        isingFermionicFixedDiamondMesh k)
      (fun k => (Hfourth.boundOne k + Hfourth.boundTwo k) *
        |isingFermionicFixedDiamondMesh k| ^ 4 / 12)
      (fun k => (4 * Hlayer.constant k) * isingFermionicFixedDiamondMesh k +
        (3 * isingFermionicGhostCoefficient) *
          ((Htrace.lipschitzConstant k : Real) *
            isingFermionicFixedDiamondMesh k))
      (fun _ => 4 + 3 * isingFermionicGhostCoefficient) := by
  let P : PhysicalEndpointOrdinaryBoundaryProjectionData
      isingFermionicProjectionPolynomialSide Phi
      isingFermionicFixedDiamondMesh
      isingFermionicProjectionPolynomialRadius :=
    Htrace.toProjectionData isingFermionicFixedDiamondMesh_nonneg
  have hranges :=
    PhysicalEndpointLocalizedMarkedClampedRobinInputs.fixedDiamondRanges hrange
  exact
    PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofVariableFourthOrderLayerTraceAndRange
      Hfourth Hlayer
      (P.toOrdinaryTraceData isingFermionicFixedDiamondMesh_nonneg
        htrace_tendsto)
      isingFermionicProjectionPolynomialRadius_pos
      isingFermionicProjectionPolynomialRadius_two_le
      isingFermionicFixedDiamondMesh_nonneg hranges.1 hranges.2
      hscaledFourth_tendsto hlayer_tendsto




theorem
    PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFixedDiamondOrdinaryTracesAndRangeWith
    {Phi : Complex -> Complex}
    (Hfourth : PhysicalEndpointFourthOrderBulkData
      isingFermionicProjectionPolynomialSide Phi
      isingFermionicFixedDiamondMesh
      isingFermionicProjectionPolynomialRadius)
    (Hlayer : PhysicalEndpointLayerIncrementData
      isingFermionicProjectionPolynomialSide Phi
      isingFermionicFixedDiamondMesh
      isingFermionicProjectionPolynomialRadius)
    (L : Nat -> NNReal)
    (hPhi : forall k,
      LipschitzOnWith (L k) (fun z => (Phi z).im)
        (fullSquareOrdinaryBoundaryProjectionCarrier
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicFixedDiamondMesh k)
          (isingFermionicProjectionPolynomialRadius k)))
    (hvertexFixedTrace : forall k x,
      fkIsingSquareFullVertexFixedBoundary
          (isingFermionicProjectionPolynomialSide k) x ->
      Not (0 < fkIsingSquareFullVertexGhostMultiplicity
        (isingFermionicProjectionPolynomialSide k) x) ->
        (Phi (fullSquareVertexBoundaryProjection
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicFixedDiamondMesh k) x)).im = 0)
    (hfaceFixedTrace : forall k c,
      fkIsingSquareFullFaceFixedBoundary
          (isingFermionicProjectionPolynomialSide k) c ->
      Not (0 < fkIsingSquareFullFaceGhostMultiplicity
        (isingFermionicProjectionPolynomialSide k) c) ->
        (Phi (fullSquareFaceFixedBoundaryProjection
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicFixedDiamondMesh k) c)).im = 1)
    (hvertexFreeTrace : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary
        (isingFermionicProjectionPolynomialSide k) x) ->
      0 < fkIsingSquareFullVertexGhostMultiplicity
        (isingFermionicProjectionPolynomialSide k) x ->
      Not (vertexMarkedEndpointLayer
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicProjectionPolynomialRadius k) (some x)) ->
        (Phi (fullSquareVertexFreeBoundaryProjection
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicFixedDiamondMesh k) x)).im = 1)
    (hfaceFreeTrace : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary
        (isingFermionicProjectionPolynomialSide k) c) ->
      0 < fkIsingSquareFullFaceGhostMultiplicity
        (isingFermionicProjectionPolynomialSide k) c ->
      Not (faceMarkedEndpointLayer
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicProjectionPolynomialRadius k) (some c)) ->
        (Phi (fullSquareFaceFreeBoundaryProjection
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicFixedDiamondMesh k) c)).im = 0)
    (hvertexRange : forall k x,
      0 <= (Phi (fullSquareScaledVertexEmbedding
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicFixedDiamondMesh k) x)).im /\
      (Phi (fullSquareScaledVertexEmbedding
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicFixedDiamondMesh k) x)).im <= 1)
    (hfaceRange : forall k c,
      0 <= (Phi (fullSquareScaledFaceEmbedding
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicFixedDiamondMesh k) c)).im /\
      (Phi (fullSquareScaledFaceEmbedding
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicFixedDiamondMesh k) c)).im <= 1)
    (htrace_tendsto : Tendsto (fun k => (L k : Real) *
      isingFermionicFixedDiamondMesh k) atTop (nhds 0)) :
    PhysicalEndpointLocalizedMarkedClampedRobinInputs
      isingFermionicProjectionPolynomialSide
      isingFermionicProjectionPolynomialSide_pos Phi
      isingFermionicFixedDiamondMesh
      isingFermionicProjectionPolynomialRadius
      (fun k => (L k : Real) * isingFermionicFixedDiamondMesh k)
      (fun k => (Hfourth.boundOne + Hfourth.boundTwo) *
        |isingFermionicFixedDiamondMesh k| ^ 4 / 12)
      (fun k => (4 * Hlayer.constant) * isingFermionicFixedDiamondMesh k +
        (3 * isingFermionicGhostCoefficient) *
          ((L k : Real) * isingFermionicFixedDiamondMesh k))
      (fun _ => 4 + 3 * isingFermionicGhostCoefficient) := by
  exact
    PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofCarrierTracesAndRange
      Hfourth Hlayer L hPhi hvertexFixedTrace hfaceFixedTrace
      hvertexFreeTrace hfaceFreeTrace
      isingFermionicProjectionPolynomialRadius_pos
      isingFermionicProjectionPolynomialRadius_two_le
      isingFermionicFixedDiamondMesh_nonneg hvertexRange hfaceRange
      tendsto_isingFermionicFixedDiamondMesh_fourthOrder htrace_tendsto
      tendsto_isingFermionicFixedDiamondMesh



theorem
    PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFixedDiamondOrdinaryTracesAndMapWith
    {Phi : Complex -> Complex}
    (Hfourth : PhysicalEndpointFourthOrderBulkData
      isingFermionicProjectionPolynomialSide Phi
      isingFermionicFixedDiamondMesh
      isingFermionicProjectionPolynomialRadius)
    (Hlayer : PhysicalEndpointLayerIncrementData
      isingFermionicProjectionPolynomialSide Phi
      isingFermionicFixedDiamondMesh
      isingFermionicProjectionPolynomialRadius)
    (L : Nat -> NNReal)
    (hPhi : forall k,
      LipschitzOnWith (L k) (fun z => (Phi z).im)
        (fullSquareOrdinaryBoundaryProjectionCarrier
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicFixedDiamondMesh k)
          (isingFermionicProjectionPolynomialRadius k)))
    (hvertexFixedTrace : forall k x,
      fkIsingSquareFullVertexFixedBoundary
          (isingFermionicProjectionPolynomialSide k) x ->
      Not (0 < fkIsingSquareFullVertexGhostMultiplicity
        (isingFermionicProjectionPolynomialSide k) x) ->
        (Phi (fullSquareVertexBoundaryProjection
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicFixedDiamondMesh k) x)).im = 0)
    (hfaceFixedTrace : forall k c,
      fkIsingSquareFullFaceFixedBoundary
          (isingFermionicProjectionPolynomialSide k) c ->
      Not (0 < fkIsingSquareFullFaceGhostMultiplicity
        (isingFermionicProjectionPolynomialSide k) c) ->
        (Phi (fullSquareFaceFixedBoundaryProjection
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicFixedDiamondMesh k) c)).im = 1)
    (hvertexFreeTrace : forall k x,
      Not (fkIsingSquareFullVertexFixedBoundary
        (isingFermionicProjectionPolynomialSide k) x) ->
      0 < fkIsingSquareFullVertexGhostMultiplicity
        (isingFermionicProjectionPolynomialSide k) x ->
      Not (vertexMarkedEndpointLayer
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicProjectionPolynomialRadius k) (some x)) ->
        (Phi (fullSquareVertexFreeBoundaryProjection
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicFixedDiamondMesh k) x)).im = 1)
    (hfaceFreeTrace : forall k c,
      Not (fkIsingSquareFullFaceFixedBoundary
        (isingFermionicProjectionPolynomialSide k) c) ->
      0 < fkIsingSquareFullFaceGhostMultiplicity
        (isingFermionicProjectionPolynomialSide k) c ->
      Not (faceMarkedEndpointLayer
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicProjectionPolynomialRadius k) (some c)) ->
        (Phi (fullSquareFaceFreeBoundaryProjection
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicFixedDiamondMesh k) c)).im = 0)
    (hrange : Set.MapsTo Phi isingFermionicFixedClosedDiamond
      isingFermionicClosedUnitStrip)
    (htrace_tendsto : Tendsto (fun k => (L k : Real) *
      isingFermionicFixedDiamondMesh k) atTop (nhds 0)) :
    PhysicalEndpointLocalizedMarkedClampedRobinInputs
      isingFermionicProjectionPolynomialSide
      isingFermionicProjectionPolynomialSide_pos Phi
      isingFermionicFixedDiamondMesh
      isingFermionicProjectionPolynomialRadius
      (fun k => (L k : Real) * isingFermionicFixedDiamondMesh k)
      (fun k => (Hfourth.boundOne + Hfourth.boundTwo) *
        |isingFermionicFixedDiamondMesh k| ^ 4 / 12)
      (fun k => (4 * Hlayer.constant) * isingFermionicFixedDiamondMesh k +
        (3 * isingFermionicGhostCoefficient) *
          ((L k : Real) * isingFermionicFixedDiamondMesh k))
      (fun _ => 4 + 3 * isingFermionicGhostCoefficient) := by
  have hranges :=
    PhysicalEndpointLocalizedMarkedClampedRobinInputs.fixedDiamondRanges hrange
  exact
    PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFixedDiamondOrdinaryTracesAndRangeWith
      Hfourth Hlayer L hPhi hvertexFixedTrace hfaceFixedTrace
      hvertexFreeTrace hfaceFreeTrace hranges.1 hranges.2 htrace_tendsto

theorem fullSquareScaledLeftSide_fixedDiamond (k : Nat) :
    fullSquareScaledLeftSide
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicFixedDiamondMesh k) =
      isingFermionicFixedDiamondLeftSide := by
  ext z
  simp only [fullSquareScaledLeftSide, isingFermionicFixedDiamondLeftSide,
    Set.mem_setOf_eq]
  have hmul :=
    isingFermionicProjectionPolynomialSide_mul_fixedDiamondMesh k
  have hscale :
      -2 * (isingFermionicProjectionPolynomialSide k : Real) *
          isingFermionicFixedDiamondMesh k = -2 := by
    calc
      _ = -2 * ((isingFermionicProjectionPolynomialSide k : Real) *
          isingFermionicFixedDiamondMesh k) := by ring
      _ = -2 := by rw [hmul]; norm_num
  rw [hscale]

theorem fullSquareScaledFreeSides_fixedDiamond (k : Nat) :
    fullSquareScaledFreeSides
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicFixedDiamondMesh k) =
      isingFermionicFixedDiamondFreeSides := by
  ext z
  simp only [fullSquareScaledFreeSides, fullSquareScaledBottomSide,
    fullSquareScaledRightSide, fullSquareScaledTopSide,
    isingFermionicFixedDiamondFreeSides, Set.mem_union,
    Set.mem_setOf_eq]
  have hmul :=
    isingFermionicProjectionPolynomialSide_mul_fixedDiamondMesh k
  have hpos :
      2 * (isingFermionicProjectionPolynomialSide k : Real) *
          isingFermionicFixedDiamondMesh k = 2 := by
    calc
      _ = 2 * ((isingFermionicProjectionPolynomialSide k : Real) *
          isingFermionicFixedDiamondMesh k) := by ring
      _ = 2 := by rw [hmul]; norm_num
  have hneg :
      -2 * (isingFermionicProjectionPolynomialSide k : Real) *
          isingFermionicFixedDiamondMesh k = -2 := by
    calc
      _ = -2 * ((isingFermionicProjectionPolynomialSide k : Real) *
          isingFermionicFixedDiamondMesh k) := by ring
      _ = -2 := by rw [hmul]; norm_num
  rw [hneg, hpos]



theorem
    PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFixedDiamondCarrierTracesAndRangeWith
    {Phi : Complex -> Complex}
    (Hfourth : PhysicalEndpointFourthOrderBulkData
      isingFermionicProjectionPolynomialSide Phi
      isingFermionicFixedDiamondMesh
      isingFermionicProjectionPolynomialRadius)
    (Hlayer : PhysicalEndpointLayerIncrementData
      isingFermionicProjectionPolynomialSide Phi
      isingFermionicFixedDiamondMesh
      isingFermionicProjectionPolynomialRadius)
    (L : Nat -> NNReal)
    (hPhi : forall k,
      LipschitzOnWith (L k) (fun z => (Phi z).im)
        (fullSquareOrdinaryBoundaryProjectionCarrier
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicFixedDiamondMesh k)
          (isingFermionicProjectionPolynomialRadius k)))
    (hleftTrace : Set.EqOn (fun z => (Phi z).im) (fun _ => 0)
      isingFermionicFixedDiamondLeftSide)
    (hfreeTrace : Set.EqOn (fun z => (Phi z).im) (fun _ => 1)
      isingFermionicFixedDiamondFreeSides)
    (hvertexRange : forall k x,
      0 <= (Phi (fullSquareScaledVertexEmbedding
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicFixedDiamondMesh k) x)).im /\
      (Phi (fullSquareScaledVertexEmbedding
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicFixedDiamondMesh k) x)).im <= 1)
    (hfaceRange : forall k c,
      0 <= (Phi (fullSquareScaledFaceEmbedding
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicFixedDiamondMesh k) c)).im /\
      (Phi (fullSquareScaledFaceEmbedding
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicFixedDiamondMesh k) c)).im <= 1)
    (htrace_tendsto : Tendsto (fun k => (L k : Real) *
      isingFermionicFixedDiamondMesh k) atTop (nhds 0)) :
    PhysicalEndpointLocalizedMarkedClampedRobinInputs
      isingFermionicProjectionPolynomialSide
      isingFermionicProjectionPolynomialSide_pos Phi
      isingFermionicFixedDiamondMesh
      isingFermionicProjectionPolynomialRadius
      (fun k => (L k : Real) * isingFermionicFixedDiamondMesh k)
      (fun k => (Hfourth.boundOne + Hfourth.boundTwo) *
        |isingFermionicFixedDiamondMesh k| ^ 4 / 12)
      (fun k => (4 * Hlayer.constant) * isingFermionicFixedDiamondMesh k +
        (3 * isingFermionicGhostCoefficient) *
          ((L k : Real) * isingFermionicFixedDiamondMesh k))
      (fun _ => 4 + 3 * isingFermionicGhostCoefficient) := by
  apply
    PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofCarrierSideTracesAndRange
      Hfourth Hlayer L hPhi
  · intro k
    simpa [fullSquareScaledLeftSide_fixedDiamond k] using hleftTrace
  · intro k
    simpa [fullSquareScaledFreeSides_fixedDiamond k] using hfreeTrace
  · exact isingFermionicProjectionPolynomialRadius_pos
  · exact isingFermionicProjectionPolynomialRadius_two_le
  · exact isingFermionicFixedDiamondMesh_nonneg
  · exact hvertexRange
  · exact hfaceRange
  · exact tendsto_isingFermionicFixedDiamondMesh_fourthOrder
  · exact htrace_tendsto
  · exact tendsto_isingFermionicFixedDiamondMesh



theorem
    PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFixedDiamondCarrierTracesAndRange
    {Phi : Complex -> Complex}
    (Hfourth : PhysicalEndpointFourthOrderBulkData
      isingFermionicProjectionPolynomialSide Phi
      isingFermionicFixedDiamondMesh
      isingFermionicProjectionPolynomialRadius)
    (Hlayer : PhysicalEndpointLayerIncrementData
      isingFermionicProjectionPolynomialSide Phi
      isingFermionicFixedDiamondMesh
      isingFermionicProjectionPolynomialRadius)
    (C : NNReal)
    (hPhi : forall k,
      LipschitzOnWith (isingFermionicQuadraticLipschitzConstant C (k + 1))
        (fun z => (Phi z).im)
        (fullSquareOrdinaryBoundaryProjectionCarrier
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicFixedDiamondMesh k)
          (isingFermionicProjectionPolynomialRadius k)))
    (hleftTrace : Set.EqOn (fun z => (Phi z).im) (fun _ => 0)
      isingFermionicFixedDiamondLeftSide)
    (hfreeTrace : Set.EqOn (fun z => (Phi z).im) (fun _ => 1)
      isingFermionicFixedDiamondFreeSides)
    (hvertexRange : forall k x,
      0 <= (Phi (fullSquareScaledVertexEmbedding
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicFixedDiamondMesh k) x)).im /\
      (Phi (fullSquareScaledVertexEmbedding
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicFixedDiamondMesh k) x)).im <= 1)
    (hfaceRange : forall k c,
      0 <= (Phi (fullSquareScaledFaceEmbedding
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicFixedDiamondMesh k) c)).im /\
      (Phi (fullSquareScaledFaceEmbedding
        (isingFermionicProjectionPolynomialSide k)
        (isingFermionicFixedDiamondMesh k) c)).im <= 1) :
    PhysicalEndpointLocalizedMarkedClampedRobinInputs
      isingFermionicProjectionPolynomialSide
      isingFermionicProjectionPolynomialSide_pos Phi
      isingFermionicFixedDiamondMesh
      isingFermionicProjectionPolynomialRadius
      (fun k =>
        (isingFermionicQuadraticLipschitzConstant C (k + 1) : Real) *
          isingFermionicFixedDiamondMesh k)
      (fun k => (Hfourth.boundOne + Hfourth.boundTwo) *
        |isingFermionicFixedDiamondMesh k| ^ 4 / 12)
      (fun k => (4 * Hlayer.constant) * isingFermionicFixedDiamondMesh k +
        (3 * isingFermionicGhostCoefficient) *
          ((isingFermionicQuadraticLipschitzConstant C (k + 1) : Real) *
            isingFermionicFixedDiamondMesh k))
      (fun _ => 4 + 3 * isingFermionicGhostCoefficient) := by
  exact
    PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFixedDiamondCarrierTracesAndRangeWith
      Hfourth Hlayer
      (fun k => isingFermionicQuadraticLipschitzConstant C (k + 1))
      hPhi hleftTrace hfreeTrace hvertexRange hfaceRange
      (tendsto_isingFermionicProjectionQuadraticLipschitz_mul_fixedDiamondMesh C)



theorem
    PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFixedDiamondMapWith
    {Phi : Complex -> Complex}
    (Hfourth : PhysicalEndpointFourthOrderBulkData
      isingFermionicProjectionPolynomialSide Phi
      isingFermionicFixedDiamondMesh
      isingFermionicProjectionPolynomialRadius)
    (Hlayer : PhysicalEndpointLayerIncrementData
      isingFermionicProjectionPolynomialSide Phi
      isingFermionicFixedDiamondMesh
      isingFermionicProjectionPolynomialRadius)
    (L : Nat -> NNReal)
    (hPhi : forall k,
      LipschitzOnWith (L k) (fun z => (Phi z).im)
        (fullSquareOrdinaryBoundaryProjectionCarrier
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicFixedDiamondMesh k)
          (isingFermionicProjectionPolynomialRadius k)))
    (hleftTrace : Set.EqOn (fun z => (Phi z).im) (fun _ => 0)
      isingFermionicFixedDiamondLeftSide)
    (hfreeTrace : Set.EqOn (fun z => (Phi z).im) (fun _ => 1)
      isingFermionicFixedDiamondFreeSides)
    (hrange : Set.MapsTo Phi isingFermionicFixedClosedDiamond
      isingFermionicClosedUnitStrip)
    (htrace_tendsto : Tendsto (fun k => (L k : Real) *
      isingFermionicFixedDiamondMesh k) atTop (nhds 0)) :
    PhysicalEndpointLocalizedMarkedClampedRobinInputs
      isingFermionicProjectionPolynomialSide
      isingFermionicProjectionPolynomialSide_pos Phi
      isingFermionicFixedDiamondMesh
      isingFermionicProjectionPolynomialRadius
      (fun k => (L k : Real) * isingFermionicFixedDiamondMesh k)
      (fun k => (Hfourth.boundOne + Hfourth.boundTwo) *
        |isingFermionicFixedDiamondMesh k| ^ 4 / 12)
      (fun k => (4 * Hlayer.constant) * isingFermionicFixedDiamondMesh k +
        (3 * isingFermionicGhostCoefficient) *
          ((L k : Real) * isingFermionicFixedDiamondMesh k))
      (fun _ => 4 + 3 * isingFermionicGhostCoefficient) := by
  have hranges :=
    PhysicalEndpointLocalizedMarkedClampedRobinInputs.fixedDiamondRanges hrange
  exact
    PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFixedDiamondCarrierTracesAndRangeWith
      Hfourth Hlayer L hPhi hleftTrace hfreeTrace hranges.1 hranges.2
        htrace_tendsto


theorem
    PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFixedDiamondMap
    {Phi : Complex -> Complex}
    (Hfourth : PhysicalEndpointFourthOrderBulkData
      isingFermionicProjectionPolynomialSide Phi
      isingFermionicFixedDiamondMesh
      isingFermionicProjectionPolynomialRadius)
    (Hlayer : PhysicalEndpointLayerIncrementData
      isingFermionicProjectionPolynomialSide Phi
      isingFermionicFixedDiamondMesh
      isingFermionicProjectionPolynomialRadius)
    (C : NNReal)
    (hPhi : forall k,
      LipschitzOnWith (isingFermionicQuadraticLipschitzConstant C (k + 1))
        (fun z => (Phi z).im)
        (fullSquareOrdinaryBoundaryProjectionCarrier
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicFixedDiamondMesh k)
          (isingFermionicProjectionPolynomialRadius k)))
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
        (isingFermionicQuadraticLipschitzConstant C (k + 1) : Real) *
          isingFermionicFixedDiamondMesh k)
      (fun k => (Hfourth.boundOne + Hfourth.boundTwo) *
        |isingFermionicFixedDiamondMesh k| ^ 4 / 12)
      (fun k => (4 * Hlayer.constant) * isingFermionicFixedDiamondMesh k +
        (3 * isingFermionicGhostCoefficient) *
          ((isingFermionicQuadraticLipschitzConstant C (k + 1) : Real) *
            isingFermionicFixedDiamondMesh k))
      (fun _ => 4 + 3 * isingFermionicGhostCoefficient) := by
  exact
    PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFixedDiamondMapWith
      Hfourth Hlayer
      (fun k => isingFermionicQuadraticLipschitzConstant C (k + 1))
      hPhi hleftTrace hfreeTrace hrange
      (tendsto_isingFermionicProjectionQuadraticLipschitz_mul_fixedDiamondMesh C)



theorem
    PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFixedDiamondEndpointLipschitzMap
    {Phi : Complex -> Complex}
    (Hfourth : PhysicalEndpointFourthOrderBulkData
      isingFermionicProjectionPolynomialSide Phi
      isingFermionicFixedDiamondMesh
      isingFermionicProjectionPolynomialRadius)
    (Hlayer : PhysicalEndpointLayerIncrementData
      isingFermionicProjectionPolynomialSide Phi
      isingFermionicFixedDiamondMesh
      isingFermionicProjectionPolynomialRadius)
    (C : NNReal)
    (hPhi : forall k,
      LipschitzOnWith
        (isingFermionicFixedDiamondEndpointLipschitzConstant C k)
        (fun z => (Phi z).im)
        (fullSquareOrdinaryBoundaryProjectionCarrier
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicFixedDiamondMesh k)
          (isingFermionicProjectionPolynomialRadius k)))
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
        (isingFermionicFixedDiamondEndpointLipschitzConstant C k : Real) *
          isingFermionicFixedDiamondMesh k)
      (fun k => (Hfourth.boundOne + Hfourth.boundTwo) *
        |isingFermionicFixedDiamondMesh k| ^ 4 / 12)
      (fun k => (4 * Hlayer.constant) * isingFermionicFixedDiamondMesh k +
        (3 * isingFermionicGhostCoefficient) *
          ((isingFermionicFixedDiamondEndpointLipschitzConstant C k : Real) *
            isingFermionicFixedDiamondMesh k))
      (fun _ => 4 + 3 * isingFermionicGhostCoefficient) := by
  exact
    PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFixedDiamondMapWith
      Hfourth Hlayer
      (isingFermionicFixedDiamondEndpointLipschitzConstant C)
      hPhi hleftTrace hfreeTrace hrange
      (tendsto_isingFermionicFixedDiamondEndpointLipschitz_mul_mesh C)




theorem
    PhysicalEndpointLocalizedMarkedClampedRobinInputs.primitive_convergence_away_fixedDiamond
    {Phi : Complex -> Complex}
    {boundaryRate bulkRate layerRate : Nat -> Real}
    (H : PhysicalEndpointLocalizedMarkedClampedRobinInputs
      isingFermionicProjectionPolynomialSide
      isingFermionicProjectionPolynomialSide_pos Phi
      isingFermionicFixedDiamondMesh
      isingFermionicProjectionPolynomialRadius boundaryRate bulkRate layerRate
      (fun _ => 4 + 3 * isingFermionicGhostCoefficient))
    (mismatchRate : Nat -> Real)
    (hmismatch_nonneg : forall k, 0 <= mismatchRate k)
    (hmismatch : forall k e, PhysicalProjectionPolynomialEndpointSafe k e ->
      |(Phi (fullSquareScaledFaceEmbedding
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicFixedDiamondMesh k)
          (fkIsingSquareFullFaceOfRadialIncidence
            (isingFermionicProjectionPolynomialSide k)
            (isingFermionicProjectionPolynomialSide_pos k) e))).im -
        (Phi (fullSquareScaledVertexEmbedding
          (isingFermionicProjectionPolynomialSide k)
          (isingFermionicFixedDiamondMesh k)
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
                (isingFermionicProjectionPolynomialSide k)
                (isingFermionicFixedDiamondMesh k)
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
                (isingFermionicProjectionPolynomialSide k)
                (isingFermionicFixedDiamondMesh k)
                (fkIsingSquareInteriorRadialEndpoint
                  (isingFermionicProjectionPolynomialSide k)
                  (isingFermionicProjectionPolynomialSide_pos k) e))).im| < eta)
      atTop := by
  exact H.primitive_convergence_away_projectionPolynomial mismatchRate
    hmismatch_nonneg hmismatch hmismatch_tendsto

end FKIsingSquareBoundaryLayerCoordinateOneForm

end

end StatMech.Universality
