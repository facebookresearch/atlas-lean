/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FK.TriHexFKGlobalSweep
import Code.FK.PeriodicPlanarGraph
import Code.Lattice.BoundaryConditions















open Finset

namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

noncomputable section



def triHexFKTerminalWiredGraph
    {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype V] [DecidableEq V]
    (terminal : ι → Fin 3 → V) (boundary : V → Prop)
    [DecidablePred boundary]
    (sector : ι → ThreeTerminalConnectivity) : SimpleGraph V :=
  triHexFKTerminalSectorGraph terminal sector ⊔ boundaryCliqueGraph boundary



def triHexFKTerminalWiredExternal
    {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype V] [DecidableEq V]
    (q : Real) (terminal : ι → Fin 3 → V) (boundary : V → Prop)
    [DecidablePred boundary]
    (sector : ι → ThreeTerminalConnectivity) : Real :=
  q ^ Nat.card (triHexFKTerminalWiredGraph terminal boundary sector).ConnectedComponent



def triHexFKTerminalBoundaryReachObservable
    {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype V] [DecidableEq V]
    (terminal : ι → Fin 3 → V) (boundary : V → Prop)
    [DecidablePred boundary] (root : V)
    (sector : ι → ThreeTerminalConnectivity) : Real := by
  classical
  exact if ∃ y : V, boundary y ∧
      (triHexFKTerminalSectorGraph terminal sector).Reachable root y then 1 else 0



def triangleFKFiniteWiredBoundaryReachRatio
    {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype V] [DecidableEq V]
    (q y0 y1 y2 : Real) (terminal : ι → Fin 3 → V)
    (boundary : V → Prop) [DecidablePred boundary] (root : V) : Real :=
  triangleFKGlobalConfigSum y0 y1 y2
      (fun sector => triHexFKTerminalWiredExternal q terminal boundary sector *
        triHexFKTerminalBoundaryReachObservable terminal boundary root sector) /
    triangleFKGlobalConfigSum y0 y1 y2
      (triHexFKTerminalWiredExternal q terminal boundary)



def starFKFiniteWiredBoundaryReachRatio
    {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype V] [DecidableEq V]
    (q y0 y1 y2 : Real) (terminal : ι → Fin 3 → V)
    (boundary : V → Prop) [DecidablePred boundary] (root : V) : Real :=
  starFKGlobalConfigSum q y0 y1 y2
      (fun sector => triHexFKTerminalWiredExternal q terminal boundary sector *
        triHexFKTerminalBoundaryReachObservable terminal boundary root sector) /
    starFKGlobalConfigSum q y0 y1 y2
      (triHexFKTerminalWiredExternal q terminal boundary)






theorem triHexFK_finiteWiredBoundaryReachRatio_eq
    {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype V] [DecidableEq V]
    {q y0 y1 y2 y0Star y1Star y2Star : Real}
    (hq : q ≠ 0) (hyprod : y0 * y1 * y2 ≠ 0)
    (h0 : y0 * y0Star = q) (h1 : y1 * y1Star = q)
    (h2 : y2 * y2Star = q)
    (hsurface : FrontierA.triangularFKCriticalSurface q y0 y1 y2 = 0)
    (terminal : ι → Fin 3 → V) (boundary : V → Prop)
    [DecidablePred boundary] (root : V) :
    starFKFiniteWiredBoundaryReachRatio q y0Star y1Star y2Star
        terminal boundary root =
      triangleFKFiniteWiredBoundaryReachRatio q y0 y1 y2
        terminal boundary root := by
  unfold starFKFiniteWiredBoundaryReachRatio
    triangleFKFiniteWiredBoundaryReachRatio
  rw [starFKGlobalConfigSum_eq_sweepSum,
    starFKGlobalConfigSum_eq_sweepSum,
    triangleFKGlobalConfigSum_eq_sweepSum,
    triangleFKGlobalConfigSum_eq_sweepSum]
  exact triHexFK_globalSweepRatio_eq hq hyprod h0 h1 h2 hsurface
    (triHexFKTerminalWiredExternal q terminal boundary)
    (triHexFKTerminalBoundaryReachObservable terminal boundary root)



theorem triHexFK_finiteWiredBoundaryReachRatio_eq_homogeneous
    {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype V] [DecidableEq V]
    {q p : Real} (hq : 0 < q) (hp : p ∈ Set.Ioo (0 : Real) 1)
    (hsurface : FrontierA.triangularFKCriticalPolynomial q
      (FrontierA.fkEdgeOdds p) = 0)
    (terminal : ι → Fin 3 → V) (boundary : V → Prop)
    [DecidablePred boundary] (root : V) :
    starFKFiniteWiredBoundaryReachRatio q
        (FrontierA.fkEdgeOdds (BeffaraDC.dualParam p q))
        (FrontierA.fkEdgeOdds (BeffaraDC.dualParam p q))
        (FrontierA.fkEdgeOdds (BeffaraDC.dualParam p q))
        terminal boundary root =
      triangleFKFiniteWiredBoundaryReachRatio q
        (FrontierA.fkEdgeOdds p) (FrontierA.fkEdgeOdds p)
        (FrontierA.fkEdgeOdds p) terminal boundary root := by
  have hy : 0 < FrontierA.fkEdgeOdds p :=
    div_pos hp.1 (sub_pos.mpr hp.2)
  have hdual := FrontierA.fkEdgeOdds_mul_dualParam hp.1 hp.2 hq
  apply triHexFK_finiteWiredBoundaryReachRatio_eq hq.ne'
    (mul_ne_zero (mul_ne_zero hy.ne' hy.ne') hy.ne')
    hdual hdual hdual
  rwa [FrontierA.triangularFKCriticalSurface_diagonal]




structure TriHexFiniteWiredLevel where
  Cell : Type
  Vertex : Type
  cellFintype : Fintype Cell
  cellDecidableEq : DecidableEq Cell
  vertexFintype : Fintype Vertex
  vertexDecidableEq : DecidableEq Vertex
  terminal : Cell → Fin 3 → Vertex
  boundary : Vertex → Prop
  boundaryDecidable : DecidablePred boundary
  root : Vertex


def TriHexFiniteWiredLevel.triangleBoundaryReachRatio
    (D : TriHexFiniteWiredLevel) (q p : Real) : Real := by
  letI := D.cellFintype
  letI := D.cellDecidableEq
  letI := D.vertexFintype
  letI := D.vertexDecidableEq
  letI := D.boundaryDecidable
  exact triangleFKFiniteWiredBoundaryReachRatio q
    (FrontierA.fkEdgeOdds p) (FrontierA.fkEdgeOdds p)
    (FrontierA.fkEdgeOdds p) D.terminal D.boundary D.root



def TriHexFiniteWiredLevel.starBoundaryReachRatio
    (D : TriHexFiniteWiredLevel) (q p : Real) : Real := by
  letI := D.cellFintype
  letI := D.cellDecidableEq
  letI := D.vertexFintype
  letI := D.vertexDecidableEq
  letI := D.boundaryDecidable
  let pStar := BeffaraDC.dualParam p q
  exact starFKFiniteWiredBoundaryReachRatio q
    (FrontierA.fkEdgeOdds pStar) (FrontierA.fkEdgeOdds pStar)
    (FrontierA.fkEdgeOdds pStar) D.terminal D.boundary D.root


theorem TriHexFiniteWiredLevel.starBoundaryReachRatio_eq_triangle
    (D : TriHexFiniteWiredLevel) {q p : Real}
    (hq : 0 < q) (hp : p ∈ Set.Ioo (0 : Real) 1)
    (hsurface : FrontierA.triangularFKCriticalPolynomial q
      (FrontierA.fkEdgeOdds p) = 0) :
    D.starBoundaryReachRatio q p = D.triangleBoundaryReachRatio q p := by
  letI := D.cellFintype
  letI := D.cellDecidableEq
  letI := D.vertexFintype
  letI := D.vertexDecidableEq
  letI := D.boundaryDecidable
  exact triHexFK_finiteWiredBoundaryReachRatio_eq_homogeneous
    hq hp hsurface D.terminal D.boundary D.root





theorem triHexFK_finiteWiredExhaustion_tendsto_iff_homogeneous
    (D : Nat → TriHexFiniteWiredLevel) {q p theta : Real}
    (hq : 0 < q) (hp : p ∈ Set.Ioo (0 : Real) 1)
    (hsurface : FrontierA.triangularFKCriticalPolynomial q
      (FrontierA.fkEdgeOdds p) = 0) :
    Filter.Tendsto (fun n => (D n).starBoundaryReachRatio q p)
        Filter.atTop (nhds theta) ↔
      Filter.Tendsto (fun n => (D n).triangleBoundaryReachRatio q p)
        Filter.atTop (nhds theta) := by
  have hseq : (fun n => (D n).starBoundaryReachRatio q p) =
      fun n => (D n).triangleBoundaryReachRatio q p := by
    funext n
    exact (D n).starBoundaryReachRatio_eq_triangle hq hp hsurface
  rw [hseq]





abbrev TriHexPlanarFiniteCell (n : Nat) :=
  {z : Site 2 // z ∈ box 2 n}

noncomputable instance triHexPlanarFiniteCellFintype (n : Nat) :
    Fintype (TriHexPlanarFiniteCell n) :=
  (box_finite 2 n).fintype


def triHexPlanarCellTerminal (z : Site 2) (i : Fin 3) : Site 2 :=
  z + hexagonalStep i


noncomputable def triHexPlanarFiniteTerminalFinset (n : Nat) : Finset (Site 2) :=
  (((box_finite 2 n).toFinset ×ˢ (Finset.univ : Finset (Fin 3))).image
    fun zi => triHexPlanarCellTerminal zi.1 zi.2)

abbrev TriHexPlanarFiniteTerminal (n : Nat) :=
  {v : Site 2 // v ∈ triHexPlanarFiniteTerminalFinset n}


noncomputable def triHexPlanarFiniteTerminalMap (n : Nat)
    (z : TriHexPlanarFiniteCell n) (i : Fin 3) :
    TriHexPlanarFiniteTerminal n := by
  refine ⟨triHexPlanarCellTerminal z.1 i, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨(z.1, i), ?_, rfl⟩
  apply Finset.mem_product.mpr
  exact ⟨by simpa using z.2, Finset.mem_univ i⟩



def triHexPlanarFiniteBoundary (n : Nat)
    (v : TriHexPlanarFiniteTerminal n) : Prop :=
  ∃ i : Fin 3, v.1 - hexagonalStep i ∉ box 2 n

noncomputable instance triHexPlanarFiniteBoundaryDecidable (n : Nat) :
    DecidablePred (triHexPlanarFiniteBoundary n) :=
  Classical.decPred _


noncomputable def triHexPlanarFiniteRootCell (n : Nat) :
    TriHexPlanarFiniteCell n :=
  ⟨0, by simp⟩




noncomputable def triHexPlanarFiniteWiredLevel (n : Nat) :
    TriHexFiniteWiredLevel where
  Cell := TriHexPlanarFiniteCell n
  Vertex := TriHexPlanarFiniteTerminal n
  cellFintype := inferInstance
  cellDecidableEq := inferInstance
  vertexFintype := inferInstance
  vertexDecidableEq := inferInstance
  terminal := triHexPlanarFiniteTerminalMap n
  boundary := triHexPlanarFiniteBoundary n
  boundaryDecidable := inferInstance
  root := triHexPlanarFiniteTerminalMap n (triHexPlanarFiniteRootCell n) 0



theorem hexagonalGraph_adj_triHexPlanarCellTerminal
    (z : Site 2) (i : Fin 3) :
    hexagonalGraph.Adj (z, false) (triHexPlanarCellTerminal z i, true) := by
  simpa [triHexPlanarCellTerminal, hexagonalNeighbor] using
    hexagonal_adj_neighbor (z, false) i



theorem triangularGraph_adj_triHexPlanarCellTerminal
    (z : Site 2) (i j : Fin 3) (hij : i ≠ j) :
    triangularGraph.Adj (triHexPlanarCellTerminal z i)
      (triHexPlanarCellTerminal z j) := by
  fin_cases i <;> fin_cases j <;>
    simp_all [triHexPlanarCellTerminal, triangularGraph_adj, triangularAdj,
      hexagonalStep, triangularStep, funext_iff] <;> decide



theorem triHexPlanarFiniteWiredBoundaryReachRatio_eq_homogeneous
    (n : Nat) {q p : Real} (hq : 0 < q)
    (hp : p ∈ Set.Ioo (0 : Real) 1)
    (hsurface : FrontierA.triangularFKCriticalPolynomial q
      (FrontierA.fkEdgeOdds p) = 0) :
    (triHexPlanarFiniteWiredLevel n).starBoundaryReachRatio q p =
      (triHexPlanarFiniteWiredLevel n).triangleBoundaryReachRatio q p :=
  (triHexPlanarFiniteWiredLevel n).starBoundaryReachRatio_eq_triangle
    hq hp hsurface



theorem triHexPlanarFiniteWiredBoundaryReach_tendsto_iff_homogeneous
    {q p theta : Real} (hq : 0 < q)
    (hp : p ∈ Set.Ioo (0 : Real) 1)
    (hsurface : FrontierA.triangularFKCriticalPolynomial q
      (FrontierA.fkEdgeOdds p) = 0) :
    Filter.Tendsto (fun n =>
        (triHexPlanarFiniteWiredLevel n).starBoundaryReachRatio q p)
        Filter.atTop (nhds theta) ↔
      Filter.Tendsto (fun n =>
        (triHexPlanarFiniteWiredLevel n).triangleBoundaryReachRatio q p)
        Filter.atTop (nhds theta) :=
  triHexFK_finiteWiredExhaustion_tendsto_iff_homogeneous
    triHexPlanarFiniteWiredLevel hq hp hsurface

end

end StatMech.FK.PeriodicPlanar
