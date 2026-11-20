/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.FKPositiveSubcriticalQ2Bridge
import Code.Percolation.GridBoxConnected








open Filter

namespace StatMech
namespace Exact3D

open StatMech.Lattice



theorem boxGraph_update_mem_box {d n : ℕ} {x : Site d}
    (hx : x ∈ box d n) (j : Fin d) {a : ℤ} (ha : a.natAbs ≤ n) :
    Function.update x j a ∈ box d n :=
  Percolation.update_mem_box hx j ha


theorem boxGraph_adj_update_succ {d n : ℕ} {x : Site d}
    (hx : x ∈ box d n) (j : Fin d) {a : ℤ}
    (ha : a.natAbs ≤ n) (ha1 : (a + 1).natAbs ≤ n) :
    (FK.boxGraph d n).Adj
      ⟨Function.update x j a, boxGraph_update_mem_box hx j ha⟩
      ⟨Function.update x j (a + 1), boxGraph_update_mem_box hx j ha1⟩ := by
  simpa [FK.boxGraph] using Lattice.adj_update_succ x j a



theorem boxGraph_adj_boxVertStrictSectorPredecessor3
    {n : ℕ} (v : FK.boxVerts 3 n)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3))) :
    (FK.boxGraph 3 n).Adj
      (boxVertStrictSectorPredecessor3 v hvwedge hlt) v := by
  change (hypercubicLattice 3).Adj
    ((boxVertStrictSectorPredecessor3 v hvwedge hlt : FK.boxVerts 3 n) :
      Lattice.Site 3) (v : Lattice.Site 3)
  rw [hypercubicLattice_adj, Fin.sum_univ_three]
  rcases boxVertStrictSectorPredecessor3_hasCoords v hvwedge hlt with
    ⟨hw0, hw1, hw2⟩
  simp [hw0, hvwedge.1, hw1, hw2]



theorem boxGraph_adj_boxVertStrictSectorYPredecessor3
    {n : ℕ} (v : FK.boxVerts 3 n)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) :
    (FK.boxGraph 3 n).Adj
      (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) v := by
  change (hypercubicLattice 3).Adj
    ((boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos :
      FK.boxVerts 3 n) : Lattice.Site 3) (v : Lattice.Site 3)
  rw [hypercubicLattice_adj, Fin.sum_univ_three]
  rcases boxVertStrictSectorYPredecessor3_hasCoords
    v hvwedge hlt hypos with
    ⟨hw0, hw1, hw2⟩
  simp [hw0, hvwedge.1, hw1, hw2]



theorem boxGraph_adj_boxVertDiagonalPredecessor3
    {n : ℕ} (v : FK.boxVerts 3 n)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hheight : boxVertTransverseHeight3 v ≠ 0)
    (hnotlt :
      ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3))) :
    (FK.boxGraph 3 n).Adj
      (boxVertDiagonalPredecessor3 v hvwedge hheight hnotlt) v := by
  change (hypercubicLattice 3).Adj
    ((boxVertDiagonalPredecessor3 v hvwedge hheight hnotlt :
      FK.boxVerts 3 n) : Lattice.Site 3) (v : Lattice.Site 3)
  rw [hypercubicLattice_adj, Fin.sum_univ_three]
  rcases boxVertDiagonalPredecessor3_hasCoords v hvwedge hheight hnotlt with
    ⟨hw0, hw1, hw2⟩
  simp [hw0, hvwedge.1, hw1, hw2]




theorem boxGraph_adj_boxVertInclLE_strictSectorPredecessor3
    {n M : ℕ} (h : n ≤ M) (v : FK.boxVerts 3 n)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3))) :
    (FK.boxGraph 3 M).Adj
      (FK.boxVertInclLE 3 h
        (boxVertStrictSectorPredecessor3 v hvwedge hlt))
      (FK.boxVertInclLE 3 h v) := by
  simpa [FK.boxGraph, FK.boxVertInclLE] using
    boxGraph_adj_boxVertStrictSectorPredecessor3 v hvwedge hlt



theorem boxGraph_adj_boxVertInclLE_strictSectorYPredecessor3
    {n M : ℕ} (h : n ≤ M) (v : FK.boxVerts 3 n)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) :
    (FK.boxGraph 3 M).Adj
      (FK.boxVertInclLE 3 h
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
      (FK.boxVertInclLE 3 h v) := by
  simpa [FK.boxGraph, FK.boxVertInclLE] using
    boxGraph_adj_boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos




theorem boxGraph_adj_boxVertInclLE_diagonalPredecessor3
    {n M : ℕ} (h : n ≤ M) (v : FK.boxVerts 3 n)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hheight : boxVertTransverseHeight3 v ≠ 0)
    (hnotlt :
      ¬ ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3))) :
    (FK.boxGraph 3 M).Adj
      (FK.boxVertInclLE 3 h
        (boxVertDiagonalPredecessor3 v hvwedge hheight hnotlt))
      (FK.boxVertInclLE 3 h v) := by
  simpa [FK.boxGraph, FK.boxVertInclLE] using
    boxGraph_adj_boxVertDiagonalPredecessor3 v hvwedge hheight hnotlt

set_option linter.style.longLine false in





theorem boxVertPositiveXFaceOrderedWedge3_lowerDoubledAdj_hasCoords3_yOrZ
    {n : ℕ} {v w : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hwwedge : boxVertPositiveXFaceOrderedWedge3 n w)
    (hheight : boxVertTransverseHeight3 w < boxVertTransverseHeight3 v)
    (hadj :
      (FK.boxGraph 3 (2 * n)).Adj
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
        (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)) :
    boxVertHasCoords3 w (n : ℤ)
        (((v : Lattice.Site 3) (1 : Fin 3)) - 1)
        ((v : Lattice.Site 3) (2 : Fin 3)) ∨
      boxVertHasCoords3 w (n : ℤ)
        ((v : Lattice.Site 3) (1 : Fin 3))
        (((v : Lattice.Site 3) (2 : Fin 3)) - 1) := by
  let y : ℤ := (v : Lattice.Site 3) (1 : Fin 3)
  let z : ℤ := (v : Lattice.Site 3) (2 : Fin 3)
  let yw : ℤ := (w : Lattice.Site 3) (1 : Fin 3)
  let zw : ℤ := (w : Lattice.Site 3) (2 : Fin 3)
  have hy_nonneg : 0 ≤ y := by
    simpa [y] using hvwedge.2.1
  have hz_nonneg : 0 ≤ z := by
    have hy_le_z : y ≤ z := by
      simpa [y, z] using hvwedge.2.2
    omega
  have hyw_nonneg : 0 ≤ yw := by
    simpa [yw] using hwwedge.2.1
  have hzw_nonneg : 0 ≤ zw := by
    have hyw_le_zw : yw ≤ zw := by
      simpa [yw, zw] using hwwedge.2.2
    omega
  have hheight_int : yw + zw < y + z := by
    have hheight_nat :
        yw.natAbs + zw.natAbs < y.natAbs + z.natAbs := by
      simpa [boxVertTransverseHeight3, y, z, yw, zw] using hheight
    have hheight_cast :
        (yw.natAbs : ℤ) + (zw.natAbs : ℤ) <
          (y.natAbs : ℤ) + (z.natAbs : ℤ) := by
      exact_mod_cast hheight_nat
    simpa [
      Int.natAbs_of_nonneg hyw_nonneg,
      Int.natAbs_of_nonneg hzw_nonneg,
      Int.natAbs_of_nonneg hy_nonneg,
      Int.natAbs_of_nonneg hz_nonneg] using hheight_cast
  have hadj_sum :
      (yw - y).natAbs + (zw - z).natAbs = 1 := by
    have hadj_lat :
        (hypercubicLattice 3).Adj
          (w : Lattice.Site 3) (v : Lattice.Site 3) := by
      simpa [FK.boxGraph, FK.boxVertInclLE] using hadj
    rw [hypercubicLattice_adj, Fin.sum_univ_three] at hadj_lat
    simpa [y, z, yw, zw, hvwedge.1, hwwedge.1] using hadj_lat
  have hcases :
      ((yw - y).natAbs = 1 ∧ (zw - z).natAbs = 0) ∨
        ((yw - y).natAbs = 0 ∧ (zw - z).natAbs = 1) := by
    omega
  rcases hcases with hY | hZ
  · rcases hY with ⟨hy_step, hz_zero⟩
    have hzw_eq : zw = z := by
      have : zw - z = 0 := Int.natAbs_eq_zero.mp hz_zero
      omega
    have hy_pm : yw - y = 1 ∨ yw - y = -1 :=
      (Int.natAbs_eq_iff.mp hy_step)
    rcases hy_pm with hy_plus | hy_minus
    · have : ¬ yw + zw < y + z := by
        omega
      exact (this hheight_int).elim
    · left
      refine ⟨hwwedge.1, ?_, ?_⟩ <;> omega
  · rcases hZ with ⟨hy_zero, hz_step⟩
    have hyw_eq : yw = y := by
      have : yw - y = 0 := Int.natAbs_eq_zero.mp hy_zero
      omega
    have hz_pm : zw - z = 1 ∨ zw - z = -1 :=
      (Int.natAbs_eq_iff.mp hz_step)
    rcases hz_pm with hz_plus | hz_minus
    · have : ¬ yw + zw < y + z := by
        omega
      exact (this hheight_int).elim
    · right
      refine ⟨hwwedge.1, ?_, ?_⟩ <;> omega

set_option linter.style.longLine false in





def FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentAt
    (β : ℝ) (hβpos : 0 < β) (n : ℕ) : Prop :=
  ∀ v w : FK.boxVerts 3 n,
    boxVertPositiveXFaceOrderedWedge3 n v →
      boxVertPositiveXFaceOrderedWedge3 n w →
        boxVertTransverseHeight3 w < boxVertTransverseHeight3 v →
          (FK.boxGraph 3 (2 * n)).Adj
            (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
            (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v) →
          freeQ2DoubledFullOriginConnProb β hβpos n v ≤
            freeQ2DoubledFullOriginConnProb β hβpos n w

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :
    Prop :=
  ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentAt
        β hβpos n

set_option linter.style.longLine false in






def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal :
    Prop :=
  ∀ {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v w : FK.boxVerts 3 n},
    boxVertPositiveXFaceOrderedWedge3 n v →
      boxVertPositiveXFaceOrderedWedge3 n w →
        boxVertTransverseHeight3 w < boxVertTransverseHeight3 v →
          (FK.boxGraph 3 (2 * n)).Adj
            (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
            (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v) →
          freeQ2DoubledFullOriginConnProb β hβpos n v ≤
            freeQ2DoubledFullOriginConnProb β hβpos n w

set_option linter.style.longLine false in





def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonLocal :
    Prop :=
  ∀ {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v w : FK.boxVerts 3 n},
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
      (hlt :
        ((v : Lattice.Site 3) (1 : Fin 3)) <
          ((v : Lattice.Site 3) (2 : Fin 3))) →
        0 < ((v : Lattice.Site 3) (1 : Fin 3)) →
        boxVertHasCoords3 w (n : ℤ)
          (((v : Lattice.Site 3) (1 : Fin 3)) - 1)
          ((v : Lattice.Site 3) (2 : Fin 3)) →
          freeQ2DoubledFullOriginConnProb β hβpos n v ≤
            freeQ2DoubledFullOriginConnProb β hβpos n w

set_option linter.style.longLine false in



def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonAt
    (β : ℝ) (hβpos : 0 < β) (n : ℕ) : Prop :=
  ∀ v w : FK.boxVerts 3 n,
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
      (hlt :
        ((v : Lattice.Site 3) (1 : Fin 3)) <
          ((v : Lattice.Site 3) (2 : Fin 3))) →
        0 < ((v : Lattice.Site 3) (1 : Fin 3)) →
        boxVertHasCoords3 w (n : ℤ)
          (((v : Lattice.Site 3) (1 : Fin 3)) - 1)
          ((v : Lattice.Site 3) (2 : Fin 3)) →
          freeQ2DoubledFullOriginConnProb β hβpos n v ≤
            freeQ2DoubledFullOriginConnProb β hβpos n w

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonPositiveSubcritical :
    Prop :=
  ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonAt
        β hβpos n

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonPositiveSubcritical_of_local
    (hlocal :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonLocal) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonPositiveSubcritical := by
  intro β hβpos _hβc
  exact Filter.Eventually.of_forall fun n => by
    intro v w hvwedge hlt hypos hcoords
    exact hlocal hβpos hvwedge hlt hypos hcoords

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonAt
    (β : ℝ) (hβpos : 0 < β) (n : ℕ) : Prop :=
  ∀ v : FK.boxVerts 3 n,
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
      (hlt :
        ((v : Lattice.Site 3) (1 : Fin 3)) <
          ((v : Lattice.Site 3) (2 : Fin 3))) →
        (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) →
          freeQ2DoubledFullOriginConnProb β hβpos n v ≤
            freeQ2DoubledFullOriginConnProb β hβpos n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonPositiveSubcritical :
    Prop :=
  ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonAt
        β hβpos n

set_option linter.style.longLine false in

def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonLocal :
    Prop :=
  ∀ {β : ℝ} (hβpos : 0 < β) {n : ℕ} {v : FK.boxVerts 3 n},
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
      (hlt :
        ((v : Lattice.Site 3) (1 : Fin 3)) <
          ((v : Lattice.Site 3) (2 : Fin 3))) →
        (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) →
          freeQ2DoubledFullOriginConnProb β hβpos n v ≤
            freeQ2DoubledFullOriginConnProb β hβpos n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonAt_of_predecessorComparison
    {β : ℝ} {hβpos : 0 < β} {n : ℕ}
    (hcmp :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonAt
        β hβpos n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonAt
      β hβpos n := by
  intro v w hvwedge hlt hypos hcoords
  have hcanon :
      boxVertHasCoords3
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
        (n : ℤ)
        (((v : Lattice.Site 3) (1 : Fin 3)) - 1)
        ((v : Lattice.Site 3) (2 : Fin 3)) := by
    simp
  calc
    freeQ2DoubledFullOriginConnProb β hβpos n v
        ≤ freeQ2DoubledFullOriginConnProb β hβpos n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) :=
      hcmp v hvwedge hlt hypos
    _ = freeQ2DoubledFullOriginConnProb β hβpos n w :=
      freeQ2DoubledFullOriginConnProb_eq_of_boxVertHasCoords3
        hcanon hcoords

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonAt_of_coordinateComparison
    {β : ℝ} {hβpos : 0 < β} {n : ℕ}
    (hcmp :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonAt
        β hβpos n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonAt
      β hβpos n := by
  intro v hvwedge hlt hypos
  exact hcmp v
    (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
    hvwedge hlt hypos (by simp)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparison_of_predecessorComparison
    (hcmp :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hcmp β hβpos hβc] with n hcmp_n
  exact
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonAt_of_predecessorComparison
      hcmp_n

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparison_of_coordinateComparison
    (hcmp :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hcmp β hβpos hβc] with n hcmp_n
  exact
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonAt_of_coordinateComparison
      hcmp_n

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonPositiveSubcritical_of_local
    (hlocal :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonLocal) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonPositiveSubcritical := by
  intro β hβpos _hβc
  exact Filter.Eventually.of_forall fun n => by
    intro v hvwedge hlt hypos
    exact hlocal hβpos hvwedge hlt hypos

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonPositiveSubcritical_of_predecessorLocal
    (hlocal :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonLocal) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparison_of_predecessorComparison
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonPositiveSubcritical_of_local
      hlocal)

set_option linter.style.longLine false in




theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_local
    (hlocal :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical := by
  intro β hβpos _hβc
  exact Filter.Eventually.of_forall fun n => by
    intro v w hvwedge hwwedge hheight hadj
    exact hlocal hβpos hvwedge hwwedge hheight hadj

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentAt_of_coordinateCases
    {β : ℝ} {hβpos : 0 < β} {n : ℕ}
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonAt
        β hβpos n)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonAt
        β hβpos n)
    (hstrictY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonAt
        β hβpos n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentAt
      β hβpos n := by
  intro v w hvwedge hwwedge hheight hadj
  have hcase :=
    boxVertPositiveXFaceOrderedWedge3_lowerDoubledAdj_hasCoords3_yOrZ
      hvwedge hwwedge hheight hadj
  rcases hcase with hpredY | hpredZ
  · by_cases hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3))
    · have hy_pos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)) := by
        rcases hpredY with ⟨_hw0, hw1, _hw2⟩
        have hwwedge_y_nonneg := hwwedge.2.1
        rw [hw1] at hwwedge_y_nonneg
        omega
      exact hstrictY v w hvwedge hlt hy_pos hpredY
    · have hheight_ne : boxVertTransverseHeight3 v ≠ 0 := by
        omega
      have hcanon :
          boxVertHasCoords3
            (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hlt)
            (n : ℤ)
            (((v : Lattice.Site 3) (1 : Fin 3)) - 1)
            ((v : Lattice.Site 3) (2 : Fin 3)) := by
        simp
      calc
        freeQ2DoubledFullOriginConnProb β hβpos n v
            ≤ freeQ2DoubledFullOriginConnProb β hβpos n
              (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hlt) :=
          hdiagY v hvwedge hheight_ne hlt
        _ = freeQ2DoubledFullOriginConnProb β hβpos n w :=
          freeQ2DoubledFullOriginConnProb_eq_of_boxVertHasCoords3
            hcanon hpredY
  · have hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)) := by
      rcases hpredZ with ⟨_hw0, hw1, hw2⟩
      have hwwedge_yz := hwwedge.2.2
      rw [hw1, hw2] at hwwedge_yz
      omega
    have hcanon :
        boxVertHasCoords3
          (boxVertStrictSectorPredecessor3 v hvwedge hlt)
          (n : ℤ)
          ((v : Lattice.Site 3) (1 : Fin 3))
          (((v : Lattice.Site 3) (2 : Fin 3)) - 1) := by
      simp
    calc
      freeQ2DoubledFullOriginConnProb β hβpos n v
          ≤ freeQ2DoubledFullOriginConnProb β hβpos n
            (boxVertStrictSectorPredecessor3 v hvwedge hlt) :=
        hstrictZ v hvwedge hlt
      _ = freeQ2DoubledFullOriginConnProb β hβpos n w :=
        freeQ2DoubledFullOriginConnProb_eq_of_boxVertHasCoords3
          hcanon hpredZ

set_option linter.style.longLine false in





theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal_of_coordinateCases
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hstrictY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonLocal) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal := by
  intro β hβpos n v w hvwedge hwwedge hheight hadj
  have hcase :=
    boxVertPositiveXFaceOrderedWedge3_lowerDoubledAdj_hasCoords3_yOrZ
      hvwedge hwwedge hheight hadj
  rcases hcase with hpredY | hpredZ
  · by_cases hlt :
        ((v : Lattice.Site 3) (1 : Fin 3)) <
          ((v : Lattice.Site 3) (2 : Fin 3))
    · have hy_pos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)) := by
        rcases hpredY with ⟨_hw0, hw1, _hw2⟩
        have hwwedge_y_nonneg := hwwedge.2.1
        rw [hw1] at hwwedge_y_nonneg
        omega
      exact hstrictY hβpos hvwedge hlt hy_pos hpredY
    · have hheight_ne : boxVertTransverseHeight3 v ≠ 0 := by
        omega
      have hcanon :
          boxVertHasCoords3
            (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hlt)
            (n : ℤ)
            (((v : Lattice.Site 3) (1 : Fin 3)) - 1)
            ((v : Lattice.Site 3) (2 : Fin 3)) := by
        simp
      calc
        freeQ2DoubledFullOriginConnProb β hβpos n v
            ≤ freeQ2DoubledFullOriginConnProb β hβpos n
              (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hlt) :=
          hdiagY hβpos hvwedge hheight_ne hlt
        _ = freeQ2DoubledFullOriginConnProb β hβpos n w :=
          freeQ2DoubledFullOriginConnProb_eq_of_boxVertHasCoords3
            hcanon hpredY
  · have hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)) := by
      rcases hpredZ with ⟨_hw0, hw1, hw2⟩
      have hwwedge_yz := hwwedge.2.2
      rw [hw1, hw2] at hwwedge_yz
      omega
    have hcanon :
        boxVertHasCoords3
          (boxVertStrictSectorPredecessor3 v hvwedge hlt)
          (n : ℤ)
          ((v : Lattice.Site 3) (1 : Fin 3))
          (((v : Lattice.Site 3) (2 : Fin 3)) - 1) := by
      simp
    calc
      freeQ2DoubledFullOriginConnProb β hβpos n v
          ≤ freeQ2DoubledFullOriginConnProb β hβpos n
            (boxVertStrictSectorPredecessor3 v hvwedge hlt) :=
        hstrictZ hβpos hvwedge hlt
      _ = freeQ2DoubledFullOriginConnProb β hβpos n w :=
        freeQ2DoubledFullOriginConnProb_eq_of_boxVertHasCoords3
          hcanon hpredZ

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_coordinateCasesLocal
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hstrictY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonLocal) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_local
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal_of_coordinateCases
      hstrictZ hdiagY hstrictY)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal_of_predecessorCases
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hstrictY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonLocal) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal_of_coordinateCases
    hstrictZ hdiagY
    (fun {β} hβpos {n} {v} {w} hvwedge hlt hypos hcoords => by
      have hcanon :
          boxVertHasCoords3
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
            (n : ℤ)
            (((v : Lattice.Site 3) (1 : Fin 3)) - 1)
            ((v : Lattice.Site 3) (2 : Fin 3)) := by
        simp
      calc
        freeQ2DoubledFullOriginConnProb β hβpos n v
            ≤ freeQ2DoubledFullOriginConnProb β hβpos n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) :=
          hstrictY hβpos hvwedge hlt hypos
        _ = freeQ2DoubledFullOriginConnProb β hβpos n w :=
          freeQ2DoubledFullOriginConnProb_eq_of_boxVertHasCoords3
            hcanon hcoords)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_predecessorCasesLocal
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hstrictY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonLocal) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_local
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal_of_predecessorCases
      hstrictZ hdiagY hstrictY)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_coordinateCases
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonPositiveSubcritical)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonPositiveSubcritical)
    (hstrictY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards
    [hstrictZ β hβpos hβc, hdiagY β hβpos hβc, hstrictY β hβpos hβc]
    with n hstrictZ_n hdiagY_n hstrictY_n
  exact
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentAt_of_coordinateCases
      hstrictZ_n hdiagY_n hstrictY_n

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_predecessorCases
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonPositiveSubcritical)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonPositiveSubcritical)
    (hstrictY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_coordinateCases
    hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparison_of_predecessorComparison
      hstrictY)

set_option linter.style.longLine false in



theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictDescent_of_fullOneEdgeDescent
    (hone :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictDescentPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hone β hβpos hβc] with n hone_n
  intro v hvwedge hheight
  by_cases hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3))
  · let w := boxVertStrictSectorPredecessor3 v hvwedge hlt
    have hwwedge : boxVertPositiveXFaceOrderedWedge3 n w :=
      boxVertStrictSectorPredecessor3_wedge v hvwedge hlt
    have hheight_lt : boxVertTransverseHeight3 w < boxVertTransverseHeight3 v :=
      boxVertStrictSectorPredecessor3_height_lt v hvwedge hlt
    have hadj :
        (FK.boxGraph 3 (2 * n)).Adj
          (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
          (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v) :=
      boxGraph_adj_boxVertInclLE_strictSectorPredecessor3
        (by omega : n ≤ 2 * n) v hvwedge hlt
    refine ⟨w, hwwedge, hheight_lt, ?_⟩
    exact hone_n v w hvwedge hwwedge hheight_lt hadj
  · let w := boxVertDiagonalPredecessor3 v hvwedge hheight hlt
    have hwwedge : boxVertPositiveXFaceOrderedWedge3 n w :=
      boxVertDiagonalPredecessor3_wedge v hvwedge hheight hlt
    have hheight_lt : boxVertTransverseHeight3 w < boxVertTransverseHeight3 v :=
      boxVertDiagonalPredecessor3_height_lt v hvwedge hheight hlt
    have hadj :
        (FK.boxGraph 3 (2 * n)).Adj
          (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
          (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v) :=
      boxGraph_adj_boxVertInclLE_diagonalPredecessor3
        (by omega : n ≤ 2 * n) v hvwedge hheight hlt
    refine ⟨w, hwwedge, hheight_lt, ?_⟩
    exact hone_n v w hvwedge hwwedge hheight_lt hadj

set_option linter.style.longLine false in



theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjection_of_fullOneEdgeDescent_profileDoubleScale
    (hone :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjectionPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjection_of_fullStrictDescent_detourPolynomialBound
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictDescent_of_fullOneEdgeDescent
      hone)
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDetourPolynomialBound_of_profileDoubleScale
      hprofile)


theorem boxGraph_reachable_update_ascend {d n : ℕ}
    {x : Site d} (hx : x ∈ box d n) (j : Fin d) :
    ∀ (k : ℕ) (a : ℤ)
      (ha : a.natAbs ≤ n) (hak : (a + (k : ℤ)).natAbs ≤ n),
      (FK.boxGraph d n).Reachable
        ⟨Function.update x j a, boxGraph_update_mem_box hx j ha⟩
        ⟨Function.update x j (a + (k : ℤ)),
          boxGraph_update_mem_box hx j hak⟩ := by
  intro k
  induction k with
  | zero =>
      intro a ha _hak
      simpa using
        (SimpleGraph.Reachable.refl
          (G := FK.boxGraph d n)
          ⟨Function.update x j a, boxGraph_update_mem_box hx j ha⟩)
  | succ m ih =>
      intro a ha hak
      have hint : (a + (m : ℤ)).natAbs ≤ n := by
        have h1 := ha
        have h2 := hak
        push_cast at h2 ⊢
        omega
      have hstep :
          (FK.boxGraph d n).Reachable
            ⟨Function.update x j (a + (m : ℤ)),
              boxGraph_update_mem_box hx j hint⟩
            ⟨Function.update x j (a + (m : ℤ) + 1),
              boxGraph_update_mem_box hx j (by
                have : a + (m : ℤ) + 1 = a + ((m + 1 : ℕ) : ℤ) := by
                  push_cast
                  ring
                rw [this]
                exact hak)⟩ := by
        exact SimpleGraph.Adj.reachable
          (boxGraph_adj_update_succ hx j hint (by
            have : a + (m : ℤ) + 1 = a + ((m + 1 : ℕ) : ℤ) := by
              push_cast
              ring
            rw [this]
            exact hak))
      have hrec := (ih a ha hint).trans hstep
      have he : a + (m : ℤ) + 1 = a + ((m + 1 : ℕ) : ℤ) := by
        push_cast
        ring
      simpa [he] using hrec



theorem boxGraph_reachable_update {d n : ℕ}
    {x : Site d} (hx : x ∈ box d n) (j : Fin d) {a : ℤ}
    (ha : a.natAbs ≤ n) :
    (FK.boxGraph d n).Reachable
      ⟨x, hx⟩
      ⟨Function.update x j a, boxGraph_update_mem_box hx j ha⟩ := by
  have hxj : (x j).natAbs ≤ n := hx j
  have hxupd : Function.update x j (x j) = x := Function.update_eq_self j x
  rcases le_total (x j) a with hle | hle
  · obtain ⟨k, hk⟩ := Int.le.dest hle
    subst hk
    have hconn := boxGraph_reachable_update_ascend hx j k (x j) hxj ha
    simpa [hxupd] using hconn
  · obtain ⟨k, hk⟩ := Int.le.dest hle
    have hconn := boxGraph_reachable_update_ascend hx j k a ha (by
      rw [hk]
      exact hxj)
    simpa [hk, hxupd] using hconn.symm



theorem boxGraph_reachable_mixSite {d n : ℕ}
    {x y : Site d} (hx : x ∈ box d n) (hy : y ∈ box d n) :
    ∀ k ≤ d,
      (FK.boxGraph d n).Reachable
        ⟨x, hx⟩
        ⟨Percolation.mixSite x y k, Percolation.mixSite_mem_box hx hy k⟩ := by
  intro k
  induction k with
  | zero =>
      intro _hk
      simpa [Percolation.mixSite_zero]
  | succ m ih =>
      intro hsucc
      have hm : m < d := by omega
      have hmle : m ≤ d := by omega
      have h1 := ih hmle
      have hstep :
          (FK.boxGraph d n).Reachable
            ⟨Percolation.mixSite x y m, Percolation.mixSite_mem_box hx hy m⟩
            ⟨Percolation.mixSite x y (m + 1),
              Percolation.mixSite_mem_box hx hy (m + 1)⟩ := by
        simpa [Percolation.mixSite_succ hm] using
          boxGraph_reachable_update
            (Percolation.mixSite_mem_box hx hy m) ⟨m, hm⟩ (hy ⟨m, hm⟩)
      exact h1.trans hstep


theorem boxGraph_reachable (d n : ℕ) (x y : FK.boxVerts d n) :
    (FK.boxGraph d n).Reachable x y := by
  have h := boxGraph_reachable_mixSite x.2 y.2 d le_rfl
  simpa [Percolation.mixSite_full] using h


def boxGraphSomeHom (d n : ℕ) :
    (FK.boxGraph d n) →g Sharpness.withGhost (FK.boxGraph d n) where
  toFun := some
  map_rel' := by
    intro a b hab
    simpa using hab



theorem finiteBoundaryGhostOriginalPathWitness_of_boxPath
    {n : ℕ} {a b : FK.boxVerts 3 n}
    (p0 : (FK.boxGraph 3 n).Path a b) :
    ∃ p :
      (Sharpness.withGhost (FK.boxGraph 3 n)).Path (some a) (some b),
      ∀ e : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset,
        0 < p.1.edges.count e.1 →
          Sharpness.edgeInside (finiteBoundaryGhostOriginalSet 3 n) e.1 := by
  classical
  let f := boxGraphSomeHom 3 n
  let p : (Sharpness.withGhost (FK.boxGraph 3 n)).Path (some a) (some b) :=
    SimpleGraph.Path.map f (Option.some_injective (FK.boxVerts 3 n)) p0
  refine ⟨p, ?_⟩
  intro e hepos
  have hemem : e.1 ∈ p.1.edges := List.count_pos_iff.mp hepos
  change e.1 ∈ (p0.1.map f).edges at hemem
  rw [SimpleGraph.Walk.edges_map] at hemem
  rcases List.mem_map.mp hemem with ⟨e0, _he0, heq⟩
  rw [← heq]
  simpa [f, boxGraphSomeHom] using
    finiteBoundaryGhostOriginalSet_edgeInside_map_some 3 n e0



theorem finiteBoundaryGhostOriginalPathWitness3D :
    FiniteBoundaryGhostOriginalPathWitness3D := by
  filter_upwards [] with n
  intro v _hv
  have hreach :
      (FK.boxGraph 3 n).Reachable (IsingFK.boxOrigin 3 n) v :=
    boxGraph_reachable 3 n (IsingFK.boxOrigin 3 n) v
  rcases hreach.exists_isPath with ⟨w, hw⟩
  exact finiteBoundaryGhostOriginalPathWitness_of_boxPath ⟨w, hw⟩



theorem finiteQ2BoundaryVertexDenominatorPositiveSupportCurrentWitness_from_boxGeometry :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositiveSupportCurrentWitnessPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositiveSupportCurrentWitness_of_originalPathWitness3D
    finiteBoundaryGhostOriginalPathWitness3D



theorem finiteQ2BoundaryVertexDenominatorPositive_from_boxGeometry :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositivePositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositive_of_originalPathWitness3D
    finiteBoundaryGhostOriginalPathWitness3D



theorem
    finiteQ2PositiveDenominatorComponentSumAbsorption_of_boxGeometry_componentSumAbsorption
    (hsum :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentSumAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorptionPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption_of_originalPathWitness3D_componentSumAbsorption
    finiteBoundaryGhostOriginalPathWitness3D
    hsum

end Exact3D
end StatMech
