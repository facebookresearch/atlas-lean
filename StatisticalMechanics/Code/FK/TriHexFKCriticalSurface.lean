/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.TriHexFKFiniteWiredCofinal
import Code.FK.TriHexCoarseGeometry
import Code.FK.TriHexSurfacePercolationClosure
import Code.FK.PeriodicPlanarCriticalNontriviality









open MeasureTheory Set StatMech.Lattice

namespace StatMech.FK.PeriodicPlanar

open BeffaraDC FrontierA
open StatMech.Lattice



theorem triHexSurfacePercolationEquivalence_of_finiteWiredSweep
    {q p : Real} (hq : 1 ≤ q) (hp : p ∈ Ioo (0 : Real) 1)
    (hsurface : triangularFKCriticalPolynomial q (fkEdgeOdds p) = 0) :
    TriHexSurfacePercolationEquivalence q p := by
  let pd := dualParam p q
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hpd0 : 0 < pd := dualParam_pos hp.1 hp.2 hq0
  have hpd1 : pd < 1 := dualParam_lt_one hp.1 hp.2 hq0
  let muTri := (triangular.wiredBufferedInfiniteVolume hp.1 hp.2 hq0 :
    Measure (ConfigSpace (Sym2 (Site 2))))
  let muHex := (hexagonal.wiredBufferedInfiniteVolume hpd0 hpd1 hq0 :
    Measure (ConfigSpace (Sym2 HexVertex)))
  have hfixedEq :
      muHex.real (hexagonal.setHitsInfinite
        ({triHexPlanarHexWhiteRoot} : Set HexVertex)) =
      muTri.real (triangular.setHitsInfinite
        ({triHexPlanarTriRoot} : Set (Site 2))) := by
    simpa only [muTri, muHex, pd] using
      triHexPlanar_fixedRootInfinite_real_eq hq hp hsurface
  have htri :
      0 < muTri.real triangular.percolationEvent ↔
        0 < muTri.real (triangular.setHitsInfinite
          ({triHexPlanarTriRoot} : Set (Site 2))) := by
    simpa [PeriodicGraph.percolationEvent,
      PeriodicGraph.setHitsInfinite] using
      triangular.clusterInfinite_real_pos_iff triangularGraph_connected muTri
        (triangular.wiredBufferedInfiniteVolume_hasFiniteEnergy
          hp.1 hp.2 hq)
        triangular.root triHexPlanarTriRoot
  have hhex :
      0 < muHex.real hexagonal.percolationEvent ↔
        0 < muHex.real (hexagonal.setHitsInfinite
          ({triHexPlanarHexWhiteRoot} : Set HexVertex)) := by
    simpa [PeriodicGraph.percolationEvent,
      PeriodicGraph.setHitsInfinite] using
      hexagonal.clusterInfinite_real_pos_iff hexagonalGraph_connected muHex
        (hexagonal.wiredBufferedInfiniteVolume_hasFiniteEnergy hpd0 hpd1 hq)
        hexagonal.root triHexPlanarHexWhiteRoot
  have hfixed :
      0 < muTri.real (triangular.setHitsInfinite
          ({triHexPlanarTriRoot} : Set (Site 2))) ↔
        0 < muHex.real (hexagonal.setHitsInfinite
          ({triHexPlanarHexWhiteRoot} : Set HexVertex)) := by
    rw [hfixedEq]
  unfold TriHexSurfacePercolationEquivalence PeriodicGraph.wiredPercolates
    PeriodicGraph.wiredPercolationProbability
  rw [dif_pos ⟨hp, hq0⟩, dif_pos ⟨⟨hpd0, hpd1⟩, hq0⟩]
  change 0 < muTri.real triangular.percolationEvent ↔
    0 < muHex.real hexagonal.percolationEvent
  exact htri.trans (hfixed.trans hhex.symm)







theorem triHexSurfaceCandidate_criticalPoints_weaklyAligned
    {q p : Real} (hq : 1 ≤ q) (hp : p ∈ Ioo (0 : Real) 1)
    (hsurface : triangularFKCriticalPolynomial q (fkEdgeOdds p) = 0) :
    (p < triangular.criticalPoint q →
        dualParam p q ≤ hexagonal.criticalPoint q) ∧
      (triangular.criticalPoint q < p →
        hexagonal.criticalPoint q ≤ dualParam p q) ∧
      (dualParam p q < hexagonal.criticalPoint q →
        p ≤ triangular.criticalPoint q) ∧
      (hexagonal.criticalPoint q < dualParam p q →
        triangular.criticalPoint q ≤ p) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hpDual : dualParam p q ∈ Ioo (0 : Real) 1 :=
    dualParam_mem_Ioo hp.1 hp.2 hq0
  have htriPos : 0 < triangular.criticalPoint q :=
    triangular.criticalPoint_pos hq
  have hhexPos : 0 < hexagonal.criticalPoint q :=
    hexagonal.criticalPoint_pos hq
  have htriMono := triangular.wiredPercolationProbability_monotoneOn hq
  have hhexMono := hexagonal.wiredPercolationProbability_monotoneOn hq
  have hequiv := triHexSurfacePercolationEquivalence_of_finiteWiredSweep
    hq hp hsurface
  have hbelow : p < triangular.criticalPoint q →
      dualParam p q ≤ hexagonal.criticalPoint q := by
    intro hpBelow
    have htriZero :=
      triangular.wiredPercolationProbability_eq_zero_of_lt_criticalPoint
        htriPos htriMono hp hpBelow
    have htriNot : ¬ triangular.wiredPercolates p q := by
      intro htri
      exact (ne_of_gt htri) htriZero
    have hhexNot : ¬ hexagonal.wiredPercolates (dualParam p q) q := by
      intro hhex
      exact htriNot (hequiv.mpr hhex)
    by_contra hnot
    exact hhexNot (hexagonal.wiredPercolates_of_criticalPoint_lt
      hpDual (lt_of_not_ge hnot))
  have habove : triangular.criticalPoint q < p →
      hexagonal.criticalPoint q ≤ dualParam p q := by
    intro hpAbove
    have htri := triangular.wiredPercolates_of_criticalPoint_lt hp hpAbove
    have hhex := hequiv.mp htri
    by_contra hnot
    have hhexZero :=
      hexagonal.wiredPercolationProbability_eq_zero_of_lt_criticalPoint
        hhexPos hhexMono hpDual (lt_of_not_ge hnot)
    exact (ne_of_gt hhex) hhexZero
  refine ⟨hbelow, habove, ?_, ?_⟩
  · intro hdualBelow
    by_contra hnot
    exact (not_lt_of_ge (habove (lt_of_not_ge hnot))) hdualBelow
  · intro hdualAbove
    by_contra hnot
    exact (not_lt_of_ge (hbelow (lt_of_not_ge hnot))) hdualAbove




theorem triangular_hexagonal_critical_of_finiteWiredSweep
    {q p : Real}
    (hq : 1 ≤ q)
    (hp : p ∈ Ioo (0 : Real) 1)
    (hpcTri : triangular.criticalPoint q ∈ Ioo (0 : Real) 1)
    (hpcHex : hexagonal.criticalPoint q ∈ Ioo (0 : Real) 1)
    (hcriticalDual : dualParam (triangular.criticalPoint q) q =
      hexagonal.criticalPoint q)
    (hsurface : triangularFKCriticalPolynomial q (fkEdgeOdds p) = 0) :
    p = triangular.criticalPoint q ∧
      triangularFKCriticalPolynomial q
        (fkEdgeOdds (triangular.criticalPoint q)) = 0 ∧
      hexagonalFKCriticalPolynomial q
        (fkEdgeOdds (hexagonal.criticalPoint q)) = 0 := by
  exact
    triangular_hexagonal_critical_of_surfacePercolationEquivalence_of_criticalDual
      hq hp hpcTri hpcHex hcriticalDual hsurface
      (triHexSurfacePercolationEquivalence_of_finiteWiredSweep
        hq hp hsurface)

end StatMech.FK.PeriodicPlanar
