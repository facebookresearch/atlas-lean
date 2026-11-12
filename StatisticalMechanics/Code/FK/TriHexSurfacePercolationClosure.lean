/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.TriHexCriticalReduction
import Code.FK.PeriodicPlanarPercolationApproximation












open Set

namespace StatMech.FK.PeriodicPlanar

open BeffaraDC FrontierA



def TriHexSurfacePercolationEquivalence (q p : Real) : Prop :=
  triangular.wiredPercolates p q <->
    hexagonal.wiredPercolates (dualParam p q) q


theorem criticalPoint_eq_of_dual_percolation_equivalence
    {primalPercolates dualPercolates : Real -> Prop}
    {q p pc pcDual : Real}
    (hq : 0 < q)
    (hp : p ∈ Ioo (0 : Real) 1)
    (hpc : pc ∈ Ioo (0 : Real) 1)
    (hsharp : OffCriticalSharpness primalPercolates pc)
    (hsharpDual : OffCriticalSharpness dualPercolates pcDual)
    (hcriticalDual : dualParam pc q = pcDual)
    (hnoCoexistence : DualNoCoexistence
      primalPercolates dualPercolates q)
    (hequiv : primalPercolates p <->
      dualPercolates (dualParam p q)) :
    p = pc ∧ dualParam p q = pcDual := by
  have hpDual : dualParam p q ∈ Ioo (0 : Real) 1 :=
    dualParam_mem_Ioo hp.1 hp.2 hq
  have hnotBoth := hnoCoexistence p hp
  have hnotPrimal : ¬ primalPercolates p := by
    intro hprimal
    exact hnotBoth ⟨hprimal, hequiv.mp hprimal⟩
  have hnotDual : ¬ dualPercolates (dualParam p q) := by
    intro hdual
    exact hnotBoth ⟨hequiv.mpr hdual, hdual⟩
  have hp_le : p <= pc := by
    by_contra hnot
    exact hnotPrimal (hsharp.2 p hp (lt_of_not_ge hnot))
  have hpDual_le : dualParam p q <= pcDual := by
    by_contra hnot
    exact hnotDual
      (hsharpDual.2 (dualParam p q) hpDual (lt_of_not_ge hnot))
  have hpc_le : pc <= p := by
    by_contra hnot
    have hlt : p < pc := lt_of_not_ge hnot
    have hanti := dualParam_strictAntiOn hq hp hpc hlt
    change dualParam pc q < dualParam p q at hanti
    rw [hcriticalDual] at hanti
    exact (not_lt_of_ge hpDual_le) hanti
  have hpeq : p = pc := le_antisymm hp_le hpc_le
  exact ⟨hpeq, by rw [hpeq, hcriticalDual]⟩





theorem criticalPoint_eq_of_dual_percolation_equivalence_of_criticalDual
    {primalPercolates dualPercolates : Real -> Prop}
    {q p pc pcDual : Real}
    (hq : 0 < q)
    (hp : p ∈ Ioo (0 : Real) 1)
    (hpc : pc ∈ Ioo (0 : Real) 1)
    (hsharp : OffCriticalSharpness primalPercolates pc)
    (hsharpDual : OffCriticalSharpness dualPercolates pcDual)
    (hcriticalDual : dualParam pc q = pcDual)
    (hequiv : primalPercolates p <->
      dualPercolates (dualParam p q)) :
    p = pc ∧ dualParam p q = pcDual := by
  have hpDual : dualParam p q ∈ Ioo (0 : Real) 1 :=
    dualParam_mem_Ioo hp.1 hp.2 hq
  have hp_le : p <= pc := by
    by_contra hnot
    have hpcp : pc < p := lt_of_not_ge hnot
    have hanti := dualParam_strictAntiOn hq hpc hp hpcp
    change dualParam p q < dualParam pc q at hanti
    rw [hcriticalDual] at hanti
    exact hsharpDual.1 (dualParam p q) hpDual hanti
      (hequiv.mp (hsharp.2 p hp hpcp))
  have hpc_le : pc <= p := by
    by_contra hnot
    have hppc : p < pc := lt_of_not_ge hnot
    have hanti := dualParam_strictAntiOn hq hp hpc hppc
    change dualParam pc q < dualParam p q at hanti
    rw [hcriticalDual] at hanti
    exact hsharp.1 p hp hppc
      (hequiv.mpr (hsharpDual.2 (dualParam p q) hpDual hanti))
  have hpeq : p = pc := le_antisymm hp_le hpc_le
  exact ⟨hpeq, by rw [hpeq, hcriticalDual]⟩




theorem triHexCriticalPolynomials_of_surfacePercolationEquivalence
    {q p pcTri pcHex : Real}
    (hq : 1 <= q)
    (hp : p ∈ Ioo (0 : Real) 1)
    (hpcTri : pcTri ∈ Ioo (0 : Real) 1)
    (hsharpTri : OffCriticalSharpness
      (fun r => triangular.wiredPercolates r q) pcTri)
    (hsharpHex : OffCriticalSharpness
      (fun r => hexagonal.wiredPercolates r q) pcHex)
    (hcriticalDual : dualParam pcTri q = pcHex)
    (hnoCoexistence : DualNoCoexistence
      (fun r => triangular.wiredPercolates r q)
      (fun r => hexagonal.wiredPercolates r q) q)
    (hsurface : triangularFKCriticalPolynomial q (fkEdgeOdds p) = 0)
    (hequiv : TriHexSurfacePercolationEquivalence q p) :
    p = pcTri ∧
      triangularFKCriticalPolynomial q (fkEdgeOdds pcTri) = 0 ∧
      hexagonalFKCriticalPolynomial q (fkEdgeOdds pcHex) = 0 := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hpinned := criticalPoint_eq_of_dual_percolation_equivalence
    hq0 hp hpcTri hsharpTri hsharpHex hcriticalDual
    hnoCoexistence hequiv
  have htri : triangularFKCriticalPolynomial q (fkEdgeOdds pcTri) = 0 := by
    rwa [hpinned.1] at hsurface
  have hproduct := fkEdgeOdds_mul_dualParam hp.1 hp.2 hq0
  rw [hpinned.1, hcriticalDual] at hproduct
  have hy : fkEdgeOdds pcTri ≠ 0 :=
    div_ne_zero (ne_of_gt hpcTri.1) (by linarith [hpcTri.2])
  exact ⟨hpinned.1, htri,
    hexagonalFKCritical_of_dual_triangular hy hproduct htri⟩


theorem triangular_hexagonal_critical_of_surfacePercolationEquivalence
    {q p : Real}
    (hq : 1 <= q)
    (hp : p ∈ Ioo (0 : Real) 1)
    (hpcTri : triangular.criticalPoint q ∈ Ioo (0 : Real) 1)
    (hpcHex : hexagonal.criticalPoint q ∈ Ioo (0 : Real) 1)
    (hcriticalDual : dualParam (triangular.criticalPoint q) q =
      hexagonal.criticalPoint q)
    (hnoCoexistence : DualNoCoexistence
      (fun r => triangular.wiredPercolates r q)
      (fun r => hexagonal.wiredPercolates r q) q)
    (hsurface : triangularFKCriticalPolynomial q (fkEdgeOdds p) = 0)
    (hequiv : TriHexSurfacePercolationEquivalence q p) :
    p = triangular.criticalPoint q ∧
      triangularFKCriticalPolynomial q
        (fkEdgeOdds (triangular.criticalPoint q)) = 0 ∧
      hexagonalFKCriticalPolynomial q
        (fkEdgeOdds (hexagonal.criticalPoint q)) = 0 := by
  exact triHexCriticalPolynomials_of_surfacePercolationEquivalence
    hq hp hpcTri
    (triangular.offCriticalSharpness hq hpcTri)
    (hexagonal.offCriticalSharpness hq hpcHex)
    hcriticalDual hnoCoexistence hsurface hequiv




theorem triangular_hexagonal_critical_of_surfacePercolationEquivalence_of_criticalDual
    {q p : Real}
    (hq : 1 <= q)
    (hp : p ∈ Ioo (0 : Real) 1)
    (hpcTri : triangular.criticalPoint q ∈ Ioo (0 : Real) 1)
    (hpcHex : hexagonal.criticalPoint q ∈ Ioo (0 : Real) 1)
    (hcriticalDual : dualParam (triangular.criticalPoint q) q =
      hexagonal.criticalPoint q)
    (hsurface : triangularFKCriticalPolynomial q (fkEdgeOdds p) = 0)
    (hequiv : TriHexSurfacePercolationEquivalence q p) :
    p = triangular.criticalPoint q ∧
      triangularFKCriticalPolynomial q
        (fkEdgeOdds (triangular.criticalPoint q)) = 0 ∧
      hexagonalFKCriticalPolynomial q
        (fkEdgeOdds (hexagonal.criticalPoint q)) = 0 := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hpinned :=
    criticalPoint_eq_of_dual_percolation_equivalence_of_criticalDual
      hq0 hp hpcTri
      (triangular.offCriticalSharpness hq hpcTri)
      (hexagonal.offCriticalSharpness hq hpcHex)
      hcriticalDual hequiv
  have htri : triangularFKCriticalPolynomial q
      (fkEdgeOdds (triangular.criticalPoint q)) = 0 := by
    rwa [hpinned.1] at hsurface
  have hproduct := fkEdgeOdds_mul_dualParam hp.1 hp.2 hq0
  rw [hpinned.1, hcriticalDual] at hproduct
  have hy : fkEdgeOdds (triangular.criticalPoint q) ≠ 0 :=
    div_ne_zero (ne_of_gt hpcTri.1) (by linarith [hpcTri.2])
  exact ⟨hpinned.1, htri,
    hexagonalFKCritical_of_dual_triangular hy hproduct htri⟩

end StatMech.FK.PeriodicPlanar
