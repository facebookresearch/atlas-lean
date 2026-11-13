/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarCriticalReduction











open MeasureTheory Set SimpleGraph

namespace StatMech.FK.PeriodicPlanar

open BeffaraDC



def StrictDualNoCoexistence
    (primalPercolates dualPercolates : Real → Prop) (q : Real) : Prop :=
  ∀ r ∈ Ioo (0 : Real) 1, ∀ p ∈ Ioo (0 : Real) 1, r < p →
    ¬(primalPercolates r ∧ dualPercolates (dualParam p q))



theorem dualCritical_crossBounds_of_sharpness_strictNoCoexistence
    {primalPercolates dualPercolates : Real → Prop}
    {pc pcDual q : Real}
    (hq : 0 < q)
    (hsharpPrimal : OffCriticalSharpness primalPercolates pc)
    (hsharpDual : OffCriticalSharpness dualPercolates pcDual)
    (hcoverage : DualSubcriticalCoverage dualPercolates pc q)
    (hstrict : StrictDualNoCoexistence primalPercolates dualPercolates q) :
    (∀ p ∈ Ioo (0 : Real) 1, p < pc →
        pcDual ≤ dualParam p q) ∧
      (∀ p ∈ Ioo (0 : Real) 1, pc < p →
        dualParam p q ≤ pcDual) := by
  constructor
  · intro p hp hppc
    have hpDual := dualParam_mem_Ioo hp.1 hp.2 hq
    have hperc := hcoverage p hp hppc
    by_contra hnot
    have hlt : dualParam p q < pcDual := lt_of_not_ge hnot
    exact hsharpDual.1 (dualParam p q) hpDual hlt hperc
  · intro p hp hpcp
    by_contra hnot
    have hpDual := dualParam_mem_Ioo hp.1 hp.2 hq
    have hdual : dualPercolates (dualParam p q) :=
      hsharpDual.2 (dualParam p q) hpDual (lt_of_not_ge hnot)
    let a := max pc 0
    have hpa : pc ≤ a := le_max_left _ _
    have ha0 : 0 ≤ a := le_max_right _ _
    have hap : a < p := max_lt hpcp hp.1
    let r := (a + p) / 2
    have hpcr : pc < r := by dsimp only [r]; linarith
    have hrp : r < p := by dsimp only [r]; linarith
    have hr0 : 0 < r := by dsimp only [r]; linarith
    have hr : r ∈ Ioo (0 : Real) 1 := ⟨hr0, hrp.trans hp.2⟩
    have hprimal : primalPercolates r := hsharpPrimal.2 r hr hpcr
    exact hstrict r hr p hp hrp ⟨hprimal, hdual⟩



theorem dualCritical_relation_of_sharpness_strictNoCoexistence
    {primalPercolates dualPercolates : Real → Prop}
    {pc pcDual q : Real}
    (hpc : pc ∈ Ioo (0 : Real) 1)
    (hpcDual : pcDual ∈ Ioo (0 : Real) 1)
    (hq : 0 < q)
    (hsharpPrimal : OffCriticalSharpness primalPercolates pc)
    (hsharpDual : OffCriticalSharpness dualPercolates pcDual)
    (hcoverage : DualSubcriticalCoverage dualPercolates pc q)
    (hstrict : StrictDualNoCoexistence primalPercolates dualPercolates q) :
    dualParam pc q = pcDual ∧
      (pc / (1 - pc)) * (pcDual / (1 - pcDual)) = q := by
  obtain ⟨hsub, hsuper⟩ :=
    dualCritical_crossBounds_of_sharpness_strictNoCoexistence hq
      hsharpPrimal hsharpDual hcoverage hstrict
  have heq := dualCritical_eq_of_crossBounds hpc hpcDual hq hsub hsuper
  refine ⟨heq, ?_⟩
  have hproduct := dualParam_product_eq hpc.1 hpc.2 hq
  rw [heq] at hproduct
  have hpcDen : 1 - pc ≠ 0 := ne_of_gt (sub_pos.mpr hpc.2)
  have hpcDualDen : 1 - pcDual ≠ 0 :=
    ne_of_gt (sub_pos.mpr hpcDual.2)
  calc
    (pc / (1 - pc)) * (pcDual / (1 - pcDual)) =
        pcDual * pc / ((1 - pcDual) * (1 - pc)) := by
          field_simp [hpcDen, hpcDualDen]
    _ = q := hproduct

end StatMech.FK.PeriodicPlanar
