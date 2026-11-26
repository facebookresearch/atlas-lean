/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.CriticalReduction

/-!
# Critical-point duality from strict no-coexistence

The self-dual relation `pc / (1 - pc) · pc* / (1 - pc*) = q` between the primal and dual critical
points, derived from a strict form of primal/dual no-coexistence.

## i. Overview

Strict no-coexistence asks that primal percolation at `r` and dual percolation at `p*` never hold
together when `r < p`. Together with off-critical sharpness of both models and the coverage input
(dual percolation at `p*` for every subcritical `p`), it gives the two cross bounds between `pc*`
and `p*`, and the strict monotonicity of `p ↦ p*` turns them into `pc* = (pc)*`.
Both results are conditional: they assume `OffCriticalSharpness` for the primal and the dual
percolation predicates, `DualSubcriticalCoverage`, and `StrictDualNoCoexistence`, besides
`pc, pc* ∈ (0, 1)` and `0 < q`.

## ii. Key results

- `dualCritical_crossBounds_of_sharpness_strictNoCoexistence` : the cross bounds between `pc*`
  and the dual parameters.
- `dualCritical_relation_of_sharpness_strictNoCoexistence` : `pc* = (pc)*` and
  `pc / (1 - pc) · pc* / (1 - pc*) = q`.

## iii. Table of contents

- A. Strict no-coexistence
- B. The critical relation

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Section 6.2.
-/

@[expose] public section

open MeasureTheory Set SimpleGraph

namespace StatMech.FK.PeriodicPlanar

open BeffaraDC

/-! ## A. Strict no-coexistence -/

/-- Strict primal/dual no-coexistence: for `r < p` in `(0, 1)`, the primal model does not percolate
at `r` while the dual model percolates at `p*`. -/
def StrictDualNoCoexistence
    (primalPercolates dualPercolates : Real → Prop) (q : Real) : Prop :=
  ∀ r ∈ Ioo (0 : Real) 1, ∀ p ∈ Ioo (0 : Real) 1, r < p →
    ¬(primalPercolates r ∧ dualPercolates (dualParam p q))

/-! ## B. The critical relation -/

lemma dualCritical_crossBounds_of_sharpness_strictNoCoexistence
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

/-- Conditional critical-point duality: off-critical sharpness of both models, dual subcritical
coverage and strict no-coexistence give `pc* = (pc)*` and `pc / (1 - pc) · pc* / (1 - pc*) = q`. -/
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
