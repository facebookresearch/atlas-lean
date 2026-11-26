/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.CriticalReduction

/-!
# Critical-point duality from monotonicity of the percolation probability

Off-critical sharpness of the wired percolation predicate follows from monotonicity of
`p ↦ θ(p, q)`, which reduces the self-dual critical relation to monotonicity, coverage and
no-coexistence.

## i. Overview

If `θ ≥ 0` is monotone on `(0, 1)` and `pc` is the supremum of its zero set, then `θ = 0` below
`pc` and `θ > 0` above it. For a periodic graph this gives off-critical sharpness of the wired
model from monotonicity of its percolation probability. Coverage in both directions keeps the
primal and dual critical points away from `1`. Feeding sharpness into the reduction of
`CriticalReduction` gives `pc* = (pc)*`.
The headline `PeriodicGraph.dualCritical_relation_of_monotonicity_noCoexistence` is conditional:
it assumes monotonicity of `θ` on `(0, 1)` for the primal and dual graphs,
`DualSubcriticalCoverage` and `DualNoCoexistence`, besides `pc, pc* ∈ (0, 1)` and `0 < q`.

## ii. Key results

- `offCriticalSharpness_of_nonnegative_monotoneOn` : a nonnegative monotone function is sharp at
  the supremum of its zero set.
- `PeriodicGraph.criticalPoints_mem_Ioo_of_bidirectionalCoverage` : coverage in both directions
  puts both critical points in `(0, 1)`.
- `PeriodicGraph.dualCritical_relation_of_monotonicity_noCoexistence` : the critical relation from
  monotonicity, coverage and no-coexistence.

## iii. Table of contents

- A. Sharpness from monotonicity
- B. Bounds on the critical point
- C. The critical relation

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Sections 5.1 and 6.2.
-/

@[expose] public section

open MeasureTheory Set SimpleGraph

namespace StatMech.FK.PeriodicPlanar

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

/-! ## A. Sharpness from monotonicity -/

/-- A nonnegative function, monotone on `(0, 1)` with a nonempty zero set, is sharp at the supremum
`pc` of its zero set: it vanishes below `pc` and is positive above. -/
lemma offCriticalSharpness_of_nonnegative_monotoneOn
    {theta : Real -> Real} {pc : Real}
    (htheta : forall p, 0 <= theta p)
    (hmono : MonotoneOn theta (Ioo (0 : Real) 1))
    (hne : ({p | p ∈ Ioo (0 : Real) 1 /\ theta p = 0} : Set Real).Nonempty)
    (hpc : pc = sSup {p | p ∈ Ioo (0 : Real) 1 /\ theta p = 0}) :
    OffCriticalSharpness (fun p => 0 < theta p) pc := by
  let S : Set Real := {p | p ∈ Ioo (0 : Real) 1 /\ theta p = 0}
  have hbdd : BddAbove S := by
    refine ⟨1, ?_⟩
    intro p hp
    exact hp.1.2.le
  constructor
  · intro p hp hppc hperc
    have hlt : p < sSup S := by
      change p < sSup {r | r ∈ Ioo (0 : Real) 1 /\ theta r = 0}
      rwa [← hpc]
    obtain ⟨r, hr, hpr⟩ := exists_lt_of_lt_csSup hne hlt
    have hle : theta p <= theta r := hmono hp hr.1 hpr.le
    have hzero : theta p = 0 := le_antisymm (by simpa [hr.2] using hle) (htheta p)
    exact hperc.ne' hzero
  · intro p hp hpcp
    have hnezero : theta p ≠ 0 := by
      intro hzero
      have hmem : p ∈ S := ⟨hp, hzero⟩
      have hle : p <= sSup S := le_csSup hbdd hmem
      change p <= sSup {r | r ∈ Ioo (0 : Real) 1 /\ theta r = 0} at hle
      rw [← hpc] at hle
      exact (not_le_of_gt hpcp) hle
    exact lt_of_le_of_ne (htheta p) (Ne.symm hnezero)

/-! ## B. Bounds on the critical point -/

section Countable

variable [Countable V]

lemma PeriodicGraph.subcriticalSet_bddAbove
    (P : PeriodicGraph V) (q : Real) :
    BddAbove (P.subcriticalSet q) := by
  refine ⟨1, ?_⟩
  intro p hp
  exact hp.1.2.le

lemma PeriodicGraph.subcriticalSet_nonempty_of_criticalPoint_pos
    (P : PeriodicGraph V) {q : Real} (hpc : 0 < P.criticalPoint q) :
    (P.subcriticalSet q).Nonempty := by
  rcases (P.subcriticalSet q).eq_empty_or_nonempty with hempty | hne
  · rw [PeriodicGraph.criticalPoint, hempty, Real.sSup_empty] at hpc
    exfalso
    exact (lt_irrefl 0) hpc
  · exact hne

lemma PeriodicGraph.criticalPoint_le_one_of_pos
    (P : PeriodicGraph V) {q : Real} (hpc : 0 < P.criticalPoint q) :
    P.criticalPoint q <= 1 := by
  rw [PeriodicGraph.criticalPoint]
  exact csSup_le (P.subcriticalSet_nonempty_of_criticalPoint_pos hpc)
    (fun _ hp => hp.1.2.le)

lemma PeriodicGraph.wiredPercolationProbability_eq_zero_of_lt_criticalPoint
    (P : PeriodicGraph V) {q p : Real}
    (hpc : 0 < P.criticalPoint q)
    (hmono : MonotoneOn
      (fun r => P.wiredPercolationProbability r q) (Ioo (0 : Real) 1))
    (hp : p ∈ Ioo (0 : Real) 1) (hlt : p < P.criticalPoint q) :
    P.wiredPercolationProbability p q = 0 := by
  have hne := P.subcriticalSet_nonempty_of_criticalPoint_pos hpc
  have hltSup : p < sSup (P.subcriticalSet q) := by
    simpa only [PeriodicGraph.criticalPoint] using hlt
  obtain ⟨r, hr, hpr⟩ := exists_lt_of_lt_csSup hne hltSup
  have hle := hmono hp hr.1 hpr.le
  exact le_antisymm (by simpa only [hr.2] using hle)
    (P.wiredPercolationProbability_nonneg p q)

lemma PeriodicGraph.wiredPercolates_of_criticalPoint_lt
    (P : PeriodicGraph V) {q p : Real}
    (hp : p ∈ Ioo (0 : Real) 1) (hlt : P.criticalPoint q < p) :
    P.wiredPercolates p q := by
  unfold PeriodicGraph.wiredPercolates
  have hne : P.wiredPercolationProbability p q ≠ 0 := by
    intro hzero
    have hmem : p ∈ P.subcriticalSet q := ⟨hp, hzero⟩
    have hle : p ≤ sSup (P.subcriticalSet q) :=
      le_csSup (P.subcriticalSet_bddAbove q) hmem
    exact (not_le_of_gt hlt) (by
      simpa only [PeriodicGraph.criticalPoint] using hle)
  exact lt_of_le_of_ne (P.wiredPercolationProbability_nonneg p q) hne.symm

lemma PeriodicGraph.criticalPoint_lt_one_of_dualSubcriticalCoverage
    [Countable W]
    (P : PeriodicGraph V) (Pdual : PeriodicGraph W) {q : Real}
    (hq : 0 < q)
    (hpc : 0 < P.criticalPoint q)
    (hpcDual : 0 < Pdual.criticalPoint q)
    (hmonoDual : MonotoneOn
      (fun r => Pdual.wiredPercolationProbability r q)
        (Ioo (0 : Real) 1))
    (hcoverage : DualSubcriticalCoverage
      (fun r => Pdual.wiredPercolates r q) (P.criticalPoint q) q) :
    P.criticalPoint q < 1 := by
  have hpc_le := P.criticalPoint_le_one_of_pos hpc
  have hpcDual_le := Pdual.criticalPoint_le_one_of_pos hpcDual
  by_contra hnot
  have hpceq : P.criticalPoint q = 1 :=
    le_antisymm hpc_le (le_of_not_gt hnot)
  let r : Real := Pdual.criticalPoint q / 2
  have hr : r ∈ Ioo (0 : Real) 1 := by
    dsimp only [r]
    constructor
    · linarith
    · linarith
  let p : Real := BeffaraDC.dualParam r q
  have hp : p ∈ Ioo (0 : Real) 1 :=
    BeffaraDC.dualParam_mem_Ioo hr.1 hr.2 hq
  have hinv : BeffaraDC.dualParam p q = r := by
    dsimp only [p]
    exact dualParam_involutive hr.1 hr.2 hq
  have hpcrit : p < P.criticalPoint q := by
    rw [hpceq]
    exact hp.2
  have hperc := hcoverage p hp hpcrit
  have hzero :=
    Pdual.wiredPercolationProbability_eq_zero_of_lt_criticalPoint
      hpcDual hmonoDual hr (by dsimp only [r]; linarith)
  rw [hinv] at hperc
  exact (ne_of_gt hperc) hzero

/-- Given positive critical points, monotone percolation probabilities and dual subcritical coverage
in both directions, both critical points lie in `(0, 1)`. -/
lemma PeriodicGraph.criticalPoints_mem_Ioo_of_bidirectionalCoverage
    [Countable W]
    (P : PeriodicGraph V) (Pdual : PeriodicGraph W) {q : Real}
    (hq : 0 < q)
    (hpc : 0 < P.criticalPoint q)
    (hpcDual : 0 < Pdual.criticalPoint q)
    (hmonoPrimal : MonotoneOn
      (fun r => P.wiredPercolationProbability r q) (Ioo (0 : Real) 1))
    (hmonoDual : MonotoneOn
      (fun r => Pdual.wiredPercolationProbability r q)
        (Ioo (0 : Real) 1))
    (hcoverage : DualSubcriticalCoverage
      (fun r => Pdual.wiredPercolates r q) (P.criticalPoint q) q)
    (hcoverageDual : DualSubcriticalCoverage
      (fun r => P.wiredPercolates r q) (Pdual.criticalPoint q) q) :
    P.criticalPoint q ∈ Ioo (0 : Real) 1 /\
      Pdual.criticalPoint q ∈ Ioo (0 : Real) 1 := by
  exact ⟨⟨hpc, P.criticalPoint_lt_one_of_dualSubcriticalCoverage
      Pdual hq hpc hpcDual hmonoDual hcoverage⟩,
    ⟨hpcDual, Pdual.criticalPoint_lt_one_of_dualSubcriticalCoverage
      P hq hpcDual hpc hmonoPrimal hcoverageDual⟩⟩

lemma PeriodicGraph.offCriticalSharpness_of_monotoneOn
    (P : PeriodicGraph V) {q : Real}
    (hpc : P.criticalPoint q ∈ Ioo (0 : Real) 1)
    (hmono : MonotoneOn
      (fun p => P.wiredPercolationProbability p q) (Ioo (0 : Real) 1)) :
    OffCriticalSharpness
      (fun p => P.wiredPercolates p q) (P.criticalPoint q) := by
  apply offCriticalSharpness_of_nonnegative_monotoneOn
    (P.wiredPercolationProbability_nonneg (q := q)) hmono
    (P.subcriticalSet_nonempty_of_criticalPoint_pos hpc.1)
  rfl

end Countable

/-! ## C. The critical relation -/

/-- Conditional critical-point duality: monotonicity of the primal and dual wired percolation
probabilities, dual subcritical coverage and no-coexistence give `pc* = (pc)*` and
`pc / (1 - pc) · pc* / (1 - pc*) = q`. -/
theorem PeriodicGraph.dualCritical_relation_of_monotonicity_noCoexistence
    [Countable V] [Countable W]
    (P : PeriodicGraph V) (Pdual : PeriodicGraph W)
    {q : Real}
    (hpc : P.criticalPoint q ∈ Ioo (0 : Real) 1)
    (hpcDual : Pdual.criticalPoint q ∈ Ioo (0 : Real) 1)
    (hq : 0 < q)
    (hmonoPrimal : MonotoneOn
      (fun p => P.wiredPercolationProbability p q) (Ioo (0 : Real) 1))
    (hmonoDual : MonotoneOn
      (fun p => Pdual.wiredPercolationProbability p q) (Ioo (0 : Real) 1))
    (hcoverage : DualSubcriticalCoverage
      (fun p => Pdual.wiredPercolates p q) (P.criticalPoint q) q)
    (hnoCoexistence : DualNoCoexistence
      (fun p => P.wiredPercolates p q)
      (fun p => Pdual.wiredPercolates p q) q) :
    BeffaraDC.dualParam (P.criticalPoint q) q = Pdual.criticalPoint q /\
      (P.criticalPoint q / (1 - P.criticalPoint q)) *
        (Pdual.criticalPoint q / (1 - Pdual.criticalPoint q)) = q := by
  apply P.dualCritical_relation_of_sharpness_noCoexistence Pdual
    hpc hpcDual hq
  · exact P.offCriticalSharpness_of_monotoneOn hpc hmonoPrimal
  · exact Pdual.offCriticalSharpness_of_monotoneOn hpcDual hmonoDual
  · exact hcoverage
  · exact hnoCoexistence

end StatMech.FK.PeriodicPlanar
