/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.ThermodynamicDuality

/-!
# Reduction of critical-point duality to sharpness and no-coexistence

Percolation probabilities and critical points of periodic random-cluster models, and the
reduction of the self-dual relation between primal and dual critical points to three inputs.

## i. Overview

For a periodic graph we define open subgraphs, clusters, the percolation event at a root vertex,
the wired percolation probability `θ(p, q)` under the buffered wired infinite-volume measure, and
the critical point `pc(q) = sup {p : θ(p, q) = 0}`. The abstract argument then shows: if the primal
and dual percolation predicates are sharp off their critical points, the dual percolates at `p*`
for every subcritical `p` (coverage), and the two never percolate together at `p` and `p*`
(no-coexistence), then `pc* = (pc)*`, that is `pc / (1 - pc) · pc* / (1 - pc*) = q`.
The two headline results are conditional on `OffCriticalSharpness` (primal and dual),
`DualSubcriticalCoverage` and `DualNoCoexistence`, besides `pc, pc* ∈ (0, 1)` and `0 < q`.

## ii. Key results

- `PeriodicGraph.criticalPoint` : the wired critical point of a periodic random-cluster model.
- `dualCritical_eq_of_crossBounds` : cross bounds between `pc*` and `p*` force `pc* = (pc)*`.
- `dualCritical_relation_of_sharpness_noCoexistence` : the abstract critical relation.
- `PeriodicGraph.dualCritical_relation_of_sharpness_noCoexistence` : the critical relation for a
  periodic graph and its dual.

## iii. Table of contents

- A. Clusters and percolation
- B. Percolation probability and critical point
- C. Sharpness, coverage and no-coexistence
- D. The critical relation

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Sections 5.1 and 6.2.
-/

@[expose] public section

open MeasureTheory Set SimpleGraph

namespace StatMech
namespace FK
namespace PeriodicPlanar

open BeffaraDC

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

/-! ## A. Clusters and percolation -/

/-- The subgraph of open edges of a configuration. -/
def PeriodicGraph.openSubgraph (P : PeriodicGraph V)
    (omega : ConfigSpace (Sym2 V)) : SimpleGraph V where
  Adj x y := P.graph.Adj x y ∧ omega s(x, y) = true
  symm := ⟨fun x y h ↦ ⟨h.1.symm, by simpa [Sym2.eq_swap] using h.2⟩⟩
  loopless := ⟨fun x h ↦ h.1.ne rfl⟩

@[simp] lemma PeriodicGraph.openSubgraph_adj
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V)) (x y : V) :
    (P.openSubgraph omega).Adj x y ↔
      P.graph.Adj x y ∧ omega s(x, y) = true :=
  Iff.rfl

/-- A chosen root vertex in the fundamental domain. -/
noncomputable def PeriodicGraph.root (P : PeriodicGraph V) : V :=
  P.fundamentalDomain_nonempty.choose

lemma PeriodicGraph.root_mem_fundamentalDomain (P : PeriodicGraph V) :
    P.root ∈ P.fundamentalDomain :=
  P.fundamentalDomain_nonempty.choose_spec

/-- The open cluster of a vertex: all vertices joined to it by an open path. -/
def PeriodicGraph.cluster (P : PeriodicGraph V)
    (omega : ConfigSpace (Sym2 V)) (v : V) : Set V :=
  {w | (P.openSubgraph omega).Reachable v w}

/-- The configuration has an infinite open cluster. -/
def PeriodicGraph.HasInfiniteCluster
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V)) : Prop :=
  ∃ x, (P.cluster omega x).Infinite

/-- The event that the open cluster of the root is infinite. -/
def PeriodicGraph.percolationEvent (P : PeriodicGraph V) :
    Set (ConfigSpace (Sym2 V)) :=
  {omega | (P.cluster omega P.root).Infinite}

/-! ## B. Percolation probability and critical point -/

section Countable

variable [Countable V]

/-- The wired percolation probability `θ(p, q)`: the probability that the root cluster is infinite
under the buffered wired infinite-volume measure, and `0` outside `0 < p < 1`, `0 < q`. -/
noncomputable def PeriodicGraph.wiredPercolationProbability
    (P : PeriodicGraph V) (p q : ℝ) : ℝ :=
  if h : p ∈ Ioo (0 : ℝ) 1 ∧ 0 < q then
    ((P.wiredBufferedInfiniteVolume h.1.1 h.1.2 h.2 :
        ProbabilityMeasure (ConfigSpace (Sym2 V))) :
      Measure (ConfigSpace (Sym2 V))).real P.percolationEvent
  else 0

lemma PeriodicGraph.wiredPercolationProbability_nonneg
    (P : PeriodicGraph V) (p q : ℝ) :
    0 ≤ P.wiredPercolationProbability p q := by
  unfold PeriodicGraph.wiredPercolationProbability
  split
  · exact ENNReal.toReal_nonneg
  · exact le_rfl

lemma PeriodicGraph.wiredPercolationProbability_le_one
    (P : PeriodicGraph V) (p q : ℝ) :
    P.wiredPercolationProbability p q ≤ 1 := by
  unfold PeriodicGraph.wiredPercolationProbability
  split
  · rw [Measure.real]
    refine ENNReal.toReal_le_of_le_ofReal (by norm_num) ?_
    rw [ENNReal.ofReal_one]
    exact prob_le_one
  · norm_num

/-- The wired model percolates at `(p, q)`: `θ(p, q) > 0`. -/
def PeriodicGraph.wiredPercolates
    (P : PeriodicGraph V) (p q : ℝ) : Prop :=
  0 < P.wiredPercolationProbability p q

/-- The parameters `p ∈ (0, 1)` at which `θ(p, q) = 0`. -/
def PeriodicGraph.subcriticalSet
    (P : PeriodicGraph V) (q : ℝ) : Set ℝ :=
  {p | p ∈ Ioo (0 : ℝ) 1 ∧ P.wiredPercolationProbability p q = 0}

@[simp] lemma PeriodicGraph.mem_subcriticalSet
    (P : PeriodicGraph V) {p q : ℝ} :
    p ∈ P.subcriticalSet q ↔
      p ∈ Ioo (0 : ℝ) 1 ∧ P.wiredPercolationProbability p q = 0 :=
  Iff.rfl

/-- The wired critical point `pc(q) = sup {p : θ(p, q) = 0}`. -/
noncomputable def PeriodicGraph.criticalPoint
    (P : PeriodicGraph V) (q : ℝ) : ℝ :=
  sSup (P.subcriticalSet q)

end Countable

/-! ## C. Sharpness, coverage and no-coexistence -/

/-- A percolation predicate is sharp off `pc`: it fails below `pc` and holds above `pc` on `(0, 1)`.
-/
def OffCriticalSharpness (percolates : ℝ → Prop) (pc : ℝ) : Prop :=
  (∀ p ∈ Ioo (0 : ℝ) 1, p < pc → ¬percolates p) ∧
  (∀ p ∈ Ioo (0 : ℝ) 1, pc < p → percolates p)

/-- Dual subcritical coverage: the dual model percolates at `p*` for every `p < pc` in `(0, 1)`. -/
def DualSubcriticalCoverage
    (dualPercolates : ℝ → Prop) (pc q : ℝ) : Prop :=
  ∀ p ∈ Ioo (0 : ℝ) 1, p < pc →
    dualPercolates (dualParam p q)

/-- Primal/dual no-coexistence: the primal model at `p` and the dual model at `p*` never percolate
together. -/
def DualNoCoexistence
    (primalPercolates dualPercolates : ℝ → Prop) (q : ℝ) : Prop :=
  ∀ p ∈ Ioo (0 : ℝ) 1,
    ¬(primalPercolates p ∧ dualPercolates (dualParam p q))

/-! ## D. The critical relation -/

lemma dualParam_strictAntiOn {q : ℝ} (hq : 0 < q) :
    StrictAntiOn (fun p : ℝ ↦ dualParam p q) (Ioo 0 1) := by
  intro p hp r hr hpr
  unfold dualParam
  rw [div_lt_div_iff₀ (dualDen_pos hr.1 hr.2 hq)
    (dualDen_pos hp.1 hp.2 hq)]
  nlinarith

lemma dualCritical_crossBounds_of_sharpness_noCoexistence
    {primalPercolates dualPercolates : ℝ → Prop}
    {pc pcDual q : ℝ}
    (hq : 0 < q)
    (hsharpPrimal : OffCriticalSharpness primalPercolates pc)
    (hsharpDual : OffCriticalSharpness dualPercolates pcDual)
    (hcoverage : DualSubcriticalCoverage dualPercolates pc q)
    (hnoCoexistence :
      DualNoCoexistence primalPercolates dualPercolates q) :
    (∀ p ∈ Ioo (0 : ℝ) 1, p < pc →
        pcDual ≤ dualParam p q) ∧
      (∀ p ∈ Ioo (0 : ℝ) 1, pc < p →
        dualParam p q ≤ pcDual) := by
  constructor
  · intro p hp hppc
    have hpDual := dualParam_mem_Ioo hp.1 hp.2 hq
    have hperc := hcoverage p hp hppc
    by_contra hnot
    have hlt : dualParam p q < pcDual := lt_of_not_ge hnot
    exact hsharpDual.1 (dualParam p q) hpDual hlt hperc
  · intro p hp hpcp
    have hpDual := dualParam_mem_Ioo hp.1 hp.2 hq
    have hperc := hsharpPrimal.2 p hp hpcp
    have hdualNot : ¬dualPercolates (dualParam p q) := by
      intro hdual
      exact hnoCoexistence p hp ⟨hperc, hdual⟩
    by_contra hnot
    have hlt : pcDual < dualParam p q := lt_of_not_ge hnot
    exact hdualNot (hsharpDual.2 (dualParam p q) hpDual hlt)

/-- Cross bounds `pc* ≤ p*` for `p < pc` and `p* ≤ pc*` for `p > pc` force `pc* = (pc)*`. -/
lemma dualCritical_eq_of_crossBounds
    {pc pcDual q : ℝ}
    (hpc : pc ∈ Ioo (0 : ℝ) 1)
    (hpcDual : pcDual ∈ Ioo (0 : ℝ) 1)
    (hq : 0 < q)
    (hsub : ∀ p ∈ Ioo (0 : ℝ) 1, p < pc →
      pcDual ≤ dualParam p q)
    (hsuper : ∀ p ∈ Ioo (0 : ℝ) 1, pc < p →
      dualParam p q ≤ pcDual) :
    dualParam pc q = pcDual := by
  have hanti := dualParam_strictAntiOn hq
  have hdpc := dualParam_mem_Ioo hpc.1 hpc.2 hq
  have hdpcDual := dualParam_mem_Ioo hpcDual.1 hpcDual.2 hq
  have hinvPc := dualParam_involutive hpc.1 hpc.2 hq
  have hinvPcDual := dualParam_involutive hpcDual.1 hpcDual.2 hq
  apply le_antisymm
  · by_contra hnot
    have hlt : pcDual < dualParam pc q := lt_of_not_ge hnot
    have hcross : pc < dualParam pcDual q := by
      have h := hanti hpcDual hdpc hlt
      simpa only [hinvPc] using h
    let p := (pc + dualParam pcDual q) / 2
    have hpL : pc < p := by dsimp [p]; linarith
    have hpR : p < dualParam pcDual q := by dsimp [p]; linarith
    have hp : p ∈ Ioo (0 : ℝ) 1 :=
      ⟨hpc.1.trans hpL, hpR.trans hdpcDual.2⟩
    have hpBound := hsuper p hp hpL
    have hpStrict : pcDual < dualParam p q := by
      have h := hanti hp hdpcDual hpR
      simpa only [hinvPcDual] using h
    linarith
  · by_contra hnot
    have hlt : dualParam pc q < pcDual := lt_of_not_ge hnot
    have hcross : dualParam pcDual q < pc := by
      have h := hanti hdpc hpcDual hlt
      simpa only [hinvPc] using h
    let p := (dualParam pcDual q + pc) / 2
    have hpL : dualParam pcDual q < p := by dsimp [p]; linarith
    have hpR : p < pc := by dsimp [p]; linarith
    have hp : p ∈ Ioo (0 : ℝ) 1 :=
      ⟨hdpcDual.1.trans hpL, hpR.trans hpc.2⟩
    have hpBound := hsub p hp hpR
    have hpStrict : dualParam p q < pcDual := by
      have h := hanti hdpcDual hp hpL
      simpa only [hinvPcDual] using h
    linarith

/-- Conditional critical-point duality: off-critical sharpness of both models, dual subcritical
coverage and no-coexistence give `pc* = (pc)*` and `pc / (1 - pc) · pc* / (1 - pc*) = q`. -/
theorem dualCritical_relation_of_sharpness_noCoexistence
    {primalPercolates dualPercolates : ℝ → Prop}
    {pc pcDual q : ℝ}
    (hpc : pc ∈ Ioo (0 : ℝ) 1)
    (hpcDual : pcDual ∈ Ioo (0 : ℝ) 1)
    (hq : 0 < q)
    (hsharpPrimal : OffCriticalSharpness primalPercolates pc)
    (hsharpDual : OffCriticalSharpness dualPercolates pcDual)
    (hcoverage : DualSubcriticalCoverage dualPercolates pc q)
    (hnoCoexistence :
      DualNoCoexistence primalPercolates dualPercolates q) :
    dualParam pc q = pcDual ∧
      (pc / (1 - pc)) * (pcDual / (1 - pcDual)) = q := by
  obtain ⟨hsub, hsuper⟩ :=
    dualCritical_crossBounds_of_sharpness_noCoexistence hq
      hsharpPrimal hsharpDual hcoverage hnoCoexistence
  have hcritical := dualCritical_eq_of_crossBounds
    hpc hpcDual hq hsub hsuper
  refine ⟨hcritical, ?_⟩
  have hproduct := dualParam_product_eq hpc.1 hpc.2 hq
  rw [hcritical] at hproduct
  have hpcDen : 1 - pc ≠ 0 := ne_of_gt (sub_pos.mpr hpc.2)
  have hpcDualDen : 1 - pcDual ≠ 0 :=
    ne_of_gt (sub_pos.mpr hpcDual.2)
  calc
    (pc / (1 - pc)) * (pcDual / (1 - pcDual)) =
        pcDual * pc / ((1 - pcDual) * (1 - pc)) := by
          field_simp [hpcDen, hpcDualDen]
    _ = q := hproduct

/-- Conditional critical-point duality for a periodic graph and its dual, under off-critical
sharpness of both wired models, dual subcritical coverage and no-coexistence. -/
theorem PeriodicGraph.dualCritical_relation_of_sharpness_noCoexistence
    [Countable V] [Countable W]
    (P : PeriodicGraph V) (Pdual : PeriodicGraph W)
    {q : ℝ}
    (hpc : P.criticalPoint q ∈ Ioo (0 : ℝ) 1)
    (hpcDual : Pdual.criticalPoint q ∈ Ioo (0 : ℝ) 1)
    (hq : 0 < q)
    (hsharpPrimal : OffCriticalSharpness
      (fun p ↦ P.wiredPercolates p q) (P.criticalPoint q))
    (hsharpDual : OffCriticalSharpness
      (fun p ↦ Pdual.wiredPercolates p q) (Pdual.criticalPoint q))
    (hcoverage : DualSubcriticalCoverage
      (fun p ↦ Pdual.wiredPercolates p q) (P.criticalPoint q) q)
    (hnoCoexistence : DualNoCoexistence
      (fun p ↦ P.wiredPercolates p q)
      (fun p ↦ Pdual.wiredPercolates p q) q) :
    dualParam (P.criticalPoint q) q = Pdual.criticalPoint q ∧
      (P.criticalPoint q / (1 - P.criticalPoint q)) *
        (Pdual.criticalPoint q / (1 - Pdual.criticalPoint q)) = q := by
  exact StatMech.FK.PeriodicPlanar.dualCritical_relation_of_sharpness_noCoexistence
    hpc hpcDual hq hsharpPrimal hsharpDual hcoverage hnoCoexistence

end PeriodicPlanar
end FK
end StatMech
