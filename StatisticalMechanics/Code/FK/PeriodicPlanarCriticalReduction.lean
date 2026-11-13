/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarThermodynamicDuality

















open MeasureTheory Set SimpleGraph

namespace StatMech
namespace FK
namespace PeriodicPlanar

open BeffaraDC

variable {V W : Type*} [DecidableEq V] [DecidableEq W]


def PeriodicGraph.openSubgraph (P : PeriodicGraph V)
    (omega : ConfigSpace (Sym2 V)) : SimpleGraph V where
  Adj x y := P.graph.Adj x y ∧ omega s(x, y) = true
  symm x y h := ⟨h.1.symm, by simpa [Sym2.eq_swap] using h.2⟩
  loopless := ⟨fun x h ↦ h.1.ne rfl⟩

@[simp] theorem PeriodicGraph.openSubgraph_adj
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V)) (x y : V) :
    (P.openSubgraph omega).Adj x y ↔
      P.graph.Adj x y ∧ omega s(x, y) = true :=
  Iff.rfl



noncomputable def PeriodicGraph.root (P : PeriodicGraph V) : V :=
  P.fundamentalDomain_nonempty.choose

theorem PeriodicGraph.root_mem_fundamentalDomain (P : PeriodicGraph V) :
    P.root ∈ P.fundamentalDomain :=
  P.fundamentalDomain_nonempty.choose_spec


def PeriodicGraph.cluster (P : PeriodicGraph V)
    (omega : ConfigSpace (Sym2 V)) (v : V) : Set V :=
  {w | (P.openSubgraph omega).Reachable v w}



def PeriodicGraph.HasInfiniteCluster
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V)) : Prop :=
  ∃ x, (P.cluster omega x).Infinite


def PeriodicGraph.percolationEvent (P : PeriodicGraph V) :
    Set (ConfigSpace (Sym2 V)) :=
  {omega | (P.cluster omega P.root).Infinite}

section Countable

variable [Countable V]




noncomputable def PeriodicGraph.wiredPercolationProbability
    (P : PeriodicGraph V) (p q : ℝ) : ℝ :=
  if h : p ∈ Ioo (0 : ℝ) 1 ∧ 0 < q then
    ((P.wiredBufferedInfiniteVolume h.1.1 h.1.2 h.2 :
        ProbabilityMeasure (ConfigSpace (Sym2 V))) :
      Measure (ConfigSpace (Sym2 V))).real P.percolationEvent
  else 0

theorem PeriodicGraph.wiredPercolationProbability_nonneg
    (P : PeriodicGraph V) (p q : ℝ) :
    0 ≤ P.wiredPercolationProbability p q := by
  unfold PeriodicGraph.wiredPercolationProbability
  split
  · exact ENNReal.toReal_nonneg
  · exact le_rfl

theorem PeriodicGraph.wiredPercolationProbability_le_one
    (P : PeriodicGraph V) (p q : ℝ) :
    P.wiredPercolationProbability p q ≤ 1 := by
  unfold PeriodicGraph.wiredPercolationProbability
  split
  · rw [Measure.real]
    refine ENNReal.toReal_le_of_le_ofReal (by norm_num) ?_
    rw [ENNReal.ofReal_one]
    exact prob_le_one
  · norm_num



def PeriodicGraph.wiredPercolates
    (P : PeriodicGraph V) (p q : ℝ) : Prop :=
  0 < P.wiredPercolationProbability p q


def PeriodicGraph.subcriticalSet
    (P : PeriodicGraph V) (q : ℝ) : Set ℝ :=
  {p | p ∈ Ioo (0 : ℝ) 1 ∧ P.wiredPercolationProbability p q = 0}

@[simp] theorem PeriodicGraph.mem_subcriticalSet
    (P : PeriodicGraph V) {p q : ℝ} :
    p ∈ P.subcriticalSet q ↔
      p ∈ Ioo (0 : ℝ) 1 ∧ P.wiredPercolationProbability p q = 0 :=
  Iff.rfl



noncomputable def PeriodicGraph.criticalPoint
    (P : PeriodicGraph V) (q : ℝ) : ℝ :=
  sSup (P.subcriticalSet q)

end Countable






def OffCriticalSharpness (percolates : ℝ → Prop) (pc : ℝ) : Prop :=
  (∀ p ∈ Ioo (0 : ℝ) 1, p < pc → ¬percolates p) ∧
  (∀ p ∈ Ioo (0 : ℝ) 1, pc < p → percolates p)



def DualSubcriticalCoverage
    (dualPercolates : ℝ → Prop) (pc q : ℝ) : Prop :=
  ∀ p ∈ Ioo (0 : ℝ) 1, p < pc →
    dualPercolates (dualParam p q)



def DualNoCoexistence
    (primalPercolates dualPercolates : ℝ → Prop) (q : ℝ) : Prop :=
  ∀ p ∈ Ioo (0 : ℝ) 1,
    ¬(primalPercolates p ∧ dualPercolates (dualParam p q))



theorem dualParam_strictAntiOn {q : ℝ} (hq : 0 < q) :
    StrictAntiOn (fun p : ℝ ↦ dualParam p q) (Ioo 0 1) := by
  intro p hp r hr hpr
  unfold dualParam
  rw [div_lt_div_iff₀ (dualDen_pos hr.1 hr.2 hq)
    (dualDen_pos hp.1 hp.2 hq)]
  nlinarith



theorem dualCritical_crossBounds_of_sharpness_noCoexistence
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



theorem dualCritical_eq_of_crossBounds
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
