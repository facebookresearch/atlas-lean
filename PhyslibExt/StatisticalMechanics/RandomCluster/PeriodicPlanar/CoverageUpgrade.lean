/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Coverage
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.CanonicalFiniteEnergy
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.BurtonKeaneMerge

/-!
# Dual subcritical coverage from exponential decay

Upgrades "the dual configuration has an infinite cluster almost surely" to dual percolation at
the root, and so derives dual subcritical coverage from subcritical exponential decay of primal
two-point connections.

## i. Overview

On a connected periodic graph, finite energy lets one open the finitely many edges of a path to
the root, so a positive-probability infinite cluster at some vertex gives a positive-probability
infinite cluster at every vertex, in particular at the root. Closing a primal edge is opening the
dual edge, so finite energy of the primal free measure under closing passes to the dual measure.
Together with the Borel–Cantelli argument of `Coverage`, exponential decay below `pc` gives free
dual percolation at every `p < pc`, which is the dual subcritical coverage input of the critical
relation.
The headlines are conditional: `dualSubcriticalCoverage_of_exponentialDecay` assumes
`PolynomialConnectionShells D` and `SubcriticalTwoPointExponentialDecay P q pc`;
`bidirectionalSubcriticalCoverage_of_exponentialDecay` assumes both of these for `D` and for the
swapped pair `D.swap` (with `Pdual` and `pcDual`). Both also need `1 ≤ q`.

## ii. Key results

- `PeriodicGraph.percolationEvent_pos_of_hasInfiniteCluster_measure_eq_one` : with finite energy,
  an almost sure infinite cluster gives positive percolation at the root.
- `PeriodicPlanarDualPair.dualMeasure_hasFiniteEnergy_of_primal_singleClosed` : finite energy of
  the dual measure from closing primal edges.
- `PeriodicPlanarDualPair.dualSubcriticalCoverage_of_exponentialDecay` : dual subcritical coverage
  from exponential decay.
- `PeriodicPlanarDualPair.bidirectionalSubcriticalCoverage_of_exponentialDecay` : coverage in both
  directions.

## iii. Table of contents

- A. Finite energy and infinite clusters
- B. Finite energy of the dual measure
- C. Coverage from exponential decay

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Sections 3.8 and 6.2.
-/

@[expose] public section

open Filter MeasureTheory Set SimpleGraph

namespace StatMech.FK.PeriodicPlanar

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

/-! ## A. Finite energy and infinite clusters -/

lemma PeriodicGraph.percolationEvent_pos_of_vertex_cluster_infinite_pos
    (P : PeriodicGraph V) (hconn : P.graph.Connected)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (hfe : HasFiniteEnergy mu) (x : V)
    (hx : 0 < mu {omega | (P.cluster omega x).Infinite}) :
    0 < mu P.percolationEvent := by
  obtain ⟨F, hF⟩ := P.exists_forceOpen_walk hconn P.root x
  have hsub : {omega | (P.cluster omega x).Infinite} ⊆
      forceOpenFinset F ⁻¹' P.percolationEvent := by
    intro omega hinfinite
    change (P.cluster (forceOpenFinset F omega) P.root).Infinite
    rw [P.cluster_eq_of_reachable (forceOpenFinset F omega) (hF omega)]
    exact hinfinite.mono
      (P.cluster_mono (forceOpenFinset_le F omega) x)
  by_contra hnot
  have hrootzero : mu P.percolationEvent = 0 :=
    le_antisymm (not_lt.mp hnot) bot_le
  have hmapzero : (mu.map (forceOpenFinset F)) P.percolationEvent = 0 :=
    hfe F hrootzero
  rw [Measure.map_apply (measurable_forceOpenFinset F)
    (PeriodicPlanarDualPair.percolationEvent_measurableSet P)] at hmapzero
  have hle :
      mu {omega | (P.cluster omega x).Infinite} ≤
        mu (forceOpenFinset F ⁻¹' P.percolationEvent) :=
    measure_mono hsub
  rw [hmapzero] at hle
  exact (not_lt_of_ge hle) hx

lemma PeriodicGraph.clusterInfinite_pos_of_clusterInfinite_pos
    (P : PeriodicGraph V) (hconn : P.graph.Connected)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (hfe : HasFiniteEnergy mu) (x y : V)
    (hx : 0 < mu {omega | (P.cluster omega x).Infinite}) :
    0 < mu {omega | (P.cluster omega y).Infinite} := by
  obtain ⟨F, hF⟩ := P.exists_forceOpen_walk hconn y x
  have hsub : {omega | (P.cluster omega x).Infinite} ⊆
      forceOpenFinset F ⁻¹' {omega | (P.cluster omega y).Infinite} := by
    intro omega hinfinite
    change (P.cluster (forceOpenFinset F omega) y).Infinite
    rw [P.cluster_eq_of_reachable (forceOpenFinset F omega) (hF omega)]
    exact hinfinite.mono
      (P.cluster_mono (forceOpenFinset_le F omega) x)
  by_contra hnot
  have htargetzero : mu {omega | (P.cluster omega y).Infinite} = 0 :=
    le_antisymm (not_lt.mp hnot) bot_le
  have hmapzero :
      (mu.map (forceOpenFinset F))
        {omega | (P.cluster omega y).Infinite} = 0 :=
    hfe F htargetzero
  rw [Measure.map_apply (measurable_forceOpenFinset F)
    (P.measurableSet_cluster_infinite y)] at hmapzero
  have hle :
      mu {omega | (P.cluster omega x).Infinite} ≤
        mu (forceOpenFinset F ⁻¹'
          {omega | (P.cluster omega y).Infinite}) :=
    measure_mono hsub
  rw [hmapzero] at hle
  exact (not_lt_of_ge hle) hx

lemma PeriodicGraph.clusterInfinite_real_pos_iff
    (P : PeriodicGraph V) (hconn : P.graph.Connected)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (hfe : HasFiniteEnergy mu) (x y : V) :
    0 < mu.real {omega | (P.cluster omega x).Infinite} ↔
      0 < mu.real {omega | (P.cluster omega y).Infinite} := by
  constructor
  · intro hx
    have hxy := P.clusterInfinite_pos_of_clusterInfinite_pos hconn mu hfe x y
      (ENNReal.toReal_pos_iff.mp hx).1
    exact ENNReal.toReal_pos hxy.ne'
      (measure_ne_top mu {omega | (P.cluster omega y).Infinite})
  · intro hy
    have hyx := P.clusterInfinite_pos_of_clusterInfinite_pos hconn mu hfe y x
      (ENNReal.toReal_pos_iff.mp hy).1
    exact ENNReal.toReal_pos hyx.ne'
      (measure_ne_top mu {omega | (P.cluster omega x).Infinite})

/-- On a connected periodic graph, a finite-energy measure under which an infinite cluster exists
almost surely gives the root an infinite cluster with positive probability. -/
lemma PeriodicGraph.percolationEvent_pos_of_hasInfiniteCluster_measure_eq_one
    (P : PeriodicGraph V) (hconn : P.graph.Connected)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (hfe : HasFiniteEnergy mu)
    (hexists : mu {omega | P.HasInfiniteCluster omega} = 1) :
    0 < mu P.percolationEvent := by
  have hsome : ∃ x : V,
      0 < mu {omega | (P.cluster omega x).Infinite} := by
    by_contra hnone
    push Not at hnone
    have hzero : ∀ x : V,
        mu {omega | (P.cluster omega x).Infinite} = 0 := by
      intro x
      exact le_antisymm (hnone x) bot_le
    have hunion : mu (⋃ x : V,
        {omega : ConfigSpace (Sym2 V) |
          (P.cluster omega x).Infinite}) = 0 :=
      measure_iUnion_null hzero
    have heq : {omega : ConfigSpace (Sym2 V) |
          P.HasInfiniteCluster omega} =
        ⋃ x : V, {omega : ConfigSpace (Sym2 V) |
          (P.cluster omega x).Infinite} := by
      ext omega
      simp [PeriodicGraph.HasInfiniteCluster]
    rw [heq, hunion] at hexists
    exact one_ne_zero hexists.symm
  obtain ⟨x, hx⟩ := hsome
  exact P.percolationEvent_pos_of_vertex_cluster_infinite_pos
    hconn mu hfe x hx

/-! ## B. Finite energy of the dual measure -/

namespace PeriodicPlanarDualPair

lemma dualConfigEquiv_setClosed_setOpen
    (D : PeriodicPlanarDualPair P Pdual) (e : Sym2 W)
    (omega : ConfigSpace (Sym2 V)) :
    setOpen e (dualConfigEquiv D.edgeDual omega) =
      dualConfigEquiv D.edgeDual
        (setClosed (D.edgeDual.symm e) omega) := by
  funext f
  by_cases hfe : f = e
  · subst f
    simp [setOpen, setClosed]
  · have hpre : D.edgeDual.symm f ≠ D.edgeDual.symm e := by
      exact fun h => hfe (D.edgeDual.symm.injective h)
    simp [setOpen, setClosed, hfe, hpre]

/-- If closing any single primal edge gives an absolutely continuous measure, the dual measure has
finite energy. -/
lemma dualMeasure_hasFiniteEnergy_of_primal_singleClosed
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (hclosed : ∀ e : Sym2 V, mu.map (setClosed e) ≪ mu) :
    HasFiniteEnergy (D.dualMeasure mu) := by
  apply hasFiniteEnergy_of_singleOpen
  intro e
  have hac := (hclosed (D.edgeDual.symm e)).map
    (continuous_dualConfigEquiv D.edgeDual).measurable
  have hfun : setOpen e ∘ dualConfigEquiv D.edgeDual =
      dualConfigEquiv D.edgeDual ∘ setClosed (D.edgeDual.symm e) := by
    funext omega
    exact D.dualConfigEquiv_setClosed_setOpen e omega
  unfold dualMeasure
  rw [Measure.map_map (measurable_setOpen e)
      (continuous_dualConfigEquiv D.edgeDual).measurable,
    hfun,
    ← Measure.map_map
      (continuous_dualConfigEquiv D.edgeDual).measurable
      (measurable_setClosed (D.edgeDual.symm e))]
  exact hac

/-! ## C. Coverage from exponential decay -/

lemma freeDualPercolates_of_hasInfiniteCluster_measure_eq_one
    (D : PeriodicPlanarDualPair P Pdual)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (hinfinite :
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V)))
          ((dualConfigEquiv D.edgeDual) ⁻¹'
            {eta | Pdual.HasInfiniteCluster eta}) = 1) :
    D.FreeDualPercolates p q := by
  let mu : Measure (ConfigSpace (Sym2 V)) :=
    P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
  let nu : Measure (ConfigSpace (Sym2 W)) := D.dualMeasure mu
  let : IsProbabilityMeasure nu := by
    dsimp only [nu]
    unfold dualMeasure
    infer_instance
  have hnu : nu {eta | Pdual.HasInfiniteCluster eta} = 1 := by
    dsimp only [nu]
    unfold dualMeasure
    rw [Measure.map_apply
      (continuous_dualConfigEquiv D.edgeDual).measurable
      Pdual.measurableSet_hasInfiniteCluster]
    exact hinfinite
  have hfeNu : HasFiniteEnergy nu := by
    dsimp only [nu]
    exact D.dualMeasure_hasFiniteEnergy_of_primal_singleClosed mu
      (P.freeBufferedInfiniteVolume_setClosed_absolutelyContinuous
        hp hp1 hq)
  have hroot : 0 < nu Pdual.percolationEvent :=
    Pdual.percolationEvent_pos_of_hasInfiniteCluster_measure_eq_one
      D.dual_connected nu hfeNu hnu
  unfold FreeDualPercolates freeDualPercolationProbability
  rw [dite_eq_left ⟨⟨hp, hp1⟩, zero_lt_one.trans_le hq⟩]
  change 0 < mu.real
    ((dualConfigEquiv D.edgeDual) ⁻¹' Pdual.percolationEvent)
  have hreal : 0 < nu.real Pdual.percolationEvent :=
    ENNReal.toReal_pos hroot.ne'
      (measure_ne_top nu Pdual.percolationEvent)
  dsimp only [nu] at hreal
  unfold dualMeasure Measure.real at hreal
  rw [Measure.map_apply
    (continuous_dualConfigEquiv D.edgeDual).measurable
    (percolationEvent_measurableSet Pdual)] at hreal
  exact hreal

lemma freeDualPercolates_of_shell_borelCantelli
    (D : PeriodicPlanarDualPair P Pdual) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (shell : ℕ → Set (ConfigSpace (Sym2 V)))
    (hsum : (∑' n,
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))) (shell n)) ≠ ⊤)
    (hplanar :
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        {eta | Pdual.HasInfiniteCluster eta})ᶜ ⊆
          limsup shell atTop) :
    D.FreeDualPercolates p q := by
  apply D.freeDualPercolates_of_hasInfiniteCluster_measure_eq_one
    hp hp1 hq
  exact D.freeDualHasInfiniteCluster_of_shell_borelCantelli
    hp hp1 hq shell hsum hplanar

lemma freeDualPercolates_of_summable_shell_bound
    (D : PeriodicPlanarDualPair P Pdual) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (shell : ℕ → Set (ConfigSpace (Sym2 V)))
    (bound : ℕ → NNReal) (hbound : Summable bound)
    (hshell : ∀ n,
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))) (shell n) ≤ bound n)
    (hplanar :
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        {eta | Pdual.HasInfiniteCluster eta})ᶜ ⊆
          limsup shell atTop) :
    D.FreeDualPercolates p q := by
  apply D.freeDualPercolates_of_hasInfiniteCluster_measure_eq_one
    hp hp1 hq
  exact D.freeDualHasInfiniteCluster_of_summable_shell_bound
    hp hp1 hq shell bound hbound hshell hplanar

lemma freeDualPercolates_of_exponentialDecay
    (D : PeriodicPlanarDualPair P Pdual)
    (H : PolynomialConnectionShells D) {p q pc : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hppc : p < pc) (hq : 1 ≤ q)
    (hdecay : SubcriticalTwoPointExponentialDecay P q pc) :
    D.FreeDualPercolates p q := by
  apply D.freeDualPercolates_of_hasInfiniteCluster_measure_eq_one
    hp hp1 hq
  exact D.freeDualHasInfiniteCluster_of_exponentialDecay
    H hp hp1 hppc hq hdecay

/-- Conditional dual subcritical coverage: polynomial connection shells and exponential decay of
primal two-point connections below `pc` give wired dual percolation at `p*` for every `p < pc`. -/
theorem dualSubcriticalCoverage_of_exponentialDecay
    (D : PeriodicPlanarDualPair P Pdual)
    (H : PolynomialConnectionShells D) {q pc : ℝ} (hq : 1 ≤ q)
    (hdecay : SubcriticalTwoPointExponentialDecay P q pc) :
    DualSubcriticalCoverage
      (fun r => Pdual.wiredPercolates r q) pc q := by
  apply (D.dualSubcriticalCoverage_iff_freeDual hq).mpr
  intro p hp hppc
  exact D.freeDualPercolates_of_exponentialDecay H
    hp.1 hp.2 hppc hq hdecay

/-- Conditional coverage in both directions: polynomial connection shells and subcritical
exponential decay for the primal and the dual graph give dual subcritical coverage both ways. -/
theorem bidirectionalSubcriticalCoverage_of_exponentialDecay
    (D : PeriodicPlanarDualPair P Pdual)
    (H : PolynomialConnectionShells D)
    (Hdual : PolynomialConnectionShells D.swap)
    {q pc pcDual : ℝ} (hq : 1 ≤ q)
    (hdecay : SubcriticalTwoPointExponentialDecay P q pc)
    (hdecayDual : SubcriticalTwoPointExponentialDecay Pdual q pcDual) :
    DualSubcriticalCoverage
        (fun r => Pdual.wiredPercolates r q) pc q ∧
      DualSubcriticalCoverage
        (fun r => P.wiredPercolates r q) pcDual q := by
  exact ⟨D.dualSubcriticalCoverage_of_exponentialDecay H hq hdecay,
    D.swap.dualSubcriticalCoverage_of_exponentialDecay
      Hdual hq hdecayDual⟩

end PeriodicPlanarDualPair

end StatMech.FK.PeriodicPlanar
