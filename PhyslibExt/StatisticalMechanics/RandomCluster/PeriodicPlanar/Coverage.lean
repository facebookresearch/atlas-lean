/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.DualPair
public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.CriticalReduction
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Dual percolation from subcritical exponential decay

Below the primal critical point, exponential decay of primal two-point connections forces the
dual configuration of the free buffered infinite-volume measure to have an infinite cluster
almost surely, provided the absence of dual infinite clusters is witnessed by long primal
connections in polynomially many shells.

## i. Overview

Two-point connection events in buffered boxes are increasing, so for `q ≥ 1` their probability
under the free infinite-volume measure is at most the wired two-point probability. A shell is a
union of two-point events over pairs at graph distance at least `n`; with polynomially many pairs
and exponential decay of the two-point function the shell probabilities are summable, and the
Borel–Cantelli lemma gives that almost surely only finitely many shells occur. If planarity
guarantees that every configuration without a dual infinite cluster lies in infinitely many
shells, the dual infinite cluster has probability one.
The headline `PeriodicPlanarDualPair.freeDualHasInfiniteCluster_of_exponentialDecay` is
conditional: it takes `PolynomialConnectionShells D` (polynomial shell counts together with the
planar input `planar_limsup`) and `SubcriticalTwoPointExponentialDecay P q pc`, besides
`0 < p < pc`, `p < 1` and `1 ≤ q`.

## ii. Key results

- `PeriodicGraph.freeBufferedInfiniteVolume_le_wired_cylinder` : free-below-wired comparison of
  increasing cylinders in infinite volume.
- `PeriodicPlanarDualPair.PolynomialConnectionShells` : polynomially many long-connection shells
  witnessing the absence of a dual infinite cluster.
- `PeriodicPlanarDualPair.freeDualHasInfiniteCluster_of_exponentialDecay` : exponential decay
  below `pc` gives a dual infinite cluster almost surely.

## iii. Table of contents

- A. Two-point events and shells
- B. Measurability of percolation events
- C. Polynomial connection shells
- D. Borel–Cantelli and dual percolation

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Sections 5.2 and 6.2.
-/

@[expose] public section

open Filter MeasureTheory Set SimpleGraph Topology

set_option linter.unusedSectionVars false

namespace StatMech.FK.PeriodicPlanar

open BeffaraDC StatMech.Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

/-! ## A. Two-point events and shells -/

/-- The event that `x` and `y` are joined by an open path in the buffered box of radius `N`. -/
def PeriodicGraph.bufferedTwoPointEvent (P : PeriodicGraph V) (N : ℕ)
    (x y : P.BufferedVertex N) :
    Set (ConfigSpace (Sym2 (P.BufferedVertex N))) :=
  {omega | (FK.openSub (P.bufferedGraph N) omega).Reachable x y}

lemma PeriodicGraph.bufferedTwoPointEvent_isIncreasing
    (P : PeriodicGraph V) (N : ℕ) (x y : P.BufferedVertex N) :
    IsIncreasing (P.bufferedTwoPointEvent N x y) := by
  intro omega eta home hreach
  exact hreach.mono fun u v huv => by
    rw [FK.openSub_adj] at huv ⊢
    refine ⟨huv.1, Bool.eq_true_of_true_le ?_⟩
    simpa [huv.2] using home s(u, v)

/-- The shell of a finite set of pairs: some pair is joined by an open path inside the buffered box.
-/
def PeriodicGraph.bufferedPairShell (P : PeriodicGraph V) (N : ℕ)
    (pairs : Finset (P.BufferedVertex N × P.BufferedVertex N)) :
    Set (ConfigSpace (Sym2 V)) :=
  ⋃ xy ∈ pairs, P.bufferedCylinder N
    (P.bufferedTwoPointEvent N xy.1 xy.2)

lemma PeriodicGraph.bufferedTwoPointCylinder_subset_twoPointEvent
    (P : PeriodicGraph V) (N : ℕ) (x y : P.BufferedVertex N) :
    P.bufferedCylinder N (P.bufferedTwoPointEvent N x y) ⊆
      P.twoPointEvent x.1 y.1 := by
  intro omega homega
  exact P.bufferedReachable_full N omega homega

/-- For `q ≥ 1`, an increasing cylinder event is no more likely under the free buffered
infinite-volume measure than under the wired one. -/
lemma PeriodicGraph.freeBufferedInfiniteVolume_le_wired_cylinder
    (P : PeriodicGraph V) (N : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
    (hS : IsIncreasing S) :
    (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) ≤
      (P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) := by
  have hfree := P.freeBufferedMeasure_tendsto_cylinder N hp hp1 hq hS
  have hwired := P.wiredBufferedMeasure_tendsto_cylinder N hp hp1 hq hS
  have heventually : ∀ᶠ m in atTop,
      (P.freeBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) :
          Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) ≤
        (P.wiredBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) :
          Measure (ConfigSpace (Sym2 V))).real (P.bufferedCylinder N S) := by
    filter_upwards [eventually_ge_atTop N] with m hm
    rw [P.freeBufferedMeasure_real_cylinder hm hp hp1 (zero_lt_one.trans_le hq),
      P.wiredBufferedMeasure_real_cylinder hm hp hp1 (zero_lt_one.trans_le hq)]
    have hpre : IsIncreasing (P.bufferedRestrictLE hm ⁻¹' S) :=
      fun omega eta home hmem =>
        hS (P.monotone_bufferedRestrictLE hm home) hmem
    exact fkProb_le_wiredFkProb_increasing
      (G := P.bufferedGraph m) (bdry := P.bufferedBoundary m)
      hp hp1 hq hpre
  exact le_of_tendsto_of_tendsto hfree hwired heventually

lemma PeriodicGraph.freeBufferedTwoPointCylinder_le_wiredTwoPoint
    (P : PeriodicGraph V) (N : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (x y : P.BufferedVertex N) :
    (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V)))
        (P.bufferedCylinder N (P.bufferedTwoPointEvent N x y)) ≤
      ENNReal.ofReal (P.wiredTwoPointProbability p q x.1 y.1) := by
  let muf : Measure (ConfigSpace (Sym2 V)) :=
    P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
  let muw : Measure (ConfigSpace (Sym2 V)) :=
    P.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
  have hreal : muf.real
        (P.bufferedCylinder N (P.bufferedTwoPointEvent N x y)) ≤
      muw.real (P.twoPointEvent x.1 y.1) :=
    (P.freeBufferedInfiniteVolume_le_wired_cylinder N hp hp1 hq
      (P.bufferedTwoPointEvent_isIncreasing N x y)).trans
      (measureReal_mono
        (P.bufferedTwoPointCylinder_subset_twoPointEvent N x y))
  have hrange : p ∈ Ioo (0 : ℝ) 1 ∧ 0 < q :=
    ⟨⟨hp, hp1⟩, zero_lt_one.trans_le hq⟩
  rw [PeriodicGraph.wiredTwoPointProbability, dite_eq_left hrange]
  rw [← ENNReal.ofReal_toReal (measure_ne_top muf _)]
  exact ENNReal.ofReal_le_ofReal hreal

/-! ## B. Measurability of percolation events -/

lemma PeriodicGraph.measurableSet_cluster_infinite
    (P : PeriodicGraph V) (x : V) :
    MeasurableSet {omega : ConfigSpace (Sym2 V) |
      (P.cluster omega x).Infinite} := by
  have heq : {omega : ConfigSpace (Sym2 V) |
        (P.cluster omega x).Infinite} =
      ⋂ n : ℕ, ⋃ y : {y : V // y ∉ P.orbitBox n},
        P.twoPointEvent x y.1 := by
    ext omega
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion,
      PeriodicGraph.twoPointEvent, PeriodicGraph.cluster]
    constructor
    · intro hinf n
      by_contra hnone
      push Not at hnone
      have hsub : P.cluster omega x ⊆ (P.orbitBox n : Set V) := by
        intro y hy
        by_contra hyout
        exact hnone ⟨y, hyout⟩ hy
      exact hinf ((P.orbitBox n).finite_toSet.subset hsub)
    · intro hout hfinite
      obtain ⟨n, hn⟩ := P.finite_subset_orbitBox hfinite.toFinset
      obtain ⟨y, hy⟩ := hout n
      exact y.2 (hn y.1 (by simpa using hy))
  rw [heq]
  exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun y =>
    P.measurableSet_twoPointEvent x y.1

lemma PeriodicGraph.measurableSet_hasInfiniteCluster
    (P : PeriodicGraph V) :
    MeasurableSet {omega : ConfigSpace (Sym2 V) |
      P.HasInfiniteCluster omega} := by
  have heq : {omega : ConfigSpace (Sym2 V) |
      P.HasInfiniteCluster omega} =
      ⋃ x : V, {omega : ConfigSpace (Sym2 V) |
        (P.cluster omega x).Infinite} := by
    ext omega
    simp [PeriodicGraph.HasInfiniteCluster]
  rw [heq]
  exact MeasurableSet.iUnion fun x => P.measurableSet_cluster_infinite x

/-! ## C. Polynomial connection shells -/

namespace PeriodicPlanarDualPair

/-- Polynomial connection shells: for each `n`, at most `multiplicity · (n + 1) ^ degree` pairs at
graph distance at least `n`, such that every configuration whose dual has no infinite cluster lies
in infinitely many shells. -/
structure PolynomialConnectionShells
    (D : PeriodicPlanarDualPair P Pdual) where
  level : ℕ → ℕ
  pairs : ∀ n, Finset
    (P.BufferedVertex (level n) × P.BufferedVertex (level n))
  degree : ℕ
  multiplicity : ℕ
  card_le : ∀ n, (pairs n).card ≤ multiplicity * (n + 1) ^ degree
  dist_ge : ∀ n xy, xy ∈ pairs n → n ≤ P.graph.dist xy.1.1 xy.2.1
  planar_limsup :
    ((dualConfigEquiv D.edgeDual) ⁻¹'
      {eta | Pdual.HasInfiniteCluster eta})ᶜ ⊆
      limsup (fun n => P.bufferedPairShell (level n) (pairs n)) atTop

end PeriodicPlanarDualPair

/-! ## D. Borel–Cantelli and dual percolation -/

lemma PeriodicGraph.freeBufferedPairShell_le_wiredTwoPointSum
    (P : PeriodicGraph V) (N : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (pairs : Finset (P.BufferedVertex N × P.BufferedVertex N)) :
    (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 V))) (P.bufferedPairShell N pairs) ≤
      ∑ xy ∈ pairs,
        ENNReal.ofReal (P.wiredTwoPointProbability p q xy.1.1 xy.2.1) := by
  calc
    _ ≤ ∑ xy ∈ pairs,
        (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
          Measure (ConfigSpace (Sym2 V)))
          (P.bufferedCylinder N
            (P.bufferedTwoPointEvent N xy.1 xy.2)) := by
      exact measure_biUnion_finset_le pairs fun xy =>
        P.bufferedCylinder N (P.bufferedTwoPointEvent N xy.1 xy.2)
    _ ≤ _ := by
      exact Finset.sum_le_sum fun xy _ =>
        P.freeBufferedTwoPointCylinder_le_wiredTwoPoint
          N hp hp1 hq xy.1 xy.2

namespace PeriodicPlanarDualPair

/-- A polynomial times a decaying exponential is summable over `ℕ`. -/
private lemma summable_polynomial_exp_shell_bound
    (k K : ℕ) {c C : ℝ} (hc : 0 < c) (hC : 0 < C) :
    Summable (fun n : ℕ => NNReal.mk
      ((K : ℝ) * C * ((n + 1 : ℕ) : ℝ) ^ k *
        Real.exp (-c * (n : ℝ)))
      (mul_nonneg
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (le_of_lt hC))
          (pow_nonneg (Nat.cast_nonneg _) _))
        (Real.exp_pos _).le)) := by
  let f : ℕ → ℝ := fun n =>
    (n : ℝ) ^ k * Real.exp (-c * (n : ℝ))
  have hf : Summable f := Real.summable_pow_mul_exp_neg_nat_mul k hc
  have hshift : Summable (fun n => f (n + 1)) :=
    hf.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hscaled := hshift.mul_left ((K : ℝ) * C * Real.exp c)
  have hreal : Summable (fun n : ℕ =>
      (K : ℝ) * C * ((n + 1 : ℕ) : ℝ) ^ k *
        Real.exp (-c * (n : ℝ))) := by
    apply hscaled.congr
    intro n
    dsimp [f]
    rw [show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by norm_num,
      show -c * ((n : ℝ) + 1) = -c * (n : ℝ) - c by ring,
      Real.exp_sub, div_eq_mul_inv, ← Real.exp_neg]
    calc
      ((K : ℝ) * C * Real.exp c) *
          (((n : ℝ) + 1) ^ k *
            (Real.exp (-c * (n : ℝ)) * Real.exp (-c))) =
        (K : ℝ) * C * ((n : ℝ) + 1) ^ k *
          Real.exp (-c * (n : ℝ)) *
            (Real.exp c * Real.exp (-c)) := by ring
      _ = _ := by rw [← Real.exp_add]; simp
  apply NNReal.summable_coe.mp
  simpa only [NNReal.coe_mk] using hreal

lemma freeDualHasInfiniteCluster_of_shell_borelCantelli
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
    (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
      Measure (ConfigSpace (Sym2 V)))
        ((dualConfigEquiv D.edgeDual) ⁻¹'
          {eta | Pdual.HasInfiniteCluster eta}) = 1 := by
  let mu : Measure (ConfigSpace (Sym2 V)) :=
    P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
  let A : Set (ConfigSpace (Sym2 V)) :=
    (dualConfigEquiv D.edgeDual) ⁻¹'
      {eta | Pdual.HasInfiniteCluster eta}
  have hAmeas : MeasurableSet A :=
    Pdual.measurableSet_hasInfiniteCluster.preimage
      (continuous_dualConfigEquiv D.edgeDual).measurable
  have hlimzero : mu (limsup shell atTop) = 0 := by
    apply measure_limsup_atTop_eq_zero
    simpa only [mu] using hsum
  have hcompl : mu Aᶜ = 0 :=
    measure_mono_null hplanar hlimzero
  change mu A = 1
  exact (prob_compl_eq_zero_iff hAmeas).mp hcompl

lemma freeDualHasInfiniteCluster_of_summable_shell_bound
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
    (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
      Measure (ConfigSpace (Sym2 V)))
        ((dualConfigEquiv D.edgeDual) ⁻¹'
          {eta | Pdual.HasInfiniteCluster eta}) = 1 := by
  apply D.freeDualHasInfiniteCluster_of_shell_borelCantelli
    hp hp1 hq shell
  · apply ne_top_of_le_ne_top
      (ENNReal.tsum_coe_ne_top_iff_summable.mpr hbound)
    exact ENNReal.tsum_le_tsum hshell
  · exact hplanar

/-- Conditional dual percolation below `pc`: given polynomial connection shells and exponential
decay of two-point connections below `pc`, the dual of the free buffered infinite-volume
configuration has an infinite cluster almost surely. -/
theorem freeDualHasInfiniteCluster_of_exponentialDecay
    (D : PeriodicPlanarDualPair P Pdual)
    (H : PolynomialConnectionShells D) {p q pc : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hppc : p < pc) (hq : 1 ≤ q)
    (hdecay : SubcriticalTwoPointExponentialDecay P q pc) :
    (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) :
      Measure (ConfigSpace (Sym2 V)))
        ((dualConfigEquiv D.edgeDual) ⁻¹'
          {eta | Pdual.HasInfiniteCluster eta}) = 1 := by
  obtain ⟨c, C, hc, hC, htwo⟩ := hdecay p ⟨hp, hppc⟩
  let bound : ℕ → NNReal := fun n => NNReal.mk
    ((H.multiplicity : ℝ) * C *
      ((n + 1 : ℕ) : ℝ) ^ H.degree * Real.exp (-c * (n : ℝ)))
    (mul_nonneg
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (le_of_lt hC))
        (pow_nonneg (Nat.cast_nonneg _) _))
      (Real.exp_pos _).le)
  have hbound : Summable bound := by
    exact summable_polynomial_exp_shell_bound
      H.degree H.multiplicity hc hC
  apply D.freeDualHasInfiniteCluster_of_summable_shell_bound hp hp1 hq
    (fun n => P.bufferedPairShell (H.level n) (H.pairs n)) bound hbound
  · intro n
    calc
      _ ≤ ∑ xy ∈ H.pairs n,
          ENNReal.ofReal
            (P.wiredTwoPointProbability p q xy.1.1 xy.2.1) :=
        P.freeBufferedPairShell_le_wiredTwoPointSum
          (H.level n) hp hp1 hq (H.pairs n)
      _ ≤ ∑ _xy ∈ H.pairs n,
          ENNReal.ofReal (C * Real.exp (-c * (n : ℝ))) := by
        exact Finset.sum_le_sum fun xy hxy =>
          ENNReal.ofReal_le_ofReal <| (htwo xy.1.1 xy.2.1).trans <| by
            apply mul_le_mul_of_nonneg_left _ (le_of_lt hC)
            apply Real.exp_le_exp.mpr
            have hdist : (n : ℝ) ≤
                (P.graph.dist xy.1.1 xy.2.1 : ℝ) := by
              exact_mod_cast H.dist_ge n xy hxy
            nlinarith
      _ ≤ (bound n : ENNReal) := by
        rw [← ENNReal.ofReal_sum_of_nonneg]
        · dsimp [bound]
          rw [← ENNReal.ofReal_eq_coe_nnreal]
          apply ENNReal.ofReal_le_ofReal
          rw [Finset.sum_const, nsmul_eq_mul]
          have hcard : ((H.pairs n).card : ℝ) ≤
              (H.multiplicity : ℝ) *
                ((n + 1 : ℕ) : ℝ) ^ H.degree := by
            exact_mod_cast H.card_le n
          calc
            ((H.pairs n).card : ℝ) *
                (C * Real.exp (-c * (n : ℝ))) ≤
              ((H.multiplicity : ℝ) *
                  ((n + 1 : ℕ) : ℝ) ^ H.degree) *
                (C * Real.exp (-c * (n : ℝ))) :=
              mul_le_mul_of_nonneg_right hcard
                (mul_nonneg (le_of_lt hC) (Real.exp_pos _).le)
            _ = _ := by ring
        · intro xy hxy
          exact mul_nonneg (le_of_lt hC) (Real.exp_pos _).le
  · exact H.planar_limsup

end PeriodicPlanarDualPair

end StatMech.FK.PeriodicPlanar
