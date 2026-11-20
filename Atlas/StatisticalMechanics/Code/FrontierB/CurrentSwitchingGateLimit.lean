/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierB.CurrentConnectivityNoEscape
import Code.FrontierB.InfiniteCurrentMeasures

open Filter MeasureTheory Set Topology

namespace StatMech.FrontierB

open Lattice Percolation

variable {d : ℕ}




theorem currentSwitchingGate_tendsto_of_uniqueInfiniteCluster
    {mu nu : ℕ → ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    {muLim nuLim : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))}
    (hmu : WeakCurrentConverges mu muLim)
    (hnu : WeakCurrentConverges nu nuLim)
    (hunique : (independentSuperposedTraceLaw muLim nuLim : Measure _)
      (atLeastTwoInfinite d) = 0)
    {Q : Set (ConfigSpace (Sym2 (Site d)))} (hQ : IsClopen Q)
    (x y : Site d) :
    Tendsto
      (fun k => ((mu k).prod (nu k) : Measure _).real
        (currentPairTraceBoxGate Q k x y)) atTop
      (nhds ((muLim.prod nuLim : Measure _).real
        (currentPairTraceConnectionGate Q x y))) := by
  apply currentPairTraceBoxGate_diagonal_tendsto hmu hnu hQ x y
  exact currentPairConnectivityNoEscape_of_uniqueInfiniteCluster
    hmu hnu hunique Q x y



theorem freeFreeCurrentSwitchingGate_tendsto
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hunique :
      (independentSuperposedTraceLaw
        (infiniteFreeCurrentMeasure d beta hbeta)
        (infiniteFreeCurrentMeasure d beta hbeta) : Measure _)
        (atLeastTwoInfinite d) = 0)
    {Q : Set (ConfigSpace (Sym2 (Site d)))} (hQ : IsClopen Q)
    (x y : Site d) :
    Tendsto
      (fun k =>
        let n := infiniteCurrentBoxSubsequence d beta hbeta k
        ((freeBoxCurrentMeasure d n beta hbeta).prod
          (freeBoxCurrentMeasure d n beta hbeta) : Measure _).real
          (currentPairTraceBoxGate Q k x y)) atTop
      (nhds (((infiniteFreeCurrentMeasure d beta hbeta).prod
        (infiniteFreeCurrentMeasure d beta hbeta) : Measure _).real
          (currentPairTraceConnectionGate Q x y))) := by
  let mu : ℕ → ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d))) :=
    (fun n => freeBoxCurrentMeasure d n beta hbeta) ∘
      infiniteCurrentBoxSubsequence d beta hbeta
  have hmu : WeakCurrentConverges mu
      (infiniteFreeCurrentMeasure d beta hbeta) :=
    freeBoxCurrentMeasure_tendsto_infiniteFree d beta hbeta
  simpa only [mu, Function.comp_apply] using
    currentSwitchingGate_tendsto_of_uniqueInfiniteCluster
      hmu hmu hunique hQ x y



theorem freePlusCurrentSwitchingGate_tendsto
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hunique :
      (independentSuperposedTraceLaw
        (infiniteFreeCurrentMeasure d beta hbeta)
        (infinitePlusCurrentMeasure d beta hbeta) : Measure _)
        (atLeastTwoInfinite d) = 0)
    {Q : Set (ConfigSpace (Sym2 (Site d)))} (hQ : IsClopen Q)
    (x y : Site d) :
    Tendsto
      (fun k =>
        let n := infiniteCurrentBoxSubsequence d beta hbeta k
        ((freeBoxCurrentMeasure d n beta hbeta).prod
          (plusBoxCurrentMeasure d n beta hbeta) : Measure _).real
          (currentPairTraceBoxGate Q k x y)) atTop
      (nhds (((infiniteFreeCurrentMeasure d beta hbeta).prod
        (infinitePlusCurrentMeasure d beta hbeta) : Measure _).real
          (currentPairTraceConnectionGate Q x y))) := by
  let mu : ℕ → ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d))) :=
    (fun n => freeBoxCurrentMeasure d n beta hbeta) ∘
      infiniteCurrentBoxSubsequence d beta hbeta
  let nu : ℕ → ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d))) :=
    (fun n => plusBoxCurrentMeasure d n beta hbeta) ∘
      infiniteCurrentBoxSubsequence d beta hbeta
  have hmu : WeakCurrentConverges mu
      (infiniteFreeCurrentMeasure d beta hbeta) :=
    freeBoxCurrentMeasure_tendsto_infiniteFree d beta hbeta
  have hnu : WeakCurrentConverges nu
      (infinitePlusCurrentMeasure d beta hbeta) :=
    plusBoxCurrentMeasure_tendsto_infinitePlus d beta hbeta
  simpa only [mu, nu, Function.comp_apply] using
    currentSwitchingGate_tendsto_of_uniqueInfiniteCluster
      hmu hnu hunique hQ x y



theorem plusPlusCurrentSwitchingGate_tendsto
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hunique :
      (independentSuperposedTraceLaw
        (infinitePlusCurrentMeasure d beta hbeta)
        (infinitePlusCurrentMeasure d beta hbeta) : Measure _)
        (atLeastTwoInfinite d) = 0)
    {Q : Set (ConfigSpace (Sym2 (Site d)))} (hQ : IsClopen Q)
    (x y : Site d) :
    Tendsto
      (fun k =>
        let n := infiniteCurrentBoxSubsequence d beta hbeta k
        ((plusBoxCurrentMeasure d n beta hbeta).prod
          (plusBoxCurrentMeasure d n beta hbeta) : Measure _).real
          (currentPairTraceBoxGate Q k x y)) atTop
      (nhds (((infinitePlusCurrentMeasure d beta hbeta).prod
        (infinitePlusCurrentMeasure d beta hbeta) : Measure _).real
          (currentPairTraceConnectionGate Q x y))) := by
  let mu : ℕ → ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d))) :=
    (fun n => plusBoxCurrentMeasure d n beta hbeta) ∘
      infiniteCurrentBoxSubsequence d beta hbeta
  have hmu : WeakCurrentConverges mu
      (infinitePlusCurrentMeasure d beta hbeta) :=
    plusBoxCurrentMeasure_tendsto_infinitePlus d beta hbeta
  simpa only [mu, Function.comp_apply] using
    currentSwitchingGate_tendsto_of_uniqueInfiniteCluster
      hmu hmu hunique hQ x y

end StatMech.FrontierB
