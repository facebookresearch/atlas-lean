/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.FrontierB.PairSourceCurrentLimit
import Code.FrontierB.FiniteBoxSwitchingBridge
import Code.FrontierB.CurrentSwitchingGateLimit
import Code.FrontierB.InfiniteCurrentPairCylinders

open Filter MeasureTheory Topology

namespace StatMech.FrontierB

open Sharpness Ising Lattice Percolation



theorem pairSource_trace_event_real_tendsto
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y)
    (Q : Set (ConfigSpace (Sym2 (Site d)))) (hQ : IsClopen Q) :
    Tendsto
      (fun k =>
        let j := pairSourceCurrentBoxSubsequence
          d N beta hbeta x y hx hy hxy k
        ((growingPairSourceCurrentMeasure d N beta hbeta x y hx hy hxy j).prod
          (growingPairSourceCurrentMeasure d N beta hbeta x y hx hy hxy j) :
            Measure _).real (superposedCurrentTrace ⁻¹' Q))
      atTop
      (nhds (((infinitePairSourceCurrentMeasure
        d N beta hbeta x y hx hy hxy).prod
          (infinitePairSourceCurrentMeasure d N beta hbeta x y hx hy hxy) :
            Measure _).real (superposedCurrentTrace ⁻¹' Q))) := by
  let mu : ℕ → ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d))) :=
    (growingPairSourceCurrentMeasure d N beta hbeta x y hx hy hxy) ∘
      pairSourceCurrentBoxSubsequence d N beta hbeta x y hx hy hxy
  let nu := infinitePairSourceCurrentMeasure d N beta hbeta x y hx hy hxy
  have hmu : WeakCurrentConverges mu nu :=
    growingPairSourceCurrentMeasure_tendsto_infinite
      d N beta hbeta x y hx hy hxy
  have htrace := independentSuperposedTraceLaw_tendsto hmu hmu
  have hport := (show WeakConvergesTo
      (fun k => independentSuperposedTraceLaw (mu k) (mu k))
      (independentSuperposedTraceLaw nu nu) from htrace).tendsto_real_of_isClopen hQ
  have hmap (rho : ProbabilityMeasure
      (InfiniteCurrentConfig (Sym2 (Site d)))) :
      (independentSuperposedTraceLaw rho rho : Measure _).real Q =
        (rho.prod rho : Measure _).real (superposedCurrentTrace ⁻¹' Q) := by
    have hcoe (sigma : ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
        (A : Set (ConfigSpace (Sym2 (Site d)))) :
        ((sigma A : NNReal) : ℝ) = (sigma : Measure _).real A := by
      rw [Measure.real, ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
      exact (ENNReal.coe_toReal _).symm
    have hcoePair (sigma : ProbabilityMeasure
        (InfiniteCurrentConfig (Sym2 (Site d)) ×
          InfiniteCurrentConfig (Sym2 (Site d))))
        (A : Set (InfiniteCurrentConfig (Sym2 (Site d)) ×
          InfiniteCurrentConfig (Sym2 (Site d)))) :
        ((sigma A : NNReal) : ℝ) = (sigma : Measure _).real A := by
      rw [Measure.real, ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
      exact (ENNReal.coe_toReal _).symm
    rw [← hcoe, ← hcoePair]
    exact congrArg (fun z : NNReal => (z : ℝ))
      (ProbabilityMeasure.map_apply (rho.prod rho)
        continuous_superposedCurrentTrace.measurable.aemeasurable
        hQ.isOpen.measurableSet)
  simpa only [hmap, mu, nu, Function.comp_apply] using hport




theorem infinitePairSource_free_switching_of_uniqueInfiniteCluster
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y)
    (hunique :
      (independentSuperposedTraceLaw
        (infiniteFreeCurrentMeasure d beta hbeta.le)
        (infiniteFreeCurrentMeasure d beta hbeta.le) : Measure _)
          (atLeastTwoInfinite d) = 0)
    (Q : Set (ConfigSpace (Sym2 (Site d)))) (hQ : IsClopen Q) :
    (∫ omega, spinProd ({x, y} : Finset (Site d)) omega
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))) ^ 2 *
      (((infinitePairSourceCurrentMeasure d N beta hbeta x y hx hy hxy).prod
        (infinitePairSourceCurrentMeasure d N beta hbeta x y hx hy hxy) :
          Measure _).real (superposedCurrentTrace ⁻¹' Q)) =
      (((infiniteFreeCurrentMeasure d beta hbeta.le).prod
        (infiniteFreeCurrentMeasure d beta hbeta.le) : Measure _).real
          (currentPairTraceConnectionGate Q x y)) := by
  let phi := pairSourceCurrentBoxSubsequence d N beta hbeta x y hx hy hxy
  let r : ℕ → ℕ := fun k => phi k + N
  let L := ∫ omega, spinProd ({x, y} : Finset (Site d)) omega
    ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))
  have hphi : StrictMono phi :=
    pairSourceCurrentBoxSubsequence_strictMono d N beta hbeta x y hx hy hxy
  have hr : Tendsto r atTop atTop :=
    ((strictMono_id.add_const N).comp hphi).tendsto_atTop
  have hcoeff : Tendsto
      (fun k => expectationJ (StatMech.FK.boxGraph d (r k)) beta (fun _ => 1)
        {pairSourceBoxSite x (box_mono d (Nat.le_add_left N (phi k)) hx),
          pairSourceBoxSite y (box_mono d (Nat.le_add_left N (phi k)) hy)})
      atTop (nhds L) := by
    simpa only [r, phi, L, Function.comp_apply] using
      (growingPairSource_expectation_tendsto d N beta hbeta x y hx hy).comp
        hphi.tendsto_atTop
  have hsource := pairSource_trace_event_real_tendsto
    d N beta hbeta x y hx hy hxy Q hQ
  have hleft := hcoeff.pow 2 |>.mul hsource
  have hfree := freeBoxCurrentMeasure_tendsto_full d beta hbeta
  have hgateFull := currentSwitchingGate_tendsto_of_uniqueInfiniteCluster
    hfree hfree hunique hQ x y
  have hright := hgateFull.comp hr
  have hid : ∀ k,
      expectationJ (StatMech.FK.boxGraph d (r k)) beta (fun _ => 1)
          {pairSourceBoxSite x (box_mono d (Nat.le_add_left N (phi k)) hx),
            pairSourceBoxSite y (box_mono d (Nat.le_add_left N (phi k)) hy)} ^ 2 *
        ((growingPairSourceCurrentMeasure d N beta hbeta x y hx hy hxy (phi k)).prod
          (growingPairSourceCurrentMeasure d N beta hbeta x y hx hy hxy (phi k)) :
            Measure _).real (superposedCurrentTrace ⁻¹' Q) =
        ((freeBoxCurrentMeasure d (r k) beta hbeta.le).prod
          (freeBoxCurrentMeasure d (r k) beta hbeta.le) : Measure _).real
            (currentPairTraceBoxGate Q (r k) x y) := by
    intro k
    simpa only [r, phi, growingPairSourceCurrentMeasure] using
      pairSource_free_box_switching_normalized_real d (r k) beta hbeta
        (pairSourceBoxSite x (box_mono d (Nat.le_add_left N (phi k)) hx))
        (pairSourceBoxSite y (box_mono d (Nat.le_add_left N (phi k)) hy))
        (pairSourceBoxSite_ne _ _ hxy) Q hQ
  exact tendsto_nhds_unique
    (hleft.congr' (Filter.Eventually.of_forall hid)) hright

end StatMech.FrontierB
