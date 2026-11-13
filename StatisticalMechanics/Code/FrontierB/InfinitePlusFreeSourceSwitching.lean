/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierB.PlusFreeSourceJointLimit
import Code.FrontierB.FinitePlusBoundarySwitchingBridge
import Code.FrontierB.CurrentSwitchingGateLimit
import Code.FrontierB.InfiniteCurrentPairCylinders

open Filter MeasureTheory Topology

namespace StatMech.FrontierB

open Sharpness Ising Lattice Percolation



theorem plusFreeSource_trace_event_real_tendsto
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y)
    (Q : Set (ConfigSpace (Sym2 (Site d)))) (hQ : IsClopen Q) :
    Tendsto
      (fun k =>
        let j := plusFreeSourceCurrentSubsequence
          d N beta hbeta x y hx hy hxy k
        ((growingPlusPairSourceCurrentMeasure
            d N beta hbeta x y hx hy hxy j).prod
          (growingFreePairSourceCurrentMeasure
            d N beta hbeta x y hx hy hxy j) : Measure _).real
              (superposedCurrentTrace ⁻¹' Q))
      atTop
      (nhds (((infinitePlusPairSourceCurrentMeasure
          d N beta hbeta x y hx hy hxy).prod
        (infiniteFreePairSourceCurrentMeasure
          d N beta hbeta x y hx hy hxy) : Measure _).real
            (superposedCurrentTrace ⁻¹' Q))) := by
  exact (growingPlusPairSourceCurrentMeasure_tendsto_jointLimit
    d N beta hbeta x y hx hy hxy).superposedTrace_real
      (growingFreePairSourceCurrentMeasure_tendsto_jointLimit
        d N beta hbeta x y hx hy hxy) Q hQ




theorem infinitePlusFreeSource_switching_of_uniqueInfiniteCluster
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y)
    (hunique :
      (independentSuperposedTraceLaw
        (infinitePlusCurrentMeasure d beta hbeta.le)
        (infiniteFreeCurrentMeasure d beta hbeta.le) : Measure _)
          (atLeastTwoInfinite d) = 0)
    (Q : Set (ConfigSpace (Sym2 (Site d)))) (hQ : IsClopen Q) :
    ((∫ omega, spinProd ({x, y} : Finset (Site d)) omega
        ∂(plusState d beta 0 : Measure (ConfigSpace (Site d)))) *
      (∫ omega, spinProd ({x, y} : Finset (Site d)) omega
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))))) *
      (((infinitePlusPairSourceCurrentMeasure
          d N beta hbeta x y hx hy hxy).prod
        (infiniteFreePairSourceCurrentMeasure
          d N beta hbeta x y hx hy hxy) : Measure _).real
            (superposedCurrentTrace ⁻¹' Q)) =
      (((infinitePlusCurrentMeasure d beta hbeta.le).prod
        (infiniteFreeCurrentMeasure d beta hbeta.le) : Measure _).real
          (currentPairTraceConnectionGate Q x y)) := by
  let phi := plusFreeSourceCurrentSubsequence
    d N beta hbeta x y hx hy hxy
  let r : ℕ → ℕ := fun k => (phi k + N) + 1
  let Lplus := ∫ omega, spinProd ({x, y} : Finset (Site d)) omega
    ∂(plusState d beta 0 : Measure (ConfigSpace (Site d)))
  let Lfree := ∫ omega, spinProd ({x, y} : Finset (Site d)) omega
    ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))
  have hphi : StrictMono phi :=
    plusFreeSourceCurrentSubsequence_strictMono
      d N beta hbeta x y hx hy hxy
  have hr : Tendsto r atTop atTop :=
    (((strictMono_id.add_const N).add_const 1).comp hphi).tendsto_atTop
  have hplusCoeff : Tendsto
      (fun k =>
        let j := phi k
        let n := j + N
        ∫ omega, spinProd ({x, y} : Finset (Site d)) omega
          ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d))))
      atTop (nhds Lplus) := by
    simpa only [phi, Lplus, Function.comp_apply] using
      (integral_plusMeasure_spinProd_full_tendsto
        d beta hbeta.le ({x, y} : Finset (Site d))).comp
          ((strictMono_id.add_const N).comp hphi).tendsto_atTop
  have hfreeCoeff : Tendsto
      (fun k =>
        let j := phi k
        let n := j + N
        expectationJ (StatMech.FK.boxGraph d (n + 1)) beta (fun _ => 1)
          {boxSiteSucc
              (pairSourceBoxSite x (box_mono d (Nat.le_add_left N j) hx)),
            boxSiteSucc
              (pairSourceBoxSite y (box_mono d (Nat.le_add_left N j) hy))})
      atTop (nhds Lfree) := by
    simpa only [phi, Lfree, Function.comp_apply] using
      (growingFreePairForPlusSwitching_expectation_tendsto
        d N beta hbeta x y hx hy).comp hphi.tendsto_atTop
  have hsource := plusFreeSource_trace_event_real_tendsto
    d N beta hbeta x y hx hy hxy Q hQ
  have hleft := (hplusCoeff.mul hfreeCoeff).mul hsource
  have hgateFull := currentSwitchingGate_tendsto_of_uniqueInfiniteCluster
    (plusBoxCurrentMeasure_tendsto_full d beta hbeta)
    (freeBoxCurrentMeasure_tendsto_full d beta hbeta) hunique hQ x y
  have hright := hgateFull.comp hr
  have hid : ∀ k,
      (let j := phi k
       let n := j + N
       let xn := pairSourceBoxSite x (box_mono d (Nat.le_add_left N j) hx)
       let yn := pairSourceBoxSite y (box_mono d (Nat.le_add_left N j) hy)
       ((∫ omega, spinProd ({x, y} : Finset (Site d)) omega
            ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d)))) *
          expectationJ (StatMech.FK.boxGraph d (n + 1)) beta (fun _ => 1)
            {boxSiteSucc xn, boxSiteSucc yn}) *
        (((growingPlusPairSourceCurrentMeasure
            d N beta hbeta x y hx hy hxy j).prod
          (growingFreePairSourceCurrentMeasure
            d N beta hbeta x y hx hy hxy j) : Measure _).real
              (superposedCurrentTrace ⁻¹' Q))) =
        ((plusBoxCurrentMeasure d (r k) beta hbeta.le).prod
          (freeBoxCurrentMeasure d (r k) beta hbeta.le) : Measure _).real
            (currentPairTraceBoxGate Q (r k) x y) := by
    intro k
    dsimp only
    simpa only [phi, r, growingPlusPairSourceCurrentMeasure,
      growingFreePairSourceCurrentMeasure, pairSourceBoxSite,
      Function.comp_apply] using
      plusPair_pairSource_plus_free_box_switching_normalized_real
        d (phi k + N) beta hbeta
        (pairSourceBoxSite x (box_mono d (Nat.le_add_left N (phi k)) hx))
        (pairSourceBoxSite y (box_mono d (Nat.le_add_left N (phi k)) hy))
        (pairSourceBoxSite_ne _ _ hxy) Q hQ
  exact tendsto_nhds_unique
    (hleft.congr' (Filter.Eventually.of_forall hid)) hright

end StatMech.FrontierB
