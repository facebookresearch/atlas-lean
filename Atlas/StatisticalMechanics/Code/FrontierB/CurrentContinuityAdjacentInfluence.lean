/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierB.CurrentContinuityBoxInfluence
import Code.FrontierB.CurrentChainClosure
import Code.FrontierB.InfiniteCurrentPairCylinders

open Filter MeasureTheory Set Topology

namespace StatMech.FrontierB

open ConfigSpace Ising Lattice Percolation Sharpness
open StatMech.OSSS.FKSharpnessWeightedPhaseTransport




theorem beta_mul_adjacent_gap_le_fixed_boundary_union
    (d m : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (x y : Site d) (hxy : (hypercubicLattice d).Adj x y)
    (hm : 1 ≤ m) (hx : x ∈ box d (m - 1)) (hy : y ∈ box d (m - 1)) :
    beta * (currentContinuityPlusTwoPoint d beta x y -
        currentContinuityFreeTwoPoint d beta x y) ≤
      (((infinitePlusCurrentMeasure d beta hbeta.le).prod
        (infiniteFreeCurrentMeasure d beta hbeta.le) : Measure _).real
          (superposedCurrentTrace ⁻¹'
            (traceBoundaryConnectionEvent m x ∪
              traceBoundaryConnectionEvent m y))) := by
  let N := m - 1
  let r : ℕ → ℕ := fun k => (k + N) + 1
  let a : ℕ → ℝ := fun k =>
    boundarySourceCurrentSum (StatMech.FK.boxGraph d (r k)) beta
          (fun _ => 1) (boxCurrentInterior d (r k))
          {boxSiteSucc
              (pairSourceBoxSite x (box_mono d (Nat.le_add_left N k) hx)),
            boxSiteSucc
              (pairSourceBoxSite y (box_mono d (Nat.le_add_left N k) hy))} /
      boundaryCurrentSum (StatMech.FK.boxGraph d (r k)) beta
        (fun _ => 1) (boxCurrentInterior d (r k))
  let b : ℕ → ℝ := fun k =>
    expectationJ (StatMech.FK.boxGraph d (r k)) beta (fun _ => 1)
      {boxSiteSucc
          (pairSourceBoxSite x (box_mono d (Nat.le_add_left N k) hx)),
        boxSiteSucc
          (pairSourceBoxSite y (box_mono d (Nat.le_add_left N k) hy))}
  let q : ℕ → ℝ := fun k =>
    (((plusBoxCurrentMeasure d (r k) beta hbeta.le).prod
      (freeBoxCurrentMeasure d (r k) beta hbeta.le) : Measure _).real
        (superposedCurrentTrace ⁻¹'
          (traceBoundaryConnectionEvent m x ∪
            traceBoundaryConnectionEvent m y)))
  have hineq : ∀ k, beta * (a k - b k) ≤ q k := by
    intro k
    let n := k + N
    let xk := pairSourceBoxSite x (box_mono d (Nat.le_add_left N k) hx)
    let yk := pairSourceBoxSite y (box_mono d (Nat.le_add_left N k) hy)
    have hxR : x ∈ box d (r k) := box_mono d (by simp [r, n]; omega) hx
    have hyR : y ∈ box d (r k) := box_mono d (by simp [r, n]; omega) hy
    have hxint : (⟨x, hxR⟩ : StatMech.FK.boxVerts d (r k)) ∈
        boxCurrentInterior d (r k) := by
      simpa only [r, n, xk, pairSourceBoxSite, boxSiteSucc] using
        (boxSiteSucc_interior xk)
    have hyint : (⟨y, hyR⟩ : StatMech.FK.boxVerts d (r k)) ∈
        boxCurrentInterior d (r k) := by
      simpa only [r, n, yk, pairSourceBoxSite, boxSiteSucc] using
        (boxSiteSucc_interior yk)
    have hfin := beta_mul_box_pair_gap_le_boundaryConnection_union
      d (r k) beta hbeta x y hxR hyR hxy hxint hyint
    have hsub :
        traceBoundaryConnectionEvent (r k) x ∪
            traceBoundaryConnectionEvent (r k) y ⊆
          traceBoundaryConnectionEvent m x ∪
            traceBoundaryConnectionEvent m y := by
      intro omega homega
      rcases homega with homega | homega
      · left
        exact traceBoundaryConnectionEvent_subset_le hm hx (by simp [r, N]; omega) homega
      · right
        exact traceBoundaryConnectionEvent_subset_le hm hy (by simp [r, N]; omega) homega
    have hprob :
        ((plusBoxCurrentMeasure d (r k) beta hbeta.le).prod
          (freeBoxCurrentMeasure d (r k) beta hbeta.le) : Measure _).real
            (superposedCurrentTrace ⁻¹'
              (traceBoundaryConnectionEvent (r k) x ∪
                traceBoundaryConnectionEvent (r k) y)) ≤ q k := by
      apply MeasureTheory.measureReal_mono
      · exact Set.preimage_mono hsub
      · exact measure_ne_top _ _
    have hfb := hfin.trans hprob
    simpa only [a, b, boundaryCurrentSum_eq_boundarySourceCurrentSum,
      current_representation] using hfb
  have ha : Tendsto a atTop
      (nhds (currentContinuityPlusTwoPoint d beta x y)) := by
    simpa only [a, r, N, currentContinuityPlusTwoPoint,
      boundaryCurrentSum_eq_boundarySourceCurrentSum] using
      growingPlusPairBoundarySourceRatio_tendsto
        d N beta hbeta.le x y hx hy
  have hb : Tendsto b atTop
      (nhds (currentContinuityFreeTwoPoint d beta x y)) := by
    simpa only [b, r, N, currentContinuityFreeTwoPoint] using
      growingFreePairForPlusSwitching_expectation_tendsto
        d N beta hbeta x y hx hy
  have hshift : Tendsto r atTop atTop := by
    exact ((strictMono_id.add_const N).add_const 1).tendsto_atTop
  have hplus : WeakCurrentConverges
      (fun k => plusBoxCurrentMeasure d (r k) beta hbeta.le)
      (infinitePlusCurrentMeasure d beta hbeta.le) := by
    exact (plusBoxCurrentMeasure_tendsto_full d beta hbeta).comp hshift
  have hfree : WeakCurrentConverges
      (fun k => freeBoxCurrentMeasure d (r k) beta hbeta.le)
      (infiniteFreeCurrentMeasure d beta hbeta.le) := by
    exact (freeBoxCurrentMeasure_tendsto_full d beta hbeta).comp hshift
  have hQ : IsClopen (traceBoundaryConnectionEvent m x ∪
      traceBoundaryConnectionEvent m y) :=
    (isClopen_traceBoundaryConnectionEvent m x).union
      (isClopen_traceBoundaryConnectionEvent m y)
  have hq : Tendsto q atTop
      (nhds (((infinitePlusCurrentMeasure d beta hbeta.le).prod
        (infiniteFreeCurrentMeasure d beta hbeta.le) : Measure _).real
          (superposedCurrentTrace ⁻¹'
            (traceBoundaryConnectionEvent m x ∪
              traceBoundaryConnectionEvent m y)))) := by
    simpa only [q] using hplus.superposedTrace_real hfree _ hQ
  exact le_of_tendsto_of_tendsto ((ha.sub hb).const_mul beta) hq
    (Filter.Eventually.of_forall hineq)



theorem currentContinuityMixedTraceLaw_clusterInfinite_real_eq_percolation
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x : Site d) :
    (currentContinuityMixedTraceLaw d beta hbeta : Measure _).real
        (StatMech.FK.clusterInfiniteEvent d x) =
      (currentContinuityMixedTraceLaw d beta hbeta : Measure _).real
        (percolationEvent d) := by
  let mu := (currentContinuityMixedTraceLaw d beta hbeta :
    Measure (ConfigSpace (Sym2 (Site d))))
  let g : Multiplicative (Site d) := Multiplicative.ofAdd x
  have hgo : g • Percolation.origin d = x := by
    change (fun i => x i + 0) = x
    funext i
    simp
  have hpre : (shift g : ConfigSpace (Sym2 (Site d)) → _) ⁻¹'
        StatMech.FK.clusterInfiniteEvent d x =
        StatMech.FK.clusterInfiniteEvent d (Percolation.origin d) := by
    rw [← hgo]
    exact shift_preimage_clusterInfiniteEvent g (Percolation.origin d)
  have hmp := currentContinuityMixedTraceLaw_isTranslationInvariant
    d beta hbeta g
  have heq := hmp.measure_preimage
    (StatMech.FK.measurableSet_clusterInfiniteEvent x).nullMeasurableSet
  rw [hpre] at heq
  have hreal := congrArg ENNReal.toReal heq
  simpa only [mu, Measure.real, percolationEvent] using hreal.symm



theorem beta_mul_currentContinuity_adjacent_gap_le_percolation
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (x y : Site d) (hxy : (hypercubicLattice d).Adj x y) :
    beta * (currentContinuityPlusTwoPoint d beta x y -
        currentContinuityFreeTwoPoint d beta x y) ≤
      2 * (currentContinuityMixedTraceLaw d beta hbeta : Measure _).real
        (percolationEvent d) := by
  let rho := currentContinuityMixedTraceLaw d beta hbeta
  obtain ⟨N, hN⟩ := Lattice.finite_subset_box
    ({x, y} : Set (Site d)) (Set.toFinite _)
  have hxN : x ∈ box d N := hN (by simp)
  have hyN : y ∈ box d N := hN (by simp)
  let f : ℕ → ℝ := fun m =>
    (rho : Measure _).real (crossingEventFrom d x m) +
      (rho : Measure _).real (crossingEventFrom d y m)
  have hlim : Tendsto f atTop
      (nhds ((rho : Measure _).real
          (StatMech.FK.clusterInfiniteEvent d x) +
        (rho : Measure _).real
          (StatMech.FK.clusterInfiniteEvent d y))) :=
    (crossingEventFrom_real_tendsto_clusterInfinite d rho x).add
      (crossingEventFrom_real_tendsto_clusterInfinite d rho y)
  have hevent : ∀ᶠ m in atTop,
      beta * (currentContinuityPlusTwoPoint d beta x y -
        currentContinuityFreeTwoPoint d beta x y) ≤ f m := by
    filter_upwards [eventually_ge_atTop (N + 1)] with m hmN
    have hm : 1 ≤ m := by omega
    have hNm : N ≤ m - 1 := by omega
    have hxm : x ∈ box d (m - 1) := box_mono d hNm hxN
    have hym : y ∈ box d (m - 1) := box_mono d hNm hyN
    have hfixed := beta_mul_adjacent_gap_le_fixed_boundary_union
      d m beta hbeta x y hxy hm hxm hym
    let Q := traceBoundaryConnectionEvent m x ∪
      traceBoundaryConnectionEvent m y
    have hQ : MeasurableSet Q :=
      ((isClopen_traceBoundaryConnectionEvent m x).union
        (isClopen_traceBoundaryConnectionEvent m y)).isOpen.measurableSet
    have hmap := independentSuperposedTraceLaw_real_apply
      (infinitePlusCurrentMeasure d beta hbeta.le)
      (infiniteFreeCurrentMeasure d beta hbeta.le) hQ
    change (rho : Measure _).real Q = _ at hmap
    rw [← hmap] at hfixed
    apply hfixed.trans
    calc
      (rho : Measure _).real Q ≤
          (rho : Measure _).real (traceBoundaryConnectionEvent m x) +
            (rho : Measure _).real (traceBoundaryConnectionEvent m y) :=
        measureReal_union_le _ _
      _ ≤ f m := add_le_add
        (MeasureTheory.measureReal_mono
          traceBoundaryConnectionEvent_subset_crossingEventFrom
          (measure_ne_top _ _))
        (MeasureTheory.measureReal_mono
          traceBoundaryConnectionEvent_subset_crossingEventFrom
          (measure_ne_top _ _))
  have htail := ge_of_tendsto hlim hevent
  rw [currentContinuityMixedTraceLaw_clusterInfinite_real_eq_percolation
      d beta hbeta x,
    currentContinuityMixedTraceLaw_clusterInfinite_real_eq_percolation
      d beta hbeta y] at htail
  simpa only [rho, f, two_mul] using htail



theorem currentContinuity_adjacent_gap_nonneg
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (x y : Site d) (hxy : (hypercubicLattice d).Adj x y) :
    0 ≤ currentContinuityPlusTwoPoint d beta x y -
      currentContinuityFreeTwoPoint d beta x y := by
  obtain ⟨N, hN⟩ := Lattice.finite_subset_box
    ({x, y} : Set (Site d)) (Set.toFinite _)
  have hx : x ∈ box d N := hN (by simp)
  have hy : y ∈ box d N := hN (by simp)
  let a : ℕ → ℝ := fun k =>
    boundarySourceCurrentSum (StatMech.FK.boxGraph d ((k + N) + 1)) beta
          (fun _ => 1) (boxCurrentInterior d ((k + N) + 1))
          {boxSiteSucc
              (pairSourceBoxSite x (box_mono d (Nat.le_add_left N k) hx)),
            boxSiteSucc
              (pairSourceBoxSite y (box_mono d (Nat.le_add_left N k) hy))} /
      boundaryCurrentSum (StatMech.FK.boxGraph d ((k + N) + 1)) beta
        (fun _ => 1) (boxCurrentInterior d ((k + N) + 1))
  let b : ℕ → ℝ := fun k =>
    expectationJ (StatMech.FK.boxGraph d ((k + N) + 1)) beta (fun _ => 1)
      {boxSiteSucc
          (pairSourceBoxSite x (box_mono d (Nat.le_add_left N k) hx)),
        boxSiteSucc
          (pairSourceBoxSite y (box_mono d (Nat.le_add_left N k) hy))}
  have hnonneg : ∀ k, 0 ≤ a k - b k := by
    intro k
    let xk := pairSourceBoxSite x (box_mono d (Nat.le_add_left N k) hx)
    let yk := pairSourceBoxSite y (box_mono d (Nat.le_add_left N k) hy)
    have hxyk : boxSiteSucc xk ≠ boxSiteSucc yk := by
      apply boxSiteSucc_ne
      intro heq
      exact hxy.ne (Subtype.ext_iff.mp heq)
    have h := boundarySource_twoPoint_ratio_gap_nonneg
      (StatMech.FK.boxGraph d ((k + N) + 1)) beta hbeta.le
      (boxCurrentInterior d ((k + N) + 1)) hxyk
      (boxSiteSucc_interior xk) (boxSiteSucc_interior yk)
    simpa only [a, b, xk, yk,
      boundaryCurrentSum_eq_boundarySourceCurrentSum,
      current_representation] using h
  have ha : Tendsto a atTop
      (nhds (currentContinuityPlusTwoPoint d beta x y)) := by
    simpa only [a, currentContinuityPlusTwoPoint,
      boundaryCurrentSum_eq_boundarySourceCurrentSum] using
      growingPlusPairBoundarySourceRatio_tendsto
        d N beta hbeta.le x y hx hy
  have hb : Tendsto b atTop
      (nhds (currentContinuityFreeTwoPoint d beta x y)) := by
    simpa only [b, currentContinuityFreeTwoPoint] using
      growingFreePairForPlusSwitching_expectation_tendsto
        d N beta hbeta x y hx hy
  exact ge_of_tendsto (ha.sub hb) (Filter.Eventually.of_forall hnonneg)



theorem currentContinuity_adjacent_eq_of_no_percolation
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (hnoperco : (currentContinuityMixedTraceLaw d beta hbeta : Measure _).real
      (percolationEvent d) = 0)
    (x y : Site d) (hxy : (hypercubicLattice d).Adj x y) :
    currentContinuityPlusTwoPoint d beta x y =
      currentContinuityFreeTwoPoint d beta x y := by
  have hu := beta_mul_currentContinuity_adjacent_gap_le_percolation
    d beta hbeta x y hxy
  rw [hnoperco] at hu
  simp only [mul_zero] at hu
  have hl := currentContinuity_adjacent_gap_nonneg d beta hbeta x y hxy
  have hgap : currentContinuityPlusTwoPoint d beta x y -
      currentContinuityFreeTwoPoint d beta x y = 0 := by
    apply le_antisymm
    · nlinarith
    · exact hl
  exact sub_eq_zero.mp hgap

end StatMech.FrontierB
