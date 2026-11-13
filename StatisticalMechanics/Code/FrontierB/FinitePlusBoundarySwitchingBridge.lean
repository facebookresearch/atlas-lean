/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierB.FiniteBoxSwitchingBridge
import Code.FrontierB.PlusBoundarySourceSpin

open MeasureTheory Set
open scoped ENNReal

namespace StatMech.FrontierB

open Sharpness Ising Lattice Percolation



theorem plusPairSource_pairSource_prod_apply
    (d n : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (x y : StatMech.FK.boxVerts d n) (hxy : x ≠ y)
    (C : Set (InfiniteCurrentConfig (Sym2 (Site d)) ×
      InfiniteCurrentConfig (Sym2 (Site d)))) (hC : MeasurableSet C) :
    ((plusPairSourceBoxCurrentMeasure d n beta hbeta x y hxy).prod
      (pairSourceBoxCurrentMeasure d (n + 1) beta hbeta
        (boxSiteSucc x) (boxSiteSucc y) (boxSiteSucc_ne hxy)) : Measure _) C =
      (boundarySourceCurrentPairPMF
        (StatMech.FK.boxGraph d (n + 1)) beta (fun _ => 1)
        hbeta.le (fun _ => by positivity) (boxCurrentInterior d (n + 1))
        {boxSiteSucc x, boxSiteSucc y} {boxSiteSucc x, boxSiteSucc y}
        (plusPairBoundarySourceCurrentSum_pos d n beta hbeta x y hxy)
        (boxCurrentSum_pair_pos d (n + 1) beta hbeta
          (boxSiteSucc x) (boxSiteSucc y) (boxSiteSucc_ne hxy))).toMeasure
        ((Prod.map (extendBoxCurrent d (n + 1))
          (extendBoxCurrent d (n + 1))) ⁻¹' C) := by
  let G := StatMech.FK.boxGraph d (n + 1)
  let mu := (boundarySourceCurrentPMF G beta (fun _ => 1) hbeta.le
    (fun _ => by positivity) (boxCurrentInterior d (n + 1))
    {boxSiteSucc x, boxSiteSucc y}
    (plusPairBoundarySourceCurrentSum_pos d n beta hbeta x y hxy)).toMeasure
  let nu := (currentPMF G beta (fun _ => 1) hbeta.le
    (fun _ => by positivity) {boxSiteSucc x, boxSiteSucc y}
    (boxCurrentSum_pair_pos d (n + 1) beta hbeta
      (boxSiteSucc x) (boxSiteSucc y) (boxSiteSucc_ne hxy))).toMeasure
  change (Measure.map (extendBoxCurrent d (n + 1)) mu).prod
      (Measure.map (extendBoxCurrent d (n + 1)) nu) C = _
  rw [Measure.map_prod_map mu nu (measurable_extendBoxCurrent d (n + 1))
    (measurable_extendBoxCurrent d (n + 1)),
    Measure.map_apply
      ((measurable_extendBoxCurrent d (n + 1)).prodMap
        (measurable_extendBoxCurrent d (n + 1))) hC,
    boundarySourceCurrentPairPMF_toMeasure_eq_prod]



theorem plus_free_BoxCurrentMeasure_prod_apply
    (d n : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (C : Set (InfiniteCurrentConfig (Sym2 (Site d)) ×
      InfiniteCurrentConfig (Sym2 (Site d)))) (hC : MeasurableSet C) :
    ((plusBoxCurrentMeasure d n beta hbeta).prod
      (freeBoxCurrentMeasure d n beta hbeta) : Measure _) C =
      (boundarySourceCurrentPairPMF (StatMech.FK.boxGraph d n) beta
        (fun _ => 1) hbeta (fun _ => by positivity) (boxCurrentInterior d n)
        ∅ ∅ (lt_of_lt_of_le Real.zero_lt_one
          (one_le_boundaryCurrentSum (StatMech.FK.boxGraph d n) beta
            (fun _ => 1) hbeta (fun _ => by positivity)
            (boxCurrentInterior d n)))
        (Ising.acr_currentSum_empty_pos
          (StatMech.FK.boxGraph d n) beta (fun _ => 1))).toMeasure
          ((Prod.map (extendBoxCurrent d n) (extendBoxCurrent d n)) ⁻¹' C) := by
  let G := StatMech.FK.boxGraph d n
  let hboundary : 0 < boundarySourceCurrentSum G beta (fun _ => 1)
      (boxCurrentInterior d n) ∅ :=
    lt_of_lt_of_le Real.zero_lt_one
      (one_le_boundaryCurrentSum G beta (fun _ => 1) hbeta
        (fun _ => by positivity) (boxCurrentInterior d n))
  let hzero := Ising.acr_currentSum_empty_pos G beta (fun _ => 1)
  let mu := (boundarySourceCurrentPMF G beta (fun _ => 1) hbeta
    (fun _ => by positivity) (boxCurrentInterior d n) ∅ hboundary).toMeasure
  let nu := (currentPMF G beta (fun _ => 1) hbeta
    (fun _ => by positivity) ∅ hzero).toMeasure
  change (Measure.map (extendBoxCurrent d n) mu).prod
      (Measure.map (extendBoxCurrent d n) nu) C = _
  rw [Measure.map_prod_map mu nu (measurable_extendBoxCurrent d n)
    (measurable_extendBoxCurrent d n),
    Measure.map_apply
      ((measurable_extendBoxCurrent d n).prodMap
        (measurable_extendBoxCurrent d n)) hC,
    boundarySourceCurrentPairPMF_toMeasure_eq_prod]



theorem plusPair_pairSource_plus_free_box_switching
    (d n : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (x y : StatMech.FK.boxVerts d n) (hxy : x ≠ y)
    (Q : Set (ConfigSpace (Sym2 (Site d)))) (hQ : IsClopen Q) :
    ENNReal.ofReal
        (boundarySourceCurrentSum (StatMech.FK.boxGraph d (n + 1)) beta
            (fun _ => 1) (boxCurrentInterior d (n + 1))
            {boxSiteSucc x, boxSiteSucc y} *
          currentSum (StatMech.FK.boxGraph d (n + 1)) beta
            (fun _ => 1) {boxSiteSucc x, boxSiteSucc y}) *
      ((plusPairSourceBoxCurrentMeasure d n beta hbeta x y hxy).prod
        (pairSourceBoxCurrentMeasure d (n + 1) beta hbeta
          (boxSiteSucc x) (boxSiteSucc y) (boxSiteSucc_ne hxy)) : Measure _)
          (superposedCurrentTrace ⁻¹' Q) =
    ENNReal.ofReal
        (boundaryCurrentSum (StatMech.FK.boxGraph d (n + 1)) beta
            (fun _ => 1) (boxCurrentInterior d (n + 1)) *
          currentSum (StatMech.FK.boxGraph d (n + 1)) beta (fun _ => 1) ∅) *
      ((plusBoxCurrentMeasure d (n + 1) beta hbeta.le).prod
        (freeBoxCurrentMeasure d (n + 1) beta hbeta.le) : Measure _)
          (currentPairTraceBoxGate Q (n + 1) x.1 y.1) := by
  let G := StatMech.FK.boxGraph d (n + 1)
  let interior := boxCurrentInterior d (n + 1)
  let u := boxSiteSucc x
  let v := boxSiteSucc y
  let P : Sharpness.Current (StatMech.FK.boxVerts d (n + 1)) → Prop :=
    finiteBoxTracePredicate d (n + 1) Q
  letI : DecidablePred P := Classical.decPred _
  have hboundaryPair :=
    plusPairBoundarySourceCurrentSum_pos d n beta hbeta x y hxy
  have hpair := boxCurrentSum_pair_pos d (n + 1) beta hbeta u v
    (boxSiteSucc_ne hxy)
  have hboundaryZero : 0 < boundarySourceCurrentSum G beta (fun _ => 1)
      interior ∅ :=
    lt_of_lt_of_le Real.zero_lt_one
      (one_le_boundaryCurrentSum G beta (fun _ => 1) hbeta.le
        (fun _ => by positivity) interior)
  have hzero := Ising.acr_currentSum_empty_pos G beta (fun _ => 1)
  have hswitch := boundarySourceCurrentPairPMF_switching G beta (fun _ => 1)
    hbeta.le (fun _ => by positivity) interior (boxSiteSucc_ne hxy)
    (boxSiteSucc_interior x) (boxSiteSucc_interior y) P
    hboundaryPair hpair hboundaryZero hzero
  rw [sourcePairSuperpositionEvent_finiteBoxTracePredicate d (n + 1) Q,
    sourcePairSuperpositionEvent_finiteBoxTracePredicate_connected
      d (n + 1) Q u v] at hswitch
  have htrace : MeasurableSet (superposedCurrentTrace ⁻¹' Q) :=
    hQ.isOpen.measurableSet.preimage continuous_superposedCurrentTrace.measurable
  have hgate : MeasurableSet
      (currentPairTraceBoxGate Q (n + 1) x.1 y.1) :=
    (isClopen_currentPairTraceBoxGate hQ (n + 1) x.1 y.1).isOpen.measurableSet
  rw [← plusPairSource_pairSource_prod_apply d n beta hbeta x y hxy
      (superposedCurrentTrace ⁻¹' Q) htrace] at hswitch
  simp only [u, v, boxSiteSucc] at hswitch
  rw [← plus_free_BoxCurrentMeasure_prod_apply d (n + 1) beta hbeta.le
      (currentPairTraceBoxGate Q (n + 1) x.1 y.1) hgate] at hswitch
  simpa only [G, interior, u, v, boundaryCurrentSum_eq_boundarySourceCurrentSum]
    using hswitch



theorem plusPair_pairSource_plus_free_box_switching_normalized
    (d n : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (x y : StatMech.FK.boxVerts d n) (hxy : x ≠ y)
    (Q : Set (ConfigSpace (Sym2 (Site d)))) (hQ : IsClopen Q) :
    ENNReal.ofReal
        ((∫ omega, spinProd ({x.1, y.1} : Finset (Site d)) omega
            ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d)))) *
          expectationJ (StatMech.FK.boxGraph d (n + 1)) beta (fun _ => 1)
            {boxSiteSucc x, boxSiteSucc y}) *
      ((plusPairSourceBoxCurrentMeasure d n beta hbeta x y hxy).prod
        (pairSourceBoxCurrentMeasure d (n + 1) beta hbeta
          (boxSiteSucc x) (boxSiteSucc y) (boxSiteSucc_ne hxy)) : Measure _)
          (superposedCurrentTrace ⁻¹' Q) =
      ((plusBoxCurrentMeasure d (n + 1) beta hbeta.le).prod
        (freeBoxCurrentMeasure d (n + 1) beta hbeta.le) : Measure _)
          (currentPairTraceBoxGate Q (n + 1) x.1 y.1) := by
  let G := StatMech.FK.boxGraph d (n + 1)
  let interior := boxCurrentInterior d (n + 1)
  let u := boxSiteSucc x
  let v := boxSiteSucc y
  let a := boundarySourceCurrentSum G beta (fun _ => 1) interior {u, v}
  let b := currentSum G beta (fun _ => 1) {u, v}
  let z := boundaryCurrentSum G beta (fun _ => 1) interior
  let w := currentSum G beta (fun _ => 1) ∅
  let p := ((plusPairSourceBoxCurrentMeasure d n beta hbeta x y hxy).prod
    (pairSourceBoxCurrentMeasure d (n + 1) beta hbeta u v
      (boxSiteSucc_ne hxy)) : Measure _) (superposedCurrentTrace ⁻¹' Q)
  let q := ((plusBoxCurrentMeasure d (n + 1) beta hbeta.le).prod
    (freeBoxCurrentMeasure d (n + 1) beta hbeta.le) : Measure _)
      (currentPairTraceBoxGate Q (n + 1) x.1 y.1)
  have ha : 0 < a := plusPairBoundarySourceCurrentSum_pos
    d n beta hbeta x y hxy
  have hb : 0 < b := boxCurrentSum_pair_pos d (n + 1) beta hbeta u v
    (boxSiteSucc_ne hxy)
  have hz : 0 < z := lt_of_lt_of_le Real.zero_lt_one
    (one_le_boundaryCurrentSum G beta (fun _ => 1) hbeta.le
      (fun _ => by positivity) interior)
  have hw : 0 < w := Ising.acr_currentSum_empty_pos G beta (fun _ => 1)
  have hswitch : ENNReal.ofReal (a * b) * p =
      ENNReal.ofReal (z * w) * q := by
    simpa only [G, interior, u, v, a, b, z, w, p, q] using
      plusPair_pairSource_plus_free_box_switching
        d n beta hbeta x y hxy Q hQ
  have hplus :
      (∫ omega, spinProd ({x.1, y.1} : Finset (Site d)) omega
          ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d)))) =
        a / z := by
    symm
    simpa only [G, interior, u, v, a, z] using
      plusPairBoundarySourceRatio_eq_plusIntegral d n beta x y
  have hfree : expectationJ G beta (fun _ => 1) {u, v} = b / w := by
    simpa only [b, w] using
      current_representation G beta (fun _ => 1) {u, v}
  let A := ENNReal.ofReal a
  let B := ENNReal.ofReal b
  let Z := ENNReal.ofReal z
  let W := ENNReal.ofReal w
  have hZ0 : Z ≠ 0 := (ENNReal.ofReal_pos.mpr hz).ne'
  have hW0 : W ≠ 0 := (ENNReal.ofReal_pos.mpr hw).ne'
  have hZtop : Z ≠ ∞ := ENNReal.ofReal_ne_top
  have hWtop : W ≠ ∞ := ENNReal.ofReal_ne_top
  have hZW0 : Z * W ≠ 0 := mul_ne_zero hZ0 hW0
  have hZWtop : Z * W ≠ ∞ := ENNReal.mul_ne_top hZtop hWtop
  rw [hplus, hfree]
  apply (ENNReal.mul_left_inj hZW0 hZWtop).mp
  rw [ENNReal.ofReal_mul (div_nonneg ha.le hz.le),
    ENNReal.ofReal_div_of_pos hz, ENNReal.ofReal_div_of_pos hw]
  rw [ENNReal.ofReal_mul ha.le, ENNReal.ofReal_mul hz.le] at hswitch
  change (((A / Z) * (B / W) * p) * (Z * W)) = q * (Z * W)
  calc
    ((A / Z) * (B / W) * p) * (Z * W) = A * B * p := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      calc
        ((A * Z⁻¹) * (B * W⁻¹) * p) * (Z * W) =
            A * B * p * (Z⁻¹ * Z) * (W⁻¹ * W) := by ac_rfl
        _ = A * B * p := by
          rw [ENNReal.inv_mul_cancel hZ0 hZtop,
            ENNReal.inv_mul_cancel hW0 hWtop]
          simp
    _ = Z * W * q := by simpa only [A, B, Z, W] using hswitch
    _ = q * (Z * W) := by ac_rfl



theorem plusPair_pairSource_plus_free_box_switching_normalized_real
    (d n : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (x y : StatMech.FK.boxVerts d n) (hxy : x ≠ y)
    (Q : Set (ConfigSpace (Sym2 (Site d)))) (hQ : IsClopen Q) :
    ((∫ omega, spinProd ({x.1, y.1} : Finset (Site d)) omega
        ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d)))) *
      expectationJ (StatMech.FK.boxGraph d (n + 1)) beta (fun _ => 1)
        {boxSiteSucc x, boxSiteSucc y}) *
      ((plusPairSourceBoxCurrentMeasure d n beta hbeta x y hxy).prod
        (pairSourceBoxCurrentMeasure d (n + 1) beta hbeta
          (boxSiteSucc x) (boxSiteSucc y) (boxSiteSucc_ne hxy)) : Measure _).real
          (superposedCurrentTrace ⁻¹' Q) =
      ((plusBoxCurrentMeasure d (n + 1) beta hbeta.le).prod
        (freeBoxCurrentMeasure d (n + 1) beta hbeta.le) : Measure _).real
          (currentPairTraceBoxGate Q (n + 1) x.1 y.1) := by
  have hplus : 0 ≤
      ∫ omega, spinProd ({x.1, y.1} : Finset (Site d)) omega
        ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d))) := by
    rw [← plusPairBoundarySourceRatio_eq_plusIntegral d n beta x y]
    exact div_nonneg
      (plusPairBoundarySourceCurrentSum_pos
        d n beta hbeta x y hxy).le
      (le_trans (by positivity)
        (one_le_boundaryCurrentSum (StatMech.FK.boxGraph d (n + 1)) beta
          (fun _ => 1) hbeta.le (fun _ => by positivity)
          (boxCurrentInterior d (n + 1))))
  have hfree : 0 ≤ expectationJ (StatMech.FK.boxGraph d (n + 1)) beta
      (fun _ => 1) {boxSiteSucc x, boxSiteSucc y} :=
    Ising.acr_expectationJ_nonneg (StatMech.FK.boxGraph d (n + 1)) beta
      (fun _ => 1) hbeta.le (fun _ => by positivity) _
  have h := congrArg ENNReal.toReal
    (plusPair_pairSource_plus_free_box_switching_normalized
      d n beta hbeta x y hxy Q hQ)
  simpa only [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (mul_nonneg hplus hfree), Measure.real] using h

end StatMech.FrontierB
