/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingLatticeGreen
import Code.FrontierA.IsingCriticalTwoPointShell
import Code.FrontierB.CurrentContinuityFreeLeftContinuous

open Filter Set Topology

namespace StatMech.FrontierA

open StatMech Ising Lattice Sharpness StatMech.FrontierB

variable {d : Nat}

noncomputable def isingTorusNormalizedZeroMode
    (d : Nat) (beta : Real) (k : Nat) : Real :=
  (finiteTorusFourierCoeff
      (fun z : IsingDyadicTorus d k => isingTorusTwoPoint beta 0 z) 0).re /
    Fintype.card (IsingDyadicTorus d k)

theorem isingTorusNormalizedZeroMode_nonneg
    (beta : Real) (k : Nat) :
    0 <= isingTorusNormalizedZeroMode d beta k := by
  rw [isingTorusNormalizedZeroMode]
  have hkernel :
      (fun z : IsingDyadicTorus d k => isingTorusTwoPoint beta 0 z) =
        isingTorusAveragedTwoPoint beta := by
    funext z
    exact (isingTorusAveragedTwoPoint_eq_twoPoint beta z).symm
  rw [hkernel, finiteTorusFourierCoeff_isingTorusAveragedTwoPoint]
  norm_cast
  apply div_nonneg
  · apply div_nonneg
    · exact Finset.sum_nonneg fun sigma _ =>
        mul_nonneg (Real.exp_pos _).le (Complex.normSq_nonneg _)
    · exact mul_nonneg (isingTorusShiftedPartition_zero_pos beta).le
        (Nat.cast_nonneg _)
  · positivity


theorem isingTorusNormalizedZeroMode_tendsto_zero_subcritical
    (hd : 2 <= d) (beta : Real) (hbeta : 0 <= beta)
    (hlt : beta < IsingFK.betaC (magnetization d)) :
    Tendsto (isingTorusNormalizedZeroMode d beta) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (isingTorusZeroMode_eventually_small_subcritical
      hd beta hbeta hlt epsilon hepsilon)
  refine ⟨N, fun k hk => ?_⟩
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (isingTorusNormalizedZeroMode_nonneg beta k)]
  exact hN k hk

theorem isingSiteToDyadicTorus_criticalAxisSite
    (hd : 1 <= d) (r k : Nat) :
    isingSiteToDyadicTorus k (criticalAxisSite hd r) =
      isingTorusCoordinateShift (k := k) (⟨0, hd⟩ : Fin d) r := by
  funext i
  by_cases hi : i = (⟨0, hd⟩ : Fin d)
  · subst i
    simp [criticalAxisSite, isingSiteToDyadicTorus,
      isingTorusCoordinateShift]
    exact Int.cast_natCast r
  · simp [criticalAxisSite, isingSiteToDyadicTorus,
      isingTorusCoordinateShift, hi]
    exact Int.cast_zero



theorem currentContinuityFreeBoxTwoPoint_le_isingTorus_axis
    (hd : 1 <= d) {n r k : Nat} (hr : 1 <= r) (hrn : r <= n)
    (hside : 2 * (n + 1) < isingDyadicSide k)
    (beta : Real) (hbeta : 0 <= beta) :
    currentContinuityFreeBoxTwoPoint d n beta (Percolation.origin d)
        (criticalAxisSite hd r) <=
      isingTorusTwoPoint (k := k) beta 0
        (isingTorusCoordinateShift (⟨0, hd⟩ : Fin d) r) := by
  let S := boxSV_boxF d n
  have h0 : Percolation.origin d ∈ S := by
    change Percolation.origin d ∈ (boxSV_boxF d n : Set (Site d))
    rw [boxSV_coe_boxF]
    exact Percolation.origin_mem_box' n
  have hxBox : criticalAxisSite hd r ∈ box d n :=
    box_mono d hrn (criticalAxisSite_mem_box hd)
  have hx : criticalAxisSite hd r ∈ S := by
    change criticalAxisSite hd r ∈ (boxSV_boxF d n : Set (Site d))
    rwa [boxSV_coe_boxF]
  let oS : {z // z ∈ S} := ⟨Percolation.origin d, h0⟩
  let xS : {z // z ∈ S} := ⟨criticalAxisSite hd r, hx⟩
  have hfree := freeCorr_le_isingTorusTwoPoint
    (R := n) S (by
      intro z hz
      change z ∈ (boxSV_boxF d n : Set (Site d)) at hz
      rwa [boxSV_coe_boxF] at hz) hside beta hbeta oS xS
  calc
    currentContinuityFreeBoxTwoPoint d n beta (Percolation.origin d)
        (criticalAxisSite hd r) =
        corrOriginInner d beta S (criticalAxisSite hd r) :=
      (corrOriginInner_box_eq_currentContinuityFreeBoxTwoPoint
        d n beta (criticalAxisSite hd r) hxBox
          (criticalAxisSite_ne_origin hd hr)).symm
    _ = freeCorr d beta S oS xS := by
      simp only [corrOriginInner, dif_pos h0, dif_pos hx]
      rfl
    _ <= isingTorusTwoPoint beta
        (isingSiteToDyadicTorus k (origin d))
        (isingSiteToDyadicTorus k (criticalAxisSite hd r)) := hfree
    _ = isingTorusTwoPoint beta 0
        (isingTorusCoordinateShift (⟨0, hd⟩ : Fin d) r) := by
      change isingTorusTwoPoint beta
        (isingSiteToDyadicTorus k (Percolation.origin d))
        (isingSiteToDyadicTorus k (criticalAxisSite hd r)) = _
      rw [isingSiteToDyadicTorus_origin,
        isingSiteToDyadicTorus_criticalAxisSite]


set_option maxHeartbeats 800000 in


theorem currentContinuityFreeTwoPoint_axis_le_latticeGreenBlock_subcritical
    (hd : 2 < d) {beta : Real} (hbeta : 0 < beta)
    (hlt : beta < IsingFK.betaC (magnetization d))
    (r : Nat) (hr : 1 <= r) :
    currentContinuityFreeTwoPoint d beta (Percolation.origin d)
        (criticalAxisSite (by omega) r) <=
      (1 / beta) * isingLatticeGreenAxisBlockAverage
        (⟨0, by omega⟩ : Fin d) r := by
  let i : Fin d := ⟨0, by omega⟩
  have hgreen : Tendsto
      (fun k => finiteTorusBlockDifferenceAverage
        (finiteTorusZeroModeGreen
          (isingTorusCharacterDispersion (d := d) (k := k)))
        (isingTorusAxisSegment (k := k) i r))
      atTop (nhds (isingLatticeGreenAxisBlockAverage i r)) := by
    apply (isingDyadicGreenAxisBlockAverage_tendsto_latticeGreen hd i r).congr'
    have hside : Tendsto isingDyadicSide atTop atTop := by
      unfold isingDyadicSide
      rw [Filter.tendsto_add_atTop_iff_nat]
      exact tendsto_pow_atTop_atTop_of_one_lt Nat.one_lt_two
    filter_upwards [hside.eventually_gt_atTop r] with k hk
    rw [finiteTorusBlockDifferenceAverage_zeroModeGreen_axisSegment i r hk]
    rfl
  have hzero := isingTorusNormalizedZeroMode_tendsto_zero_subcritical
    (d := d) (by omega) beta hbeta.le hlt
  have htorusBound : Tendsto
      (fun k => isingTorusNormalizedZeroMode d beta k +
        (1 / beta) * finiteTorusBlockDifferenceAverage
          (finiteTorusZeroModeGreen
            (isingTorusCharacterDispersion (d := d) (k := k)))
          (isingTorusAxisSegment (k := k) i r))
      atTop
      (nhds ((1 / beta) * isingLatticeGreenAxisBlockAverage i r)) := by
    convert hzero.add (hgreen.const_mul (1 / beta)) using 1 <;> simp
  have hbox (n : Nat) (hrn : r <= n) :
      currentContinuityFreeBoxTwoPoint d n beta (Percolation.origin d)
          (criticalAxisSite (by omega) r) <=
        (1 / beta) * isingLatticeGreenAxisBlockAverage i r := by
    apply ge_of_tendsto htorusBound
    have hsideTendsto : Tendsto isingDyadicSide atTop atTop := by
      unfold isingDyadicSide
      rw [Filter.tendsto_add_atTop_iff_nat]
      exact tendsto_pow_atTop_atTop_of_one_lt Nat.one_lt_two
    filter_upwards [hsideTendsto.eventually_gt_atTop (2 * (n + 1))] with k hk
    have hhalf : r <= 2 ^ (k + 1) := by
      unfold isingDyadicSide at hk
      rw [show k + 2 = (k + 1) + 1 by omega, pow_succ] at hk
      omega
    exact (currentContinuityFreeBoxTwoPoint_le_isingTorus_axis
      (d := d) (by omega) hr hrn hk beta hbeta.le).trans
        (isingTorusTwoPoint_axisEndpoint_le_greenBlockAverage
          i beta hbeta r hhalf)
  let A : Finset (Site d) :=
    {Percolation.origin d, criticalAxisSite (by omega) r}
  have hlim : Tendsto
      (fun n => currentContinuityFreeBoxTwoPoint d n beta (Percolation.origin d)
        (criticalAxisSite (by omega) r)) atTop
      (nhds (currentContinuityFreeTwoPoint d beta (Percolation.origin d)
        (criticalAxisSite (by omega) r))) := by
    simpa [A, currentContinuityFreeBoxTwoPoint,
      currentContinuityFreeTwoPoint] using
      (integral_freeMeasure_spinProd_tendsto_freeState d beta hbeta.le A)
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop r] with n hn
  exact hbox n hn


set_option maxHeartbeats 800000 in


theorem criticalFreeTwoPoint_axis_le_latticeGreenBlock
    (hd : 2 < d) (r : Nat) (hr : 1 <= r) :
    currentContinuityFreeTwoPoint d
        (IsingFK.betaC (magnetization d)) (Percolation.origin d)
        (criticalAxisSite (by omega) r) <=
      (1 / IsingFK.betaC (magnetization d)) *
        isingLatticeGreenAxisBlockAverage
          (⟨0, by omega⟩ : Fin d) r := by
  let betaC := IsingFK.betaC (magnetization d)
  let b : Nat -> Real := fun n => betaC - 1 / (n + 1 : Real)
  have hbetaC : 0 < betaC := by
    dsimp [betaC]
    rw [isingFK_betaC_eq_tildeBetaCIsing (by omega : 2 <= d)]
    exact tildeBetaCIsing_pos (by omega)
  have hb : Tendsto b atTop (nhds betaC) := by
    simpa [b] using (tendsto_const_nhds.sub
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : Nat => (1 : Real) / (n + 1)) atTop (nhds 0)))
  have hleft := currentContinuityFreeTwoPoint_tendsto_fromBelow
    betaC hbetaC (Percolation.origin d) (criticalAxisSite (by omega) r)
  have hright : Tendsto
      (fun n => (1 / b n) * isingLatticeGreenAxisBlockAverage
        (⟨0, by omega⟩ : Fin d) r)
      atTop
      (nhds ((1 / betaC) * isingLatticeGreenAxisBlockAverage
        (⟨0, by omega⟩ : Fin d) r)) := by
    exact (tendsto_const_nhds.div hb (ne_of_gt hbetaC)).mul_const _
  apply le_of_tendsto_of_tendsto hleft hright
  have hbpos : ∀ᶠ n in atTop, 0 < b n :=
    (tendsto_order.mp hb).1 0 hbetaC
  filter_upwards [hbpos] with n hn
  exact currentContinuityFreeTwoPoint_axis_le_latticeGreenBlock_subcritical
    hd hn (by
      dsimp [b, betaC]
      have hpos : 0 < (1 / (n + 1 : Real)) := by positivity
      linarith) r hr

end StatMech.FrontierA
