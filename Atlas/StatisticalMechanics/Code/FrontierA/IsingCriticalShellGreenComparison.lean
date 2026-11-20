/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingCriticalAxisGreenComparison
import Code.FrontierA.IsingTorusCoordinateSymmetry
import Code.FrontierA.IsingLatticeGreenBlockDecay

open Filter MeasureTheory Set Topology

namespace StatMech.FrontierA

open StatMech Ising Lattice Percolation Sharpness StatMech.FrontierB

variable {d : Nat}



theorem boundaryEdges_fst_mem_boxSV_vbF
    {r : Nat} (hr : 1 <= r)
    {e : Site d × Site d}
    (he : e ∈ boundaryEdges d (boxSV_boxF d r)) :
    e.1 ∈ boxSV_vbF d r := by
  rw [boxSV_vbF, Finset.mem_sdiff]
  obtain ⟨heIn, heOut, heAdj⟩ := shk_mem_boundaryEdges_iff.mp he
  refine ⟨heIn, ?_⟩
  intro heInner
  apply heOut
  change e.2 ∈ (boxSV_boxF d r : Set (Site d))
  rw [boxSV_coe_boxF]
  have heInner' : e.1 ∈ box d (r - 1) := by
    change e.1 ∈ (boxSV_boxF d (r - 1) : Set (Site d)) at heInner
    rwa [boxSV_coe_boxF] at heInner
  exact sct_adj_mem_box_of_mem_box_pred hr heInner' heAdj




theorem currentContinuityFreeBoxTwoPoint_shell_le_isingTorus_axis
    (hd : 1 <= d) {n r k : Nat} (hr : 1 <= r) (hrn : r <= n)
    (hside : 2 * (n + 1) < isingDyadicSide k)
    (beta : Real) (hbeta : 0 <= beta)
    (x : Site d) (hx : x ∈ boxSV_vbF d r) :
    currentContinuityFreeBoxTwoPoint d n beta (Percolation.origin d) x <=
      isingTorusTwoPoint (k := k) beta 0
        (isingTorusCoordinateShift (⟨0, hd⟩ : Fin d) r) := by
  let S := boxSV_boxF d n
  have hxR : x ∈ box d r := by
    have hx' := hx
    rw [boxSV_vbF, Finset.mem_sdiff] at hx'
    have hxBoxR := hx'.1
    change x ∈ (boxSV_boxF d r : Set (Site d)) at hxBoxR
    rwa [boxSV_coe_boxF] at hxBoxR
  have hxBox : x ∈ box d n := box_mono d hrn hxR
  have h0 : Percolation.origin d ∈ S := by
    change Percolation.origin d ∈ (boxSV_boxF d n : Set (Site d))
    rw [boxSV_coe_boxF]
    exact Percolation.origin_mem_box' n
  have hxS : x ∈ S := by
    change x ∈ (boxSV_boxF d n : Set (Site d))
    rwa [boxSV_coe_boxF]
  have hx0 : x ≠ Percolation.origin d := by
    obtain ⟨i, hi⟩ :=
      exists_natAbs_coordinate_eq_of_mem_boxSV_vbF hr x hx
    intro h
    subst x
    simp [Percolation.origin] at hi
    omega
  let oS : {z // z ∈ S} := ⟨Percolation.origin d, h0⟩
  let xS : {z // z ∈ S} := ⟨x, hxS⟩
  have hfree := freeCorr_le_isingTorusTwoPoint
    (R := n) S (by
      intro z hz
      change z ∈ (boxSV_boxF d n : Set (Site d)) at hz
      rwa [boxSV_coe_boxF] at hz) hside beta hbeta oS xS
  have hhalf : r < 2 ^ (k + 1) := by
    unfold isingDyadicSide at hside
    rw [show k + 2 = (k + 1) + 1 by omega, pow_succ] at hside
    omega
  calc
    currentContinuityFreeBoxTwoPoint d n beta (Percolation.origin d) x =
        corrOriginInner d beta S x :=
      (corrOriginInner_box_eq_currentContinuityFreeBoxTwoPoint
        d n beta x hxBox hx0).symm
    _ = freeCorr d beta S oS xS := by
      simp only [corrOriginInner, dif_pos h0, dif_pos hxS]
      rfl
    _ <= isingTorusTwoPoint beta
        (isingSiteToDyadicTorus k (Percolation.origin d))
        (isingSiteToDyadicTorus k x) := hfree
    _ = isingTorusTwoPoint beta 0 (isingSiteToDyadicTorus k x) := by
      rw [isingSiteToDyadicTorus_origin]
    _ <= isingTorusTwoPoint (k := k) beta 0
        (isingTorusCoordinateShift (⟨0, hd⟩ : Fin d) r) :=
      isingTorusTwoPoint_embedded_shell_le_axis
        (⟨0, hd⟩ : Fin d) beta hbeta hr hhalf x hx

set_option maxHeartbeats 800000 in


theorem currentContinuityFreeTwoPoint_shell_le_latticeGreenBlock_subcritical
    (hd : 2 < d) {beta : Real} (hbeta : 0 < beta)
    (hlt : beta < IsingFK.betaC (magnetization d))
    (r : Nat) (hr : 1 <= r) (x : Site d) (hx : x ∈ boxSV_vbF d r) :
    currentContinuityFreeTwoPoint d beta (Percolation.origin d) x <=
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
      currentContinuityFreeBoxTwoPoint d n beta (Percolation.origin d) x <=
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
    exact (currentContinuityFreeBoxTwoPoint_shell_le_isingTorus_axis
      (d := d) (by omega) hr hrn hk beta hbeta.le x hx).trans
        (isingTorusTwoPoint_axisEndpoint_le_greenBlockAverage
          i beta hbeta r hhalf)
  let A : Finset (Site d) := {Percolation.origin d, x}
  have hlim : Tendsto
      (fun n => currentContinuityFreeBoxTwoPoint d n beta
        (Percolation.origin d) x) atTop
      (nhds (currentContinuityFreeTwoPoint d beta
        (Percolation.origin d) x)) := by
    simpa [A, currentContinuityFreeBoxTwoPoint,
      currentContinuityFreeTwoPoint] using
      (integral_freeMeasure_spinProd_tendsto_freeState d beta hbeta.le A)
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop r] with n hn
  exact hbox n hn

set_option maxHeartbeats 800000 in


theorem criticalFreeTwoPoint_shell_le_latticeGreenBlock
    (hd : 2 < d) (r : Nat) (hr : 1 <= r)
    (x : Site d) (hx : x ∈ boxSV_vbF d r) :
    currentContinuityFreeTwoPoint d
        (IsingFK.betaC (magnetization d)) (Percolation.origin d) x <=
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
    betaC hbetaC (Percolation.origin d) x
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
  exact currentContinuityFreeTwoPoint_shell_le_latticeGreenBlock_subcritical
    hd hn (by
      dsimp [b, betaC]
      have hpos : 0 < (1 / (n + 1 : Real)) := by positivity
      linarith) r hr x hx




theorem criticalFreeTwoPoint_uniform_shell_decay
    (hd : 2 < d) (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ R : Nat, ∀ r : Nat, R <= r -> ∀ x ∈ boxSV_vbF d r,
      |currentContinuityFreeTwoPoint d
        (IsingFK.betaC (magnetization d)) (Percolation.origin d) x| < epsilon := by
  let betaC := IsingFK.betaC (magnetization d)
  let i : Fin d := ⟨0, by omega⟩
  have hbetaC : 0 < betaC := by
    dsimp [betaC]
    rw [isingFK_betaC_eq_tildeBetaCIsing (by omega : 2 <= d)]
    exact tildeBetaCIsing_pos (by omega)
  have hmajorant : Tendsto
      (fun r => (1 / betaC) * isingLatticeGreenAxisBlockAverage i r)
      atTop (nhds 0) := by
    convert (isingLatticeGreenAxisBlockAverage_tendsto_zero hd i).const_mul
      (1 / betaC) using 1 <;> simp
  rw [Metric.tendsto_atTop] at hmajorant
  obtain ⟨R0, hR0⟩ := hmajorant epsilon hepsilon
  refine ⟨max 1 R0, ?_⟩
  intro r hr x hx
  have hr1 : 1 <= r := le_trans (le_max_left 1 R0) hr
  have hr0 : R0 <= r := le_trans (le_max_right 1 R0) hr
  have hx0 : x ≠ Percolation.origin d := by
    obtain ⟨j, hj⟩ :=
      exists_natAbs_coordinate_eq_of_mem_boxSV_vbF hr1 x hx
    intro h
    subst x
    simp [Percolation.origin] at hj
    omega
  have hnonneg : 0 <= currentContinuityFreeTwoPoint d betaC
      (Percolation.origin d) x := by
    rw [currentContinuityFreeTwoPoint_eq_freeInfiniteTwoPoint
      betaC hbetaC (by omega) (Percolation.origin d) x hx0.symm]
    exact measureReal_nonneg
  have hupper := criticalFreeTwoPoint_shell_le_latticeGreenBlock
    hd r hr1 x hx
  have hmajorantNonneg : 0 <=
      (1 / betaC) * isingLatticeGreenAxisBlockAverage i r :=
    hnonneg.trans (by simpa [betaC, i] using hupper)
  rw [abs_of_nonneg hnonneg]
  calc
    currentContinuityFreeTwoPoint d betaC (Percolation.origin d) x <=
        (1 / betaC) * isingLatticeGreenAxisBlockAverage i r := by
      simpa [betaC, i] using hupper
    _ < epsilon := by
      have h := hR0 r hr0
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hmajorantNonneg] at h
      exact h

end StatMech.FrontierA
