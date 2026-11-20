/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingPositiveCube
import Code.FrontierA.IsingCriticalShellGreenComparison

open Filter Finset MeasureTheory Set Topology
open scoped BigOperators

namespace StatMech.FrontierA

open StatMech Ising Lattice Percolation Sharpness StatMech.FrontierB

variable {d : Nat}



noncomputable def currentContinuityFreePairKernel
    (d : Nat) (beta : Real) (z : Site d) : Real :=
  if z = 0 then 1 else
    currentContinuityFreeTwoPoint d beta (Percolation.origin d) z


noncomputable def currentContinuityFreeBoxPairKernel
    (d n : Nat) (beta : Real) (z : Site d) : Real :=
  if z = 0 then 1 else
    currentContinuityFreeBoxTwoPoint d n beta (Percolation.origin d) z



noncomputable def currentContinuityFreePositiveCubeAverage
    (d : Nat) (beta : Real) (m : Nat) : Real :=
  finiteTorusBlockDifferenceAverage
    (currentContinuityFreePairKernel d beta) (isingPositiveCube d m)


noncomputable def currentContinuityFreeBoxPositiveCubeAverage
    (d n : Nat) (beta : Real) (m : Nat) : Real :=
  finiteTorusBlockDifferenceAverage
    (currentContinuityFreeBoxPairKernel d n beta) (isingPositiveCube d m)

theorem isingSiteToDyadicTorus_sub (k : Nat) (a b : Site d) :
    isingSiteToDyadicTorus k (b - a) =
      isingSiteToDyadicTorus k b - isingSiteToDyadicTorus k a := by
  funext i
  simp only [isingSiteToDyadicTorus, Pi.sub_apply]
  exact Int.cast_sub (b i) (a i)



theorem currentContinuityFreeBoxPositiveCubeAverage_tendsto
    (beta : Real) (hbeta : 0 <= beta) (m : Nat) :
    Tendsto (fun n => currentContinuityFreeBoxPositiveCubeAverage d n beta m)
      atTop (nhds (currentContinuityFreePositiveCubeAverage d beta m)) := by
  unfold currentContinuityFreeBoxPositiveCubeAverage
    currentContinuityFreePositiveCubeAverage
    finiteTorusBlockDifferenceAverage
  apply Tendsto.const_mul
  apply tendsto_finsetSum
  intro a ha
  apply tendsto_finsetSum
  intro b hb
  unfold currentContinuityFreeBoxPairKernel currentContinuityFreePairKernel
  by_cases hz : b - a = 0
  · simp [hz]
  · simp only [if_neg hz]
    let A : Finset (Site d) := {Percolation.origin d, b - a}
    simpa [currentContinuityFreeBoxTwoPoint,
      currentContinuityFreeTwoPoint, A] using
      (integral_freeMeasure_spinProd_tendsto_freeState d beta hbeta A)

private theorem coordinateAxis_ne_origin
    (i : Fin d) (r : Nat) (hr : 1 <= r) :
    (Pi.single i (r : Int) : Site d) ≠ Percolation.origin d := by
  intro h
  have hi := congrFun h i
  simp [Percolation.origin] at hi
  omega

private theorem currentContinuityFreeTwoPoint_axis_le_one
    (hd : 1 <= d) (i : Fin d) (beta : Real) (hbeta : 0 < beta)
    (r : Nat) (hr : 1 <= r) :
    currentContinuityFreeTwoPoint d beta (Percolation.origin d)
        (Pi.single i (r : Int)) <= 1 := by
  rw [currentContinuityFreeTwoPoint_eq_freeInfiniteTwoPoint
    beta hbeta hd (Percolation.origin d) (Pi.single i (r : Int))]
  · exact measureReal_le_one
  · exact (coordinateAxis_ne_origin i r hr).symm

private theorem currentContinuityFreeTwoPoint_axis_coordinate_eq
    (i j : Fin d) (beta : Real) (hbeta : 0 <= beta) (r : Nat) :
    currentContinuityFreeTwoPoint d beta (Percolation.origin d)
        (Pi.single i (r : Int)) =
      currentContinuityFreeTwoPoint d beta (Percolation.origin d)
        (Pi.single j (r : Int)) := by
  by_cases hij : i = j
  · subst j
    rfl
  · have hsymm := currentContinuityFreeTwoPoint_coordinateSwap
      i j hij beta hbeta (Pi.single i (r : Int))
    have hreflect : isingDiagonalReflect i j 0
        (Pi.single i (r : Int) : Site d) = Pi.single j (r : Int) := by
      funext a
      by_cases hai : a = i
      · subst a
        simp [hij]
      · by_cases haj : a = j
        · subst a
          simp [hij]
        · rw [isingDiagonalReflect_apply_of_ne i j a hai haj]
          simp [hai, haj]
    rw [hreflect] at hsymm
    exact hsymm.symm



theorem currentContinuityFreeTwoPoint_axis_le_pairKernel_of_l1
    (hd : 2 <= d) (j : Fin d) (beta : Real) (hbeta : 0 < beta)
    (r : Nat) (hr : 1 <= r) (z : Site d)
    (hz : (∑ i, (z i).natAbs) <= r) :
    currentContinuityFreeTwoPoint d beta (Percolation.origin d)
        (Pi.single j (r : Int)) <=
      currentContinuityFreePairKernel d beta z := by
  by_cases hz0 : z = 0
  · rw [currentContinuityFreePairKernel, if_pos hz0]
    exact currentContinuityFreeTwoPoint_axis_le_one (by omega)
      j beta hbeta r hr
  · rw [currentContinuityFreePairKernel, if_neg hz0]
    obtain ⟨i, hi⟩ : ∃ i : Fin d, z i ≠ 0 := by
      by_contra h
      apply hz0
      funext i
      push Not at h
      exact h i
    let L : Nat := ∑ a, (z a).natAbs
    have hL : 1 <= L := by
      dsimp [L]
      have hpos : 0 < (z i).natAbs := Int.natAbs_pos.mpr hi
      have hle : (z i).natAbs <= ∑ a, (z a).natAbs :=
        Finset.single_le_sum (f := fun a : Fin d => (z a).natAbs)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    have hanti := currentContinuityFreeTwoPoint_axis_antitone
      hd j beta hbeta.le L r hL hz
    have hcoord := currentContinuityFreeTwoPoint_axis_coordinate_eq
      j i beta hbeta.le L
    have hl1 := currentContinuityFreeTwoPoint_l1Axis_le
      i beta hbeta.le z hi
    change currentContinuityFreeTwoPoint d beta (Percolation.origin d)
        (Pi.single i (L : Int)) <= _ at hl1
    exact hanti.trans (hcoord.trans_le hl1)



theorem currentContinuityFreeTwoPoint_axis_le_positiveCube_pairKernel
    (hd : 2 <= d) (j : Fin d) (beta : Real) (hbeta : 0 < beta)
    (r m : Nat) (hr : 1 <= r) (hdm : d * m <= r)
    {a b : Site d} (ha : a ∈ isingPositiveCube d m)
    (hb : b ∈ isingPositiveCube d m) :
    currentContinuityFreeTwoPoint d beta (Percolation.origin d)
        (Pi.single j (r : Int)) <=
      currentContinuityFreePairKernel d beta (b - a) := by
  apply currentContinuityFreeTwoPoint_axis_le_pairKernel_of_l1
    hd j beta hbeta r hr
  exact (isingPositiveCube_difference_l1_le ha hb).trans hdm



theorem currentContinuityFreeBoxPairKernel_le_isingTorus
    (beta : Real) (hbeta : 0 <= beta) (n k : Nat)
    (hside : 2 * (n + 1) < isingDyadicSide k)
    (z : Site d) (hzBox : z ∈ box d n) :
    currentContinuityFreeBoxPairKernel d n beta z <=
      isingTorusTwoPoint (k := k) beta 0 (isingSiteToDyadicTorus k z) := by
  by_cases hz : z = 0
  · subst z
    rw [currentContinuityFreeBoxPairKernel, if_pos rfl]
    rw [show isingSiteToDyadicTorus k (0 : Site d) = 0 by
      exact isingSiteToDyadicTorus_origin]
    rw [isingTorusTwoPoint_eq_twoPointJ_unitEdge, twoPointJ_self]
  · have h0 : Percolation.origin d ∈ boxSV_boxF d n := by
      change Percolation.origin d ∈ (boxSV_boxF d n : Set (Site d))
      rw [boxSV_coe_boxF]
      exact origin_mem_box' n
    have hzS : z ∈ boxSV_boxF d n := by
      change z ∈ (boxSV_boxF d n : Set (Site d))
      rwa [boxSV_coe_boxF]
    let oS : {x // x ∈ boxSV_boxF d n} := ⟨Percolation.origin d, h0⟩
    let zS : {x // x ∈ boxSV_boxF d n} := ⟨z, hzS⟩
    have htorus := freeCorr_le_isingTorusTwoPoint
      (R := n) (boxSV_boxF d n) (by
        intro x hx
        change x ∈ (boxSV_boxF d n : Set (Site d)) at hx
        rwa [boxSV_coe_boxF] at hx) hside beta hbeta oS zS
    have hzo : z ≠ Percolation.origin d := by
      simpa [Percolation.origin] using hz
    calc
      currentContinuityFreeBoxPairKernel d n beta z =
          currentContinuityFreeBoxTwoPoint d n beta (Percolation.origin d) z := by
        rw [currentContinuityFreeBoxPairKernel, if_neg hz]
      _ = corrOriginInner d beta (boxSV_boxF d n) z :=
        (corrOriginInner_box_eq_currentContinuityFreeBoxTwoPoint
          d n beta z hzBox hzo).symm
      _ = freeCorr d beta (boxSV_boxF d n) oS zS := by
        simp only [corrOriginInner, dif_pos h0, dif_pos hzS]
        rfl
      _ <= isingTorusTwoPoint beta
          (isingSiteToDyadicTorus k (Percolation.origin d))
          (isingSiteToDyadicTorus k z) := htorus
      _ = isingTorusTwoPoint beta 0 (isingSiteToDyadicTorus k z) := by
        rw [isingSiteToDyadicTorus_origin]



theorem currentContinuityFreeBoxPositiveCubeAverage_le_isingTorus
    (beta : Real) (hbeta : 0 <= beta) (m n k : Nat) (hmn : m <= n)
    (hside : 2 * (n + 1) < isingDyadicSide k) :
    currentContinuityFreeBoxPositiveCubeAverage d n beta m <=
      finiteTorusBlockDifferenceAverage
        (fun z : IsingDyadicTorus d k => isingTorusTwoPoint beta 0 z)
        (isingTorusPositiveCube d m k) := by
  have hcubeSide : 2 * m < isingDyadicSide k := by omega
  have hinj : Set.InjOn (isingSiteToDyadicTorus k)
      (isingPositiveCube d m : Set (Site d)) :=
    isingSiteToDyadicTorus_injectiveOn_finset
      (isingPositiveCube d m) (isingPositiveCube_subset_box d m) hcubeSide
  rw [show isingTorusPositiveCube d m k =
      (isingPositiveCube d m).image (isingSiteToDyadicTorus k) by rfl]
  rw [finiteTorusBlockDifferenceAverage_image _ _ _ hinj]
  unfold currentContinuityFreeBoxPositiveCubeAverage
    finiteTorusBlockDifferenceAverage
  gcongr with a ha b hb
  rw [← isingSiteToDyadicTorus_sub]
  exact currentContinuityFreeBoxPairKernel_le_isingTorus
    beta hbeta n k hside (b - a)
      (box_mono d hmn (isingPositiveCube_difference_mem_box ha hb))



theorem exists_currentContinuityFreePositiveCubeAverage_le_power_subcritical
    (hd : 2 < d) :
    ∃ C : Real, 0 < C ∧ ∀ (beta : Real), 0 < beta ->
      beta < IsingFK.betaC (magnetization d) -> ∀ m : Nat, 2 <= m ->
        currentContinuityFreePositiveCubeAverage d beta m <=
          (1 / beta) * (C / (m : Real) ^ (d - 2)) := by
  obtain ⟨C, hC, hgreen⟩ :=
    exists_isingTorusPositiveCube_green_le_power hd
  refine ⟨C, hC, ?_⟩
  intro beta hbeta hlt m hm
  have hlim := currentContinuityFreeBoxPositiveCubeAverage_tendsto
    (d := d) beta hbeta.le m
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop m] with n hmn
  apply le_of_forall_pos_le_add
  intro epsilon hepsilon
  have hside : ∀ᶠ k : Nat in atTop,
      2 * (n + 1) < isingDyadicSide k := by
    have htendsto : Tendsto isingDyadicSide atTop atTop := by
      unfold isingDyadicSide
      rw [Filter.tendsto_add_atTop_iff_nat]
      exact tendsto_pow_atTop_atTop_of_one_lt Nat.one_lt_two
    exact htendsto.eventually_gt_atTop (2 * (n + 1))
  have hzero := isingTorusZeroMode_eventually_small_subcritical
    (d := d) (by omega) beta hbeta.le hlt epsilon hepsilon
  have hall := (hgreen m hm).and (hside.and hzero)
  obtain ⟨k, hkGreen, hkSide, hkZero⟩ := hall.exists
  have htorus := currentContinuityFreeBoxPositiveCubeAverage_le_isingTorus
    (d := d) beta hbeta.le m n k hmn hkSide
  have hgaussian := isingTorusTwoPoint_blockDifferenceAverage_le_green
    (d := d) (k := k) beta hbeta
    (isingTorusPositiveCube d m k)
    (isingTorusPositiveCube_nonempty (d := d) (k := k) (by omega))
  calc
    currentContinuityFreeBoxPositiveCubeAverage d n beta m <=
        finiteTorusBlockDifferenceAverage
          (fun z : IsingDyadicTorus d k => isingTorusTwoPoint beta 0 z)
          (isingTorusPositiveCube d m k) := htorus
    _ <= (finiteTorusFourierCoeff
            (fun z : IsingDyadicTorus d k => isingTorusTwoPoint beta 0 z) 0).re /
          Fintype.card (IsingDyadicTorus d k) +
        (1 / beta) * finiteTorusBlockDifferenceAverage
          (finiteTorusZeroModeGreen
            (isingTorusCharacterDispersion (d := d) (k := k)))
          (isingTorusPositiveCube d m k) := hgaussian
    _ <= (1 / beta) * (C / (m : Real) ^ (d - 2)) + epsilon := by
      have hcoef : 0 <= 1 / beta := by positivity
      have hrest := mul_le_mul_of_nonneg_left hkGreen hcoef
      linarith




theorem currentContinuityFreeTwoPoint_axis_le_positiveCubeAverage
    (hd : 2 <= d) (j : Fin d) (beta : Real) (hbeta : 0 < beta)
    (r m : Nat) (hr : 1 <= r) (hm : 1 <= m) (hdm : d * m <= r) :
    currentContinuityFreeTwoPoint d beta (Percolation.origin d)
        (Pi.single j (r : Int)) <=
      currentContinuityFreePositiveCubeAverage d beta m := by
  apply le_finiteTorusBlockDifferenceAverage
    (currentContinuityFreePairKernel d beta) (isingPositiveCube d m) _
    (isingPositiveCube_nonempty d m hm)
  intro a ha b hb
  exact currentContinuityFreeTwoPoint_axis_le_positiveCube_pairKernel
    hd j beta hbeta r m hr hdm ha hb



theorem exists_currentContinuityFreeTwoPoint_axis_le_power_subcritical
    (hd : 2 < d) :
    ∃ C : Real, 0 < C ∧ ∀ (beta : Real), 0 < beta ->
      beta < IsingFK.betaC (magnetization d) -> ∀ (j : Fin d) (r : Nat),
        2 * d <= r ->
        currentContinuityFreeTwoPoint d beta (Percolation.origin d)
            (Pi.single j (r : Int)) <=
          (1 / beta) * (C / (r : Real) ^ (d - 2)) := by
  obtain ⟨C0, hC0, hcube⟩ :=
    exists_currentContinuityFreePositiveCubeAverage_le_power_subcritical hd
  let C := C0 * (2 * (d : Real)) ^ (d - 2)
  have hC : 0 < C := mul_pos hC0 (pow_pos (by positivity) _)
  refine ⟨C, hC, ?_⟩
  intro beta hbeta hlt j r hr
  let m := r / d
  have hdpos : 0 < d := by omega
  have hm : 2 <= m := by
    dsimp [m]
    rw [Nat.le_div_iff_mul_le hdpos]
    omega
  have hdm : d * m <= r := by
    dsimp [m]
    simpa [mul_comm] using Nat.div_mul_le_self r d
  have haxis := currentContinuityFreeTwoPoint_axis_le_positiveCubeAverage
    (d := d) (by omega) j beta hbeta r m (by omega) (by omega) hdm
  have havg := hcube beta hbeta hlt m hm
  have hrlt : r < m * d + d := by
    dsimp [m]
    exact Nat.lt_div_mul_add hdpos
  have hrscale : r <= 2 * d * m := by
    calc
      r <= m * d + d := Nat.le_of_lt hrlt
      _ = (m + 1) * d := by ring
      _ <= (2 * m) * d := Nat.mul_le_mul_right d (by omega)
      _ = 2 * d * m := by ring
  have hmR : (0 : Real) < m := by exact_mod_cast (by omega : 0 < m)
  have hrR : (0 : Real) < r := by exact_mod_cast (by omega : 0 < r)
  have hscalePow : (r : Real) ^ (d - 2) <=
      (2 * (d : Real)) ^ (d - 2) * (m : Real) ^ (d - 2) := by
    have hscaleR : (r : Real) <= (2 * (d : Real)) * m := by
      exact_mod_cast hrscale
    calc
      (r : Real) ^ (d - 2) <=
          ((2 * (d : Real)) * m) ^ (d - 2) := by gcongr
      _ = (2 * (d : Real)) ^ (d - 2) * (m : Real) ^ (d - 2) :=
        mul_pow _ _ _
  have hfrac : C0 / (m : Real) ^ (d - 2) <=
      C / (r : Real) ^ (d - 2) := by
    rw [div_le_div_iff₀ (pow_pos hmR _) (pow_pos hrR _)]
    dsimp [C]
    nlinarith [mul_le_mul_of_nonneg_left hscalePow hC0.le]
  exact haxis.trans (havg.trans
    (mul_le_mul_of_nonneg_left hfrac (by positivity)))



theorem exists_criticalFreeTwoPoint_axis_le_power
    (hd : 2 < d) :
    ∃ C : Real, 0 < C ∧ ∀ (j : Fin d) (r : Nat), 2 * d <= r ->
      currentContinuityFreeTwoPoint d
          (IsingFK.betaC (magnetization d)) (Percolation.origin d)
          (Pi.single j (r : Int)) <=
        C / (r : Real) ^ (d - 2) := by
  obtain ⟨C0, hC0, hsub⟩ :=
    exists_currentContinuityFreeTwoPoint_axis_le_power_subcritical hd
  let betaC := IsingFK.betaC (magnetization d)
  have hbetaC : 0 < betaC := by
    dsimp [betaC]
    rw [isingFK_betaC_eq_tildeBetaCIsing (by omega : 2 <= d)]
    exact tildeBetaCIsing_pos (by omega)
  let C := (1 / betaC) * C0
  have hC : 0 < C := mul_pos (by positivity) hC0
  refine ⟨C, hC, ?_⟩
  intro j r hr
  let b : Nat -> Real := fun n => betaC - 1 / (n + 1 : Real)
  have hb : Tendsto b atTop (nhds betaC) := by
    simpa [b] using (tendsto_const_nhds.sub
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : Nat => (1 : Real) / (n + 1)) atTop (nhds 0)))
  have hleft := currentContinuityFreeTwoPoint_tendsto_fromBelow
    betaC hbetaC (Percolation.origin d) (Pi.single j (r : Int))
  have hright : Tendsto
      (fun n => (1 / b n) * (C0 / (r : Real) ^ (d - 2))) atTop
      (nhds (C / (r : Real) ^ (d - 2))) := by
    convert (tendsto_const_nhds.div hb (ne_of_gt hbetaC)).mul_const
      (C0 / (r : Real) ^ (d - 2)) using 1 <;> simp [C] <;> ring
  apply le_of_tendsto_of_tendsto hleft hright
  have hbpos : ∀ᶠ n in atTop, 0 < b n :=
    (tendsto_order.mp hb).1 0 hbetaC
  filter_upwards [hbpos] with n hn
  exact hsub (b n) hn (by
    dsimp [b, betaC]
    have hpos : 0 < (1 / (n + 1 : Real)) := by positivity
    linarith) j r hr



theorem exists_criticalFreeTwoPoint_shell_le_power
    (hd : 2 < d) :
    ∃ C : Real, 0 < C ∧ ∀ (r : Nat), 2 * d <= r ->
      ∀ x ∈ boxSV_vbF d r,
        currentContinuityFreeTwoPoint d
            (IsingFK.betaC (magnetization d)) (Percolation.origin d) x <=
          C / (r : Real) ^ (d - 2) := by
  obtain ⟨C, hC, haxis⟩ := exists_criticalFreeTwoPoint_axis_le_power hd
  refine ⟨C, hC, ?_⟩
  intro r hr x hx
  have hbetaC : 0 <= IsingFK.betaC (magnetization d) := by
    rw [isingFK_betaC_eq_tildeBetaCIsing (by omega : 2 <= d)]
    exact (tildeBetaCIsing_pos (by omega)).le
  have hshell := currentContinuityFreeTwoPoint_shell_le_axis
    (d := d) (by omega) (IsingFK.betaC (magnetization d)) hbetaC
      r (by omega) x hx
  let j : Fin d := ⟨0, by omega⟩
  have hcritical : criticalAxisSite (by omega) r =
      (Pi.single j (r : Int) : Site d) := by
    funext a
    by_cases ha : a = j
    · subst a
      simp [criticalAxisSite, j]
    · simp [criticalAxisSite, j, ha]
  rw [hcritical] at hshell
  exact hshell.trans (haxis j r hr)




theorem criticalFreeTwoPoint_shell_powerBounds
    (hd : 2 < d) :
    ∃ C : Real, 0 < C ∧ ∀ (r : Nat), 2 * d <= r ->
      ∀ x ∈ boxSV_vbF d r,
        1 / (4 * d ^ 2 * Real.tanh (IsingFK.betaC (magnetization d)) *
              (2 * ((d * r : Nat) : Real) + 1) ^ (d - 1)) <=
          currentContinuityFreeTwoPoint d
            (IsingFK.betaC (magnetization d)) (Percolation.origin d) x ∧
        currentContinuityFreeTwoPoint d
            (IsingFK.betaC (magnetization d)) (Percolation.origin d) x <=
          C / (r : Real) ^ (d - 2) := by
  obtain ⟨C, hC, hupper⟩ := exists_criticalFreeTwoPoint_shell_le_power hd
  refine ⟨C, hC, ?_⟩
  intro r hr x hx
  exact ⟨criticalBoundaryTwoPoint_powerLower (by omega) (by omega) x hx,
    hupper r hr x hx⟩

end StatMech.FrontierA
