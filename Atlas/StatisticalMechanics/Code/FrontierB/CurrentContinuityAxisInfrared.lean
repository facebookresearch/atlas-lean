/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingTorusSparseGreenDecay
import Code.FrontierA.IsingTorusEmbedding
import Code.FrontierB.CurrentContinuityFreeLeftContinuous
import Code.FrontierB.MixedCurrentAxisPersistence

open Filter Finset MeasureTheory Set Topology
open scoped BigOperators

namespace StatMech.FrontierB

open StatMech.FrontierA StatMech.Ising StatMech.Lattice
open StatMech.Percolation StatMech.Sharpness

variable {d : Nat}

private noncomputable def boxFinsetEquiv (d n : Nat) :
    sctBox d n ≃ {x // x ∈ Ising.boxFinset d n} where
  toFun x := ⟨x.1, Ising.mem_boxFinset.mpr x.2⟩
  invFun x := ⟨x.1, Ising.mem_boxFinset.mp x.2⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl

private theorem boxFinsetEquiv_adj (d n : Nat) (x y : sctBox d n) :
    (sctBoxGraph d n).Adj x y ↔
      (graphS d (Ising.boxFinset d n)).Adj
        (boxFinsetEquiv d n x) (boxFinsetEquiv d n y) := by
  rfl

set_option maxHeartbeats 800000 in

private theorem currentContinuityFreeBoxTwoPoint_eq_freeCorr
    (beta : Real) (n : Nat) (x y : Site d)
    (hx : x ∈ box d n) (hy : y ∈ box d n) (hxy : x ≠ y) :
    currentContinuityFreeBoxTwoPoint d n beta x y =
      freeCorr d beta (Ising.boxFinset d n)
        ⟨x, Ising.mem_boxFinset.mpr hx⟩
        ⟨y, Ising.mem_boxFinset.mpr hy⟩ := by
  let a : sctBox d n := ⟨x, hx⟩
  let b : sctBox d n := ⟨y, hy⟩
  letI : Fintype {z // z ∈ Ising.boxFinset d n} :=
    Finset.Subtype.fintype (Ising.boxFinset d n)
  rw [currentContinuityFreeBoxTwoPoint,
    integral_freeMeasure_spinProd d n beta 0 ({x, y} : Finset (Site d))]
  · have hrel := Ising.isingExpectation_spinProd_relabel
      (sctBoxGraph d n) (graphS d (Ising.boxFinset d n))
      (boxFinsetEquiv d n) (boxFinsetEquiv_adj d n) beta 0
      ({a, b} : Finset (sctBox d n))
    have hsupp : boxSpinSupport d n ({x, y} : Finset (Site d)) =
        ({a, b} : Finset (sctBox d n)) := by
      ext z
      simp only [boxSpinSupport, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (hz | hz)
        · exact Or.inl (Subtype.ext hz)
        · exact Or.inr (Subtype.ext hz)
      · rintro (rfl | rfl)
        · exact Or.inl rfl
        · exact Or.inr rfl
    have hmap : ({a, b} : Finset (sctBox d n)).map
        (boxFinsetEquiv d n).toEmbedding =
          ({⟨x, Ising.mem_boxFinset.mpr hx⟩,
            ⟨y, Ising.mem_boxFinset.mpr hy⟩} :
              Finset {z // z ∈ Ising.boxFinset d n}) := by
      ext z
      simp [a, b, boxFinsetEquiv]
    rw [hsupp]
    rw [hmap] at hrel
    rw [freeCorr, if_neg]
    · exact hrel
    · intro h
      exact hxy (congrArg Subtype.val h)
  · intro z hz
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy




theorem currentContinuityFreeBoxTwoPoint_le_isingTorusAxis
    (i : Fin d) (beta : Real) (hbeta : 0 ≤ beta)
    (n r k : Nat) (hrpos : 0 < r) (hrn : r ≤ n)
    (hside : 2 * (n + 1) < isingDyadicSide k) :
    currentContinuityFreeBoxTwoPoint d n beta (Percolation.origin d)
        (Pi.single i (-(r : Int))) ≤
      isingTorusTwoPoint (k := k) beta 0
        (isingTorusCoordinateShift i r) := by
  have hzero : Percolation.origin d ∈ box d n := origin_mem_box' n
  have hx : Pi.single i (-(r : Int)) ∈ box d n := by
    intro j
    by_cases hji : j = i
    · subst j
      simp
      exact hrn
    · simp [Pi.single_eq_of_ne hji]
  have hne : Percolation.origin d ≠ Pi.single i (-(r : Int)) := by
    intro h
    have hi := congrFun h i
    simp [Percolation.origin, hrpos.ne'] at hi
  rw [currentContinuityFreeBoxTwoPoint_eq_freeCorr beta n _ _ hzero hx hne]
  have htorus := freeCorr_le_isingTorusTwoPoint
    (S := Ising.boxFinset d n) (R := n)
    (fun _ hz => Ising.mem_boxFinset.mp hz) hside beta hbeta
    ⟨Percolation.origin d, Ising.mem_boxFinset.mpr hzero⟩
    ⟨Pi.single i (-(r : Int)), Ising.mem_boxFinset.mpr hx⟩
  rw [isingSiteToDyadicTorus_origin] at htorus
  have himage :
      isingSiteToDyadicTorus k (Pi.single i (-(r : Int))) =
        -isingTorusCoordinateShift i r := by
    funext j
    by_cases hji : j = i
    · subst j
      simp only [isingSiteToDyadicTorus, Pi.single_eq_same, Pi.neg_apply,
        isingTorusCoordinateShift_apply_same]
      simpa only [Int.cast_natCast] using
        (Int.cast_neg (R := ZMod (2 ^ (k + 2))) (r : Int))
    · simp only [isingSiteToDyadicTorus, Pi.single_eq_of_ne hji,
        Pi.neg_apply, isingTorusCoordinateShift_apply_of_ne i j hji]
      simpa only [neg_zero] using
        (Int.cast_zero (R := ZMod (2 ^ (k + 2))))
  rw [himage, isingTorusTwoPoint_origin_neg] at htorus
  exact htorus



theorem currentContinuityFreeTwoPoint_axis_le_of_eventually_torus_le
    (i : Fin d) (beta : Real) (hbeta : 0 ≤ beta)
    (r : Nat) (hr : 0 < r) (bound : Real)
    (hbound : ∀ᶠ k : Nat in atTop,
      isingTorusTwoPoint (k := k) beta 0
        (isingTorusCoordinateShift i r) ≤ bound) :
    currentContinuityFreeTwoPoint d beta (Percolation.origin d)
        (Pi.single i (-(r : Int))) ≤ bound := by
  let x : Site d := Pi.single i (-(r : Int))
  let A : Finset (Site d) := {Percolation.origin d, x}
  have hlim : Tendsto
      (fun n => currentContinuityFreeBoxTwoPoint d n beta
        (Percolation.origin d) x) atTop
      (nhds (currentContinuityFreeTwoPoint d beta
        (Percolation.origin d) x)) := by
    simpa [currentContinuityFreeBoxTwoPoint,
      currentContinuityFreeTwoPoint, A] using
      (integral_freeMeasure_spinProd_tendsto_freeState d beta hbeta A)
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop r] with n hrn
  have hside : ∀ᶠ k : Nat in atTop,
      2 * (n + 1) < isingDyadicSide k := by
    have htendsto : Tendsto isingDyadicSide atTop atTop := by
      unfold isingDyadicSide
      rw [Filter.tendsto_add_atTop_iff_nat]
      exact tendsto_pow_atTop_atTop_of_one_lt Nat.one_lt_two
    exact htendsto.eventually_gt_atTop (2 * (n + 1))
  obtain ⟨k, hkBound, hkSide⟩ := (hbound.and hside).exists
  exact (currentContinuityFreeBoxTwoPoint_le_isingTorusAxis
    i beta hbeta n r k hr hrn hkSide).trans hkBound



theorem currentContinuityFreeTwoPoint_axis_le_sparseGreenBound
    (hd : 2 < d) (beta : Real) (hbeta : 0 < beta)
    (hlt : beta < IsingFK.betaC (StatMech.Ising.magnetization d))
    (delta : Real) (hdelta : 0 < delta)
    (M : Real) (R : Nat)
    (hgreen : ∀ (i : Fin d) (spacing count : Nat), R < spacing →
      0 < count → ∀ᶠ k : Nat in atTop,
        finiteTorusBlockDifferenceAverage
            (finiteTorusZeroModeGreen
              (isingTorusCharacterDispersion (d := d) (k := k)))
            (isingTorusSparseAxisBlock i spacing count) ≤
          M / count + delta)
    (i : Fin d) (count r : Nat) (hcount : 2 ≤ count)
    (hrlarge : (R + 1) * (count - 1) ≤ r) :
    currentContinuityFreeTwoPoint d beta (Percolation.origin d)
        (Pi.single i (-(r : Int))) ≤
      delta + (1 / beta) * (M / count + delta) := by
  let spacing := r / (count - 1)
  let endpoint := (count - 1) * spacing
  have hdenom : 0 < count - 1 := by omega
  have hspacingLower : R + 1 ≤ spacing := by
    apply (Nat.le_div_iff_mul_le hdenom).2
    simpa [mul_comm] using hrlarge
  have hspacing : R < spacing := by omega
  have hspacingPos : 0 < spacing := by omega
  have hcountPos : 0 < count := by omega
  have hendpoint : endpoint ≤ r := by
    dsimp [endpoint, spacing]
    exact Nat.mul_div_le r (count - 1)
  have hrpos : 0 < r := by
    have : 0 < (R + 1) * (count - 1) := Nat.mul_pos (by omega) hdenom
    omega
  have hgreenEvent := hgreen i spacing count hspacing hcountPos
  have hzeroEvent := isingTorusZeroMode_eventually_small_subcritical
    (d := d) (by omega : 2 ≤ d) beta hbeta.le hlt delta hdelta
  have hhalf : ∀ᶠ k : Nat in atTop, r ≤ 2 ^ (k + 1) := by
    have htendsto : Tendsto (fun k : Nat => 2 ^ (k + 1)) atTop atTop := by
      rw [Filter.tendsto_add_atTop_iff_nat]
      exact tendsto_pow_atTop_atTop_of_one_lt Nat.one_lt_two
    exact htendsto.eventually_ge_atTop r
  have htorus : ∀ᶠ k : Nat in atTop,
      isingTorusTwoPoint (k := k) beta 0
          (isingTorusCoordinateShift i r) <
        delta + (1 / beta) * (M / count + delta) := by
    filter_upwards [hgreenEvent, hzeroEvent, hhalf] with k hgreenK hzeroK hhalfK
    have hmono := isingTorusTwoPoint_axis_antitone
      (k := k) i beta hbeta.le hendpoint hhalfK
    have hsparse :=
      isingTorusTwoPoint_sparseAxisEndpoint_le_greenBlockAverage
        (k := k) i beta hbeta spacing count hcountPos
          (hendpoint.trans hhalfK)
    calc
      isingTorusTwoPoint (k := k) beta 0
          (isingTorusCoordinateShift i r) ≤
        isingTorusTwoPoint (k := k) beta 0
          (isingTorusCoordinateShift i endpoint) := hmono
      _ ≤
          (finiteTorusFourierCoeff
              (fun z : IsingDyadicTorus d k =>
                isingTorusTwoPoint beta 0 z) 0).re /
            Fintype.card (IsingDyadicTorus d k) +
          (1 / beta) * finiteTorusBlockDifferenceAverage
            (finiteTorusZeroModeGreen
              (isingTorusCharacterDispersion (d := d) (k := k)))
            (isingTorusSparseAxisBlock i spacing count) := hsparse
      _ < delta + (1 / beta) * (M / count + delta) := by
        calc
          (finiteTorusFourierCoeff
                (fun z : IsingDyadicTorus d k =>
                  isingTorusTwoPoint beta 0 z) 0).re /
              Fintype.card (IsingDyadicTorus d k) +
            (1 / beta) * finiteTorusBlockDifferenceAverage
              (finiteTorusZeroModeGreen
                (isingTorusCharacterDispersion (d := d) (k := k)))
              (isingTorusSparseAxisBlock i spacing count) <
            delta + (1 / beta) * finiteTorusBlockDifferenceAverage
              (finiteTorusZeroModeGreen
                (isingTorusCharacterDispersion (d := d) (k := k)))
              (isingTorusSparseAxisBlock i spacing count) := by
            linarith
          _ ≤ delta + (1 / beta) * (M / count + delta) := by
            gcongr
  have htorusLe : ∀ᶠ k : Nat in atTop,
      isingTorusTwoPoint (k := k) beta 0
          (isingTorusCoordinateShift i r) ≤
        delta + (1 / beta) * (M / count + delta) := by
    filter_upwards [htorus] with k hk
    exact hk.le
  exact currentContinuityFreeTwoPoint_axis_le_of_eventually_torus_le
    i beta hbeta.le r hrpos
      (delta + (1 / beta) * (M / count + delta)) htorusLe

theorem currentContinuityAxisSite_eq_negative_single
    (hd : 1 ≤ d) (r : Nat) :
    currentContinuityAxisSite hd r =
      Pi.single (⟨0, hd⟩ : Fin d) (-(r : Int)) := by
  funext j
  by_cases hj : j = (⟨0, hd⟩ : Fin d)
  · subst j
    simp [currentContinuityAxisSite, FK.freeAxisTranslationPower,
      smul_site_apply, Percolation.origin]
  · simp [currentContinuityAxisSite, FK.freeAxisTranslationPower,
      smul_site_apply, Percolation.origin, hj]

theorem currentContinuityFreeTwoPoint_negativeAxis_nonneg
    (i : Fin d) (beta : Real) (hbeta : 0 ≤ beta)
    (r : Nat) (hr : 0 < r) :
    0 ≤ currentContinuityFreeTwoPoint d beta (Percolation.origin d)
      (Pi.single i (-(r : Int))) := by
  let x : Site d := Pi.single i (-(r : Int))
  let A : Finset (Site d) := {Percolation.origin d, x}
  have hlim : Tendsto
      (fun n => currentContinuityFreeBoxTwoPoint d n beta
        (Percolation.origin d) x) atTop
      (nhds (currentContinuityFreeTwoPoint d beta
        (Percolation.origin d) x)) := by
    simpa [currentContinuityFreeBoxTwoPoint,
      currentContinuityFreeTwoPoint, A] using
      (integral_freeMeasure_spinProd_tendsto_freeState d beta hbeta A)
  change 0 ≤ currentContinuityFreeTwoPoint d beta
    (Percolation.origin d) x
  apply ge_of_tendsto hlim
  filter_upwards [eventually_ge_atTop r] with n hrn
  have hzero : Percolation.origin d ∈ box d n := origin_mem_box' n
  have hx : x ∈ box d n := by
    intro j
    by_cases hji : j = i
    · subst j
      simp [x]
      exact hrn
    · simp [x, Pi.single_eq_of_ne hji]
  have hne : Percolation.origin d ≠ x := by
    intro h
    have hi := congrFun h i
    simp [x, Percolation.origin, hr.ne'] at hi
  rw [currentContinuityFreeBoxTwoPoint_eq_freeCorr beta n _ _ hzero hx hne]
  exact freeCorr_nonneg d hbeta (Ising.boxFinset d n) _ _




theorem currentContinuityFreeAxisLROZero_at_betaC
    (hd : 2 < d)
    (hbetaC : 0 < IsingFK.betaC (StatMech.Ising.magnetization d)) :
    CurrentContinuityFreeAxisLROZero d (by omega)
      (IsingFK.betaC (StatMech.Ising.magnetization d)) := by
  let betaC := IsingFK.betaC (StatMech.Ising.magnetization d)
  let axis : Fin d := ⟨0, by omega⟩
  intro epsilon hepsilon
  let delta : Real := epsilon * betaC / (8 * (betaC + 1))
  have hdenom : 0 < 8 * (betaC + 1) := by
    dsimp [betaC]
    positivity
  have hdelta : 0 < delta := by
    dsimp [delta, betaC]
    positivity
  obtain ⟨M, hM, R, hgreen⟩ :=
    isingTorusSparseGreenAverage_eventually_le hd delta hdelta
  obtain ⟨N, hN⟩ := exists_nat_gt (M / delta)
  let count := max 2 N
  have hcount : 2 ≤ count := le_max_left _ _
  have hcountPos : (0 : Real) < count := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hcount)
  have hratio : M / delta < (count : Real) := by
    exact hN.trans_le (by exact_mod_cast (le_max_right 2 N))
  have hMcount : M / (count : Real) < delta := by
    apply (div_lt_iff₀ hcountPos).2
    have hmul := (div_lt_iff₀ hdelta).mp hratio
    simpa [mul_comm] using hmul
  let K := (R + 1) * (count - 1)
  refine ⟨K, ?_⟩
  intro r hrK
  have hrpos : 0 < r := by
    have hcountSub : 0 < count - 1 := by omega
    have hKpos : 0 < K := by
      dsimp [K]
      exact Nat.mul_pos (by omega) hcountSub
    omega
  let b : Nat → Real := fun n => betaC - 1 / (n + 1 : Real)
  have hb : Tendsto b atTop (nhds betaC) := by
    simpa [b] using (tendsto_const_nhds.sub
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : Nat => (1 : Real) / (n + 1)) atTop (nhds 0)))
  have hbHalf : ∀ᶠ n : Nat in atTop, betaC / 2 < b n :=
    (tendsto_order.mp hb).1 (betaC / 2) (by
      dsimp [betaC]
      linarith)
  have hbLt : ∀ n : Nat, b n < betaC := by
    intro n
    dsimp [b]
    have : 0 < (1 / (n + 1 : Real)) := by positivity
    linarith
  let errorBound : Real :=
    delta + (2 / betaC) * (M / (count : Real) + delta)
  have herrorSmall : errorBound < epsilon := by
    have hsum : M / (count : Real) + delta < 2 * delta := by
      linarith
    have hfirst : errorBound < delta + (2 / betaC) * (2 * delta) := by
      dsimp [errorBound]
      gcongr
    have hdeltaEq : delta * (8 * (betaC + 1)) = epsilon * betaC := by
      dsimp [delta]
      have hne : betaC + 1 ≠ 0 := by
        dsimp [betaC]
        linarith
      field_simp [hne]
    have hscaled :
        betaC * (delta + (2 / betaC) * (2 * delta)) <
          betaC * epsilon := by
      have heq : betaC * (delta + (2 / betaC) * (2 * delta)) =
          delta * (betaC + 4) := by
        have hne : betaC ≠ 0 := by
          dsimp [betaC]
          exact hbetaC.ne'
        field_simp [hne]
        ring
      rw [heq]
      calc
        delta * (betaC + 4) < delta * (8 * (betaC + 1)) := by
          nlinarith
        _ = epsilon * betaC := hdeltaEq
        _ = betaC * epsilon := by ring
    exact hfirst.trans (lt_of_mul_lt_mul_left hscaled (by
      dsimp [betaC]
      exact hbetaC.le))
  have hleft := currentContinuityFreeTwoPoint_tendsto_fromBelow
    (d := d) betaC (by simpa [betaC] using hbetaC)
      (Percolation.origin d) (Pi.single axis (-(r : Int)))
  have hevent : ∀ᶠ n : Nat in atTop,
      currentContinuityFreeTwoPoint d (b n) (Percolation.origin d)
          (Pi.single axis (-(r : Int))) ≤ errorBound := by
    filter_upwards [hbHalf] with n hbn
    have hbpos : 0 < b n := (half_pos (by
      simpa [betaC] using hbetaC)).trans hbn
    have hsparse := currentContinuityFreeTwoPoint_axis_le_sparseGreenBound
      hd (b n) hbpos (hbLt n) delta hdelta M R hgreen axis count r
        hcount (by simpa [K] using hrK)
    have hinv : 1 / b n ≤ 2 / betaC := by
      have hone := one_div_le_one_div_of_le
        (half_pos (by simpa [betaC] using hbetaC)) hbn.le
      have heq : 1 / (betaC / 2) = 2 / betaC := by
        have hne : betaC ≠ 0 := by
          simpa [betaC] using hbetaC.ne'
        field_simp [hne]
      rwa [heq] at hone
    exact hsparse.trans (by
      dsimp [errorBound]
      gcongr)
  have hcritical :
      currentContinuityFreeTwoPoint d betaC (Percolation.origin d)
          (Pi.single axis (-(r : Int))) ≤ errorBound :=
    le_of_tendsto hleft hevent
  have hnonneg := currentContinuityFreeTwoPoint_negativeAxis_nonneg
    axis betaC (by simpa [betaC] using hbetaC.le) r hrpos
  rw [currentContinuityAxisSite_eq_negative_single (d := d) (by omega) r]
  change |currentContinuityFreeTwoPoint d betaC (Percolation.origin d)
    (Pi.single axis (-(r : Int)))| < epsilon
  rw [abs_of_nonneg hnonneg]
  exact hcritical.trans_lt herrorSmall


theorem currentContinuityFreeAxisLROZero_at_isingCritical
    (hd : 2 < d) :
    CurrentContinuityFreeAxisLROZero d (by omega)
      (IsingFK.betaC (StatMech.Ising.magnetization d)) := by
  apply currentContinuityFreeAxisLROZero_at_betaC hd
  rw [isingFK_betaC_eq_tildeBetaCIsing (by omega : 2 ≤ d)]
  exact tildeBetaCIsing_pos (by omega : 2 ≤ d)

end StatMech.FrontierB
