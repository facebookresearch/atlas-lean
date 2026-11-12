/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierB.CurrentContinuityReduction
import Code.FrontierB.FreeEvenHomogeneity
import Code.IsingFK.CorrelationMonotone

open Filter MeasureTheory Set Topology

namespace StatMech.FrontierB

open Ising Lattice Percolation Sharpness

variable {d : Nat}

noncomputable def currentContinuityFreeBoxTwoPoint
    (d n : Nat) (beta : Real) (x y : Site d) : Real :=
  ∫ omega, spinProd ({x, y} : Finset (Site d)) omega
    ∂(freeMeasure d n beta 0 : Measure (ConfigSpace (Site d)))

theorem continuous_currentContinuityFreeBoxTwoPoint
    (n : Nat) (x y : Site d)
    (hxy : ({x, y} : Finset (Site d)) ⊆ Ising.boxFinset d n) :
    Continuous (fun beta =>
      currentContinuityFreeBoxTwoPoint d n beta x y) := by
  have heq : (fun beta => currentContinuityFreeBoxTwoPoint d n beta x y) =
      fun beta => isingExpectation (sctBoxGraph d n) beta 0
        (spinProd (boxSpinSupport d n ({x, y} : Finset (Site d)))) := by
    funext beta
    unfold currentContinuityFreeBoxTwoPoint
    rw [integral_freeMeasure_spinProd d n beta 0 ({x, y} : Finset (Site d))]
    intro z hz
    exact Ising.mem_boxFinset.mp (hxy hz)
  rw [heq, continuous_iff_continuousAt]
  intro beta
  exact (IsingFK.corr_hasDerivAt (sctBoxGraph d n) 0 beta
    (boxSpinSupport d n ({x, y} : Finset (Site d)))).continuousAt

theorem currentContinuityFreeBoxTwoPoint_mono_beta
    {beta gamma : Real} (hbeta : 0 ≤ beta) (hbg : beta ≤ gamma)
    (n : Nat) (x y : Site d)
    (hxy : ({x, y} : Finset (Site d)) ⊆ Ising.boxFinset d n) :
    currentContinuityFreeBoxTwoPoint d n beta x y ≤
      currentContinuityFreeBoxTwoPoint d n gamma x y := by
  unfold currentContinuityFreeBoxTwoPoint
  rw [integral_freeMeasure_spinProd d n beta 0 ({x, y} : Finset (Site d)),
    integral_freeMeasure_spinProd d n gamma 0 ({x, y} : Finset (Site d))]
  · exact IsingFK.corr_monotone (sctBoxGraph d n) 0 le_rfl
      (boxSpinSupport d n ({x, y} : Finset (Site d)))
      hbeta (le_trans hbeta hbg) hbg
  · intro z hz
    exact Ising.mem_boxFinset.mp (hxy hz)
  · intro z hz
    exact Ising.mem_boxFinset.mp (hxy hz)

theorem currentContinuityFreeBoxTwoPoint_le_freeTwoPoint
    (beta : Real) (hbeta : 0 ≤ beta)
    (n : Nat) (x y : Site d)
    (hxy : ({x, y} : Finset (Site d)) ⊆ Ising.boxFinset d n) :
    currentContinuityFreeBoxTwoPoint d n beta x y ≤
      currentContinuityFreeTwoPoint d beta x y := by
  let A : Finset (Site d) := {x, y}
  let f : Nat → Real := fun m =>
    currentContinuityFreeBoxTwoPoint d m beta x y
  have hlim : Tendsto f atTop
      (nhds (currentContinuityFreeTwoPoint d beta x y)) := by
    simpa [f, A, currentContinuityFreeBoxTwoPoint,
      currentContinuityFreeTwoPoint] using
      (integral_freeMeasure_spinProd_tendsto_freeState d beta hbeta A)
  apply ge_of_tendsto hlim
  filter_upwards [eventually_ge_atTop n] with m hnm
  unfold f currentContinuityFreeBoxTwoPoint
  rw [integral_freeMeasure_spinProd d n beta 0 A,
    integral_freeMeasure_spinProd d m beta 0 A]
  · exact isingExpectation_boxSpinSupport_mono d hnm beta hbeta A
      (fun z hz => Ising.mem_boxFinset.mp (hxy hz))
  · intro z hz
    exact box_mono d hnm (Ising.mem_boxFinset.mp (hxy hz))
  · intro z hz
    exact Ising.mem_boxFinset.mp (hxy hz)

theorem currentContinuityFreeTwoPoint_mono_beta
    {beta gamma : Real} (hbeta : 0 ≤ beta) (hbg : beta ≤ gamma)
    (x y : Site d) :
    currentContinuityFreeTwoPoint d beta x y ≤
      currentContinuityFreeTwoPoint d gamma x y := by
  let A : Finset (Site d) := {x, y}
  obtain ⟨N, hAN⟩ := Lattice.finite_subset_box
    (↑A : Set (Site d)) A.finite_toSet
  have hlimBeta := integral_freeMeasure_spinProd_tendsto_freeState
    d beta hbeta A
  have hlimGamma := integral_freeMeasure_spinProd_tendsto_freeState
    d gamma (le_trans hbeta hbg) A
  apply le_of_tendsto_of_tendsto hlimBeta hlimGamma
  filter_upwards [eventually_ge_atTop N] with n hn
  apply currentContinuityFreeBoxTwoPoint_mono_beta hbeta hbg n x y
  intro z hz
  rw [Ising.mem_boxFinset]
  exact box_mono d hn (hAN hz)



theorem currentContinuityFreeTwoPoint_tendsto_fromBelow
    (beta0 : Real) (hbeta0 : 0 < beta0) (x y : Site d) :
    Tendsto
      (fun n : Nat => currentContinuityFreeTwoPoint d
        (beta0 - 1 / (n + 1 : Real)) x y)
      atTop (nhds (currentContinuityFreeTwoPoint d beta0 x y)) := by
  let b : Nat → Real := fun n => beta0 - 1 / (n + 1 : Real)
  let L := currentContinuityFreeTwoPoint d beta0 x y
  have hb : Tendsto b atTop (nhds beta0) := by
    simpa [b] using (tendsto_const_nhds.sub
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : Nat => (1 : Real) / (n + 1)) atTop (nhds 0)))
  rw [tendsto_order]
  constructor
  · intro a ha
    let A : Finset (Site d) := {x, y}
    have hvol := integral_freeMeasure_spinProd_tendsto_freeState
      d beta0 hbeta0.le A
    have halow : ∀ᶠ n in atTop,
        a < currentContinuityFreeBoxTwoPoint d n beta0 x y := by
      simpa [currentContinuityFreeBoxTwoPoint,
        currentContinuityFreeTwoPoint, L, A] using
        (tendsto_order.mp hvol).1 a ha
    obtain ⟨N, hAN⟩ := Lattice.finite_subset_box
      (↑A : Set (Site d)) A.finite_toSet
    obtain ⟨n, hnN, han⟩ : ∃ n ≥ N,
        a < currentContinuityFreeBoxTwoPoint d n beta0 x y := by
      have hevent := halow.and (eventually_ge_atTop N)
      obtain ⟨n, han, hnN⟩ := hevent.exists
      exact ⟨n, hnN, han⟩
    have hAn : A ⊆ Ising.boxFinset d n := by
      intro z hz
      rw [Ising.mem_boxFinset]
      exact box_mono d hnN (hAN hz)
    have hfiniteBase :=
      (continuous_currentContinuityFreeBoxTwoPoint n x y hAn).tendsto beta0
    have hfinite : Tendsto
        (fun m => currentContinuityFreeBoxTwoPoint d n (b m) x y)
        atTop (nhds (currentContinuityFreeBoxTwoPoint d n beta0 x y)) :=
      hfiniteBase.comp hb
    have hbelow : ∀ᶠ m in atTop, a <
        currentContinuityFreeBoxTwoPoint d n (b m) x y :=
      (tendsto_order.mp hfinite).1 a han
    have hbpos : ∀ᶠ m in atTop, 0 ≤ b m := by
      filter_upwards [(tendsto_order.mp hb).1 0 hbeta0] with m hm
      exact hm.le
    filter_upwards [hbelow, hbpos] with m ham hbm
    exact ham.trans_le
      (currentContinuityFreeBoxTwoPoint_le_freeTwoPoint (b m) hbm n x y hAn)
  · intro a ha
    have hbpos : ∀ᶠ n in atTop, 0 ≤ b n := by
      filter_upwards [(tendsto_order.mp hb).1 0 hbeta0] with n hn
      exact hn.le
    have hble : ∀ n, b n ≤ beta0 := by
      intro n
      dsimp [b]
      have : 0 ≤ (1 / (n + 1 : Real)) := by positivity
      linarith
    filter_upwards [hbpos] with n hbn
    exact (currentContinuityFreeTwoPoint_mono_beta hbn (hble n) x y).trans_lt ha




theorem currentContinuityFreeLROZero_of_subcritical_bound
    (beta0 : Real) (hbeta0 : 0 < beta0)
    (majorant : Site d → Real)
    (hbound : ∀ beta, 0 < beta → beta < beta0 → ∀ x,
      |currentContinuityFreeTwoPoint d beta (Percolation.origin d) x| ≤
        majorant x)
    (hdecay : ∀ epsilon : Real, 0 < epsilon → ∃ R : Nat,
      ∀ x : Site d, x ∉ box d R → majorant x < epsilon) :
    CurrentContinuityFreeLROZero d beta0 := by
  intro epsilon hepsilon
  obtain ⟨R, hR⟩ := hdecay epsilon hepsilon
  refine ⟨R, ?_⟩
  intro x hx
  let b : Nat → Real := fun n => beta0 - 1 / (n + 1 : Real)
  have hleft := currentContinuityFreeTwoPoint_tendsto_fromBelow
    beta0 hbeta0 (Percolation.origin d) x
  have habs : Tendsto
      (fun n => |currentContinuityFreeTwoPoint d (b n)
        (Percolation.origin d) x|) atTop
      (nhds |currentContinuityFreeTwoPoint d beta0
        (Percolation.origin d) x|) := by
    simpa [b] using hleft.abs
  have hb : Tendsto b atTop (nhds beta0) := by
    simpa [b] using (tendsto_const_nhds.sub
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : Nat => (1 : Real) / (n + 1)) atTop (nhds 0)))
  have hbpos : ∀ᶠ n in atTop, 0 < b n :=
    (tendsto_order.mp hb).1 0 hbeta0
  have hble : ∀ n, b n < beta0 := by
    intro n
    dsimp [b]
    have : 0 < (1 / (n + 1 : Real)) := by positivity
    linarith
  have hevent : ∀ᶠ n in atTop,
      |currentContinuityFreeTwoPoint d (b n)
        (Percolation.origin d) x| ≤ majorant x := by
    filter_upwards [hbpos] with n hn
    exact hbound (b n) hn (hble n) x
  have hcritical :
      |currentContinuityFreeTwoPoint d beta0
        (Percolation.origin d) x| ≤ majorant x :=
    le_of_tendsto habs hevent
  exact hcritical.trans_lt (hR x hx)

end StatMech.FrontierB
