/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Sharpness.MeanfieldIsingFull
import Code.Sharpness.MeanfieldIsingIntegrated
import Code.Sharpness.IsingSharpnessUnconditional
import Code.IsingFK.PottsCriticalCorrespondence

open Finset Filter Set Topology
open scoped BigOperators

namespace StatMech.FrontierA

open Lattice Percolation Sharpness Ising

theorem continuous_freeCorr_beta (d : Nat) (S : Finset (Site d))
    (a b : {v // v ∈ S}) :
    Continuous (fun beta ↦ freeCorr d beta S a b) := by
  by_cases hab : a = b
  · simpa [freeCorr, hab] using
      (continuous_const : Continuous (fun _ : Real ↦ (1 : Real)))
  · simp only [freeCorr, if_neg hab]
    exact continuous_isingExpectation_beta (graphS d S) 0
      (spinProd {a, b})

theorem continuous_corrOriginInner_beta
    (d : Nat) (S : Finset (Site d)) (x : Site d) :
    Continuous (fun beta ↦ corrOriginInner d beta S x) := by
  classical
  unfold corrOriginInner
  split
  · split
    · exact continuous_freeCorr_beta d S _ _
    · exact continuous_const
  · exact continuous_const

theorem continuous_phiIsing_beta (d : Nat) (S : Finset (Site d)) :
    Continuous (fun beta ↦ phiIsing d beta S) := by
  unfold phiIsing
  have htanh : Continuous Real.tanh := by
    rw [show Real.tanh = fun x ↦ Real.sinh x / Real.cosh x by
      funext x
      exact Real.tanh_eq_sinh_div_cosh x]
    exact Real.continuous_sinh.div Real.continuous_cosh
      (fun x ↦ (Real.cosh_pos x).ne')
  exact htanh.mul (continuous_finsetSum (boundaryEdges d S) fun e _ ↦
    continuous_corrOriginInner_beta d S e.1)




theorem phiIsing_ge_one_at_tildeBetaC
    (d : Nat) (hbdd : BddAbove (tildeBetaCIsingSet d))
    (S : Finset (Site d)) (hS : Percolation.origin d ∈ S) :
    1 ≤ phiIsing d (tildeBetaCIsing d) S := by
  have hzero : (0 : Real) ∈ tildeBetaCIsingSet d := by
    refine ⟨le_rfl, {Percolation.origin d}, by simp, ?_⟩
    simp [phiIsing]
  have hcrit0 : 0 ≤ tildeBetaCIsing d := by
    unfold tildeBetaCIsing
    exact le_csSup hbdd hzero
  let b : Nat → Real := fun n ↦
    tildeBetaCIsing d + 1 / (n + 1 : Real)
  have hb : Tendsto b atTop (nhds (tildeBetaCIsing d)) := by
    simpa only [b, add_zero] using
      (tendsto_const_nhds.add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real)))
  have hphi : Tendsto (fun n ↦ phiIsing d (b n) S) atTop
      (nhds (phiIsing d (tildeBetaCIsing d) S)) :=
    (continuous_phiIsing_beta d S).tendsto _ |>.comp hb
  apply ge_of_tendsto' hphi
  intro n
  have hfrac : 0 < (1 : Real) / (n + 1) := by positivity
  have hb0 : 0 ≤ b n := by
    dsimp only [b]
    linarith
  have hbcrit : tildeBetaCIsing d < b n := by
    dsimp only [b]
    linarith
  exact si4_phiIsing_ge_one_above_tildeBc d (b n) hb0 hbdd hbcrit S hS



theorem isingBetaC_eq_of_strict_transition
    (d : Nat) (t : Real) (ht : 0 < t) (hbcpos : 0 < Ising.betaC d)
    (hbelow : ∀ beta, 0 < beta → beta < t → magnetization d beta = 0)
    (habove : ∀ beta, t < beta → 0 < magnetization d beta) :
    Ising.betaC d = t := by
  let S := Ising.positiveMagnetizationSet d
  have hne : S.Nonempty := by
    refine ⟨t + 1, ?_⟩
    exact ⟨by linarith, habove (t + 1) (by linarith)⟩
  have hbdd : BddBelow S := by
    refine ⟨0, ?_⟩
    intro beta hbeta
    exact hbeta.1
  have hlower : t ≤ sInf S := by
    apply le_csInf hne
    intro beta hbeta
    by_contra hnot
    have hbt : beta < t := lt_of_not_ge hnot
    have hbpos : 0 < beta := by
      rcases hbeta.1.eq_or_lt with hzero | hpos
      · have hle : Ising.betaC d ≤ beta := by
          unfold Ising.betaC
          exact csInf_le hbdd hbeta
        rw [← hzero] at hle
        exact (not_lt_of_ge hle hbcpos).elim
      · exact hpos
    have hz := hbelow beta hbpos hbt
    exact (lt_irrefl 0) (hz ▸ hbeta.2)
  have hupper : sInf S ≤ t := by
    let b : Nat → Real := fun n ↦ t + 1 / (n + 1 : Real)
    have hb : Tendsto b atTop (nhds t) := by
      simpa only [b, add_zero] using
        (tendsto_const_nhds.add
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real)))
    apply ge_of_tendsto' hb
    intro n
    apply csInf_le hbdd
    refine ⟨by dsimp only [b]; positivity, ?_⟩
    apply habove
    dsimp only [b]
    have hfrac : 0 < (1 : Real) / (n + 1) := by positivity
    linarith
  unfold Ising.betaC
  exact le_antisymm hupper hlower



theorem isingFK_betaC_eq_tildeBetaCIsing
    {d : Nat} (hd : 2 ≤ d) :
    IsingFK.betaC (magnetization d) = tildeBetaCIsing d := by
  obtain ⟨t, ht, hbelow, habove⟩ :=
    IsingFK.ising_transition_unconditional_of_two_le hd
  have hSup : IsingFK.betaC (magnetization d) = t :=
    IsingFK.betaC_eq_of_strict_transition
      (magnetization d) t ht hbelow habove
  have hbdd := tildeBetaCIsingSet_bddAbove (d := d) hd
  have hcrit := tildeBetaCIsing_pos (d := d) hd
  have hsqrt : ∀ beta, tildeBetaCIsing d ≤ beta →
      Real.sqrt (1 - (tildeBetaCIsing d / beta) ^ 2) ≤
        magnetization d beta :=
    fun beta hbeta ↦
      sct_magnetization_meanfield_lower_bound_integrated d hbdd hcrit hbeta
  have hEq : Ising.betaC d = tildeBetaCIsing d :=
    bc_eq_ising_of_sqrt_and_susceptibility (d := d) (by omega) hsqrt
  have hInf : Ising.betaC d = t :=
    isingBetaC_eq_of_strict_transition d t ht (by rw [hEq]; exact hcrit)
      hbelow habove
  calc
    IsingFK.betaC (magnetization d) = t := hSup
    _ = Ising.betaC d := hInf.symm
    _ = tildeBetaCIsing d := hEq



theorem phiIsing_ge_one_at_isingFK_betaC
    {d : Nat} (hd : 2 ≤ d) (S : Finset (Site d))
    (hS : Percolation.origin d ∈ S) :
    1 ≤ phiIsing d (IsingFK.betaC (magnetization d)) S := by
  rw [isingFK_betaC_eq_tildeBetaCIsing hd]
  exact phiIsing_ge_one_at_tildeBetaC d
    (tildeBetaCIsingSet_bddAbove (d := d) hd) S hS

end StatMech.FrontierA
