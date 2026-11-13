/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingSurfaceTensionCriticalReduction
import Code.FrontierB.CurrentContinuityVaryingTemperature

open Filter MeasureTheory Set Topology

namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Lattice StatMech.Sharpness

noncomputable section





theorem magnetization_three_tendsto_at_isingBetaC
    (betaSeq : Nat -> Real)
    (hbeta : Tendsto betaSeq atTop (nhds (Ising.betaC 3))) :
    Tendsto (fun k => magnetization 3 (betaSeq k)) atTop (nhds 0) := by
  have hbdd := tildeBetaCIsingSet_bddAbove (d := 3) (by omega : 2 <= 3)
  have hcrit := tildeBetaCIsing_pos (d := 3) (by omega : 2 <= 3)
  have hsqrt : forall beta, tildeBetaCIsing 3 <= beta ->
      Real.sqrt (1 - (tildeBetaCIsing 3 / beta) ^ 2) <=
        magnetization 3 beta := fun beta hbeta' =>
    sct_magnetization_meanfield_lower_bound_integrated 3 hbdd hcrit hbeta'
  have hbcEq : Ising.betaC 3 = tildeBetaCIsing 3 :=
    bc_eq_ising_of_sqrt_and_susceptibility (d := 3) (by omega) hsqrt
  have hcriticalEq :
      IsingFK.betaC (magnetization 3) = Ising.betaC 3 := by
    rw [StatMech.FrontierA.isingFK_betaC_eq_tildeBetaCIsing
      (by omega : 2 <= 3), hbcEq]
  have hcritical :=
    StatMech.FrontierB.isingCritical_magnetization_zero_and_gibbs_unique
      (d := 3) (by omega)
  have hunique : forall (mu : Measure (ConfigSpace (Site 3)))
      [IsProbabilityMeasure mu],
      IsDLRState 3 (Ising.betaC 3) 0 mu ->
        mu = (minusState 3 (Ising.betaC 3) 0 :
          Measure (ConfigSpace (Site 3))) := by
    simpa only [hcriticalEq] using hcritical.2
  let mu : Nat -> ProbabilityMeasure (ConfigSpace (Site 3)) := fun k =>
    plusState 3 (betaSeq k) 0
  have hweak : WeakConvergesTo mu (minusState 3 (Ising.betaC 3) 0) := by
    apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨nu, phi, hphi, hnuWeak⟩ := prokhorov_seq_compact (mu ∘ ns)
    have hbetaSub : Tendsto (betaSeq ∘ ns ∘ phi) atTop
        (nhds (Ising.betaC 3)) :=
      hbeta.comp (hns.comp hphi.tendsto_atTop)
    have hdlr : IsDLRState 3 (Ising.betaC 3) 0
        (nu : Measure (ConfigSpace (Site 3))) := by
      apply StatMech.FrontierB.varyingDLRWeakLimit_isDLR
        (mu := mu ∘ ns ∘ phi) (betaSeq := betaSeq ∘ ns ∘ phi)
        (beta := Ising.betaC 3) (h := 0)
      · intro k
        exact psdlr_plusState_isDLR_uncond (betaSeq (ns (phi k))) 0
      · exact hbetaSub
      · simpa only [Function.comp_assoc] using hnuWeak
    have hnuMeasure : (nu : Measure (ConfigSpace (Site 3))) =
        (minusState 3 (Ising.betaC 3) 0 :
          Measure (ConfigSpace (Site 3))) :=
      hunique (nu : Measure (ConfigSpace (Site 3))) hdlr
    have hnu : nu = minusState 3 (Ising.betaC 3) 0 := by
      apply ProbabilityMeasure.toMeasure_injective
      exact hnuMeasure
    refine ⟨phi, ?_⟩
    simpa only [mu, Function.comp_assoc, hnu] using hnuWeak
  have hphase :
      (plusState 3 (Ising.betaC 3) 0 : Measure (ConfigSpace (Site 3))) =
        (minusState 3 (Ising.betaC 3) 0 :
          Measure (ConfigSpace (Site 3))) := by
    exact StatMech.FrontierB.plusState_eq_minusState_of_magnetization_eq_zero
      (Ising.betaC 3) (by rw [hbcEq]; exact hcrit.le)
        magnetization_three_isingBetaC_eq_zero
  have hlimit := hweak.tendsto_integral
    (spinBCF (StatMech.Percolation.origin 3))
  rw [← hphase] at hlimit
  simpa only [mu, integral_spinBCF_eq,
    magnetization_three_isingBetaC_eq_zero] using hlimit





theorem rectangularIsingSurfaceTension_critical_eq_zero_of_ordered_upper
    (hprism : forall beta, 0 < beta ->
      HasPrismCubicalSurfaceComparison beta)
    (hupper : forall beta, Ising.betaC 3 < beta ->
      rectangularIsingSurfaceTension beta <=
        2 * beta * (magnetization 3 beta) ^ 2) :
    rectangularIsingSurfaceTension (Ising.betaC 3) = 0 := by
  have hbdd := tildeBetaCIsingSet_bddAbove (d := 3) (by omega : 2 <= 3)
  have hcrit := tildeBetaCIsing_pos (d := 3) (by omega : 2 <= 3)
  have hsqrt : forall beta, tildeBetaCIsing 3 <= beta ->
      Real.sqrt (1 - (tildeBetaCIsing 3 / beta) ^ 2) <=
        magnetization 3 beta := fun beta hbeta =>
    sct_magnetization_meanfield_lower_bound_integrated 3 hbdd hcrit hbeta
  have hbcEq : Ising.betaC 3 = tildeBetaCIsing 3 :=
    bc_eq_ising_of_sqrt_and_susceptibility (d := 3) (by omega) hsqrt
  have hbetaC : 0 < Ising.betaC 3 := by rw [hbcEq]; exact hcrit
  let betaSeq : Nat -> Real := fun n =>
    Ising.betaC 3 + 1 / (n + 1 : Real)
  have hbetaSeq : Tendsto betaSeq atTop (nhds (Ising.betaC 3)) := by
    simpa only [betaSeq, add_zero] using
      (tendsto_const_nhds.add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real)))
  have hbetaSeqGt : forall n, Ising.betaC 3 < betaSeq n := by
    intro n
    dsimp only [betaSeq]
    have hpos : 0 < (1 : Real) / (n + 1) := by positivity
    linarith
  have hmag := magnetization_three_tendsto_at_isingBetaC betaSeq hbetaSeq
  have hrhs : Tendsto
      (fun n => 2 * betaSeq n * (magnetization 3 (betaSeq n)) ^ 2)
      atTop (nhds 0) := by
    have htwo : Tendsto (fun _ : Nat => (2 : Real)) atTop (nhds 2) :=
      tendsto_const_nhds
    have h := (htwo.mul hbetaSeq).mul (hmag.pow 2)
    simpa using h
  have hweak :=
    rectangularIsingSurfaceTension_hasWeakLowerBound_of_prismComparison hprism
  have hpoint : forall n,
      rectangularIsingSurfaceTension (Ising.betaC 3) <=
        2 * betaSeq n * (magnetization 3 (betaSeq n)) ^ 2 := by
    intro n
    have hinc := hweak (Ising.betaC 3) (betaSeq n) hbetaC
      (hbetaSeqGt n).le
    rw [magnetization_three_isingBetaC_eq_zero] at hinc
    norm_num at hinc
    exact hinc.trans (hupper (betaSeq n) (hbetaSeqGt n))
  have hle : rectangularIsingSurfaceTension (Ising.betaC 3) <= 0 :=
    ge_of_tendsto hrhs (Filter.Eventually.of_forall hpoint)
  exact le_antisymm hle
    (rectangularIsingSurfaceTension_nonneg hbetaC)

end

end StatMech.FrontierA
