/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.SignedLoopCriticalCycleCover
import Code.Sharpness.IsingSharpnessUnconditional
import Code.FrontierB.CurrentContinuityPhaseCollapse
import Code.FrontierB.CurrentContinuityVaryingTemperature

















open MeasureTheory

namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.Percolation
  StatMech.Sharpness StatMech.FrontierB


noncomputable def ons_signedLoopPhaseWeight (beta : Real) : Real :=
  if beta ≤ ons_betaC then Real.tanh beta else Real.exp (-2 * beta)

theorem ons_signedLoopPhaseWeight_eq_tanh {beta : Real}
    (hbeta : beta ≤ ons_betaC) :
    ons_signedLoopPhaseWeight beta = Real.tanh beta := by
  simp [ons_signedLoopPhaseWeight, hbeta]

theorem ons_signedLoopPhaseWeight_eq_exp {beta : Real}
    (hbeta : ons_betaC < beta) :
    ons_signedLoopPhaseWeight beta = Real.exp (-2 * beta) := by
  simp [ons_signedLoopPhaseWeight, not_le.mpr hbeta]



theorem ons_signedLoopPhaseWeight_lt_critical {beta : Real}
    (hbeta : beta ≠ ons_betaC) :
    ons_signedLoopPhaseWeight beta < ons_signedLoopCriticalWeight := by
  by_cases hle : beta ≤ ons_betaC
  · rw [ons_signedLoopPhaseWeight_eq_tanh hle]
    exact tanh_lt_signedLoopCriticalWeight (lt_of_le_of_ne hle hbeta)
  · have hgt : ons_betaC < beta := lt_of_not_ge hle
    rw [ons_signedLoopPhaseWeight_eq_exp hgt]
    exact exp_neg_two_lt_signedLoopCriticalWeight hgt

@[simp] theorem ons_signedLoopPhaseWeight_selfDual :
    ons_signedLoopPhaseWeight ons_betaC = ons_signedLoopCriticalWeight := by
  rw [ons_signedLoopPhaseWeight_eq_tanh le_rfl, tanh_ons_betaC]



theorem ons_signedLoopPhaseWeight_eq_critical_iff (beta : Real) :
    ons_signedLoopPhaseWeight beta = ons_signedLoopCriticalWeight ↔
      beta = ons_betaC := by
  constructor
  · intro heq
    by_contra hne
    have hlt := ons_signedLoopPhaseWeight_lt_critical hne
    rw [heq] at hlt
    exact (lt_irrefl _ hlt).elim
  · rintro rfl
    exact ons_signedLoopPhaseWeight_selfDual

theorem isingBetaC_two_pos : 0 < StatMech.Ising.betaC 2 := by
  have hbdd := tildeBetaCIsingSet_bddAbove (d := 2) (by omega)
  have hcrit := tildeBetaCIsing_pos (d := 2) (by omega)
  have hsqrt : ∀ beta, tildeBetaCIsing 2 ≤ beta →
      Real.sqrt (1 - (tildeBetaCIsing 2 / beta) ^ 2) ≤
        magnetization 2 beta :=
    fun beta hbeta =>
      sct_magnetization_meanfield_lower_bound_integrated 2 hbdd hcrit hbeta
  rw [bc_eq_ising_of_sqrt_and_susceptibility (d := 2) (by omega) hsqrt]
  exact hcrit



theorem freeState_eq_plusState_of_magnetization_eq_zero
    {d : Nat} (beta : Real) (hbeta : 0 ≤ beta)
    (hmag : magnetization d beta = 0) :
    (freeState d beta 0 : Measure (ConfigSpace (Site d))) =
      (plusState d beta 0 : Measure (ConfigSpace (Site d))) := by
  have hpm :
      (plusState d beta 0 : Measure (ConfigSpace (Site d))) =
        (minusState d beta 0 : Measure (ConfigSpace (Site d))) :=
    plusState_eq_minusState_of_magnetization_eq_zero beta hbeta hmag
  obtain ⟨hlower, hupper⟩ := gsi_infinite_volume_sandwich
    beta 0 hbeta le_rfl
    (freeState d beta 0 : Measure (ConfigSpace (Site d)))
    (freeState_isDLR beta 0)
  rw [← hpm] at hlower
  exact gsi_clopen_antisymm hupper hlower




theorem freeState_twoPoint_exponential_below_isingBetaC
    {beta : Real} (hbeta0 : 0 < beta)
    (hbeta : beta < StatMech.Ising.betaC 2) :
    ∃ c > 0, ∀ z : Site 2,
      (∫ config, spin config (Percolation.origin 2) * spin config z
        ∂(freeState 2 beta 0 : Measure (ConfigSpace (Site 2)))) ≤
        Real.exp (-c * (l1dist 2 (Percolation.origin 2) z : Real)) := by
  have hsharp := ising_sharpness_unconditional (d := 2) (by omega)
  have hsum := hsharp.2.1 beta hbeta0.le hbeta
  have hmag : magnetization 2 beta = 0 :=
    magnetization_eq_zero_of_plusCorr_summable
      (d := 2) (by omega) beta hbeta0.le hsum
  have hstates := freeState_eq_plusState_of_magnetization_eq_zero
    beta hbeta0.le hmag
  obtain ⟨c, hc, hcorr⟩ :=
    (ising_sharpness_unconditional (d := 2) (by omega)).2.2
      beta hbeta0.le hbeta
  refine ⟨c, hc, ?_⟩
  intro z
  rw [hstates]
  exact hcorr z



theorem plusState_twoPoint_longRange_above_isingBetaC
    {beta : Real} (hbeta : StatMech.Ising.betaC 2 < beta) :
    ∃ c > 0, ∀ z : Site 2,
      c ≤ plusCorr 2 beta (Percolation.origin 2) z := by
  have hsqrt :=
    (ising_sharpness_unconditional (d := 2) (by omega)).1 beta hbeta.le
  have hbetaPos : 0 < beta := isingBetaC_two_pos.trans hbeta
  have hratio : (StatMech.Ising.betaC 2 / beta) ^ 2 < 1 := by
    have hdiv : 0 ≤ StatMech.Ising.betaC 2 / beta :=
      div_nonneg isingBetaC_two_pos.le hbetaPos.le
    have hdivlt : StatMech.Ising.betaC 2 / beta < 1 :=
      (div_lt_one hbetaPos).2 hbeta
    nlinarith
  have hsqrtPos :
      0 < Real.sqrt (1 - (StatMech.Ising.betaC 2 / beta) ^ 2) :=
    Real.sqrt_pos.2 (by linarith)
  have hmag : 0 < magnetization 2 beta := hsqrtPos.trans_le hsqrt
  refine ⟨magnetization 2 beta ^ 2, sq_pos_of_pos hmag, ?_⟩
  intro z
  exact magnetization_sq_le_plusCorr beta
    hbetaPos.le (Percolation.origin 2) z



theorem isingBetaC_two_eq_ons_betaC_of_dual_fixed
    (hfixed : dualTemp (StatMech.Ising.betaC 2) =
      StatMech.Ising.betaC 2) :
    StatMech.Ising.betaC 2 = ons_betaC := by
  have hlog := kramersWannier_critical_eq_log
    (StatMech.Ising.betaC 2) isingBetaC_two_pos hfixed
  simpa [ons_betaC] using hlog



theorem signedLoop_physical_phase_threshold
    (hfixed : dualTemp (StatMech.Ising.betaC 2) =
      StatMech.Ising.betaC 2) :
    (∀ {beta : Real}, 0 < beta → beta < ons_betaC →
      ∃ c > 0, ∀ z : Site 2,
        (∫ config, spin config (Percolation.origin 2) * spin config z
          ∂(freeState 2 beta 0 : Measure (ConfigSpace (Site 2)))) ≤
          Real.exp (-c * (l1dist 2 (Percolation.origin 2) z : Real))) ∧
    (∀ {beta : Real}, ons_betaC < beta →
      ∃ c > 0, ∀ z : Site 2,
        c ≤ plusCorr 2 beta (Percolation.origin 2) z) := by
  have hcritical := isingBetaC_two_eq_ons_betaC_of_dual_fixed hfixed
  constructor
  · intro beta hbeta0 hbeta
    apply freeState_twoPoint_exponential_below_isingBetaC hbeta0
    rwa [hcritical]
  · intro beta hbeta
    apply plusState_twoPoint_longRange_above_isingBetaC
    rwa [hcritical]

end StatMech.Onsager
