/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











































































































import Mathlib
import Code.Ising.TransitionRegime
import Code.IsingFK.MagnetizationCorrespondence
import Code.IsingFK.MagnetizationFK
import Code.IsingFK.HisingBoxClose
import Code.FK.ThetaZeroBelowPc
import Code.FK.PcUpperUncond
import Code.Ising.OuterContourWindingClose

open Real

namespace StatMech

namespace Ising

open StatMech.IsingFK StatMech.FK




















theorem ita_hmag_nonneg (d : ℕ) {β : ℝ} (hβ : 0 ≤ β) : 0 ≤ magnetization d β :=
  IsingFK.magnetization_nonneg d hβ
















theorem ita_hFKsub_of_atCriticality (d : ℕ)
    (hθpc : ∀ (hp : 0 < FK.fkPc d 2) (hp1 : FK.fkPc d 2 < 1),
      FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0) :
    ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 →
      FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0 :=
  FK.tzp_fkTheta_eq_zero_of_le_pc_of_pc hθpc









































theorem ita_ising_transition (d : ℕ) (hd : 2 ≤ d)
    (hisingBox : ∀ β, 0 < β → ∀ n, 1 ≤ n → fvMagnetization d β n
        = esWiredOnePoint (boxGraph d (n + 1)) (boxBoundary d (n + 1)) (0 : Fin 2)
            (pOfBeta β) (boxOrigin d (n + 1)))
    (hθpc : ∀ (hp : 0 < FK.fkPc d 2) (hp1 : FK.fkPc d 2 < 1),
      FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
    (hpc1 : FK.fkPc d 2 < 1) :
    ∃ βc : ℝ, 0 < βc ∧
      (∀ β, 0 < β → β < βc → magnetization d β = 0) ∧
      (∀ β, βc < β → 0 < magnetization d β) :=
  ising_transition_of_fkPc_lt_one d hd
    (mfc_magPercoId d (le_trans (by norm_num) hd) hisingBox)
    (ita_hFKsub_of_atCriticality d hθpc) hpc1










theorem ita_ising_transition_two_of_fkNonPercolationBound
    (hθpc : ∀ (hp : 0 < FK.fkPc 2 2) (hp1 : FK.fkPc 2 2 < 1),
      FK.fkTheta 2 hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
    (hBound : ∃ p₀ : ℝ, p₀ < 1 ∧
      ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p₀ < p →
        FK.FkNonPercolationBound 2 hp hp1 (by norm_num : (0 : ℝ) < 2)) :
    ∃ βc : ℝ, 0 < βc ∧
      (∀ β, 0 < β → β < βc → magnetization 2 β = 0) ∧
      (∀ β, βc < β → 0 < magnetization 2 β) := by
  have hpc1 : FK.fkPc 2 2 < 1 := FK.fkPc_lt_one (q := 2) (by norm_num) hBound
  exact ita_ising_transition 2 (le_refl 2) (IsingFK.hbx_hisingBox 2) hθpc hpc1




theorem ita_peierls_phase_separation_two :
    ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β →
      plusMeasure 2 n β 0 ≠ minusMeasure 2 n β 0 :=
  peierls_long_range_order_spinCompatibleFill









theorem ita_isingBetaC_eq (d : ℕ) (hd : 2 ≤ d)
    (hisingBox : ∀ β, 0 < β → ∀ n, 1 ≤ n → fvMagnetization d β n
        = esWiredOnePoint (boxGraph d (n + 1)) (boxBoundary d (n + 1)) (0 : Fin 2)
            (pOfBeta β) (boxOrigin d (n + 1)))
    (hθpc : ∀ (hp : 0 < FK.fkPc d 2) (hp1 : FK.fkPc d 2 < 1),
      FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
    (hpc1 : FK.fkPc d 2 < 1) :
    IsingFK.betaC (magnetization d) = -(1 / 2) * Real.log (1 - FK.fkPc d 2) :=
  isingBetaC_eq_of_fkPc_lt_one d hd
    (mfc_magPercoId d (le_trans (by norm_num) hd) hisingBox)
    (ita_hFKsub_of_atCriticality d hθpc) hpc1





theorem ita_isingBetaC_pos (d : ℕ) (hd : 2 ≤ d)
    (hisingBox : ∀ β, 0 < β → ∀ n, 1 ≤ n → fvMagnetization d β n
        = esWiredOnePoint (boxGraph d (n + 1)) (boxBoundary d (n + 1)) (0 : Fin 2)
            (pOfBeta β) (boxOrigin d (n + 1)))
    (hθpc : ∀ (hp : 0 < FK.fkPc d 2) (hp1 : FK.fkPc d 2 < 1),
      FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
    (hpc1 : FK.fkPc d 2 < 1) :
    0 < IsingFK.betaC (magnetization d) :=
  isingBetaC_pos_of_fkPc_lt_one d hd
    (mfc_magPercoId d (le_trans (by norm_num) hd) hisingBox)
    (ita_hFKsub_of_atCriticality d hθpc) hpc1

end Ising

end StatMech
