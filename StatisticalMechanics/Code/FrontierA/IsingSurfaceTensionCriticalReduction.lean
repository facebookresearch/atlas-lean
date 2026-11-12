/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierA.IsingSurfaceTensionWeakLower
import Code.FrontierA.IsingCriticalSimonMass
import Code.FrontierB.CurrentContinuityCriticalAxisClosure

open Filter Set Topology

namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

noncomputable section




theorem magnetization_three_isingBetaC_eq_zero :
    magnetization 3 (Ising.betaC 3) = 0 := by
  have hcritical :=
    (StatMech.FrontierB.isingCritical_magnetization_zero_and_gibbs_unique
      (d := 3) (by omega)).1
  rw [isingFK_betaC_eq_tildeBetaCIsing (by omega : 2 <= 3)] at hcritical
  have hbdd := tildeBetaCIsingSet_bddAbove (d := 3) (by omega : 2 <= 3)
  have hcrit := tildeBetaCIsing_pos (d := 3) (by omega : 2 <= 3)
  have hsqrt : forall beta, tildeBetaCIsing 3 <= beta ->
      Real.sqrt (1 - (tildeBetaCIsing 3 / beta) ^ 2) <=
        magnetization 3 beta := fun beta hbeta =>
    sct_magnetization_meanfield_lower_bound_integrated 3 hbdd hcrit hbeta
  have heq : Ising.betaC 3 = tildeBetaCIsing 3 :=
    bc_eq_ising_of_sqrt_and_susceptibility (d := 3) (by omega) hsqrt
  rw [heq]
  exact hcritical











theorem rectangularIsingSurfaceTension_critical_eq_zero_of_asymptotic_standard_upper
    (hprism : HasPrismCubicalSurfaceComparison (Ising.betaC 3))
    (hupper : forall eps, 0 < eps ->
      Filter.Eventually (fun n =>
      standardCubicInterfaceDensity (Ising.betaC 3) n <=
        2 * Ising.betaC 3 *
          (magnetization 3 (Ising.betaC 3)) ^ 2 + eps) atTop) :
    rectangularIsingSurfaceTension (Ising.betaC 3) = 0 := by
  have hbdd := tildeBetaCIsingSet_bddAbove (d := 3) (by omega : 2 <= 3)
  have hcrit := tildeBetaCIsing_pos (d := 3) (by omega : 2 <= 3)
  have hsqrt : forall beta, tildeBetaCIsing 3 <= beta ->
      Real.sqrt (1 - (tildeBetaCIsing 3 / beta) ^ 2) <=
        magnetization 3 beta := fun beta hbeta =>
    sct_magnetization_meanfield_lower_bound_integrated 3 hbdd hcrit hbeta
  have heq : Ising.betaC 3 = tildeBetaCIsing 3 :=
    bc_eq_ising_of_sqrt_and_susceptibility (d := 3) (by omega) hsqrt
  have hbetaC : 0 < Ising.betaC 3 := by rw [heq]; exact hcrit
  have hlim :=
    standardCubicInterfaceDensity_tendsto_rectangularIsingSurfaceTension
      hbetaC hprism (hasStandardPrismSurfaceComparison (Ising.betaC 3))
  have hzero := magnetization_three_isingBetaC_eq_zero
  have hle : rectangularIsingSurfaceTension (Ising.betaC 3) <= 0 := by
    apply le_of_forall_pos_le_add
    intro eps heps
    apply le_of_tendsto hlim
    filter_upwards [hupper eps heps] with n hn
    rw [hzero] at hn
    norm_num at hn ⊢
    exact hn
  exact le_antisymm hle
    (rectangularIsingSurfaceTension_nonneg hbetaC)

end

end StatMech.FrontierA
