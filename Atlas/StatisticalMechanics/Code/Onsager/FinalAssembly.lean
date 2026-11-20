/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.CriticalIntegrability
import Code.Onsager.SpinAssembly











namespace StatMech.Onsager

open StatMech.Ising

theorem ons_free_energy_of_spinKacWard_all
    (hall : ∀ beta : ℝ, ons_spinKacWardIdentities beta)
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Filter.Tendsto (ons_torusPressureSeq beta)
      Filter.atTop (nhds (ons_pressure beta)) := by
  by_cases hcrit : beta = ons_betaC
  · subst beta
    apply ons_free_energy_critical_of_noncritical
      ons_continuousAt_pressure_betaC
    intro gamma hgamma hne
    have hres := ons_KacWardResidue_of_spinKacWard
      gamma hgamma hne (hall gamma)
    simpa only [ons_torusPressureSeq] using
      ons_free_energy_of_KacWardResidue gamma hgamma hres
  · have hres := ons_KacWardResidue_of_spinKacWard
      beta hbeta hcrit (hall beta)
    simpa only [ons_torusPressureSeq] using
      ons_free_energy_of_KacWardResidue beta hbeta hres



theorem ons_KacWardResidue_of_spinKacWard_all
    (hall : ∀ beta : ℝ, ons_spinKacWardIdentities beta)
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    ons_KacWardResidue beta := by
  have ht := (ons_free_energy_of_spinKacWard_all hall beta hbeta).sub_const
    (Real.log 2 + 2 * Real.log (Real.cosh beta))
  unfold ons_KacWardResidue
  have htarget : ons_pressure beta -
      (Real.log 2 + 2 * Real.log (Real.cosh beta)) =
      ons_freeEnergyIntegral beta - 2 * Real.log (Real.cosh beta) := by
    unfold ons_pressure
    ring
  rw [htarget] at ht
  refine ht.congr' (Filter.eventually_atTop.2 ⟨3, fun L hL => ?_⟩)
  have h2 : 2 < L := by omega
  letI : Fact (2 < L) := ⟨h2⟩
  simp only [ons_torusPressureSeq, dif_pos h2]
  rw [ons_torusPressure_eq L beta hbeta]
  ring

end StatMech.Onsager
