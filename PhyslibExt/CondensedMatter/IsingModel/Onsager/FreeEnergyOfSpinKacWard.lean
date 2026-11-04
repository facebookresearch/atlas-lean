/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Onsager.CriticalIntegrability
public import PhyslibExt.CondensedMatter.IsingModel.Onsager.SpinKacWardResidue
public import PhyslibExt.CondensedMatter.IsingModel.Onsager.CriticalTransfer

/-!

# Onsager's formula from the spin Kac-Ward identities

If the spin Kac-Ward identities hold for all `β`, the torus pressure converges to Onsager's pressure
for every `β ≥ 0`, including `β_c`.

## i. Overview

Away from `β_c`, the spin Kac-Ward identities give `ons_KacWardResidue β`, hence convergence of the
torus pressure. At `β_c` the Lipschitz bound and continuity of Onsager's pressure transfer the
convergence. Conversely, convergence of the pressure gives the residue statement for every `β ≥ 0`.

## ii. Key results

- `ons_free_energy_of_spinKacWard_all` : Onsager's formula from the spin Kac-Ward identities
- `ons_KacWardResidue_of_spinKacWard_all` : the residue statement at every `β ≥ 0`

## iii. Table of contents

- A. Assembly

## iv. References

- L. Onsager, *Crystal statistics. I. A two-dimensional model with an order-disorder transition*,
  Phys. Rev. 65 (1944) 117-149
- M. Kac and J. C. Ward, *A combinatorial solution of the two-dimensional Ising model*, Phys. Rev.
  88 (1952) 1332-1337

-/

@[expose] public section

namespace StatMech.Onsager

open StatMech.Ising

/-! ## A. Assembly -/

lemma ons_free_energy_of_spinKacWard_all
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
    exact ons_free_energy_of_KacWardResidue gamma hgamma hres
  · have hres := ons_KacWardResidue_of_spinKacWard
      beta hbeta hcrit (hall beta)
    exact ons_free_energy_of_KacWardResidue beta hbeta hres

lemma ons_KacWardResidue_of_spinKacWard_all
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
  let : Fact (2 < L) := ⟨h2⟩
  simp only [ons_torusPressureSeq, dite_eq_left h2]
  rw [ons_torusPressure_eq L beta hbeta]
  ring

end StatMech.Onsager
