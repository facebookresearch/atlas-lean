/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.DecorationFormalMultiaffine









namespace StatMech.Onsager

open StatMech.Ising

section FiniteVolume

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem main_high_temperature_expansion (beta : ℝ) :
    ons_Z G beta =
      (2 : ℝ) ^ Fintype.card V * (Real.cosh beta) ^ G.edgeFinset.card *
        ons_X G (Real.tanh beta) :=
  ons_hte G beta


theorem main_finite_pressure_decomposition
    (beta : ℝ) (hbeta : 0 ≤ beta) (hV : 0 < Fintype.card V) :
    ons_pressureFinite G beta =
      Real.log 2 +
        (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ) *
          Real.log (Real.cosh beta) +
        Real.log (ons_X G (Real.tanh beta)) / (Fintype.card V : ℝ) :=
  ons_pressureFinite_eq G beta hbeta hV

end FiniteVolume

section CriticalPoint


theorem main_critical_beta_value :
    Real.sinh (2 * ons_betaC) = 1 :=
  ons_betaC_sinh


theorem main_critical_beta_unique (beta : ℝ) (hbeta : 0 < beta) :
    Real.sinh (2 * beta) = 1 ↔ beta = ons_betaC :=
  ons_betaC_unique beta hbeta


theorem main_pressure_continuous_at_critical :
    ContinuousAt ons_pressure ons_betaC :=
  ons_continuousAt_pressure_betaC

end CriticalPoint

section TorusLimit


theorem main_torus_pressure_decomposition
    (L : ℕ) [Fact (2 < L)] (beta : ℝ) (hbeta : 0 ≤ beta) :
    ons_pressureFinite (onsTorusGraph L) beta =
      Real.log 2 + 2 * Real.log (Real.cosh beta) +
        Real.log (ons_X (onsTorusGraph L) (Real.tanh beta)) / ((L : ℝ) ^ 2) :=
  ons_torusPressure_eq L beta hbeta


theorem main_free_energy_from_spin_kacWard
    (hall : ∀ beta : ℝ, ons_spinKacWardIdentities beta)
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Filter.Tendsto (ons_torusPressureSeq beta)
      Filter.atTop (nhds (ons_pressure beta)) :=
  ons_free_energy_of_spinKacWard_all hall beta hbeta

end TorusLimit

section FiniteKacWard


theorem main_spin_kacWard_from_weighted_root
    (hweighted : ∀ (L : ℕ) (hL : 2 < L),
      letI : Fact (2 < L) := ⟨hL⟩
      ons_weightedRootIdentity L)
    (beta : ℝ) :
    ons_spinKacWardIdentities beta :=
  ons_spinKacWardIdentities_of_weightedRoot hweighted beta


theorem main_weighted_root_from_decorated_formal
    (L : ℕ) [Fact (2 < L)]
    (hformal : ons_decoratedFormalKacWardIdentity L) :
    ons_weightedRootIdentity L :=
  ons_weightedRootIdentity_of_decoratedFormal L hformal


theorem main_spin_kacWard_from_decorated_formal
    (hformal : ∀ (L : ℕ) (hL : 2 < L),
      letI : Fact (2 < L) := ⟨hL⟩
      ons_decoratedFormalKacWardIdentity L)
    (beta : ℝ) :
    ons_spinKacWardIdentities beta :=
  ons_spinKacWardIdentities_of_decoratedFormal hformal beta


theorem main_free_energy
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Filter.Tendsto (ons_torusPressureSeq beta)
      Filter.atTop
        (nhds
          (Real.log 2 +
            (1 / (8 * Real.pi ^ 2)) *
              ∫ k₁ in (-Real.pi)..Real.pi,
                ∫ k₂ in (-Real.pi)..Real.pi,
                  Real.log
                    (Real.cosh (2 * beta) ^ 2 -
                      Real.sinh (2 * beta) *
                        (Real.cos k₁ + Real.cos k₂)))) := by
  simpa [ons_pressure, ons_freeEnergyIntegral, ons_gInt] using
    ons_free_energy_unconditional beta hbeta

end FiniteKacWard

end StatMech.Onsager
