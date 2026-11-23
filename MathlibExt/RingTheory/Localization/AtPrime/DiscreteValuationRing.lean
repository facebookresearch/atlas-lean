/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Localization_AtPrime_isDiscreteValuationRing_of_height_eq_one.lean` and
`P2M/Sol/S_Localization_AtPrime_isDiscreteValuationRing_of_height_eq_one.lean`
(fermats-last-theorem):
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statement and proof are reused here with that machinery
removed and the name restated in Mathlib style.
-/

module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Localizations of integrally closed domains at height-one primes

In a Noetherian integrally closed domain, the localization at a height-one
prime is a discrete valuation ring. Mathlib has this for Dedekind domains;
the same proof works under the weaker hypotheses.
-/

@[expose] public section

open IsLocalRing

/-- In a Noetherian integrally closed domain, the localization at a
height-one prime ideal is a discrete valuation ring. -/
theorem Localization.AtPrime.isDiscreteValuationRing_of_height_eq_one
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (p : Ideal R) [p.IsPrime] (hp : p.height = 1) :
    IsDiscreteValuationRing (Localization.AtPrime p) := by
  have hIC : IsIntegrallyClosed (Localization.AtPrime p) :=
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime p) p.primeCompl
      p.primeCompl_le_nonZeroDivisors
  have hdim : ringKrullDim (Localization.AtPrime p) = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p), hp]
    norm_cast
  have hKDL : Ring.KrullDimLE 1 (Localization.AtPrime p) :=
    Ring.krullDimLE_iff.mpr (le_of_eq (by rw [hdim, Nat.cast_one]))
  have hprime_max : ∀ P : Ideal (Localization.AtPrime p), P ≠ ⊥ → P.IsPrime → P.IsMaximal :=
    Ring.krullDimLE_one_iff_of_noZeroDivisors.mp hKDL
  have h3 : IsIntegrallyClosed (Localization.AtPrime p) ∧
      ∀ P : Ideal (Localization.AtPrime p), P ≠ ⊥ → P.IsPrime →
        P = IsLocalRing.maximalIdeal (Localization.AtPrime p) :=
    ⟨hIC, fun P hPne hPprime => IsLocalRing.eq_maximalIdeal (hprime_max P hPne hPprime)⟩
  have : IsNoetherianRing (Localization.AtPrime p) :=
    IsLocalization.isNoetherianRing p.primeCompl (Localization.AtPrime p) inferInstance
  have hPIR : IsPrincipalIdealRing (Localization.AtPrime p) :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (Localization.AtPrime p)).out 4 1).mp h3
  have hp_ne : p ≠ ⊥ := by
    rintro rfl
    have h0 : (⊥ : Ideal R).height = 0 := Ideal.height_bot
    rw [h0] at hp
    exact zero_ne_one hp
  have hne_bot : IsLocalRing.maximalIdeal (Localization.AtPrime p) ≠ ⊥ := by
    obtain ⟨x, hxp, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp_ne
    intro hbot
    have hxm : algebraMap R (Localization.AtPrime p) x ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.mem_map_of_mem _ hxp
    rw [hbot, Ideal.mem_bot] at hxm
    exact hx0 ((IsLocalization.injective (Localization.AtPrime p) p.primeCompl_le_nonZeroDivisors)
      (by rw [hxm, map_zero]))
  exact { hPIR with not_a_field' := hne_bot }
