/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_PowerSeries_exists_isRegularLocalRing_isRegularRing_ringKrullDim_le_two_of_isDiscreteValuationRing.lean`
and
`P2M/Sol/S_PowerSeries_exists_isRegularLocalRing_isRegularRing_ringKrullDim_le_two_of_isDiscreteValuationRing.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
import MathlibExt.RingTheory.PowerSeries.RegularLocalRing
import MathlibExt.RingTheory.MvPowerSeries.AdicComplete
import MathlibExt.RingTheory.RegularLocalRing.IsDomain
import MathlibExt.RingTheory.RegularLocalRing.UFD
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Power series over a discrete valuation ring

Power series over a complete discrete valuation ring form a regular local
ring of Krull dimension at most two, and hence a regular ring. The natural
map from the coefficient ring is local, and a natural number that lies in
the maximal ideal of the coefficient ring, without being zero there, keeps
both properties in the power series ring.
-/

@[expose] public section

open IsLocalRing

namespace PowerSeriesDVRRegularAux

/-- A localization of an integrally closed local ring of Krull dimension
at most two, at a prime other than the maximal ideal, is regular local. -/
private theorem isRegularLocalRing_localization_of_ne_maximalIdeal_of_ringKrullDim_le_two
    {R₀ : Type*} [CommRing R₀] [IsDomain R₀] [IsNoetherianRing R₀] [IsLocalRing R₀]
    [IsIntegrallyClosed R₀] (hdim : ringKrullDim R₀ ≤ (2 : WithBot ℕ∞))
    (𝔯 : Ideal R₀) [𝔯.IsPrime] (h𝔯 : 𝔯 ≠ maximalIdeal R₀) :
    IsRegularLocalRing (Localization.AtPrime 𝔯) := by
  classical
  set A := Localization.AtPrime 𝔯
  have hlt : 𝔯 < maximalIdeal R₀ :=
    lt_of_le_of_ne (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) h𝔯
  have h1 : 𝔯.height + 1 ≤ (maximalIdeal R₀).height :=
    Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have hm : (maximalIdeal R₀).height ≤ 2 := by
    have h2 := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R₀)
    rw [← h2] at hdim
    exact WithBot.coe_le_coe.mp hdim
  have hrh : 𝔯.height ≤ 1 := by
    have h3 : 𝔯.height + 1 ≤ 2 := h1.trans hm
    have hne : 𝔯.height ≠ ⊤ := by
      intro htop; rw [htop] at h3; exact absurd h3 (by decide)
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
    rw [← hn] at h3 ⊢
    have hcast : (n : ℕ∞) + 1 = ((n + 1 : ℕ) : ℕ∞) := by push_cast; rfl
    rw [hcast] at h3
    have h4 : n + 1 ≤ 2 := by exact_mod_cast h3
    exact_mod_cast (by omega : n ≤ 1)
  have hdimA : ringKrullDim A ≤ 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔯 A]
    exact_mod_cast hrh
  haveI : IsIntegrallyClosed A :=
    isIntegrallyClosed_of_isLocalization A 𝔯.primeCompl
      (Ideal.primeCompl_le_nonZeroDivisors 𝔯)
  by_cases hF : IsField A
  · letI : Field A := hF.toField
    infer_instance
  · haveI : Ring.DimensionLEOne A := by
      refine ⟨fun {p} hp0 hp => ?_⟩
      haveI : p.IsPrime := hp
      have hb : (⊥ : Ideal A) < p := bot_lt_iff_ne_bot.mpr hp0
      have hh : (⊥ : Ideal A).height + 1 ≤ p.height :=
        Ideal.height_add_one_le_of_lt_of_isPrime hb
      rw [Ideal.height_bot, zero_add] at hh
      have hle : (p.height : WithBot ℕ∞) ≤ ringKrullDim A :=
        Ideal.height_le_ringKrullDim_of_isPrime
      have hge : (1 : WithBot ℕ∞) ≤ p.height := by exact_mod_cast hh
      exact Ideal.isMaximal_of_height_eq_ringKrullDim (le_antisymm hle (hdimA.trans hge))
    haveI : IsNoetherianRing A := IsLocalization.isNoetherianRing 𝔯.primeCompl A inferInstance
    have hded : IsDedekindDomain A := { }
    haveI : IsDiscreteValuationRing A :=
      ((IsDiscreteValuationRing.TFAE A hF).out 1 3).mpr hded
    infer_instance

/-- A regular local ring of Krull dimension at most two is a regular ring. -/
private theorem isRegularRing_of_ringKrullDim_le_two
    (R : Type*) [CommRing R] [IsRegularLocalRing R] (hdim : ringKrullDim R ≤ 2) :
    IsRegularRing R := by
  haveI : IsDomain R := IsRegularLocalRing.isDomain R
  haveI : UniqueFactorizationMonoid R :=
    IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_two R hdim
  haveI : IsIntegrallyClosed R := inferInstance
  rw [isRegularRing_iff]
  intro p _
  by_cases h : p = maximalIdeal R
  · subst h
    exact IsRegularLocalRing.of_ringEquiv
      (IsLocalization.atUnits R (maximalIdeal R).primeCompl
        (fun x ↦ by simp; exact fun a ↦ a)).toRingEquiv
  · exact isRegularLocalRing_localization_of_ne_maximalIdeal_of_ringKrullDim_le_two hdim p h

end PowerSeriesDVRRegularAux

namespace PowerSeries

/-- Power series over a discrete valuation ring are regular local. This
does not need completeness of the coefficient ring. -/
public theorem isRegularLocalRing_of_isDiscreteValuationRing
    (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    IsRegularLocalRing (PowerSeries O) :=
  isRegularLocalRing_powerSeries O

/-- Power series over a discrete valuation ring are regular. This does
not need completeness of the coefficient ring or a characteristic
witness. -/
public theorem isRegularRing_of_isDiscreteValuationRing
    (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    IsRegularRing (PowerSeries O) := by
  haveI : IsRegularLocalRing (PowerSeries O) := isRegularLocalRing_powerSeries O
  apply PowerSeriesDVRRegularAux.isRegularRing_of_ringKrullDim_le_two
  rw [ringKrullDim_powerSeries, IsDiscreteValuationRing.ringKrullDim_eq_one]
  norm_num

/-- Power series over a complete discrete valuation ring form a regular
local ring of Krull dimension at most two, and hence a regular ring; the
coefficient map is local, and the stated properties of a natural number
carry over to the power series ring. -/
public theorem exists_isRegularLocalRing_isRegularRing_ringKrullDim_le_two_of_isDiscreteValuationRing
    (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O]
    (p : ℕ) (hpO : ((p : ℕ) : O) ∈ maximalIdeal O) (hpO0 : ((p : ℕ) : O) ≠ 0) :
    ∃ (_ : IsRegularLocalRing (PowerSeries O)) (_ : IsRegularRing (PowerSeries O))
      (_ : IsAdicComplete (maximalIdeal (PowerSeries O)) (PowerSeries O))
      (_ : IsLocalHom (algebraMap O (PowerSeries O))),
      ringKrullDim (PowerSeries O) ≤ 2 ∧ ((p : ℕ) : PowerSeries O) ≠ 0 ∧
        ((p : ℕ) : PowerSeries O) ∈ maximalIdeal (PowerSeries O) := by
  haveI hreg : IsRegularLocalRing (PowerSeries O) :=
    isRegularLocalRing_of_isDiscreteValuationRing O
  have hdim : ringKrullDim (PowerSeries O) ≤ 2 := by
    rw [ringKrullDim_powerSeries, IsDiscreteValuationRing.ringKrullDim_eq_one]
    norm_num
  have hRR : IsRegularRing (PowerSeries O) := isRegularRing_of_isDiscreteValuationRing O
  have hcomplete : IsAdicComplete (maximalIdeal (PowerSeries O)) (PowerSeries O) :=
    MvPowerSeries.isAdicComplete_maximalIdeal
  have hloc : IsLocalHom (algebraMap O (PowerSeries O)) := by
    refine ⟨fun a ha => ?_⟩
    rw [← C_eq_algebraMap, isUnit_iff_constantCoeff, constantCoeff_C] at ha
    exact ha
  have hpC : ((p : ℕ) : PowerSeries O) = C ((p : ℕ) : O) :=
    (map_natCast (C (R := O)) p).symm
  have hp0 : ((p : ℕ) : PowerSeries O) ≠ 0 := by
    intro h
    apply hpO0
    have hcc := congrArg constantCoeff h
    rwa [hpC, constantCoeff_C, map_zero] at hcc
  have hpm : ((p : ℕ) : PowerSeries O) ∈ maximalIdeal (PowerSeries O) := by
    rw [hpC]
    exact PowerSeriesRegularAux.C_mem_maximalIdeal hpO
  exact ⟨hreg, hRR, hcomplete, hloc, hdim, hp0, hpm⟩

end PowerSeries
