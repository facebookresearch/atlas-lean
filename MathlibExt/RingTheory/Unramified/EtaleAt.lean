/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Algebra_IsUnramifiedAt_isEtaleAt_of_ringKrullDim_le.lean` and
`P2M/Sol/S_Algebra_IsUnramifiedAt_isEtaleAt_of_ringKrullDim_le.lean`
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statement and proof are reused here with that machinery
removed and the name restated in Mathlib style.

The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

module

public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Unramified.Basic

import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Unramified.LocalStructure
import MathlibExt.Algebra.Etale.Localization

/-!
# Unramified implies étale under a dimension inequality

If `S` is a finite type algebra over a normal Noetherian domain `R`,
unramified at a prime `q`, and the local dimension at `q` does not drop
relative to the prime below it, then `S` is étale at `q` and the
localization at `q` is flat over `R`.
-/

@[expose] public section

universe u v

open IsLocalRing

namespace Algebra.IsUnramifiedAt.DimensionAux

variable {A T : Type*} [CommRing A] [CommRing T]

private theorem injective_of_surjective_of_ringKrullDim_le [IsDomain A] (ψ : A →+* T)
    (hψ : Function.Surjective ψ) (hfin : ringKrullDim A < ⊤)
    (hdim : ringKrullDim A ≤ ringKrullDim T) :
    Function.Injective ψ := by
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hJ
  obtain ⟨r, hrJ, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  have hr : r ∈ nonZeroDivisors A := mem_nonZeroDivisors_of_ne_zero hr0
  have e : A ⧸ RingHom.ker ψ ≃+* T := RingHom.quotientKerEquivOfSurjective hψ
  have h1 : ringKrullDim T = ringKrullDim (A ⧸ RingHom.ker ψ) :=
    (ringKrullDim_eq_of_ringEquiv e).symm
  have h2 : ringKrullDim (A ⧸ RingHom.ker ψ) ≤ ringKrullDim (A ⧸ Ideal.span {r}) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor (Ideal.span_le.mpr (by simpa using hrJ)))
      (Ideal.Quotient.factor_surjective _)
  have h3 : ringKrullDim (A ⧸ Ideal.span {r}) + 1 ≤ ringKrullDim A :=
    ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr
  have h4 : ringKrullDim A + 1 ≤ ringKrullDim A :=
    le_trans (by rw [h1] at hdim; exact add_le_add (hdim.trans h2) le_rfl) h3
  have hne : ringKrullDim A ≠ ⊥ :=
    ne_bot_of_le_ne_bot WithBot.zero_ne_bot ringKrullDim_nonneg_of_nontrivial
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hne
  rw [← hd] at h4 hfin
  have hfin' : d < ⊤ := WithBot.coe_lt_coe.mp (by rwa [WithBot.coe_top])
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp hfin'.ne
  have hle : ((n : ℕ∞) : WithBot ℕ∞) + 1 ≤ (n : ℕ∞) := h4
  rw [← WithBot.coe_one, ← WithBot.coe_add, WithBot.coe_le_coe] at hle
  have h5 : ((n + 1 : ℕ) : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast hle
  have h6 := ENat.coe_le_coe.mp h5
  omega

variable {R : Type u} [CommRing R] {E : Type u} [CommRing E] [Algebra R E]

private theorem height_le_height_of_isUnramifiedAt [IsNoetherianRing R] [IsNoetherianRing E]
    [Algebra.EssFiniteType R E]
    (𝔔 : Ideal E) [𝔔.IsPrime] [Algebra.IsUnramifiedAt R 𝔔] :
    𝔔.height ≤ (𝔔.under R).height := by
  set 𝔭 := 𝔔.under R with h𝔭
  haveI : 𝔔.LiesOver 𝔭 := ⟨rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver 𝔭 𝔔
  have hmap : 𝔭.map (algebraMap R (Localization.AtPrime 𝔔)) = maximalIdeal _ :=
    ((Algebra.isUnramifiedAt_iff_map_eq R 𝔭 𝔔).mp inferInstance).2
  have hle := Ideal.height_le_height_add_of_liesOver 𝔭 𝔔
  suffices h0 : (𝔔.map (Ideal.Quotient.mk (𝔭.map (algebraMap R E)))).height = 0 by
    rw [h0, add_zero] at hle; exact hle
  have hker : RingHom.ker (Ideal.Quotient.mk (𝔭.map (algebraMap R E))) ≤ 𝔔 := by
    rw [Ideal.mk_ker]; exact Ideal.map_le_iff_le_comap.mpr le_rfl
  haveI hprime : (𝔔.map (Ideal.Quotient.mk (𝔭.map (algebraMap R E)))).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  rw [Ideal.height_eq_zero_iff]
  refine ⟨⟨hprime, bot_le⟩, ?_⟩
  rintro J' ⟨hJ', -⟩ hJ'le
  set J : Ideal E := J'.comap (Ideal.Quotient.mk (𝔭.map (algebraMap R E))) with hJ
  haveI : J.IsPrime := Ideal.IsPrime.comap _
  have hJ𝔔 : J ≤ 𝔔 := by
    have hmono := Ideal.comap_mono (f := Ideal.Quotient.mk (𝔭.map (algebraMap R E))) hJ'le
    rwa [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hker] at hmono
  have h𝔭J : 𝔭.map (algebraMap R E) ≤ J := by
    intro x hx
    rw [hJ, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact J'.zero_mem
  have h𝔔J : 𝔔 ≤ J := by
    intro x hx
    have hx' : algebraMap E (Localization.AtPrime 𝔔) x ∈
        maximalIdeal (Localization.AtPrime 𝔔) := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]; exact Ideal.mem_map_of_mem _ hx
    rw [← hmap] at hx'
    have hx'' : algebraMap E (Localization.AtPrime 𝔔) x ∈
        (𝔭.map (algebraMap R E)).map (algebraMap E (Localization.AtPrime 𝔔)) := by
      rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]; exact hx'
    rw [IsLocalization.mem_map_algebraMap_iff 𝔔.primeCompl] at hx''
    obtain ⟨⟨y, s⟩, hys⟩ := hx''
    dsimp only at hys
    rw [← map_mul] at hys
    obtain ⟨t, ht⟩ := (IsLocalization.eq_iff_exists 𝔔.primeCompl (Localization.AtPrime 𝔔)).mp hys
    have hmem : (t : E) * ((s : E) * x) ∈ J := by
      have htx : (t : E) * (x * (s : E)) = (t : E) * (y : E) := ht
      rw [mul_comm (s : E) x, htx]
      exact J.mul_mem_left _ (h𝔭J y.2)
    have ht' : (t : E) ∉ J := fun h => t.2 (hJ𝔔 h)
    have hs' : (s : E) ∉ J := fun h => s.2 (hJ𝔔 h)
    rcases (‹J.IsPrime›).mem_or_mem hmem with h | h
    · exact absurd h ht'
    rcases (‹J.IsPrime›).mem_or_mem h with h | h
    · exact absurd h hs'
    · exact h
  calc 𝔔.map (Ideal.Quotient.mk (𝔭.map (algebraMap R E)))
      ≤ J.map (Ideal.Quotient.mk (𝔭.map (algebraMap R E))) := Ideal.map_mono h𝔔J
    _ = J' := Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _

end Algebra.IsUnramifiedAt.DimensionAux

open Algebra.IsUnramifiedAt.DimensionAux in
/-- If `S` is unramified over a normal Noetherian domain `R` at `q` and
`dim R_{q ∩ R} ≤ dim S_q`, then `S` is étale at `q` and `S_q` is `R`-flat. -/
public theorem Algebra.IsUnramifiedAt.isEtaleAt_of_ringKrullDim_le
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (S : Type v) [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (q : Ideal S) [q.IsPrime] [Algebra.IsUnramifiedAt R q]
    (hdim : ringKrullDim (Localization.AtPrime (q.under R)) ≤
      ringKrullDim (Localization.AtPrime q)) :
    Algebra.IsEtaleAt R q ∧ Module.Flat R (Localization.AtPrime q) := by
  classical
  obtain ⟨f, hfq, P, φ, hφ⟩ := Algebra.IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn (R := R) q
  set Sf := Localization.Away f
  set E := P.Ring
  have hdisj : Disjoint ((Submonoid.powers f : Submonoid S) : Set S) (q : Set S) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime f).mpr hfq
  set qf : Ideal Sf := q.map (algebraMap S Sf) with hqf
  haveI hqfp : qf.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (.powers f) Sf q ‹_› hdisj
  have hunder : qf.under S = q :=
    IsLocalization.under_map_of_isPrime_disjoint (.powers f) Sf ‹_› hdisj
  set 𝔔 : Ideal E := qf.comap φ.toRingHom with h𝔔
  haveI h𝔔p : 𝔔.IsPrime := Ideal.IsPrime.comap _
  set ψ : Localization.AtPrime 𝔔 →+* Localization.AtPrime qf :=
    Localization.localRingHom 𝔔 qf φ.toRingHom rfl with hψ
  have hψsurj : Function.Surjective ψ := by
    intro z
    obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective qf.primeCompl z
    obtain ⟨a, rfl⟩ := hφ x
    obtain ⟨b, hb⟩ := hφ s
    have hb' : b ∈ 𝔔.primeCompl := by
      change b ∉ 𝔔
      rw [h𝔔, Ideal.mem_comap]
      change φ b ∉ qf
      rw [hb]; exact s.2
    refine ⟨IsLocalization.mk' _ a ⟨b, hb'⟩, ?_⟩
    rw [hψ, Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext hb
  haveI : IsDomain (Localization.AtPrime 𝔔) :=
    (Algebra.Etale.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime R E 𝔔
      (Localization.AtPrime 𝔔)).1
  haveI : IsNoetherianRing E := Algebra.FiniteType.isNoetherianRing R E
  have h𝔔under : 𝔔.under R = q.under R := by
    rw [h𝔔, Ideal.under_def, Ideal.comap_comap, AlgHom.toRingHom_eq_coe, φ.comp_algebraMap,
      ← Ideal.under_def, ← Ideal.under_under (B := S) qf, hunder]
  have hA : ringKrullDim (Localization.AtPrime 𝔔) ≤
      ringKrullDim (Localization.AtPrime (q.under R)) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔔 (Localization.AtPrime 𝔔),
      IsLocalization.AtPrime.ringKrullDim_eq_height (q.under R) (Localization.AtPrime (q.under R)),
      ← h𝔔under]
    exact WithBot.coe_le_coe.mpr (height_le_height_of_isUnramifiedAt 𝔔)
  have hT : ringKrullDim (Localization.AtPrime qf) = ringKrullDim (Localization.AtPrime q) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height qf (Localization.AtPrime qf),
      IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q), hqf,
      IsLocalization.height_map_of_disjoint (.powers f) q hdisj]
  have hfin : ringKrullDim (Localization.AtPrime 𝔔) < ⊤ := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔔 (Localization.AtPrime 𝔔)]
    exact WithBot.coe_lt_coe.mpr (lt_top_iff_ne_top.mpr (Ideal.height_ne_top Ideal.IsPrime.ne_top'))
  have hψinj : Function.Injective ψ :=
    injective_of_surjective_of_ringKrullDim_le ψ hψsurj hfin (hA.trans (hdim.trans hT.symm.le))
  have hψalg : ∀ r : R, ψ (algebraMap R _ r) = algebraMap R _ r := by
    intro r
    rw [IsScalarTower.algebraMap_apply R E (Localization.AtPrime 𝔔), hψ,
      Localization.localRingHom_to_map, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  let eψ : Localization.AtPrime 𝔔 ≃ₐ[R] Localization.AtPrime qf :=
    AlgEquiv.ofBijective { ψ with commutes' := hψalg } ⟨hψinj, hψsurj⟩
  have hloc : IsLocalization.AtPrime (Localization.AtPrime qf) (qf.comap (algebraMap S Sf)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (.powers f) _ qf
  have hcomap : qf.comap (algebraMap S Sf) = q := hunder
  have hM : q.primeCompl = (qf.comap (algebraMap S Sf)).primeCompl := by
    ext x
    change x ∉ q ↔ x ∉ qf.comap (algebraMap S Sf)
    rw [hcomap]
  haveI : IsLocalization q.primeCompl (Localization.AtPrime qf) := by rw [hM]; exact hloc
  let eT : Localization.AtPrime qf ≃ₐ[S] Localization.AtPrime q :=
    IsLocalization.algEquiv q.primeCompl (Localization.AtPrime qf) (Localization.AtPrime q)
  let e : Localization.AtPrime 𝔔 ≃ₐ[R] Localization.AtPrime q := eψ.trans (eT.restrictScalars R)
  haveI : Algebra.FormallyEtale R (Localization.AtPrime 𝔔) := inferInstance
  haveI : Module.Flat R (Localization.AtPrime 𝔔) :=
    Module.Flat.trans R E (Localization.AtPrime 𝔔)
  exact ⟨Algebra.FormallyEtale.of_equiv e, Module.Flat.of_linearEquiv e.symm.toLinearEquiv⟩
