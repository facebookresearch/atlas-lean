/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgHom_length_cotangent_le_and_congruenceIdeal_le_of_surjective.lean`,
`P2M/Sol/S_AlgHom_length_cotangent_le_and_congruenceIdeal_le_of_surjective.lean`,
`Theorems/Thm_AlgHom_congruenceIdeal_ne_bot_of_isReduced.lean`, and
`P2M/Sol/S_AlgHom_congruenceIdeal_ne_bot_of_isReduced.lean`
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

public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Cotangent length and congruence ideals under a surjection

Two inputs to the numerical criterion for a surjection of algebras over a
base ring `𝒪` equipped with sections to `𝒪`: the cotangent space can only
shrink under a compatible surjection, the congruence ideal can only grow,
and, when `𝒪` is a domain, the congruence ideal of a module-finite, reduced,
Noetherian algebra is nonzero.
-/

@[expose] public section

/-- Under a compatible surjection `R →ₐ[𝒪] T`, the cotangent length of
`T` is at most that of `R`, and the congruence ideal of `R` is contained
in that of `T`. -/
public theorem AlgHom.length_cotangent_le_and_congruenceIdeal_le_of_surjective
    {𝒪 : Type*} {R : Type*} {T : Type*} [CommRing 𝒪]
    [CommRing R] [Algebra 𝒪 R] [CommRing T] [Algebra 𝒪 T]
    (φ : R →ₐ[𝒪] T) (hφ : Function.Surjective φ) (πR : R →ₐ[𝒪] 𝒪) (πT : T →ₐ[𝒪] 𝒪)
    (hπ : πT.comp φ = πR) :
    Module.length 𝒪 (RingHom.ker πT).Cotangent ≤
        Module.length 𝒪 (RingHom.ker πR).Cotangent ∧
      (RingHom.ker πR).annihilator.map πR ≤ (RingHom.ker πT).annihilator.map πT := by
  have hmem : ∀ r, r ∈ RingHom.ker πR ↔ φ r ∈ RingHom.ker πT := fun r => by
    rw [RingHom.mem_ker, RingHom.mem_ker, ← AlgHom.congr_fun hπ r]; rfl
  have hcomap : RingHom.ker πR ≤ (RingHom.ker πT).comap φ := fun r hr =>
    Ideal.mem_comap.mpr ((hmem r).mp hr)
  constructor
  · refine Module.length_le_of_surjective (Ideal.mapCotangent _ _ φ hcomap) ?_
    intro m
    obtain ⟨⟨t, ht⟩, rfl⟩ := (RingHom.ker πT).toCotangent_surjective m
    obtain ⟨r, rfl⟩ := hφ t
    exact ⟨(RingHom.ker πR).toCotangent ⟨r, (hmem r).mpr ht⟩, by simp⟩
  · refine Ideal.map_le_iff_le_comap.mpr fun x hx => ?_
    rw [Ideal.mem_comap, show πR x = πT (φ x) from (AlgHom.congr_fun hπ x).symm]
    refine Ideal.mem_map_of_mem _ ?_
    rw [Submodule.mem_annihilator] at hx ⊢
    intro t ht
    obtain ⟨r, rfl⟩ := hφ t
    rw [smul_eq_mul, ← map_mul, ← smul_eq_mul, hx r ((hmem r).mpr ht), map_zero]

/-- Over a domain `𝒪`, the congruence ideal of a module-finite, reduced,
Noetherian `𝒪`-algebra with a section to `𝒪` is nonzero. -/
public theorem AlgHom.congruenceIdeal_ne_bot_of_isReduced
    {𝒪 : Type*} {T : Type*} [CommRing 𝒪] [IsDomain 𝒪]
    [CommRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [IsNoetherianRing T] [IsReduced T]
    (πT : T →ₐ[𝒪] 𝒪) :
    (RingHom.ker πT).annihilator.map πT ≠ ⊥ := by
  classical
  set 𝔭 : Ideal T := RingHom.ker πT with h𝔭def
  have h𝔭prime : 𝔭.IsPrime := RingHom.ker_isPrime πT
  have hcomap : 𝔭.comap (algebraMap 𝒪 T) = ⊥ := by
    refine le_bot_iff.mp fun a ha => ?_
    rw [Ideal.mem_comap, h𝔭def, RingHom.mem_ker] at ha
    have ha' : πT (algebraMap 𝒪 T a) = 0 := ha
    rw [AlgHom.commutes] at ha'
    exact (Ideal.mem_bot).mpr ha'
  have hmin : 𝔭 ∈ minimalPrimes T := by
    refine ⟨⟨h𝔭prime, bot_le⟩, ?_⟩
    rintro Q ⟨hQ, -⟩ hQle
    by_contra hnot
    obtain ⟨x, hx𝔭, hxQ⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
    have := hQ
    have hlt := Ideal.under_lt_under_of_integral_mem_sdiff (R := 𝒪) hQle ⟨hx𝔭, hxQ⟩
      (Algebra.IsIntegral.isIntegral x)
    rw [show 𝔭.under 𝒪 = 𝔭.comap (algebraMap 𝒪 T) from rfl,
      show Q.under 𝒪 = Q.comap (algebraMap 𝒪 T) from rfl, hcomap] at hlt
    exact not_lt_bot hlt
  have hfin : (minimalPrimes T).Finite := minimalPrimes.finite_of_isNoetherianRing T
  set s : Finset (Ideal T) := hfin.toFinset.erase 𝔭 with hsdef
  set I : Ideal T := s.inf id with hIdef
  have hI_ann : I ≤ 𝔭.annihilator := by
    intro t ht
    refine Submodule.mem_annihilator.mpr fun x hx => ?_
    have hmem : t * x ∈ sInf (minimalPrimes T) := by
      refine Submodule.mem_sInf.mpr fun Q hQ => ?_
      by_cases hQ𝔭 : Q = 𝔭
      · subst hQ𝔭; exact Ideal.mul_mem_left _ t hx
      · have hQs : Q ∈ s := Finset.mem_erase.mpr ⟨hQ𝔭, hfin.mem_toFinset.mpr hQ⟩
        have htQ : t ∈ Q := by
          have hle : I ≤ id Q := Finset.inf_le hQs
          exact hle ht
        exact Ideal.mul_mem_right x Q htQ
    have hnil : sInf (minimalPrimes T) = (⊥ : Ideal T) := by
      have h := Ideal.sInf_minimalPrimes (I := (⊥ : Ideal T))
      have h0 : (⊥ : Ideal T).radical = ⊥ := nilradical_eq_zero T
      rw [h0] at h
      exact h
    rw [hnil, Ideal.mem_bot] at hmem
    simpa [smul_eq_mul] using hmem
  have hI_not_le : ¬ I ≤ 𝔭 := by
    intro hle
    rcases s.eq_empty_or_nonempty with hs | hs
    · have hItop : I = ⊤ := by rw [hIdef, hs, Finset.inf_empty]
      exact h𝔭prime.ne_top (top_le_iff.mp (hItop ▸ hle))
    · obtain ⟨Q, hQs, hQle⟩ := (h𝔭prime.inf_le' (s := s) (f := id)).mp hle
      obtain ⟨hQ𝔭, hQmin⟩ := Finset.mem_erase.mp hQs
      have hQmin' : Q ∈ minimalPrimes T := hfin.mem_toFinset.mp hQmin
      have h𝔭leQ : 𝔭 ≤ Q := hmin.2 ⟨hQmin'.1.1, bot_le⟩ hQle
      exact hQ𝔭 (le_antisymm hQle h𝔭leQ)
  obtain ⟨t, htI, ht𝔭⟩ := IsConcreteLE.not_le_iff_exists.mp hI_not_le
  intro hbot
  have hmem : πT t ∈ (RingHom.ker πT).annihilator.map πT :=
    Ideal.mem_map_of_mem _ (hI_ann htI)
  rw [hbot, Ideal.mem_bot] at hmem
  exact ht𝔭 (by rw [h𝔭def, RingHom.mem_ker]; exact hmem)
