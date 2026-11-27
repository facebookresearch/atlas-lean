/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ArtinL_Abelian_dvd_conductor_iff_not_isUnramifiedAt.lean`
and
`P2M/Sol/S_ArtinL_Abelian_dvd_conductor_iff_not_isUnramifiedAt.lean`
and
`Definitions/Def_ArtinL_Abelian.lean`
and
`Definitions/Def_LanglandsTunnell_ArtinFrobenius.lean`
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

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.Ideal.GoingUp

import Mathlib.Algebra.BigOperators.Associated
import Mathlib.RingTheory.IsGaloisGroup.Basic

@[expose] public section

open NumberField IsDedekindDomain
open scoped Classical

universe u v

namespace ArtinConductor

variable {K : Type u} {M : Type v} [Field K] [NumberField K] [Field M]
  [NumberField M] [Algebra K M] [IsGalois K M]

omit [IsGalois K M] in
private theorem algebraMap_ringOfIntegers_injective :
    Function.Injective (algebraMap (𝓞 K) (𝓞 M)) := by
  intro x y h
  have h' : algebraMap (𝓞 K) M x = algebraMap (𝓞 K) M y := by
    rw [IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 M) M,
      IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 M) M, h]
  rw [IsScalarTower.algebraMap_apply (𝓞 K) K M,
    IsScalarTower.algebraMap_apply (𝓞 K) K M] at h'
  exact RingOfIntegers.coe_injective ((algebraMap K M).injective h')

omit [IsGalois K M] in
/-- There is a maximal prime of `𝓞 M` above `v`, lying over `v`. -/
theorem exists_prime_over (v : HeightOneSpectrum (𝓞 K)) :
    ∃ Q : Ideal (𝓞 M), Q.IsMaximal ∧ Q.under (𝓞 K) = v.asIdeal := by
  haveI := v.isMaximal
  obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral v.asIdeal
    (by
      rw [(RingHom.injective_iff_ker_eq_bot _).mp
        (algebraMap_ringOfIntegers_injective (K := K) (M := M))]
      exact bot_le)
  exact ⟨Q, hQ, hQv⟩

/-- A chosen prime of `𝓞 M` above the prime `v` of `𝓞 K`. -/
noncomputable def primeAbove (K : Type u) (M : Type v) [Field K] [NumberField K]
    [Field M] [NumberField M] [Algebra K M] (v : HeightOneSpectrum (𝓞 K)) :
    Ideal (𝓞 M) :=
  (exists_prime_over (K := K) (M := M) v).choose

/-- The chosen prime above `v` is maximal. -/
theorem primeAbove_isMaximal (v : HeightOneSpectrum (𝓞 K)) :
    (primeAbove K M v).IsMaximal :=
  (exists_prime_over (K := K) (M := M) v).choose_spec.1

instance (v : HeightOneSpectrum (𝓞 K)) : (primeAbove K M v).IsMaximal :=
  primeAbove_isMaximal v

/-- The chosen prime above `v` lies over `v`. -/
theorem under_primeAbove (v : HeightOneSpectrum (𝓞 K)) :
    (primeAbove K M v).under (𝓞 K) = v.asIdeal :=
  (exists_prime_over (K := K) (M := M) v).choose_spec.2

/-- The chosen prime above `v` is nonzero. -/
theorem primeAbove_ne_bot (v : HeightOneSpectrum (𝓞 K)) :
    primeAbove K M v ≠ ⊥ := by
  intro h
  have hQ := under_primeAbove (K := K) (M := M) v
  rw [h, Ideal.under_def,
    Ideal.comap_bot_of_injective _
      (algebraMap_ringOfIntegers_injective (K := K) (M := M))] at hQ
  exact v.ne_bot hQ.symm

/-- The inertia group at `v`: the inertia subgroup of the chosen prime
above `v` in the Galois group of `M/K`. -/
noncomputable def inertiaGroup (v : HeightOneSpectrum (𝓞 K)) : Subgroup (M ≃ₐ[K] M) :=
  (primeAbove K M v).inertia (M ≃ₐ[K] M)

/-- The `i`-th ramification group at `v`, for the `(i + 1)`-st power of
the chosen prime above `v`. -/
noncomputable def ramificationGroup (v : HeightOneSpectrum (𝓞 K)) (i : ℕ) :
    Subgroup (M ≃ₐ[K] M) :=
  (primeAbove K M v ^ (i + 1)).inertia (M ≃ₐ[K] M)

/-- The character `ψ` is unramified at `v` if it is trivial on the
inertia group at `v`. -/
def IsUnramifiedAt (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) :
    Prop :=
  ∀ σ ∈ inertiaGroup (K := K) (M := M) v, ψ σ = 1

/-- The Swan conductor of `ψ` at `v`: the sum over higher ramification
groups of the proportion of the inertia group on which `ψ` is nontrivial
outside the higher group. -/
noncomputable def swanConductor (ψ : (M ≃ₐ[K] M) →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K)) : ℚ :=
  ∑ᶠ i : ℕ,
    (Nat.card (ramificationGroup (K := K) (M := M) v (i + 1)) : ℚ) /
      (Nat.card (inertiaGroup (K := K) (M := M) v) : ℚ) *
      (if ∀ σ ∈ ramificationGroup (K := K) (M := M) v (i + 1), ψ σ = 1
        then 0 else 1)

/-- The conductor exponent of `ψ` at `v`: zero when `ψ` is unramified at
`v`, and one plus the ceiling of the Swan conductor otherwise. -/
noncomputable def conductorExponent (ψ : (M ≃ₐ[K] M) →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  (if IsUnramifiedAt (K := K) (M := M) ψ v then 0 else 1) +
    ⌈swanConductor ψ v⌉₊

/-- The conductor of `ψ`: the product over all finite primes `v` of
`v ^ conductorExponent ψ v`. -/
noncomputable def conductor (ψ : (M ≃ₐ[K] M) →* ℂˣ) : Ideal (𝓞 K) :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K), v.asIdeal ^ conductorExponent ψ v

private theorem ramificationGroup_succ_le (v : HeightOneSpectrum (𝓞 K))
    (i : ℕ) :
    ramificationGroup (K := K) (M := M) v (i + 1) ≤
      inertiaGroup (K := K) (M := M) v := by
  intro σ hσ x
  exact Ideal.pow_le_self (Nat.succ_ne_zero _) (hσ x)

private theorem conductorExponent_eq_zero_of_isUnramifiedAt
    (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
    (h : IsUnramifiedAt (K := K) (M := M) ψ v) :
    conductorExponent ψ v = 0 := by
  have hsw : swanConductor ψ v = 0 := by
    unfold swanConductor
    refine finsum_eq_zero_of_forall_eq_zero fun i ↦ ?_
    rw [if_pos, mul_zero]
    intro σ hσ
    exact h σ (ramificationGroup_succ_le v i hσ)
  rw [conductorExponent, if_pos h, hsw]
  simp

private theorem one_le_conductorExponent_of_not_isUnramifiedAt
    (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
    (h : ¬ IsUnramifiedAt (K := K) (M := M) ψ v) :
    1 ≤ conductorExponent ψ v := by
  rw [conductorExponent, if_neg h]
  exact Nat.le_add_right 1 _

private theorem exists_ne_zero_forall_mem
    (h1 : ∀ σ : M ≃ₐ[K] M, σ ≠ 1 → ∃ x : 𝓞 M, σ • x - x ≠ 0) :
    ∃ N : 𝓞 M, N ≠ 0 ∧ ∀ σ : M ≃ₐ[K] M, σ ≠ 1 →
      ∀ P : Ideal (𝓞 M), (∀ x : 𝓞 M, σ • x - x ∈ P) → N ∈ P := by
  choose! x hx using h1
  refine ⟨∏ σ ∈ (Finset.univ.filter fun σ : M ≃ₐ[K] M ↦ σ ≠ 1),
    (σ • x σ - x σ), ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro σ hσ
    exact hx σ (Finset.mem_filter.1 hσ).2
  · intro σ hσ P hP
    have hmem : σ ∈ Finset.univ.filter fun σ : M ≃ₐ[K] M ↦ σ ≠ 1 :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hσ⟩
    rw [← Finset.mul_prod_erase _ _ hmem]
    exact Ideal.mul_mem_right _ _ (hP (x σ))

private theorem exists_smul_sub_ne_zero (σ : M ≃ₐ[K] M) (hσ : σ ≠ 1) :
    ∃ x : 𝓞 M, σ • x - x ≠ 0 := by
  by_contra h
  push Not at h
  apply hσ
  haveI : FaithfulSMul (M ≃ₐ[K] M) (𝓞 M) :=
    (inferInstance : IsGaloisGroup (M ≃ₐ[K] M) (𝓞 K) (𝓞 M)).faithful
  exact FaithfulSMul.eq_of_smul_eq_smul (M := M ≃ₐ[K] M) (α := 𝓞 M)
    fun x ↦ by rw [one_smul]; exact sub_eq_zero.1 (h x)

private theorem finite_setOf_not_isUnramifiedAt (ψ : (M ≃ₐ[K] M) →* ℂˣ) :
    {v : HeightOneSpectrum (𝓞 K) |
      ¬ IsUnramifiedAt (K := K) (M := M) ψ v}.Finite := by
  obtain ⟨N, hN0, hN⟩ := exists_ne_zero_forall_mem (K := K) (M := M)
    fun σ hσ ↦ exists_smul_sub_ne_zero σ hσ
  let f : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 M) := fun v ↦
    ⟨primeAbove K M v, (primeAbove_isMaximal (K := K) (M := M) v).isPrime,
      primeAbove_ne_bot (K := K) (M := M) v⟩
  have hinj : Set.InjOn f
      {v : HeightOneSpectrum (𝓞 K) |
        ¬ IsUnramifiedAt (K := K) (M := M) ψ v} := by
    intro v _ w _ h
    have h' : primeAbove K M v = primeAbove K M w :=
      congrArg HeightOneSpectrum.asIdeal h
    apply HeightOneSpectrum.ext
    rw [← under_primeAbove (K := K) (M := M) v,
      ← under_primeAbove (K := K) (M := M) w, h']
  refine Set.Finite.of_finite_image ?_ hinj
  refine (Ideal.finite_factors (I := Ideal.span {N}) ?_).subset ?_
  · rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
    exact hN0
  · rintro P ⟨v, hv, rfl⟩
    rw [Set.mem_setOf_eq] at hv ⊢
    rw [IsUnramifiedAt] at hv
    push Not at hv
    obtain ⟨σ, hσI, hσψ⟩ := hv
    have hσ1 : σ ≠ 1 := by
      rintro rfl
      exact hσψ (map_one ψ)
    show primeAbove K M v ∣ Ideal.span {N}
    rw [Ideal.dvd_span_singleton]
    exact hN σ hσ1 _ hσI

private theorem hasFiniteMulSupport_of_finite (ψ : (M ≃ₐ[K] M) →* ℂˣ)
    (hfin : {v : HeightOneSpectrum (𝓞 K) |
      ¬ IsUnramifiedAt (K := K) (M := M) ψ v}.Finite) :
    Function.HasFiniteMulSupport
      fun w : HeightOneSpectrum (𝓞 K) ↦ w.asIdeal ^ conductorExponent ψ w := by
  refine hfin.subset fun w hw ↦ ?_
  rw [Function.mem_mulSupport] at hw
  rw [Set.mem_setOf_eq]
  intro hunr
  exact hw (by
    rw [conductorExponent_eq_zero_of_isUnramifiedAt ψ w hunr, pow_zero])

/-- A prime divides the conductor of an abelian Artin character if and
only if the character ramifies at that prime. -/
public theorem dvd_conductor_iff_not_isUnramifiedAt
    (K : Type u) (M : Type v) [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M] [IsGalois K M]
    (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) :
    v.asIdeal ∣ conductor ψ ↔
      ¬ IsUnramifiedAt (K := K) (M := M) ψ v := by
  have hfin := hasFiniteMulSupport_of_finite (K := K) (M := M) ψ
    (finite_setOf_not_isUnramifiedAt (K := K) (M := M) ψ)
  have hconductor : conductor ψ =
      ∏ w ∈ hfin.toFinset, w.asIdeal ^ conductorExponent ψ w := by
    unfold conductor
    exact finprod_eq_prod _ hfin
  rw [hconductor]
  constructor
  · intro hv hunr
    have hf0 := conductorExponent_eq_zero_of_isUnramifiedAt ψ v hunr
    have hprime : Prime v.asIdeal := Ideal.prime_of_isPrime v.ne_bot v.isPrime
    obtain ⟨w, hw, hvw⟩ := (Prime.dvd_finsetProd_iff hprime _).1 hv
    have hvw' : v.asIdeal ∣ w.asIdeal := hprime.dvd_of_dvd_pow hvw
    have heq : v = w := by
      have hle : w.asIdeal ≤ v.asIdeal := Ideal.le_of_dvd hvw'
      exact HeightOneSpectrum.ext
        (w.isMaximal.eq_of_le v.isPrime.ne_top hle).symm
    subst heq
    rw [hfin.mem_toFinset, Function.mem_mulSupport, hf0, pow_zero] at hw
    exact hw rfl
  · intro hram
    have h1 := one_le_conductorExponent_of_not_isUnramifiedAt ψ v hram
    have hmem : v ∈ hfin.toFinset := by
      rw [hfin.mem_toFinset, Function.mem_mulSupport]
      intro h
      have h' : v.asIdeal ^ conductorExponent ψ v ≤ v.asIdeal :=
        Ideal.pow_le_self (by omega)
      rw [h, Ideal.one_eq_top, top_le_iff] at h'
      exact v.isPrime.ne_top h'
    refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ hmem)
    exact dvd_pow_self _ (by omega)

end ArtinConductor
