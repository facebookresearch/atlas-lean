/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsRegularLocalRing_isDomain.lean` and
`P2M/Sol/S_IsRegularLocalRing_isDomain.lean`
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

public import MathlibExt.RingTheory.RegularLocalRing.QuotientSpanSingleton
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.Field

/-!
# Regular local rings are domains

Matsumura's argument: induct on the embedding dimension. A parameter
outside the square of the maximal ideal and outside every minimal prime
exists by prime avoidance; quotienting by it drops the embedding
dimension by one and stays regular; a minimal prime below its span is
forced to be zero by Nakayama, so the bottom ideal is prime.
-/

@[expose] public section

universe u

open IsLocalRing

namespace RegularDomainAux

private theorem maximalIdeal_ne_bot_of_ringKrullDim_pos (R : Type u) [CommRing R]
    [IsLocalRing R] (hdim : 0 < ringKrullDim R) : maximalIdeal R ≠ ⊥ := by
  intro hbot
  rw [ringKrullDim_eq_zero_of_isField
    (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hbot)] at hdim
  exact hdim.false

private theorem maximalIdeal_notMem_minimalPrimes_of_ringKrullDim_pos
    (R : Type u) [CommRing R] [IsLocalRing R] (hdim : 0 < ringKrullDim R) :
    maximalIdeal R ∉ minimalPrimes R := by
  intro hmem
  have hall : ∀ p : PrimeSpectrum R, p.asIdeal = maximalIdeal R := fun p =>
    le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top)
      (hmem.2 ⟨p.isPrime, bot_le⟩ (IsLocalRing.le_maximalIdeal p.isPrime.ne_top))
  have : Subsingleton (PrimeSpectrum R) :=
    ⟨fun p q => PrimeSpectrum.ext ((hall p).trans (hall q).symm)⟩
  have heq : ringKrullDim R = 0 := by
    rw [ringKrullDim]
    have : Nonempty (PrimeSpectrum R) := ⟨⟨maximalIdeal R, inferInstance⟩⟩
    let _ : Unique (PrimeSpectrum R) := uniqueOfSubsingleton (Classical.arbitrary _)
    exact Order.krullDim_eq_zero_of_unique
  rw [heq] at hdim
  exact hdim.false

end RegularDomainAux

/-- In a Noetherian local ring of positive Krull dimension, there is a
parameter in the maximal ideal, outside its square and outside every
minimal prime. -/
theorem IsLocalRing.exists_mem_maximalIdeal_notMem_sq_forall_minimalPrimes_notMem
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : 0 < ringKrullDim R) :
    ∃ x ∈ maximalIdeal R, x ∉ (maximalIdeal R) ^ 2 ∧
      ∀ p ∈ minimalPrimes R, x ∉ p := by
  classical
  have hbot : maximalIdeal R ≠ ⊥ :=
    RegularDomainAux.maximalIdeal_ne_bot_of_ringKrullDim_pos R hdim
  have hfin : (insert ((maximalIdeal R) ^ 2) (minimalPrimes R)).Finite :=
    Set.Finite.insert _ (minimalPrimes.finite_of_isNoetherianRing R)
  have hnotle : ¬ ∃ I ∈ hfin.toFinset, maximalIdeal R ≤ I := by
    rintro ⟨I, hIs, hle⟩
    rw [Set.Finite.mem_toFinset, Set.mem_insert_iff] at hIs
    rcases hIs with rfl | hI
    · refine hbot (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R)
        (maximalIdeal R) (IsNoetherian.noetherian _) ?_
        (IsLocalRing.maximalIdeal_le_jacobson _))
      rwa [Ideal.smul_eq_mul, ← pow_two]
    · have hp_prime : I.IsPrime := Ideal.IsMinimalPrime.isPrime hI
      have heq : I = maximalIdeal R :=
        (IsLocalRing.le_maximalIdeal hp_prime.ne_top).antisymm hle
      rw [heq] at hI
      exact RegularDomainAux.maximalIdeal_notMem_minimalPrimes_of_ringKrullDim_pos R hdim hI
  have havoid : ¬ ((maximalIdeal R : Set R) ⊆
      ⋃ I ∈ (hfin.toFinset : Set (Ideal R)), (I : Set R)) := by
    intro hsub
    refine hnotle ((Ideal.subset_union_prime (s := hfin.toFinset) (f := fun I => I)
      ((maximalIdeal R) ^ 2) ((maximalIdeal R) ^ 2) ?_).mp hsub)
    intro I hIs hI₁ _
    rw [Set.Finite.mem_toFinset, Set.mem_insert_iff] at hIs
    rcases hIs with rfl | hI
    · exact absurd rfl hI₁
    · exact Ideal.IsMinimalPrime.isPrime hI
  rw [hfin.coe_toFinset] at havoid
  obtain ⟨x, hxm, hxout⟩ := Set.not_subset.mp havoid
  refine ⟨x, hxm, ?_, ?_⟩
  · intro hx2
    exact hxout (Set.mem_biUnion (Set.mem_insert _ _) hx2)
  · intro p hp hxp
    exact hxout (Set.mem_biUnion (Set.mem_insert_of_mem _ hp) hxp)

namespace RegularDomainAux

private theorem isDomain_of_isRegularLocalRing_aux :
    ∀ (n : ℕ) (R : Type u) [CommRing R] [IsRegularLocalRing R],
      (maximalIdeal R).spanFinrank = n → IsDomain R := by
  intro n
  induction n with
  | zero =>
    intro R _ _ hn
    have hbot : maximalIdeal R = ⊥ :=
      (Submodule.spanFinrank_eq_zero_iff_eq_bot
        ((maximalIdeal R).fg_of_isNoetherianRing)).mp hn
    have hprime : (⊥ : Ideal R).IsPrime := hbot ▸ (maximalIdeal.isMaximal R).isPrime
    exact IsDomain.of_bot_isPrime R
  | succ n IH =>
    intro R _ _ hn
    have hdim : ringKrullDim R = ((n + 1 : ℕ) : WithBot ℕ∞) := by
      rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R), hn]
    have hdim_pos : 0 < ringKrullDim R := by
      rw [hdim]
      exact_mod_cast Nat.succ_pos n
    obtain ⟨x, hx_mem, hx_sq, hx_min⟩ :=
      IsLocalRing.exists_mem_maximalIdeal_notMem_sq_forall_minimalPrimes_notMem R hdim_pos
    have hloc : IsLocalRing (R ⧸ Ideal.span {x}) := by
      have hne : Ideal.span {x} ≠ ⊤ := by
        intro h
        exact (maximalIdeal.isMaximal R).ne_top
          (top_le_iff.mp (h ▸ Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx_mem)))
      have : Nontrivial (R ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr hne
      exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    obtain ⟨hreg', hsf'⟩ :=
      IsRegularLocalRing.quotient_span_singleton_of_notMem_sq_of_forall_minimalPrimes_notMem
        R hx_mem hx_sq hx_min
    have : IsRegularLocalRing (R ⧸ Ideal.span {x}) := hreg'
    have hsf'n : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank = n := by
      rw [hn] at hsf'
      omega
    have hdom' : IsDomain (R ⧸ Ideal.span {x}) := IH (R ⧸ Ideal.span {x}) hsf'n
    have hprime : (Ideal.span {x}).IsPrime := by
      rw [← Ideal.Quotient.isDomain_iff_prime]
      exact hdom'
    have : (Ideal.span {x}).IsPrime := hprime
    obtain ⟨p, hp_min, hp_le⟩ :=
      Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R)) (J := Ideal.span {x}) bot_le
    have hp_prime : p.IsPrime := Ideal.IsMinimalPrime.isPrime hp_min
    have hxp : x ∉ p := hx_min p hp_min
    have hple : p ≤ (maximalIdeal R) • p := by
      intro a ha
      obtain ⟨r, hrx⟩ := Ideal.mem_span_singleton'.mp (hp_le ha)
      have hrp : r ∈ p := by
        have hmem : r * x ∈ p := by rw [hrx]; exact ha
        rcases hp_prime.mem_or_mem hmem with h | h
        · exact h
        · exact absurd h hxp
      rw [Ideal.smul_eq_mul, ← hrx, mul_comm r x]
      exact Ideal.mul_mem_mul hx_mem hrp
    have hp_bot : p = ⊥ :=
      Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) p
        (IsNoetherian.noetherian p) hple (IsLocalRing.maximalIdeal_le_jacobson _)
    have : (⊥ : Ideal R).IsPrime := hp_bot ▸ hp_prime
    exact IsDomain.of_bot_isPrime R

end RegularDomainAux

/-- Every regular local ring is a domain. -/
theorem IsRegularLocalRing.isDomain (R : Type*) [CommRing R] [IsRegularLocalRing R] :
    IsDomain R :=
  RegularDomainAux.isDomain_of_isRegularLocalRing_aux ((maximalIdeal R).spanFinrank) R rfl
