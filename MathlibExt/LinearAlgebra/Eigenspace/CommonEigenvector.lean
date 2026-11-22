/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Module_End_exists_common_eigenvector_of_commute.lean`
and
`P2M/Sol/S_Module_End_exists_common_eigenvector_of_commute.lean`
and
`Theorems/Thm_DeligneSerre_exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul.lean`
and
`P2M/Sol/S_DeligneSerre_exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul.lean`
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

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

@[expose] public section

open Module
open scoped IsMulCommutative

private theorem exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul
    {K : Type*} [Field K] [IsAlgClosed K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {T : Type*} [CommRing T] [Module T V] [SMulCommClass T K V] [FaithfulSMul T V]
    {𝔭 : Ideal T} (h𝔭 : 𝔭 ∈ minimalPrimes T) :
    ∃ χ : T →+* K, RingHom.ker χ = 𝔭 ∧
      ∃ x : V, x ≠ 0 ∧ (∀ p ∈ 𝔭, p • x = 0) ∧ (∀ r : T, r • x = 0 → r ∈ 𝔭) ∧
        ∀ t : T, t • x = χ t • x := by
  classical
  let φ : T →+* Module.End K V := Module.toModuleEnd K V
  have hφ : ∀ (t : T) (v : V), φ t v = t • v := fun t v => rfl
  have hφinj : Function.Injective φ := by
    intro t t' h
    exact FaithfulSMul.eq_of_smul_eq_smul (M := T) (α := V) fun v => by
      rw [← hφ, ← hφ, h]
  let A : Subalgebra K (Module.End K V) := Algebra.adjoin K (Set.range φ)
  haveI : IsMulCommutative A := Algebra.isMulCommutative_adjoin (R := K) (by
    rintro _ ⟨t, rfl⟩ _ ⟨t', rfl⟩ _
    show φ t * φ t' = φ t' * φ t
    rw [← map_mul, ← map_mul, mul_comm])
  haveI : Module.Finite K A :=
    Module.Finite.of_injective A.val.toLinearMap Subtype.val_injective
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  haveI : IsScalarTower K A V := ⟨fun c a v => by
    simp only [Subalgebra.smul_def, Subalgebra.coe_smul, LinearMap.smul_apply,
      Module.End.smul_def]⟩
  haveI : Module.Finite A V := Module.Finite.of_restrictScalars_finite K A V
  have hann : Module.annihilator A V = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [Module.mem_annihilator] at ha
    rw [Submodule.mem_bot]
    exact Subtype.ext (LinearMap.ext fun v => by simpa [Subalgebra.smul_def] using ha v)
  let φA : T →+* A := φ.codRestrict A fun t => Algebra.subset_adjoin ⟨t, rfl⟩
  have hφA : ∀ t : T, ((φA t : A) : Module.End K V) = φ t := fun t => rfl
  have hφAinj : Function.Injective φA := fun t t' h =>
    hφinj (by rw [← hφA, ← hφA, h])
  have hφAsmul : ∀ (t : T) (v : V), φA t • v = t • v := fun t v => rfl
  haveI h𝔭prime : 𝔭.IsPrime := h𝔭.1.1
  have hfin : (minimalPrimes A).Finite := minimalPrimes.finite_of_isNoetherianRing A
  obtain ⟨𝔓, h𝔓min, h𝔓le⟩ : ∃ 𝔓 ∈ minimalPrimes A, 𝔓.comap φA ≤ 𝔭 := by
    have hinf : hfin.toFinset.inf (fun 𝔓 => 𝔓.comap φA) ≤ 𝔭 := by
      intro t ht
      have hmem : φA t ∈ sInf (minimalPrimes A) := by
        rw [Ideal.mem_sInf]
        intro 𝔓 h𝔓
        have hle : hfin.toFinset.inf (fun 𝔓 => 𝔓.comap φA) ≤ 𝔓.comap φA :=
          Finset.inf_le (hfin.mem_toFinset.mpr h𝔓)
        exact Ideal.mem_comap.mp (hle ht)
      have hnil : IsNilpotent (φA t) := by
        have h' : φA t ∈ (⊥ : Ideal A).radical := by
          rw [← Ideal.sInf_minimalPrimes]; exact hmem
        exact h'
      obtain ⟨n, hn⟩ := hnil
      have htn : t ^ n = 0 := hφAinj (by rw [map_pow, hn, map_zero])
      exact h𝔭prime.mem_of_pow_mem n (htn ▸ 𝔭.zero_mem)
    obtain ⟨𝔓, h𝔓S, h𝔓le⟩ := (Ideal.IsPrime.inf_le' h𝔭prime).mp hinf
    exact ⟨𝔓, hfin.mem_toFinset.mp h𝔓S, h𝔓le⟩
  haveI h𝔓prime : 𝔓.IsPrime := h𝔓min.1.1
  have hcomap : 𝔓.comap φA = 𝔭 :=
    le_antisymm h𝔓le (h𝔭.2 ⟨Ideal.comap_isPrime φA 𝔓, bot_le⟩ h𝔓le)
  have hass : 𝔓 ∈ associatedPrimes A V := by
    refine Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes A V ?_
    rw [hann]
    exact h𝔓min
  obtain ⟨-, x, hx⟩ := (isAssociatedPrime_iff.mp hass)
  have hx' : ∀ a : A, a ∈ 𝔓 ↔ a • x = 0 := fun a => by
    rw [hx, Submodule.mem_colon_singleton, Submodule.mem_bot]
  have hx0 : x ≠ 0 := by
    intro h0
    apply h𝔓prime.ne_top
    rw [eq_top_iff]
    intro a _
    rw [hx' a, h0, smul_zero]
  haveI : 𝔓.IsMaximal := IsArtinianRing.isMaximal_of_isPrime 𝔓
  haveI : Module.Finite K (A ⧸ 𝔓) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K 𝔓).toLinearMap
      (Ideal.Quotient.mkₐ_surjective K 𝔓)
  haveI : Algebra.IsIntegral K (A ⧸ 𝔓) := Algebra.IsIntegral.of_finite K _
  let e : K ≃+* A ⧸ 𝔓 :=
    RingEquiv.ofBijective (algebraMap K (A ⧸ 𝔓)) IsAlgClosed.algebraMap_bijective_of_isIntegral
  let χA : A →+* K := e.symm.toRingHom.comp (Ideal.Quotient.mk 𝔓)
  have hχA : ∀ a : A, a - algebraMap K A (χA a) ∈ 𝔓 := by
    intro a
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, Ideal.Quotient.mk_algebraMap]
    change Ideal.Quotient.mk 𝔓 a = e (e.symm (Ideal.Quotient.mk 𝔓 a))
    exact (e.apply_symm_apply (Ideal.Quotient.mk 𝔓 a)).symm
  have hkerA : RingHom.ker χA = 𝔓 := by
    ext a
    rw [RingHom.mem_ker]
    change e.symm (Ideal.Quotient.mk 𝔓 a) = 0 ↔ a ∈ 𝔓
    rw [EmbeddingLike.map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  have heigA : ∀ a : A, a • x = χA a • x := by
    intro a
    have h := (hx' _).mp (hχA a)
    rwa [sub_smul, sub_eq_zero, algebraMap_smul] at h
  refine ⟨χA.comp φA, ?_, x, hx0, ?_, ?_, ?_⟩
  · rw [← RingHom.comap_ker, hkerA, hcomap]
  · intro p hp
    have : φA p ∈ 𝔓 := by rw [← hcomap] at hp; exact Ideal.mem_comap.mp hp
    rw [← hφAsmul, (hx' _).mp this]
  · intro r hr
    rw [← hcomap, Ideal.mem_comap, hx', hφAsmul]
    exact hr
  · intro t
    rw [← hφAsmul, heigA]
    rfl

namespace Module.End

/-- A commuting family of endomorphisms of a nonzero finite-dimensional
vector space over an algebraically closed field has a common eigenvector. -/
public theorem exists_common_eigenvector_of_commute
    {K : Type*} [Field K] [IsAlgClosed K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Nontrivial V] {ι : Type*} (T : ι → Module.End K V)
    (hcomm : ∀ i j, Commute (T i) (T j)) :
    ∃ (χ : ι → K) (v : V), v ≠ 0 ∧ ∀ i, T i v = χ i • v := by
  classical
  let A : Subalgebra K (Module.End K V) := Algebra.adjoin K (Set.range T)
  haveI : IsMulCommutative A := Algebra.isMulCommutative_adjoin K
    (by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
      exact hcomm i j)
  letI : CommRing A := inferInstance
  haveI : Nontrivial A :=
    ⟨⟨0, 1, fun h => (zero_ne_one (α := Module.End K V)) (Subtype.ext_iff.mp h)⟩⟩
  obtain ⟨⟨𝔭, h𝔭⟩⟩ := Ideal.nonempty_minimalPrimes (R := A) (I := ⊥) bot_ne_top
  have h𝔭' : 𝔭 ∈ minimalPrimes A := h𝔭
  obtain ⟨χ, -, v, hv0, -, -, heig⟩ :=
    exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul
      (K := K) (V := V) (T := A) h𝔭'
  have hTmem : ∀ i, T i ∈ A := fun i => Algebra.subset_adjoin ⟨i, rfl⟩
  refine ⟨fun i => χ ⟨T i, hTmem i⟩, v, hv0, fun i => ?_⟩
  have h : (⟨T i, hTmem i⟩ : A) • v = χ ⟨T i, hTmem i⟩ • v := heig _
  simp only [Subalgebra.smul_def, Subalgebra.coe_smul] at h
  exact h

end Module.End
