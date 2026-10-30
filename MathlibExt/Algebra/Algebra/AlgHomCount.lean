/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgHom_natCard_eq_finrank_of_isReduced_of_isAlgClosed.lean` and
`P2M/Sol/S_AlgHom_natCard_eq_finrank_of_isReduced_of_isAlgClosed.lean`
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

public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# Algebra homomorphisms into an algebraically closed field

A finite reduced algebra over an algebraically closed field has as many
algebra homomorphisms to the field as its dimension: the algebra is the
product of its residue fields at maximal ideals, each a copy of the field,
and homomorphisms correspond bijectively to maximal ideals.
-/

@[expose] public section

/-- A finite reduced algebra over an algebraically closed field has
`finrank` many algebra homomorphisms to the field. -/
theorem AlgHom.natCard_eq_finrank_of_isReduced_of_isAlgClosed
    (K B : Type*) [Field K] [IsAlgClosed K] [CommRing B] [Algebra K B]
    [Module.Finite K B] [IsReduced B] :
    Nat.card (B →ₐ[K] K) = Module.finrank K B := by
  classical
  have : IsArtinianRing B := IsArtinianRing.of_finite K B
  have : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  have hquot : ∀ I : MaximalSpectrum B, Module.finrank K (B ⧸ I.asIdeal) = 1 := by
    intro I
    let _ : Field (B ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    have : Module.Finite K (B ⧸ I.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ K I.asIdeal).toLinearMap
        (Ideal.Quotient.mkₐ_surjective K I.asIdeal)
    have : Algebra.IsAlgebraic K (B ⧸ I.asIdeal) := Algebra.IsAlgebraic.of_finite K _
    have hbij : Function.Bijective (algebraMap K (B ⧸ I.asIdeal)) :=
      IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := B ⧸ I.asIdeal)
    have e : K ≃ₗ[K] (B ⧸ I.asIdeal) :=
      LinearEquiv.ofBijective (Algebra.linearMap K (B ⧸ I.asIdeal)) hbij
    rw [← e.finrank_eq, Module.finrank_self]
  let e : B ≃ₐ[K] ((I : MaximalSpectrum B) → B ⧸ I.asIdeal) :=
    AlgEquiv.ofRingEquiv (f := IsArtinianRing.equivPi B) (fun r => by
      ext I
      rfl)
  have hfin : Module.finrank K B = Fintype.card (MaximalSpectrum B) := by
    rw [e.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]
    simp [hquot]
  have hker_max : ∀ φ : B →ₐ[K] K, (RingHom.ker φ.toRingHom).IsMaximal := fun φ =>
    RingHom.ker_isMaximal_of_surjective φ.toRingHom (fun k => ⟨algebraMap K B k, by simp⟩)
  let kerMap : (B →ₐ[K] K) → MaximalSpectrum B := fun φ => ⟨RingHom.ker φ.toRingHom, hker_max φ⟩
  have hinj : Function.Injective kerMap := by
    intro φ ψ h
    have hk : RingHom.ker φ.toRingHom = RingHom.ker ψ.toRingHom :=
      congrArg MaximalSpectrum.asIdeal h
    apply AlgHom.ext
    intro b
    have h1 : b - algebraMap K B (φ b) ∈ RingHom.ker ψ.toRingHom := by
      rw [← hk, RingHom.mem_ker]
      simp
    rw [RingHom.mem_ker] at h1
    have hthis : ψ b - φ b = 0 := by
      simpa [map_sub, AlgHom.commutes] using h1
    exact (sub_eq_zero.mp hthis).symm
  have hsurj : Function.Surjective kerMap := by
    intro I
    let _ : Field (B ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    have : Module.Finite K (B ⧸ I.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ K I.asIdeal).toLinearMap
        (Ideal.Quotient.mkₐ_surjective K I.asIdeal)
    have : Algebra.IsAlgebraic K (B ⧸ I.asIdeal) := Algebra.IsAlgebraic.of_finite K _
    have hbij : Function.Bijective (algebraMap K (B ⧸ I.asIdeal)) :=
      IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := B ⧸ I.asIdeal)
    let eI : K ≃ₐ[K] (B ⧸ I.asIdeal) := AlgEquiv.ofBijective (Algebra.ofId K (B ⧸ I.asIdeal)) hbij
    let φ : B →ₐ[K] K := (eI.symm : (B ⧸ I.asIdeal) →ₐ[K] K).comp (Ideal.Quotient.mkₐ K I.asIdeal)
    refine ⟨φ, ?_⟩
    apply MaximalSpectrum.ext
    change RingHom.ker φ.toRingHom = I.asIdeal
    ext b
    rw [RingHom.mem_ker]
    change eI.symm (Ideal.Quotient.mk I.asIdeal b) = 0 ↔ b ∈ I.asIdeal
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_eq_zero_iff _ eI.symm.injective]
  have : Fintype (B →ₐ[K] K) := Fintype.ofFinite _
  rw [hfin, Nat.card_eq_fintype_card]
  exact Fintype.card_of_bijective ⟨hinj, hsurj⟩
