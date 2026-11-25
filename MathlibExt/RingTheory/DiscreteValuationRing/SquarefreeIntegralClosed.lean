/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsDiscreteValuationRing_isIntegrallyClosedIn_adjoin_singleton_of_squarefree.lean`
and
`P2M/Sol/S_IsDiscreteValuationRing_isIntegrallyClosedIn_adjoin_singleton_of_squarefree.lean`
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

public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.RingTheory.Nilpotent.Lemmas

@[expose] public section

open Polynomial IsLocalRing

private theorem isReduced_quotient_span_singleton_of_squarefree {R : Type*}
    [CommRing R] [DecompositionMonoid R] {f : R} (hf : Squarefree f) :
    IsReduced (R ⧸ Ideal.span {f}) := by
  rw [← Ideal.isRadical_iff_quotient_reduced, ← isRadical_iff_span_singleton]
  exact hf.isRadical

private theorem pow_natDegree_mem_of_aeval_scaleRoots_eq_zero {B : Type*}
    [CommRing B] {p : B[X]} (hp : p.Monic) {s b : B} (I : Ideal B) (hs : s ∈ I)
    (h : aeval b (p.scaleRoots s) = 0) : b ^ p.natDegree ∈ I := by
  have hsum : aeval b (p.scaleRoots s) =
      ∑ i ∈ Finset.range ((p.scaleRoots s).natDegree + 1),
        (p.scaleRoots s).coeff i * b ^ i := by
    rw [aeval_def, eval₂_eq_sum_range]
    rfl
  rw [h, natDegree_scaleRoots, Finset.sum_range_succ, coeff_scaleRoots,
    Nat.sub_self, pow_zero, mul_one, hp.coeff_natDegree, one_mul] at hsum
  have hrest : (∑ i ∈ Finset.range p.natDegree,
      (p.scaleRoots s).coeff i * b ^ i) ∈ I := by
    refine Ideal.sum_mem _ fun i hi => ?_
    rw [Finset.mem_range] at hi
    refine Ideal.mul_mem_right _ _ ?_
    rw [coeff_scaleRoots]
    refine Ideal.mul_mem_left _ _ ?_
    exact Ideal.pow_mem_of_mem I hs (p.natDegree - i) (by omega)
  have hb : b ^ p.natDegree =
      -(∑ i ∈ Finset.range p.natDegree, (p.scaleRoots s).coeff i * b ^ i) :=
    eq_neg_of_add_eq_zero_right hsum.symm
  rw [hb]
  exact I.neg_mem_iff.mpr hrest

private theorem mem_span_of_isIntegral_mk' {B : Type*} [CommRing B] (ϖ : B)
    [IsReduced (B ⧸ Ideal.span {ϖ})]
    (L : Type*) [CommRing L] [Algebra B L] [IsLocalization.Away ϖ L]
    (hinj : Function.Injective (algebraMap B L))
    (m : ℕ) (b : B)
    (hz : IsIntegral B (IsLocalization.mk' L b
      (⟨ϖ ^ (m + 1), m + 1, rfl⟩ : Submonoid.powers ϖ))) :
    b ∈ Ideal.span {ϖ} := by
  obtain ⟨p, hp, hpz⟩ := hz
  have h1 := scaleRoots_aeval_eq_zero_of_aeval_mk'_eq_zero hpz
  rw [aeval_algebraMap_apply L b, map_eq_zero_iff _ hinj] at h1
  have hbn : b ^ p.natDegree ∈ Ideal.span {ϖ} :=
    pow_natDegree_mem_of_aeval_scaleRoots_eq_zero hp (Ideal.span {ϖ})
      (Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_singleton ϖ))
        (m + 1) (Nat.succ_pos m)) h1
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply IsReduced.eq_zero
  refine ⟨p.natDegree, ?_⟩
  have := (Ideal.Quotient.eq_zero_iff_mem (I := Ideal.span {ϖ})).mpr hbn
  simpa only [map_pow] using this

private theorem isIntegrallyClosedIn_of_isReduced_quotient_span_singleton
    {B : Type*} [CommRing B] (ϖ : B) (hϖ : ϖ ∈ nonZeroDivisors B)
    [IsReduced (B ⧸ Ideal.span {ϖ})]
    (L : Type*) [CommRing L] [Algebra B L] [IsLocalization.Away ϖ L] :
    IsIntegrallyClosedIn B L := by
  have hle : Submonoid.powers ϖ ≤ nonZeroDivisors B :=
    (Submonoid.powers_le).mpr hϖ
  have hinj : Function.Injective (algebraMap B L) :=
    IsLocalization.injective L hle
  rw [isIntegrallyClosedIn_iff]
  refine ⟨hinj, ?_⟩
  suffices key : ∀ (m : ℕ) (b : B),
      IsIntegral B (IsLocalization.mk' L b
        (⟨ϖ ^ m, m, rfl⟩ : Submonoid.powers ϖ)) →
      ∃ y, algebraMap B L y = IsLocalization.mk' L b
        (⟨ϖ ^ m, m, rfl⟩ : Submonoid.powers ϖ) by
    intro z hz
    obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers ϖ) z
    obtain ⟨_, m, rfl⟩ := s
    exact key m b hz
  intro m
  induction m with
  | zero =>
    intro b _
    refine ⟨b, ?_⟩
    rw [IsLocalization.eq_mk'_iff_mul_eq]
    simp
  | succ m ih =>
    intro b hz
    have hb : b ∈ Ideal.span {ϖ} := mem_span_of_isIntegral_mk' ϖ L hinj m b hz
    obtain ⟨b', rfl⟩ := Ideal.mem_span_singleton'.mp hb
    have heq : IsLocalization.mk' L (b' * ϖ)
        (⟨ϖ ^ (m + 1), m + 1, rfl⟩ : Submonoid.powers ϖ) =
        IsLocalization.mk' L b' (⟨ϖ ^ m, m, rfl⟩ : Submonoid.powers ϖ) := by
      rw [IsLocalization.mk'_eq_iff_eq]
      congr 1
      simp only [pow_succ]
      ring
    rw [heq] at hz ⊢
    exact ih b' hz

/-- Dedekind's squarefree-reduction criterion: if `ϖ` is an irreducible
element of a discrete valuation ring `O`, `α` is integral over `O`, the
reduction of the minimal polynomial of `α` modulo `ϖ` is squarefree, and
every element of the field `F` acquires a denominator that is a power of
`ϖ` landing in `O[α]`, then `O[α]` is integrally closed in `F`. -/
public theorem IsDiscreteValuationRing.isIntegrallyClosedIn_adjoin_singleton_of_squarefree
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ : O} (hϖ : Irreducible ϖ)
    {F : Type*} [Field F] [Algebra O F] [FaithfulSMul O F]
    {α : F} (hα : IsIntegral O α)
    (hsq : Squarefree ((minpoly O α).map
      (Ideal.Quotient.mk (Ideal.span {ϖ}))))
    (hgen : ∀ x : F, ∃ n : ℕ, algebraMap O F ϖ ^ n * x ∈
      Algebra.adjoin O {α}) :
    IsIntegrallyClosedIn (Algebra.adjoin O {α}) F := by
  set B : Subalgebra O F := Algebra.adjoin O {α} with hB
  have hinjOF : Function.Injective (algebraMap O F) :=
    FaithfulSMul.algebraMap_injective O F
  have hϖF : algebraMap O F ϖ ≠ 0 := (map_ne_zero_iff _ hinjOF).mpr hϖ.ne_zero
  set ϖB : B := algebraMap O B ϖ with hϖB_def
  have hϖBval : (ϖB : F) = algebraMap O F ϖ := rfl
  have hϖB0 : ϖB ≠ 0 := fun h => hϖF (by rw [← hϖBval, h]; rfl)
  have hϖB : ϖB ∈ nonZeroDivisors B := mem_nonZeroDivisors_iff_ne_zero.mpr hϖB0
  haveI : IsReduced (B ⧸ Ideal.span {ϖB}) := by
    have hmax : (Ideal.span {ϖ}).IsMaximal := by
      rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]
      exact IsLocalRing.maximalIdeal.isMaximal (R := O)
    letI : Field (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field (Ideal.span {ϖ})
    have e : AdjoinRoot (minpoly O α) ≃ₐ[O] B := minpoly.equivAdjoin hα
    have hJ : Ideal.span {ϖB} =
        Ideal.map (e : AdjoinRoot (minpoly O α) →+* B)
          (Ideal.map (AdjoinRoot.of (minpoly O α)) (Ideal.span {ϖ})) := by
      rw [Ideal.map_map, Ideal.map_span, Set.image_singleton]
      congr 2
      change algebraMap O B ϖ = e (algebraMap O (AdjoinRoot (minpoly O α)) ϖ)
      rw [AlgEquiv.commutes]
    let e1 := Ideal.quotientEquivAlg
      (Ideal.map (AdjoinRoot.of (minpoly O α)) (Ideal.span {ϖ}))
      (Ideal.span {ϖB}) e hJ
    let e2 := AdjoinRoot.quotEquivQuotMap (minpoly O α) (Ideal.span {ϖ})
    haveI : IsReduced (Polynomial (O ⧸ Ideal.span {ϖ}) ⧸
        Ideal.span (Set.singleton ((minpoly O α).map
          (Ideal.Quotient.mk (Ideal.span {ϖ}))))) :=
      isReduced_quotient_span_singleton_of_squarefree hsq
    exact isReduced_of_injective (e1.symm.trans e2).toRingEquiv
      (e1.symm.trans e2).toRingEquiv.injective
  haveI : IsLocalization.Away ϖB F := by
    rw [IsLocalization.Away, isLocalization_iff]
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨y, hy⟩
      obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff y ϖB).mp hy
      rw [map_pow]
      exact IsUnit.pow n (isUnit_iff_ne_zero.mpr (by
        rw [show algebraMap B F ϖB = algebraMap O F ϖ from rfl]; exact hϖF))
    · intro s
      obtain ⟨n, hn⟩ := hgen s
      refine ⟨⟨⟨algebraMap O F ϖ ^ n * s, hn⟩,
        ⟨ϖB ^ n, n, rfl⟩⟩, ?_⟩
      change s * (algebraMap O F ϖ) ^ n = algebraMap O F ϖ ^ n * s
      ring
    · intro a b h
      refine ⟨1, ?_⟩
      have hab : a = b := Subtype.val_injective h
      rw [hab]
  exact isIntegrallyClosedIn_of_isReduced_quotient_span_singleton ϖB hϖB F
