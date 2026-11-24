/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_RingHom_Etale_isPushout_frobenius.lean`
and
`P2M/Sol/S_RingHom_Etale_isPushout_frobenius.lean`
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

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.RingHom.Etale
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Finiteness.Nakayama
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Unramified.Basic

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits



namespace EtaleFrobeniusPushoutAux

open TensorProduct


private theorem surjective_algebraMap_of_pow_mem_range
    (K C : Type*) [Field K] [CommRing C] [Algebra K C]
    [Algebra.FormallyUnramified K C] [Algebra.EssFiniteType K C]
    (p : ℕ) [ExpChar K p]
    (h : ∀ x : C, x ^ p ∈ (algebraMap K C).range) :
    Function.Surjective (algebraMap K C) := by
  classical
  rcases subsingleton_or_nontrivial C with hC | hC
  · intro x
    exact ⟨0, Subsingleton.elim _ _⟩
  intro x
  have hinj : Function.Injective (algebraMap K (C ⊗[K] C)) := (algebraMap K _).injective
  have : ExpChar (C ⊗[K] C) p := expChar_of_injective_ringHom hinj p
  have hnil : (1 ⊗ₜ x - x ⊗ₜ 1 : C ⊗[K] C) ^ p = 0 := by
    rw [sub_pow_expChar, Algebra.TensorProduct.tmul_pow, one_pow,
      Algebra.TensorProduct.tmul_pow, one_pow]
    obtain ⟨r, hr⟩ := h x
    rw [← hr, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, sub_self]
  have H : (1 ⊗ₜ x : C ⊗[K] C) = x ⊗ₜ 1 := by
    haveI : Algebra.FormallyUnramified K (C ⊗[K] C) := Algebra.FormallyUnramified.comp K C _
    haveI : Algebra.EssFiniteType K (C ⊗[K] C) := Algebra.EssFiniteType.comp K C _
    have inst : IsReduced (C ⊗[K] C) := Algebra.FormallyUnramified.isReduced_of_field K _
    exact sub_eq_zero.mp (IsNilpotent.eq_zero ⟨_, hnil⟩)
  by_cases h' : LinearIndependent K ![1, x]
  · have hli := h'.linearIndepOn_id
    let S := hli.extend (Set.subset_univ _)
    let a : S := ⟨1, hli.subset_extend _ (by simp)⟩
    have ha : Module.Basis.extend hli a = 1 := by simp [a]
    let b : S := ⟨x, hli.subset_extend _ (by simp)⟩
    have hb : Module.Basis.extend hli b = x := by simp [b]
    by_cases e : a = b
    · obtain rfl : 1 = x := congr_arg Subtype.val e
      exact ⟨1, map_one _⟩
    have := DFunLike.congr_fun
      (DFunLike.congr_arg
        ((Module.Basis.extend hli).tensorProduct (Module.Basis.extend hli)).repr H)
        (a, b)
    simp only [Module.Basis.tensorProduct_repr_tmul_apply, ← ha, ← hb, Module.Basis.repr_self,
      smul_eq_mul, Finsupp.single_apply, e, Ne.symm e, ↓reduceIte, mul_one, mul_zero,
      one_ne_zero] at this
  · rw [LinearIndependent.pair_iff] at h'
    simp only [not_forall, not_and, exists_prop] at h'
    obtain ⟨a, b, e, hab⟩ := h'
    have : IsUnit b := by
      rw [isUnit_iff_ne_zero]
      rintro rfl
      rw [zero_smul, ← Algebra.algebraMap_eq_smul_one, add_zero,
        (injective_iff_map_eq_zero' _).mp (algebraMap K C).injective] at e
      cases hab e rfl
    use (-this.unit⁻¹ * a)
    rw [map_mul, ← Algebra.smul_def, Algebra.algebraMap_eq_smul_one, eq_neg_iff_add_eq_zero.mpr e,
      smul_neg, neg_smul, neg_neg, smul_smul, this.val_inv_mul, one_smul]

section

variable {A P B : Type*} [CommRing A] [CommRing P] [CommRing B]
  [Algebra A P] [Algebra A B] [Algebra P B] [IsScalarTower A P B]

private theorem surjective_algebraMap_of_frobenius_factor
    (p : ℕ) [Fact p.Prime] [CharP P p]
    [Algebra.FormallyUnramified P B] [Algebra.FiniteType P B]
    (G : B → P) (hGΦ : ∀ b : B, algebraMap P B (G b) = b ^ p) :
    Function.Surjective (algebraMap P B) := by
  classical
  have hp : p.Prime := Fact.out

  have hint : Algebra.IsIntegral P B := by
    refine ⟨fun b => ?_⟩
    refine ⟨Polynomial.X ^ p - Polynomial.C (G b), ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub_C _ hp.ne_zero
    · simp [hGΦ]
  have hfin : Module.Finite P B := Algebra.IsIntegral.finite

  set N : Submodule P B := LinearMap.range (Algebra.linearMap P B) with hN
  suffices hN' : N = ⊤ by
    intro b
    have hb : b ∈ N := hN' ▸ Submodule.mem_top
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hb
    exact ⟨x, hx⟩
  by_contra hNtop

  have hM : Nontrivial (B ⧸ N) := Submodule.Quotient.nontrivial_iff.mpr hNtop
  set ann : Ideal P := Module.annihilator P (B ⧸ N) with hann
  have hann_ne : ann ≠ ⊤ := by
    intro htop
    have h1 : (1 : P) ∈ ann := htop ▸ Submodule.mem_top
    rw [hann, Module.mem_annihilator] at h1
    obtain ⟨m, hm⟩ := exists_ne (0 : B ⧸ N)
    exact hm (by simpa using h1 m)
  obtain ⟨𝔪, h𝔪max, hann𝔪⟩ := Ideal.exists_le_maximal ann hann_ne

  letI : Field (P ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  have hntP : Nontrivial (P ⧸ 𝔪) := inferInstance
  have hcharL : CharP (P ⧸ 𝔪) p := by
    rw [CharP.charP_iff_prime_eq_zero hp, ← map_natCast (Ideal.Quotient.mk 𝔪), CharP.cast_eq_zero,
      map_zero]
  haveI : ExpChar (P ⧸ 𝔪) p := ExpChar.prime hp
  set 𝔪B : Ideal B := 𝔪.map (algebraMap P B) with h𝔪B
  have hsurjL : Function.Surjective (algebraMap (P ⧸ 𝔪) (B ⧸ 𝔪B)) := by
    apply surjective_algebraMap_of_pow_mem_range (P ⧸ 𝔪) (B ⧸ 𝔪B) p
    intro c
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
    refine ⟨Ideal.Quotient.mk 𝔪 (G b), ?_⟩
    rw [← map_pow, ← hGΦ]
    rfl

  have hle : (⊤ : Submodule P (B ⧸ N)) ≤ 𝔪 • ⊤ := by
    rintro m -
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective N m
    obtain ⟨l, hl⟩ := hsurjL (Ideal.Quotient.mk 𝔪B b)
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective l
    have hbx : b - algebraMap P B x ∈ 𝔪B := by
      rw [← Ideal.Quotient.eq, ← hl]
      rfl
    have hmem : b - algebraMap P B x ∈ (𝔪 • ⊤ : Submodule P B) := by
      rw [Ideal.smul_top_eq_map]
      exact hbx
    have hq : Submodule.Quotient.mk (p := N) b = Submodule.Quotient.mk (b - algebraMap P B x) := by
      rw [Submodule.Quotient.mk_sub, eq_comm, sub_eq_self, Submodule.Quotient.mk_eq_zero]
      exact ⟨x, rfl⟩
    rw [hq]
    have : Submodule.map (N.mkQ) (𝔪 • ⊤ : Submodule P B) ≤ 𝔪 • ⊤ := by
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
    exact this ⟨_, hmem, rfl⟩

  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul 𝔪
    (⊤ : Submodule P (B ⧸ N)) Module.Finite.fg_top hle
  have hrann : r ∈ ann := by
    rw [hann, Module.mem_annihilator]
    intro m
    exact hr m Submodule.mem_top
  have h1 : (1 : P) ∈ 𝔪 := by
    have := 𝔪.sub_mem (hann𝔪 hrann) hr1
    simpa using this
  exact h𝔪max.ne_top (𝔪.eq_top_of_isUnit_mem h1 isUnit_one)

private theorem bijective_algebraMap_of_frobenius_factor
    (p : ℕ) [Fact p.Prime] [CharP P p]
    [Algebra.Etale A P] [Algebra.Etale A B]
    (G : B → P) (hGΦ : ∀ b : B, algebraMap P B (G b) = b ^ p)
    (hΦG : ∀ x : P, G (algebraMap P B x) = x ^ p) (hG0 : G 0 = 0) :
    Function.Bijective (algebraMap P B) := by
  have hp : p.Prime := Fact.out
  have hPB : Algebra.Etale P B := Algebra.Etale.of_restrictScalars A P B
  have hsurj : Function.Surjective (algebraMap P B) :=
    surjective_algebraMap_of_frobenius_factor p G hGΦ
  refine ⟨?_, hsurj⟩
  set I : Ideal P := RingHom.ker (algebraMap P B) with hI
  have hidem : IsIdempotentElem I :=
    (Algebra.FormallySmooth.iff_of_surjective hsurj).mp inferInstance
  have hfg : I.FG := by
    have := Algebra.FinitePresentation.ker_fG_of_surjective (IsScalarTower.toAlgHom A P B) hsurj
    simpa using this
  have hnil : I ≤ Ideal.jacobson ⊥ := by
    intro x hx
    apply Ideal.radical_le_jacobson
    refine ⟨p, ?_⟩
    rw [RingHom.mem_ker] at hx
    simpa [hx, hG0] using (hΦG x).symm
  have hIbot : I = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I I hfg ?_ hnil
    rw [Ideal.smul_eq_mul]
    exact le_of_eq hidem.eq.symm
  rw [RingHom.injective_iff_ker_eq_bot]
  exact hIbot

end

section

private theorem isPushout_frobenius_of_etale
    {A B : Type u} [CommRing A] [CommRing B] (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p]
    {φ : A →+* B} (hφ : φ.Etale) :
    IsPushout (CommRingCat.ofHom (frobenius A p)) (CommRingCat.ofHom φ)
      (CommRingCat.ofHom φ) (CommRingCat.ofHom (frobenius B p)) := by
  have hp : p.Prime := Fact.out
  set f : CommRingCat.of A ⟶ CommRingCat.of A := CommRingCat.ofHom (frobenius A p) with hf
  set g : CommRingCat.of A ⟶ CommRingCat.of B := CommRingCat.ofHom φ with hg
  have w : f ≫ CommRingCat.ofHom φ = g ≫ CommRingCat.ofHom (frobenius B p) := by
    ext a
    simp [f, g, frobenius_def]

  set Φ : pushout f g ⟶ CommRingCat.of B :=
    pushout.desc (CommRingCat.ofHom φ) (CommRingCat.ofHom (frobenius B p)) w with hΦ
  have hinlΦ : pushout.inl f g ≫ Φ = CommRingCat.ofHom φ := pushout.inl_desc _ _ _
  have hinrΦ : pushout.inr f g ≫ Φ = CommRingCat.ofHom (frobenius B p) := pushout.inr_desc _ _ _

  have hGΦ : ∀ b : B, Φ.hom ((pushout.inr f g).hom b) = b ^ p := by
    intro b
    have := congr($(hinrΦ).hom b)
    simpa [frobenius_def] using this

  have hΦG : ∀ x : ↥(pushout f g), (pushout.inr f g).hom (Φ.hom x) = x ^ p := by

    rcases subsingleton_or_nontrivial ↥(pushout f g) with hPs | hPs
    · intro x
      exact Subsingleton.elim _ _
    haveI : CharP ↥(pushout f g) p := by
      rw [CharP.charP_iff_prime_eq_zero hp, ← map_natCast (pushout.inl f g).hom, CharP.cast_eq_zero,
        map_zero]
    have key : Φ ≫ pushout.inr f g = CommRingCat.ofHom (frobenius ↥(pushout f g) p) := by
      apply pushout.hom_ext
      · rw [reassoc_of% hinlΦ]
        have h1 : CommRingCat.ofHom φ ≫ pushout.inr f g = f ≫ pushout.inl f g :=
          (pushout.condition (f := f) (g := g)).symm
        rw [h1]
        ext a
        simp [f, frobenius_def]
      · rw [reassoc_of% hinrΦ]
        ext b
        simp [frobenius_def]
    intro x
    have := congr($(key).hom x)
    simpa [frobenius_def] using this

  have hbij : Function.Bijective Φ.hom := by
    rcases subsingleton_or_nontrivial B with hB | hB
    · haveI : Subsingleton ↥(pushout f g) := by
        refine subsingleton_of_zero_eq_one ?_
        rw [← map_one (pushout.inr f g).hom, Subsingleton.elim (1 : B) 0, map_zero]
      exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun b => ⟨0, Subsingleton.elim _ _⟩⟩
    haveI : Nontrivial ↥(pushout f g) := Φ.hom.domain_nontrivial
    haveI : CharP ↥(pushout f g) p := by
      rw [CharP.charP_iff_prime_eq_zero hp, ← map_natCast (pushout.inl f g).hom, CharP.cast_eq_zero,
        map_zero]

    letI : Algebra A B := φ.toAlgebra
    letI : Algebra A ↥(pushout f g) := (pushout.inl f g).hom.toAlgebra
    letI : Algebra ↥(pushout f g) B := Φ.hom.toAlgebra
    haveI : IsScalarTower A ↥(pushout f g) B := by
      refine IsScalarTower.of_algebraMap_eq' ?_
      change φ = Φ.hom.comp (pushout.inl f g).hom
      have := congr($(hinlΦ).hom)
      simpa using this.symm
    haveI : Algebra.Etale A B := hφ
    haveI : Algebra.Etale A ↥(pushout f g) := by
      have hst : (RingHom.toMorphismProperty @RingHom.Etale).IsStableUnderCobaseChange :=
        (RingHom.isStableUnderCobaseChange_toMorphismProperty_iff).mpr
          RingHom.Etale.isStableUnderBaseChange
      have hinl : (RingHom.toMorphismProperty @RingHom.Etale) (pushout.inl f g) :=
        MorphismProperty.IsStableUnderCobaseChange.of_isPushout (IsPushout.of_hasPushout f g)
          (show (RingHom.toMorphismProperty @RingHom.Etale) g from hφ)
      exact hinl
    exact bijective_algebraMap_of_frobenius_factor (A := A) (P := ↥(pushout f g)) (B := B) p
      (G := (pushout.inr f g).hom) hGΦ hΦG (map_zero _)

  haveI : IsIso Φ := by
    have : IsIso (CommRingCat.ofHom (RingEquiv.ofBijective Φ.hom hbij).toRingHom) :=
      (RingEquiv.ofBijective Φ.hom hbij).toCommRingCatIso.isIso_hom
    simp at this
    exact this
  refine IsPushout.of_iso_pushout ⟨w⟩ (asIso Φ).symm ?_ ?_
  · rw [Iso.symm_hom, asIso_inv, IsIso.comp_inv_eq, hinlΦ]
  · rw [Iso.symm_hom, asIso_inv, IsIso.comp_inv_eq, hinrΦ]

end

end EtaleFrobeniusPushoutAux

namespace RingHom.Etale

/-- Frobenius forms a pushout square along an étale map of
characteristic-`p` rings. -/
public theorem isPushout_frobenius
    {A B : Type u} [CommRing A] [CommRing B] (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p]
    {φ : A →+* B} (hφ : φ.Etale) :
    IsPushout (CommRingCat.ofHom (frobenius A p)) (CommRingCat.ofHom φ)
      (CommRingCat.ofHom φ) (CommRingCat.ofHom (frobenius B p)) :=
  EtaleFrobeniusPushoutAux.isPushout_frobenius_of_etale p hφ

end RingHom.Etale
