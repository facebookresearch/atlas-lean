/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_RingHom_isPushout_eqLocus_of_finiteLocallyFree_equivalenceRelation.lean`
and
`P2M/Sol/S_RingHom_isPushout_eqLocus_of_finiteLocallyFree_equivalenceRelation.lean`
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
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.RingHom.Flat

namespace FiniteLocallyFreeQuotient

set_option autoImplicit false

open CategoryTheory TensorProduct Polynomial

universe u

namespace QuotFLF

variable {A B : Type u} [CommRing A] [CommRing B] (s t : A →+* B)

private def Rel (T : Type u) [CommRing T] (x y : A →+* T) : Prop :=
  ∃ φ : B →+* T, φ.comp s = x ∧ φ.comp t = y

variable {s t}

private theorem rel_iff {T : Type u} [CommRing T] (x y : A →+* T) :
    Rel s t T x y ↔ ∃ φ : B →+* T, φ.comp s = x ∧ φ.comp t = y := Iff.rfl

private theorem rel_self : Rel s t B s t := ⟨RingHom.id B, RingHom.id_comp _, RingHom.id_comp _⟩

private theorem Rel.map {T T' : Type u} [CommRing T] [CommRing T'] (g : T →+* T') {x y : A →+* T}
    (h : Rel s t T x y) : Rel s t T' (g.comp x) (g.comp y) := by
  obtain ⟨φ, rfl, rfl⟩ := h
  exact ⟨g.comp φ, by rw [RingHom.comp_assoc], by rw [RingHom.comp_assoc]⟩

private theorem hom_ext (hgen : s.range ⊔ t.range = ⊤) {T : Type u} [CommRing T] {φ ψ : B →+* T}
    (h₁ : φ.comp s = ψ.comp s) (h₂ : φ.comp t = ψ.comp t) : φ = ψ := by
  apply RingHom.eq_of_eqOn_set_dense (s := (s.range : Set B) ∪ (t.range : Set B))
  · rw [Subring.closure_union, Subring.closure_eq, Subring.closure_eq, hgen]
  · rintro b (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · exact RingHom.congr_fun h₁ a
    · exact RingHom.congr_fun h₂ a

section structureMaps

variable (hequiv : ∀ (T : Type u) [CommRing T], _root_.Equivalence (Rel s t T))
include hequiv

private theorem exists_counit : ∃ e : B →+* A, e.comp s = RingHom.id A ∧ e.comp t = RingHom.id A :=
  (hequiv A).refl (RingHom.id A)

private theorem exists_antipode : ∃ ι : B →+* B, ι.comp s = t ∧ ι.comp t = s :=
  (hequiv B).symm rel_self

private theorem exists_comul {P : Type u} [CommRing P] (inl inr : B →+* P) (hP : inl.comp t =
  inr.comp s) :
    ∃ c : B →+* P, c.comp s = inl.comp s ∧ c.comp t = inr.comp t := by
  have h₁ : Rel s t P (inl.comp s) (inl.comp t) := ⟨inl, rfl, rfl⟩
  have h₂ : Rel s t P (inr.comp s) (inr.comp t) := ⟨inr, rfl, rfl⟩
  rw [hP] at h₁
  exact (hequiv P).trans h₁ h₂

private theorem exists_shear {T : Type u} [CommRing T] (u v : B →+* T) (huv : u.comp s = v.comp s) :
    ∃ v' : B →+* T, v'.comp s = u.comp t ∧ v'.comp t = v.comp t := by
  have hu : Rel s t T (u.comp t) (u.comp s) := (hequiv T).symm ⟨u, rfl, rfl⟩
  have hv : Rel s t T (v.comp s) (v.comp t) := ⟨v, rfl, rfl⟩
  rw [huv] at hu
  exact (hequiv T).trans hu hv

end structureMaps

section shear

open CommRingCat

variable (hgen : s.range ⊔ t.range = ⊤)
  (hequiv : ∀ (T : Type u) [CommRing T], _root_.Equivalence (Rel s t T))
  {P : Type u} [CommRing P] {inl inr c : B →+* P}
  (hP : IsPushout (ofHom t) (ofHom s) (ofHom inl) (ofHom inr))
  (hcs : c.comp s = inl.comp s) (hct : c.comp t = inr.comp t)
include hgen hequiv hP hcs hct

private theorem isPushout_shear : IsPushout (ofHom s) (ofHom s) (ofHom inl) (ofHom c) := by
  classical
  have hw : inl.comp t = inr.comp s := by
    have := hP.w
    simpa [← CommRingCat.ofHom_comp] using congrArg CommRingCat.Hom.hom this.symm |>.symm

  have cond : ∀ sq : Limits.PushoutCocone (ofHom s) (ofHom s),
      sq.inl.hom.comp s = sq.inr.hom.comp s := fun sq => by
    have := congrArg CommRingCat.Hom.hom sq.condition
    simpa using this
  let v' : ∀ sq : Limits.PushoutCocone (ofHom s) (ofHom s), B →+* sq.pt := fun sq =>
    (exists_shear hequiv sq.inl.hom sq.inr.hom (cond sq)).choose
  have hv'₁ : ∀ sq : Limits.PushoutCocone (ofHom s) (ofHom s),
      (v' sq).comp s = sq.inl.hom.comp t := fun sq =>
    (exists_shear hequiv sq.inl.hom sq.inr.hom (cond sq)).choose_spec.1
  have hv'₂ : ∀ sq : Limits.PushoutCocone (ofHom s) (ofHom s),
      (v' sq).comp t = sq.inr.hom.comp t := fun sq =>
    (exists_shear hequiv sq.inl.hom sq.inr.hom (cond sq)).choose_spec.2
  have hdesc : ∀ sq : Limits.PushoutCocone (ofHom s) (ofHom s),
      ofHom t ≫ sq.inl = ofHom s ≫ ofHom (v' sq) := fun sq => by
    ext a
    simpa using (RingHom.congr_fun (hv'₁ sq) a).symm
  refine IsPushout.of_isColimit' ⟨by rw [← ofHom_comp, ← ofHom_comp, hcs]⟩ ?_
  refine Limits.PushoutCocone.IsColimit.mk _ (fun sq => hP.desc sq.inl (ofHom (v' sq)) (hdesc sq))
    (fun sq => hP.inl_desc _ _ _) (fun sq => ?_) (fun sq m hm₁ hm₂ => ?_)
  · ext b : 2
    change ((hP.desc sq.inl (ofHom (v' sq)) (hdesc sq)).hom.comp c) b = sq.inr.hom b
    congr 1
    apply hom_ext hgen
    · rw [RingHom.comp_assoc, hcs, ← RingHom.comp_assoc, ← cond sq]
      congr 1
      exact congrArg CommRingCat.Hom.hom (hP.inl_desc sq.inl (ofHom (v' sq)) (hdesc sq))
    · rw [RingHom.comp_assoc, hct, ← RingHom.comp_assoc, ← hv'₂ sq]
      congr 1
      exact congrArg CommRingCat.Hom.hom (hP.inr_desc sq.inl (ofHom (v' sq)) (hdesc sq))
  · apply hP.hom_ext
    · rw [hP.inl_desc]; exact hm₁
    · rw [hP.inr_desc]
      ext b : 2
      change (m.hom.comp inr) b = v' sq b
      congr 1
      apply hom_ext hgen
      · rw [RingHom.comp_assoc, ← hw, ← RingHom.comp_assoc, hv'₁ sq]
        congr 1
        exact congrArg CommRingCat.Hom.hom hm₁
      · rw [RingHom.comp_assoc, ← hct, ← RingHom.comp_assoc, hv'₂ sq]
        congr 1
        exact congrArg CommRingCat.Hom.hom hm₂

end shear

section models

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (t : A →+* B)

private def Tgt (_t : A →+* B) : Type u := B

private scoped instance : CommRing (Tgt t) := inferInstanceAs (CommRing B)

private scoped instance : Algebra A (Tgt t) := RingHom.toAlgebra (R := A) (S := B) t

private def Tgt.of : B ≃+* Tgt t := RingEquiv.refl B

omit [Algebra A B] in
@[scoped simp] private theorem Tgt.algebraMap_eq : algebraMap A (Tgt t) = (Tgt.of t).toRingHom.comp
  t := rfl

open FiniteLocallyFreeQuotient.QuotFLF.Tgt
omit [Algebra A B] in
private theorem Tgt.algebraMap_apply (a : A) : algebraMap A (Tgt t) a = Tgt.of t (t a) := rfl

private abbrev P₁ : Type u := Tgt t ⊗[A] B

private abbrev P₂ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] : Type u := B ⊗[A] B

private def inl₁ : B →+* P₁ t :=
  (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := Tgt t) (B := B)).comp (Tgt.of
    t).toRingHom

private def inr₁ : B →+* P₁ t := (Algebra.TensorProduct.includeRight (R := A) (A := Tgt t) (B :=
  B)).toRingHom

private theorem inl₁_apply (b : B) : inl₁ t b = (Tgt.of t b) ⊗ₜ[A] (1 : B) := rfl
private theorem inr₁_apply (b : B) : inr₁ t b = (1 : Tgt t) ⊗ₜ[A] b := rfl

private theorem isPushout_P₁ :
    IsPushout (CommRingCat.ofHom t) (CommRingCat.ofHom (algebraMap A B))
      (CommRingCat.ofHom (inl₁ t)) (CommRingCat.ofHom (inr₁ t)) :=
  CommRingCat.isPushout_tensorProduct A (Tgt t) B

private theorem inl₁_comp_t : (inl₁ t).comp t = (inr₁ t).comp (algebraMap A B) := by
  have := (isPushout_P₁ t).w
  have := congrArg CommRingCat.Hom.hom this
  simpa using this

private theorem isPushout_P₂ :
    IsPushout (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (algebraMap A B))
      (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : B →+* P₂ A B))
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : B →+* P₂ A B)) :=
  CommRingCat.isPushout_tensorProduct A B B

end models
open FiniteLocallyFreeQuotient.QuotFLF.Tgt

section theta

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {t : A →+* B}
  (hgen : (algebraMap A B).range ⊔ t.range = ⊤)
  (hequiv : ∀ (T : Type u) [CommRing T], _root_.Equivalence (Rel (algebraMap A B) t T))

include hequiv in
private theorem exists_comul₁ : ∃ c : B →+* P₁ t,
  c.comp (algebraMap A B) = (inl₁ t).comp (algebraMap A B) ∧
    c.comp t = (inr₁ t).comp t :=
  exists_comul hequiv (inl₁ t) (inr₁ t) (inl₁_comp_t t)

include hgen hequiv in

private theorem exists_theta : ∃ (c : B →+* P₁ t) (θ : P₂ A B ≃+* P₁ t),
    c.comp (algebraMap A B) = (inl₁ t).comp (algebraMap A B) ∧ c.comp t = (inr₁ t).comp t ∧
    (∀ b : B, θ (b ⊗ₜ 1) = inl₁ t b) ∧ (∀ b : B, θ (1 ⊗ₜ b) = c b) := by
  obtain ⟨c, hcs, hct⟩ := exists_comul₁ (t := t) hequiv
  have h₁ := isPushout_shear hgen hequiv (isPushout_P₁ t) hcs hct
  have h₂ := isPushout_P₂ (A := A) (B := B)

  let e : CommRingCat.of (P₂ A B) ≅ CommRingCat.of (P₁ t) := h₂.isoIsPushout _ _ h₁
  refine ⟨c, e.commRingCatIsoToRingEquiv, hcs, hct, fun b => ?_, fun b => ?_⟩
  · change e.hom.hom (b ⊗ₜ[A] 1) = inl₁ t b
    have h := congrArg CommRingCat.Hom.hom (h₂.inl_isoIsPushout_hom _ _ h₁)
    exact RingHom.congr_fun h b
  · change e.hom.hom (1 ⊗ₜ[A] b) = c b
    have h := congrArg CommRingCat.Hom.hom (h₂.inr_isoIsPushout_hom _ _ h₁)
    exact RingHom.congr_fun h b

end theta
open FiniteLocallyFreeQuotient.QuotFLF.Tgt

section rank

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {t : A →+* B}
  (hgen : (algebraMap A B).range ⊔ t.range = ⊤)
  (hequiv : ∀ (T : Type u) [CommRing T], _root_.Equivalence (Rel (algebraMap A B) t T))

private scoped instance instModuleLeftP₁ (t : A →+* B) : Module B (P₁ t) := inferInstanceAs (Module
  (Tgt t)
  (P₁ t))

private theorem smul_P₁_def (t : A →+* B) (b : B) (z : P₁ t) : b • z = inl₁ t b * z := by
  change (show Tgt t from b) • z = _
  rw [Algebra.smul_def]
  rfl

include hgen hequiv in

private theorem exists_linearEquiv_P₂_P₁ : Nonempty (P₂ A B ≃ₗ[B] P₁ t) := by
  obtain ⟨c, θ, -, -, hθl, -⟩ := exists_theta (t := t) hgen hequiv
  refine ⟨{ θ with
    map_smul' := fun b z => ?_ }⟩
  change θ (b • z) = b • θ z
  rw [Algebra.smul_def, smul_P₁_def, map_mul, ← hθl]
  rfl

private theorem rankAtStalk_P₁_eq [Module.Finite A B] [Module.Flat A B] (t : A →+* B)
    (𝔯 : PrimeSpectrum (Tgt t)) :
    Module.rankAtStalk (R := Tgt t) (P₁ t) 𝔯 =
      Module.rankAtStalk (R := A) B (𝔯.comap (algebraMap A (Tgt t))) :=
  Module.rankAtStalk_baseChange (R := A) (M := B) (S := Tgt t) 𝔯

include hgen hequiv in

private theorem rankAtStalk_comap_algebraMap_eq_rankAtStalk_comap [Module.Finite A B] [Module.Flat
  A B]
    (𝔯 : PrimeSpectrum B) :
    Module.rankAtStalk (R := A) B (𝔯.comap (algebraMap A B)) =
      Module.rankAtStalk (R := A) B (𝔯.comap t) := by
  obtain ⟨e⟩ := exists_linearEquiv_P₂_P₁ (t := t) hgen hequiv
  have h₂ : Module.rankAtStalk (R := B) (P₂ A B) 𝔯 =
      Module.rankAtStalk (R := A) B (𝔯.comap (algebraMap A B)) :=
    Module.rankAtStalk_baseChange (R := A) (M := B) (S := B) 𝔯
  have h₁ := rankAtStalk_P₁_eq (A := A) (B := B) t 𝔯
  have h₃ : Module.rankAtStalk (R := B) (P₂ A B) 𝔯 = Module.rankAtStalk (R := B) (P₁ t) 𝔯 :=
    congrFun (Module.rankAtStalk_eq_of_equiv e) 𝔯
  rw [← h₂, h₃]
  exact h₁

end rank
open FiniteLocallyFreeQuotient.QuotFLF.Tgt

section const

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra C A]
  {t : A →+* B} [Module.Finite A B] [Module.Projective A B]
  (hgen : (algebraMap A B).range ⊔ t.range = ⊤)
  (hequiv : ∀ (T : Type u) [CommRing T], _root_.Equivalence (Rel (algebraMap A B) t T))
  (hinj : Function.Injective (algebraMap C A))
  (hinv : ∀ a : A, algebraMap A B a = t a ↔ a ∈ Set.range (algebraMap C A))

omit [Module.Finite A B] [Module.Projective A B] in
include hinj hinv in

private theorem eq_zero_or_eq_one_of_isIdempotentElem [IsLocalRing C] {e : A} (he :
  IsIdempotentElem e)
    (hst : algebraMap A B e = t e) : e = 0 ∨ e = 1 := by
  obtain ⟨c, rfl⟩ := (hinv e).1 hst
  have hc : IsIdempotentElem c := hinj (by rw [map_mul]; exact he.eq)
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self c with hu | hu
  · right
    have : c = 1 := by
      have h := hc.eq
      nth_rw 3 [← mul_one c] at h
      exact hu.mul_left_cancel h
    simp [this]
  · left
    have h1 : IsIdempotentElem (1 - c) := hc.one_sub
    have : 1 - c = 1 := by
      have h := h1.eq
      nth_rw 3 [← mul_one (1 - c)] at h
      exact hu.mul_left_cancel h
    have : c = 0 := by
      have := congrArg (fun x => 1 - x) this
      simpa using this
    simp [this]

include hgen hequiv hinj hinv in

private theorem rankAtStalk_eq_rankAtStalk_of_isLocalRing [IsLocalRing C] (p q : PrimeSpectrum A) :
    Module.rankAtStalk (R := A) B p = Module.rankAtStalk (R := A) B q := by
  classical
  haveI : Module.FinitePresentation A B := Module.finitePresentation_of_projective A B
  set f : PrimeSpectrum A → ℕ := Module.rankAtStalk (R := A) B with hf_def
  have hf : IsLocallyConstant f := Module.isLocallyConstant_rankAtStalk
  have hU : IsClopen (f ⁻¹' {f p}) := hf.isClopen_fiber (f p)
  obtain ⟨e, he, hUe⟩ := PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen hU

  have hst : (PrimeSpectrum.comap (algebraMap A B)) ⁻¹' (f ⁻¹' {f p}) =
      (PrimeSpectrum.comap t) ⁻¹' (f ⁻¹' {f p}) := by
    ext 𝔯
    simp only [Set.mem_preimage, Set.mem_singleton_iff, hf_def]
    rw [rankAtStalk_comap_algebraMap_eq_rankAtStalk_comap (t := t) hgen hequiv 𝔯]
  have h1 : ∀ (g : A →+* B), (PrimeSpectrum.comap g) ⁻¹' (PrimeSpectrum.basicOpen e : Set _) =
      (PrimeSpectrum.basicOpen (g e) : Set (PrimeSpectrum B)) := fun g => by
    ext 𝔯
    simp
  have hb : (PrimeSpectrum.basicOpen (algebraMap A B e) : Set (PrimeSpectrum B)) =
      PrimeSpectrum.basicOpen (t e) := by
    rw [← h1, ← h1, ← hUe]
    exact hst
  have hse : algebraMap A B e = t e :=
    PrimeSpectrum.basicOpen_injOn_isIdempotentElem (he.map _) (he.map _) (SetLike.ext' hb)
  have hp : p ∈ f ⁻¹' {f p} := rfl
  rcases eq_zero_or_eq_one_of_isIdempotentElem (t := t) hinj hinv he hse with rfl | rfl
  · rw [hUe, PrimeSpectrum.basicOpen_zero] at hp
    exact absurd hp (by simp)
  · have hq : q ∈ f ⁻¹' {f p} := by rw [hUe, PrimeSpectrum.basicOpen_one]; trivial
    exact hq.symm

include hgen hequiv hinj hinv in
private theorem exists_rankAtStalk_eq_of_isLocalRing [IsLocalRing C] :
    ∃ r : ℕ, ∀ p : PrimeSpectrum A, Module.rankAtStalk (R := A) B p = r := by
  by_cases h : Nonempty (PrimeSpectrum A)
  · obtain ⟨p₀⟩ := h
    exact ⟨_, fun p => rankAtStalk_eq_rankAtStalk_of_isLocalRing (t := t) hgen hequiv hinj hinv p
      p₀⟩
  · exact ⟨0, fun p => (h ⟨p⟩).elim⟩

end const
open FiniteLocallyFreeQuotient.QuotFLF.Tgt

namespace L1

section envelope

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

private structure Envelope where

  n : ℕ

  π : (Fin n → R) →ₗ[R] S

  ι : S →ₗ[R] (Fin n → R)
  πι : π ∘ₗ ι = LinearMap.id

private theorem nonempty_envelope [Module.Finite R S] [Module.Projective R S] :
    Nonempty (Envelope R S) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R S
  obtain ⟨g, hg⟩ := Module.projective_lifting_property f LinearMap.id hf
  exact ⟨⟨n, f, g, hg⟩⟩

variable {R S} (𝓔 : Envelope R S)

@[scoped simp] private theorem π_ι (y : S) : 𝓔.π (𝓔.ι y) = y := LinearMap.congr_fun 𝓔.πι y

private theorem ι_injective : Function.Injective 𝓔.ι :=
  Function.LeftInverse.injective (π_ι 𝓔)

private noncomputable def ψ (b : S) : Module.End R (Fin 𝓔.n → R) :=
  𝓔.ι ∘ₗ LinearMap.mulLeft R b ∘ₗ 𝓔.π + (LinearMap.id - 𝓔.ι ∘ₗ 𝓔.π)

private theorem ψ_apply (b : S) (v : Fin 𝓔.n → R) :
    ψ 𝓔 b v = 𝓔.ι (b * 𝓔.π v) + (v - 𝓔.ι (𝓔.π v)) := rfl

private theorem ψ_ι (b y : S) : ψ 𝓔 b (𝓔.ι y) = 𝓔.ι (b * y) := by
  simp [ψ_apply]

private theorem ψ_pow_ι (b y : S) (k : ℕ) : (ψ 𝓔 b ^ k) (𝓔.ι y) = 𝓔.ι (b ^ k * y) := by
  induction k generalizing y with
  | zero => simp
  | succ k ih => rw [pow_succ, Module.End.mul_apply, ψ_ι, ih, pow_succ, mul_assoc]

private theorem aeval_ψ_ι (b y : S) (p : R[X]) :
    (aeval (ψ 𝓔 b) p) (𝓔.ι y) = 𝓔.ι (aeval b p * y) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, add_mul]
  | monomial k c =>
    simp only [aeval_monomial, Module.End.mul_apply, ψ_pow_ι]
    rw [Module.algebraMap_end_apply, ← map_smul, Algebra.smul_def, mul_assoc]

private noncomputable def χ (b : S) : R[X] := LinearMap.charpoly (ψ 𝓔 b)

private theorem χ_monic (b : S) : (χ 𝓔 b).Monic := LinearMap.charpoly_monic _

private theorem χ_natDegree [Nontrivial R] (b : S) : (χ 𝓔 b).natDegree = 𝓔.n := by
  rw [χ, LinearMap.charpoly_natDegree, Module.finrank_fin_fun]

private theorem aeval_χ (b : S) : aeval b (χ 𝓔 b) = 0 := by
  have h1 : aeval (ψ 𝓔 b) (χ 𝓔 b) = 0 := LinearMap.aeval_self_charpoly _
  have h3 := aeval_ψ_ι 𝓔 b 1 (χ 𝓔 b)
  rw [h1, LinearMap.zero_apply, mul_one, eq_comm, map_eq_zero_iff _ (ι_injective 𝓔)] at h3
  exact h3

end envelope
open FiniteLocallyFreeQuotient.QuotFLF.Tgt

section baseChange

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (𝓔 : Envelope R S)
  (R' : Type u) [CommRing R'] [Algebra R R']

private noncomputable abbrev eF : R' ⊗[R] (Fin 𝓔.n → R) ≃ₗ[R'] (Fin 𝓔.n → R') :=
  TensorProduct.piScalarRight R R' R' (Fin 𝓔.n)

private noncomputable def πb : (Fin 𝓔.n → R') →ₗ[R'] R' ⊗[R] S :=
  𝓔.π.baseChange R' ∘ₗ (eF 𝓔 R').symm.toLinearMap

private noncomputable def ιb : R' ⊗[R] S →ₗ[R'] (Fin 𝓔.n → R') :=
  (eF 𝓔 R').toLinearMap ∘ₗ 𝓔.ι.baseChange R'

private theorem πb_comp_ιb : πb 𝓔 R' ∘ₗ ιb 𝓔 R' = LinearMap.id := by
  apply LinearMap.ext
  intro y
  simp only [πb, ιb, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    LinearMap.id_apply]
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, 𝓔.πι, LinearMap.baseChange_id,
    LinearMap.id_apply]

private noncomputable abbrev Envelope.baseChange : Envelope R' (R' ⊗[R] S) :=
  ⟨𝓔.n, πb 𝓔 R', ιb 𝓔 R', πb_comp_ιb 𝓔 R'⟩

private theorem ψ_baseChange (b : S) :
    ψ (𝓔.baseChange R') ((1 : R') ⊗ₜ[R] b) = (eF 𝓔 R').conj ((ψ 𝓔 b).baseChange R') := by
  apply LinearMap.ext
  intro w
  obtain ⟨x, rfl⟩ := (eF 𝓔 R').surjective w
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c v =>
    change ιb 𝓔 R' ((1 : R') ⊗ₜ[R] b * πb 𝓔 R' (eF 𝓔 R' (c ⊗ₜ v))) +
        (eF 𝓔 R' (c ⊗ₜ v) - ιb 𝓔 R' (πb 𝓔 R' (eF 𝓔 R' (c ⊗ₜ v)))) = _
    simp only [πb, ιb, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ψ_apply,
      tmul_add, tmul_sub, map_add, map_sub]

private theorem χ_baseChange (b : S) :
    χ (𝓔.baseChange R') ((1 : R') ⊗ₜ[R] b) = (χ 𝓔 b).map (algebraMap R R') := by
  have e1 := LinearEquiv.charpoly_conj (eF 𝓔 R') ((ψ 𝓔 b).baseChange R')
  have e2 := LinearMap.charpoly_baseChange (ψ 𝓔 b) R'
  have e0 : χ (𝓔.baseChange R') ((1 : R') ⊗ₜ[R] b) =
      LinearMap.charpoly ((eF 𝓔 R').conj ((ψ 𝓔 b).baseChange R')) :=
    congrArg LinearMap.charpoly (ψ_baseChange 𝓔 R' b)
  rw [e0, e1, e2]
  rfl

end baseChange
open FiniteLocallyFreeQuotient.QuotFLF.Tgt

section mapEquiv

variable {R S S₂ : Type u} [CommRing R] [CommRing S] [Algebra R S] [CommRing S₂] [Algebra R S₂]
  (𝓔 : Envelope R S) (σ : S ≃ₐ[R] S₂)

private noncomputable abbrev Envelope.mapEquiv : Envelope R S₂ :=
  ⟨𝓔.n, σ.toLinearEquiv.toLinearMap ∘ₗ 𝓔.π, 𝓔.ι ∘ₗ σ.symm.toLinearEquiv.toLinearMap, by
    apply LinearMap.ext
    intro y
    simp⟩

private theorem ψ_mapEquiv (b : S) : ψ (𝓔.mapEquiv σ) (σ b) = ψ 𝓔 b := by
  apply LinearMap.ext
  intro v
  change (𝓔.ι ∘ₗ σ.symm.toLinearEquiv.toLinearMap)
      (σ b * (σ.toLinearEquiv.toLinearMap ∘ₗ 𝓔.π) v) +
      (v - (𝓔.ι ∘ₗ σ.symm.toLinearEquiv.toLinearMap) ((σ.toLinearEquiv.toLinearMap ∘ₗ 𝓔.π) v)) =
    𝓔.ι (b * 𝓔.π v) + (v - 𝓔.ι (𝓔.π v))
  simp

private theorem χ_mapEquiv (b : S) : χ (𝓔.mapEquiv σ) (σ b) = χ 𝓔 b :=
  congrArg LinearMap.charpoly (ψ_mapEquiv 𝓔 σ b)

end mapEquiv
open FiniteLocallyFreeQuotient.QuotFLF.Tgt

section split

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (𝓔 : Envelope R S)

private theorem sub_ι_π_mem_ker (v : Fin 𝓔.n → R) : v - 𝓔.ι (𝓔.π v) ∈ LinearMap.ker 𝓔.π := by
  simp [LinearMap.mem_ker]

private noncomputable def toKer : (Fin 𝓔.n → R) →ₗ[R] LinearMap.ker 𝓔.π :=
  (LinearMap.id - 𝓔.ι ∘ₗ 𝓔.π).codRestrict _ (sub_ι_π_mem_ker 𝓔)

@[scoped simp] private theorem coe_toKer (v : Fin 𝓔.n → R) : (toKer 𝓔 v : Fin 𝓔.n → R) = v - 𝓔.ι
  (𝓔.π v) :=
  rfl

private theorem toKer_subtype (k : LinearMap.ker 𝓔.π) : toKer 𝓔 (k : Fin 𝓔.n → R) = k := by
  apply Subtype.ext
  have hk : 𝓔.π k = 0 := k.2
  simp [hk]

private noncomputable def splitEquiv : (Fin 𝓔.n → R) ≃ₗ[R] S × LinearMap.ker 𝓔.π :=
  LinearEquiv.ofLinear (LinearMap.prod 𝓔.π (toKer 𝓔))
    (𝓔.ι.coprod (LinearMap.ker 𝓔.π).subtype)
    (by
      apply LinearMap.ext
      rintro ⟨y, k⟩
      have hk : 𝓔.π k = 0 := k.2
      have h0 : toKer 𝓔 (𝓔.ι y) = 0 := Subtype.ext (by simp)
      refine Prod.ext ?_ ?_
      · simp [hk]
      · change toKer 𝓔 (𝓔.ι y + (k : Fin 𝓔.n → R)) = k
        rw [map_add, toKer_subtype, h0, zero_add])
    (by
      apply LinearMap.ext
      intro v
      simp)

private theorem finite_ker : Module.Finite R (LinearMap.ker 𝓔.π) :=
  Module.Finite.of_surjective (toKer 𝓔) fun k => ⟨k, toKer_subtype 𝓔 k⟩

private theorem flat_ker : Module.Flat R (LinearMap.ker 𝓔.π) :=
  Module.Flat.of_retract (LinearMap.ker 𝓔.π).subtype (toKer 𝓔)
    (LinearMap.ext fun k => toKer_subtype 𝓔 k)

private theorem conj_ψ (b : S) :
    (splitEquiv 𝓔).conj (ψ 𝓔 b) = (LinearMap.mulLeft R b).prodMap (1 : Module.End R _) := by
  apply LinearMap.ext
  rintro ⟨y, k⟩
  have hk : 𝓔.π k = 0 := k.2
  have h0 : toKer 𝓔 (𝓔.ι (b * y)) = 0 := Subtype.ext (by simp)
  rw [LinearEquiv.conj_apply_apply]
  change splitEquiv 𝓔 (ψ 𝓔 b (𝓔.ι y + (k : Fin 𝓔.n → R))) = (b * y, k)
  rw [map_add, ψ_ι, ψ_apply, hk, mul_zero, map_zero, sub_zero, zero_add]
  change (𝓔.π (𝓔.ι (b * y) + ↑k), toKer 𝓔 (𝓔.ι (b * y) + ↑k)) = (b * y, k)
  rw [map_add, map_add, π_ι, hk, add_zero, toKer_subtype, h0, zero_add]

private theorem n_eq_finrank_add [Nontrivial R] [Module.Free R S] [Module.Finite R S]
    [Module.Free R (LinearMap.ker 𝓔.π)] :
    𝓔.n = Module.finrank R S + Module.finrank R (LinearMap.ker 𝓔.π) := by
  haveI := finite_ker 𝓔
  have h := (splitEquiv 𝓔).finrank_eq
  rw [Module.finrank_fin_fun, Module.finrank_prod] at h
  exact h

private theorem χ_eq_mul_of_free [Nontrivial R] [Module.Free R S] [Module.Finite R S]
    [Module.Free R (LinearMap.ker 𝓔.π)] (b : S) :
    χ 𝓔 b = LinearMap.charpoly (LinearMap.mulLeft R b) *
      (X - 1) ^ Module.finrank R (LinearMap.ker 𝓔.π) := by
  haveI := finite_ker 𝓔
  rw [χ, ← LinearEquiv.charpoly_conj (splitEquiv 𝓔), conj_ψ, LinearMap.charpoly_prodMap,
    LinearMap.charpoly_one]

end split
open FiniteLocallyFreeQuotient.QuotFLF.Tgt

section localize

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
  [Module.Projective R S] (r : ℕ) (hr : ∀ p, Module.rankAtStalk (R := R) S p = r)
  (𝓔 : Envelope R S) (J : Ideal R) [J.IsPrime]

private scoped instance free_localization :
    Module.Free (Localization.AtPrime J) (Localization.AtPrime J ⊗[R] S) :=
  Module.free_of_flat_of_isLocalRing

include hr in
private theorem finrank_localization :
    Module.finrank (Localization.AtPrime J) (Localization.AtPrime J ⊗[R] S) = r := by
  have h := congrFun (Module.rankAtStalk_eq_finrank_of_free (R := Localization.AtPrime J)
    (M := Localization.AtPrime J ⊗[R] S)) ⟨IsLocalRing.maximalIdeal _, inferInstance⟩
  rw [Module.rankAtStalk_baseChange, hr] at h
  simp only [Pi.natCast_apply, Nat.cast_id] at h
  exact h.symm

omit [Module.Finite R S] [Module.Projective R S] in
private theorem free_ker_localization :
    Module.Free (Localization.AtPrime J)
      (LinearMap.ker (𝓔.baseChange (Localization.AtPrime J)).π) :=
  haveI := finite_ker (𝓔.baseChange (Localization.AtPrime J))
  haveI := flat_ker (𝓔.baseChange (Localization.AtPrime J))
  Module.free_of_flat_of_isLocalRing

include hr in
private theorem n_eq_add_finrank_ker_localization :
    𝓔.n = r + Module.finrank (Localization.AtPrime J)
      (LinearMap.ker (𝓔.baseChange (Localization.AtPrime J)).π) := by
  haveI := free_ker_localization 𝓔 J
  have h := n_eq_finrank_add (𝓔.baseChange (Localization.AtPrime J))
  rw [finrank_localization r hr J] at h
  exact h

include hr in

private theorem χ_map_localization (b : S) :
    (χ 𝓔 b).map (algebraMap R (Localization.AtPrime J)) =
      LinearMap.charpoly (LinearMap.mulLeft (Localization.AtPrime J) ((1 : Localization.AtPrime J)
        ⊗ₜ[R] b)) *
        (X - 1) ^ (𝓔.n - r) := by
  haveI := free_ker_localization 𝓔 J
  rw [← χ_baseChange, χ_eq_mul_of_free]
  have hk : Module.finrank (Localization.AtPrime J)
      (LinearMap.ker (𝓔.baseChange (Localization.AtPrime J)).π) = 𝓔.n - r := by
    have := n_eq_add_finrank_ker_localization r hr 𝓔 J
    omega
  rw [hk]

end localize
open FiniteLocallyFreeQuotient.QuotFLF.Tgt

private theorem poly_eq_of_localization {R : Type u} [CommRing R] {p p' : R[X]}
    (h : ∀ (J : Ideal R) (_ : J.IsMaximal),
      p.map (algebraMap R (Localization.AtPrime J)) = p'.map (algebraMap R (Localization.AtPrime
        J))) :
    p = p' := by
  rw [← sub_eq_zero]
  ext k
  rw [coeff_sub, coeff_zero]
  refine eq_zero_of_localization _ fun J hJ => ?_
  have := congrArg (fun q => q.coeff k) (h J hJ)
  simp only [coeff_map] at this
  rw [map_sub, this, sub_self]

end L1
open FiniteLocallyFreeQuotient.QuotFLF.Tgt FiniteLocallyFreeQuotient.QuotFLF.L1

section L1
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
  [Module.Projective R S]

open L1

private noncomputable def 𝓔₀ : Envelope R S := Classical.choice (nonempty_envelope R S)

set_option linter.unusedVariables false in

private noncomputable def charpoly (r : ℕ) (hr : ∀ p, Module.rankAtStalk (R := R) S p = r) (b : S) :
    R[X] :=
  χ (𝓔₀ R S) b /ₘ (X - 1) ^ ((𝓔₀ R S).n - r)

variable (r : ℕ) (hr : ∀ p, Module.rankAtStalk (R := R) S p = r)

private theorem monic_X_sub_one_pow (k : ℕ) : ((X - 1 : R[X]) ^ k).Monic := (monic_X_sub_C (1 :
  R)).pow k

private theorem map_X_sub_one_pow {R' : Type u} [CommRing R'] (f : R →+* R') (k : ℕ) :
    ((X - 1 : R[X]) ^ k).map f = (X - 1) ^ k := by
  rw [Polynomial.map_pow, Polynomial.map_sub, map_X, Polynomial.map_one]

include hr in
private theorem χ₀_modByMonic (b : S) : χ (𝓔₀ R S) b %ₘ (X - 1) ^ ((𝓔₀ R S).n - r) = 0 := by
  refine poly_eq_of_localization fun J hJ => ?_
  rw [map_modByMonic _ (monic_X_sub_one_pow R _), map_X_sub_one_pow, Polynomial.map_zero,
    χ_map_localization r hr, (modByMonic_eq_zero_iff_dvd (monic_X_sub_one_pow _ _)).mpr
      (dvd_mul_left _ _)]

include hr in
private theorem χ₀_eq (b : S) :
    χ (𝓔₀ R S) b = (X - 1) ^ ((𝓔₀ R S).n - r) * charpoly R S r hr b := by
  have h := modByMonic_add_div (χ (𝓔₀ R S) b) ((X - 1) ^ ((𝓔₀ R S).n - r))
  rw [χ₀_modByMonic R S r hr, zero_add] at h
  exact h.symm

private theorem charpoly_map_localization (J : Ideal R) [J.IsPrime] (b : S) :
    (charpoly R S r hr b).map (algebraMap R (Localization.AtPrime J)) =
      LinearMap.charpoly (LinearMap.mulLeft (Localization.AtPrime J)
        ((1 : Localization.AtPrime J) ⊗ₜ[R] b)) := by
  have h := χ_map_localization r hr (𝓔₀ R S) J b
  rw [χ₀_eq R S r hr, Polynomial.map_mul, map_X_sub_one_pow, mul_comm] at h
  exact (monic_X_sub_one_pow _ _).isRegular.right h

private theorem χ_eq_charpoly_mul (𝓔 : Envelope R S) (b : S) :
    χ 𝓔 b = charpoly R S r hr b * (X - 1) ^ (𝓔.n - r) := by
  refine poly_eq_of_localization fun J hJ => ?_
  rw [χ_map_localization r hr, Polynomial.map_mul, map_X_sub_one_pow,
    charpoly_map_localization R S r hr]

private theorem L1_monic (b : S) : (charpoly R S r hr b).Monic :=
  Monic.of_mul_monic_left (monic_X_sub_one_pow R _) (by rw [← χ₀_eq R S r hr]; exact χ_monic _ _)

private theorem L1_natDegree [Nontrivial R] (b : S) : (charpoly R S r hr b).natDegree = r := by
  obtain ⟨J, hJ⟩ := Ideal.exists_maximal R
  have hle : r ≤ (𝓔₀ R S).n := by
    rw [n_eq_add_finrank_ker_localization r hr (𝓔₀ R S) J]
    exact Nat.le_add_right _ _
  have hX1 : (X - 1 : R[X]).Monic := monic_X_sub_C 1
  have hX1d : (X - 1 : R[X]).natDegree = 1 := by rw [← C_1, natDegree_X_sub_C]
  have h := congrArg natDegree (χ₀_eq R S r hr b)
  rw [χ_natDegree, Monic.natDegree_mul (monic_X_sub_one_pow R _) (L1_monic R S r hr b),
    hX1.natDegree_pow, hX1d, mul_one] at h
  omega

private theorem L1_aeval_self (b : S) : aeval b (charpoly R S r hr b) = 0 := by
  refine Module.eq_zero_of_localization_maximal
    (fun P _ => Localization.AtPrime P ⊗[R] S)
    (fun P _ => TensorProduct.mk R (Localization.AtPrime P) S 1) _ fun P hP => ?_

  have h1 : (TensorProduct.mk R (Localization.AtPrime P) S 1) (aeval b (charpoly R S r hr b)) =
      aeval ((1 : Localization.AtPrime P) ⊗ₜ[R] b)
        ((charpoly R S r hr b).map (algebraMap R (Localization.AtPrime P))) := by
    rw [aeval_map_algebraMap]
    exact (aeval_algHom_apply (Algebra.TensorProduct.includeRight :
      S →ₐ[R] Localization.AtPrime P ⊗[R] S) b (charpoly R S r hr b)).symm
  rw [h1, charpoly_map_localization R S r hr P]
  have hlm : ∀ a : Localization.AtPrime P ⊗[R] S,
      (Algebra.lmul (Localization.AtPrime P) (Localization.AtPrime P ⊗[R] S)) a =
        LinearMap.mulLeft (Localization.AtPrime P) a := fun a => rfl
  have h2 := aeval_algHom_apply (Algebra.lmul (Localization.AtPrime P)
    (Localization.AtPrime P ⊗[R] S)) ((1 : Localization.AtPrime P) ⊗ₜ[R] b)
    (LinearMap.charpoly (LinearMap.mulLeft (Localization.AtPrime P)
      ((1 : Localization.AtPrime P) ⊗ₜ[R] b)))
  rw [hlm, LinearMap.aeval_self_charpoly, hlm] at h2
  have h3 := LinearMap.congr_fun h2 1
  rw [LinearMap.zero_apply, LinearMap.mulLeft_apply, mul_one] at h3
  exact h3.symm

private theorem L1_map_baseChange (R' : Type u) [CommRing R'] [Algebra R R']
    (hr' : ∀ p, Module.rankAtStalk (R := R') (TensorProduct R R' S) p = r) (b : S) :
    (charpoly R S r hr b).map (algebraMap R R') =
      charpoly R' (TensorProduct R R' S) r hr' ((1 : R') ⊗ₜ[R] b) := by
  have h := χ_eq_charpoly_mul R' (R' ⊗[R] S) r hr' ((𝓔₀ R S).baseChange R') ((1 : R') ⊗ₜ[R] b)
  rw [χ_baseChange, χ₀_eq R S r hr, Polynomial.map_mul, map_X_sub_one_pow, mul_comm] at h
  exact (monic_X_sub_one_pow _ _).isRegular.right h

private theorem L1_algEquiv (S₂ : Type u) [CommRing S₂] [Algebra R S₂] [Module.Finite R S₂]
    [Module.Projective R S₂] (hr₂ : ∀ p, Module.rankAtStalk (R := R) S₂ p = r)
    (σ : S ≃ₐ[R] S₂) (b : S) :
    charpoly R S₂ r hr₂ (σ b) = charpoly R S r hr b := by
  have h := χ_eq_charpoly_mul R S₂ r hr₂ ((𝓔₀ R S).mapEquiv σ) (σ b)
  rw [χ_mapEquiv, χ₀_eq R S r hr, mul_comm] at h
  exact ((monic_X_sub_one_pow _ _).isRegular.right h).symm

private theorem L1_eq_linearMap_charpoly [Module.Free R S] (b : S) :
    charpoly R S r hr b = LinearMap.charpoly (LinearMap.mulLeft R b) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _

  let b₀ := Module.Free.chooseBasis R S
  let m := Fintype.card (Module.Free.ChooseBasisIndex R S)
  let b₁ : Module.Basis (Fin m) R S := b₀.reindex (Fintype.equivFin _)
  let 𝓔₁ : Envelope R S := ⟨m, b₁.equivFun.symm.toLinearMap, b₁.equivFun.toLinearMap, by
    apply LinearMap.ext; intro y; simp⟩
  haveI : Subsingleton (LinearMap.ker 𝓔₁.π) := ⟨fun x y => Subtype.ext (by
    have hx : 𝓔₁.π x = 0 := x.2
    have hy : 𝓔₁.π y = 0 := y.2
    have : Function.Injective 𝓔₁.π := b₁.equivFun.symm.injective
    exact this (hx.trans hy.symm))⟩
  have hm : 𝓔₁.n = r := by
    obtain ⟨J, hJ⟩ := Ideal.exists_maximal R
    have h := congrFun (Module.rankAtStalk_eq_finrank_of_free (R := R) (M := S)) ⟨J, hJ.isPrime⟩
    rw [hr] at h
    simp only [Pi.natCast_apply, Nat.cast_id] at h
    change m = r
    rw [h, Module.finrank_eq_card_basis b₁, Fintype.card_fin]
  have h := χ_eq_charpoly_mul R S r hr 𝓔₁ b
  rw [χ_eq_mul_of_free, Module.finrank_zero_of_subsingleton, pow_zero, mul_one, hm,
    Nat.sub_self, pow_zero, mul_one] at h
  exact h.symm

private theorem L1_rankAtStalk_baseChange (R' : Type u) [CommRing R'] [Algebra R R']
    (p : PrimeSpectrum R') :
    Module.rankAtStalk (R := R') (TensorProduct R R' S) p =
      Module.rankAtStalk (R := R) S (PrimeSpectrum.comap (algebraMap R R') p) :=
  Module.rankAtStalk_baseChange p

end L1
open FiniteLocallyFreeQuotient.QuotFLF.Tgt FiniteLocallyFreeQuotient.QuotFLF.L1

section L2

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {t : A →+* B}
  [Module.Finite A B] [Module.Projective A B]
  (hgen : (algebraMap A B).range ⊔ t.range = ⊤)
  (hequiv : ∀ (T : Type u) [CommRing T], _root_.Equivalence (Rel (algebraMap A B) t T))
  (r : ℕ) (hr : ∀ p, Module.rankAtStalk (R := A) B p = r)

private scoped instance instAlgebraLeftP₁ (t : A →+* B) : Algebra B (P₁ t) :=
  inferInstanceAs (Algebra (Tgt t) (P₁ t))

private scoped instance instFiniteLeftP₁ (t : A →+* B) : Module.Finite B (P₁ t) :=
  inferInstanceAs (Module.Finite (Tgt t) (P₁ t))

private scoped instance instProjectiveLeftP₁ (t : A →+* B) : Module.Projective B (P₁ t) :=
  inferInstanceAs (Module.Projective (Tgt t) (P₁ t))

omit [Module.Finite A B] [Module.Projective A B] in
private theorem algebraMap_P₁_apply (t : A →+* B) (b : B) : algebraMap B (P₁ t) b = inl₁ t b := rfl

include hgen hequiv in

private theorem charpoly_map_algebraMap_eq_map (f : A) :
    (charpoly A B r hr (t f)).map (algebraMap A B) = (charpoly A B r hr (t f)).map t := by

  have hr₂ : ∀ p, Module.rankAtStalk (R := B) (P₂ A B) p = r := fun p => by
    rw [Module.rankAtStalk_baseChange]; exact hr _
  have hr₁ : ∀ p, Module.rankAtStalk (R := Tgt t) (P₁ t) p = r := fun p => by
    rw [Module.rankAtStalk_baseChange]; exact hr _
  have hr₁' : ∀ p, Module.rankAtStalk (R := B) (P₁ t) p = r := hr₁

  have e₂ := L1_map_baseChange A B r hr B hr₂ (t f)
  have e₁ := L1_map_baseChange A B r hr (Tgt t) hr₁ (t f)
  rw [e₂]
  change _ = (charpoly A B r hr (t f)).map (algebraMap A (Tgt t))
  rw [e₁]

  obtain ⟨c, θ, hcs, hct, hθl, hθr⟩ := exists_theta (t := t) hgen hequiv
  let θ' : P₂ A B ≃ₐ[B] P₁ t :=
    AlgEquiv.ofRingEquiv (f := θ) (fun b => by
      rw [algebraMap_P₁_apply, ← hθl b]
      rfl)
  have key := L1_algEquiv B (P₂ A B) r hr₂ (P₁ t) hr₁' θ' ((1 : B) ⊗ₜ[A] t f)
  have hθ1 : θ' ((1 : B) ⊗ₜ[A] t f) = (1 : Tgt t) ⊗ₜ[A] t f := by
    change θ (1 ⊗ₜ t f) = _
    rw [hθr]
    exact RingHom.congr_fun hct f
  rw [hθ1] at key
  rw [← key]
  rfl

include hgen hequiv in

private theorem coeff_charpoly_invariant (f : A) (i : ℕ) :
    algebraMap A B ((charpoly A B r hr (t f)).coeff i) = t ((charpoly A B r hr (t f)).coeff i) := by
  have := congrArg (fun P : B[X] => P.coeff i) (charpoly_map_algebraMap_eq_map (t := t) hgen hequiv
    r hr f)
  simpa [Polynomial.coeff_map] using this

end L2
open FiniteLocallyFreeQuotient.QuotFLF.Tgt FiniteLocallyFreeQuotient.QuotFLF.L1

section L3

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra C A] (s t : A →+* B)

private theorem L3_exists_counit (hequiv : ∀ (T : Type u) [CommRing T],
  _root_.Equivalence (Rel s t T)) :
    ∃ e : B →+* A, e.comp s = RingHom.id A ∧ e.comp t = RingHom.id A :=
  (hequiv A).refl (RingHom.id A)

private theorem L3_t_injective (hequiv : ∀ (T : Type u) [CommRing T],
  _root_.Equivalence (Rel s t T)) :
    Function.Injective t := by
  obtain ⟨e, -, he⟩ := L3_exists_counit s t hequiv
  exact Function.LeftInverse.injective (g := e) fun a => RingHom.congr_fun he a

private theorem L3_s_injective (hequiv : ∀ (T : Type u) [CommRing T],
  _root_.Equivalence (Rel s t T)) :
    Function.Injective s := by
  obtain ⟨e, he, -⟩ := L3_exists_counit s t hequiv
  exact Function.LeftInverse.injective (g := e) fun a => RingHom.congr_fun he a

private theorem L3_isIntegral_of_charpoly_invariant
    (hequiv : ∀ (T : Type u) [CommRing T], _root_.Equivalence (Rel s t T))
    (hinv : ∀ a : A, s a = t a ↔ a ∈ Set.range (algebraMap C A))
    (hL2 : ∀ f : A, ∃ P : A[X], P.Monic ∧ (∀ i, s (P.coeff i) = t (P.coeff i)) ∧
      aeval (t f) (P.map s) = 0) :
    Algebra.IsIntegral C A := by
  have hst : s.comp (algebraMap C A) = t.comp (algebraMap C A) :=
    RingHom.ext fun c => (hinv _).mpr ⟨c, rfl⟩
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact ⟨fun f => by rw [Subsingleton.elim f 0]; exact isIntegral_zero⟩
  refine ⟨fun f => ?_⟩
  obtain ⟨P, hPm, hPinv, hP0⟩ := hL2 f
  have hlifts : P ∈ Polynomial.lifts (algebraMap C A) :=
    (lifts_iff_coeff_lifts P).mpr fun i => (hinv _).mp (hPinv i)
  obtain ⟨Q, hQP, -, hQm⟩ := lifts_and_degree_eq_and_monic hlifts hPm
  have key : t (eval₂ (algebraMap C A) f Q) = aeval (t f) (P.map s) := by
    rw [hom_eval₂, ← hst, ← hQP, Polynomial.map_map, aeval_def, eval₂_map, Algebra.algebraMap_self,
      RingHom.id_comp]
  have h0 : eval₂ (algebraMap C A) f Q = 0 := by
    apply L3_t_injective s t hequiv
    rw [map_zero, key, hP0]
  exact ⟨Q, hQm, h0⟩

set_option linter.unusedVariables false in

private theorem L3_isIntegral
    (hequiv : ∀ (T : Type u) [CommRing T], _root_.Equivalence (Rel s t T))
    (hinj : Function.Injective (algebraMap C A))
    (hinv : ∀ a : A, s a = t a ↔ a ∈ Set.range (algebraMap C A))
    (hL2 : ∀ f : A, ∃ P : A[X], P.Monic ∧ (∀ i, s (P.coeff i) = t (P.coeff i)) ∧
      aeval (t f) (P.map s) = 0) :
    Algebra.IsIntegral C A :=
  L3_isIntegral_of_charpoly_invariant s t hequiv hinv hL2

end L3
open FiniteLocallyFreeQuotient.QuotFLF.Tgt FiniteLocallyFreeQuotient.QuotFLF.L1

section L6

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra C A]
  {t : A →+* B}
  (hgen : (algebraMap A B).range ⊔ t.range = ⊤)
  (hequiv : ∀ (T : Type u) [CommRing T], _root_.Equivalence (Rel (algebraMap A B) t T))
  (hinj : Function.Injective (algebraMap C A))
  (hinv : ∀ a : A, algebraMap A B a = t a ↔ a ∈ Set.range (algebraMap C A))
  {r : ℕ} (x : Fin r → A)
  (hx : Function.Bijective fun a : Fin r → A => ∑ i, algebraMap A B (a i) * t (x i))

private noncomputable def vA (t : A →+* B) (x : Fin r → A) : (Fin r → A) →ₗ[A] B :=
  Fintype.linearCombination A (fun i => t (x i))

omit [Algebra C A] in
private theorem vA_apply (a : Fin r → A) : vA t x a = ∑ i, algebraMap A B (a i) * t (x i) := by
  simp [vA, Fintype.linearCombination_apply, Algebra.smul_def]

private noncomputable def vC (x : Fin r → A) : (Fin r → C) →ₗ[C] A :=
  Fintype.linearCombination C x

omit [Algebra A B] in
private theorem vC_apply (w : Fin r → C) : vC (C := C) x w = ∑ i, algebraMap C A (w i) * x i := by
  simp [vC, Fintype.linearCombination_apply, Algebra.smul_def]

private noncomputable def vB (t : A →+* B) (x : Fin r → A) (b : Fin r → B) : P₁ t :=
  ∑ i, (Tgt.of t (b i)) ⊗ₜ[A] t (x i)

omit [Algebra C A] in
include hx in
private theorem vB_injective : Function.Injective (vB t x) := by
  classical

  let e : (Fin r → A) ≃ₗ[A] B := LinearEquiv.ofBijective (vA t x) (by
    convert hx using 1
    funext a
    exact vA_apply x a)
  let 𝒷 : Module.Basis (Fin r) A B := Module.Basis.ofEquivFun e.symm
  have h𝒷 : ∀ i, 𝒷 i = t (x i) := fun i => by
    rw [Module.Basis.coe_ofEquivFun, LinearEquiv.symm_symm]
    change vA t x (Pi.single i 1) = _
    simp [vA, Fintype.linearCombination_apply_single]
  let 𝒷₁ : Module.Basis (Fin r) (Tgt t) (P₁ t) := Algebra.TensorProduct.basis (Tgt t) 𝒷
  have key : ∀ b : Fin r → B, vB t x b = 𝒷₁.equivFun.symm (fun i => Tgt.of t (b i)) := fun b => by
    rw [Module.Basis.equivFun_symm_apply]
    simp only [vB, 𝒷₁, Algebra.TensorProduct.basis_apply, h𝒷]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  intro b b' h
  rw [key, key] at h
  have := 𝒷₁.equivFun.symm.injective h
  funext i
  exact (Tgt.of t).injective (congrFun this i)

omit [Algebra C A] in
private theorem vB_comp_t (a : Fin r → A) : vB t x (fun i => t (a i)) = inr₁ t (vA t x a) := by
  simp only [vB, vA_apply, inr₁_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : Tgt.of t (t (a i)) = algebraMap A (Tgt t) (a i) := rfl
  rw [this, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.smul_def]

omit [Algebra C A] in
private theorem vB_comp_s {c : B →+* P₁ t} (hcs : c.comp (algebraMap A B) = (inl₁ t).comp
  (algebraMap A B))
    (hct : c.comp t = (inr₁ t).comp t) (a : Fin r → A) :
    vB t x (fun i => algebraMap A B (a i)) = c (vA t x a) := by
  simp only [vB, vA_apply, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show c (algebraMap A B (a i)) = inl₁ t (algebraMap A B (a i)) from RingHom.congr_fun hcs (a
    i),
    show c (t (x i)) = inr₁ t (t (x i)) from RingHom.congr_fun hct (x i), inl₁_apply, inr₁_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

include hequiv in
omit [Algebra C A] in
private theorem t_injective : Function.Injective t := by
  obtain ⟨e, -, het⟩ := exists_counit hequiv
  exact Function.LeftInverse.injective (g := e) fun a => RingHom.congr_fun het a

include hequiv hinj hinv hx in

private theorem vC_bijective : Function.Bijective fun w : Fin r → C => ∑ i,
  algebraMap C A (w i) * x i := by
  have hfun : (fun w : Fin r → C => ∑ i, algebraMap C A (w i) * x i) = vC (C := C) x := by
    funext w; exact (vC_apply x w).symm
  rw [hfun]
  obtain ⟨c, hcs, hct⟩ := exists_comul hequiv (inl₁ t) (inr₁ t) (inl₁_comp_t t)
  have hst : ∀ a : A, (algebraMap A B a = t a) ↔ a ∈ Set.range (algebraMap C A) := hinv

  have hcomm : ∀ w : Fin r → C, t (vC (C := C) x w) = vA t x (fun i => algebraMap C A (w i)) := by
    intro w
    rw [vC_apply, vA_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ((hst _).2 ⟨w i, rfl⟩)]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro w hw
    have h1 : vA t x (fun i => algebraMap C A (w i)) = 0 := by rw [← hcomm, hw, map_zero]
    have h2 : (fun i => algebraMap C A (w i)) = 0 := by
      have := hx.1 (a₁ := fun i => algebraMap C A (w i)) (a₂ := 0)
      apply this
      simpa [vA_apply] using h1
    funext i
    exact hinj (by simpa using congrFun h2 i)
  · intro a
    obtain ⟨α, hα⟩ := hx.2 (t a)
    have hα' : vA t x α = t a := by rw [vA_apply]; exact hα

    have h3 : (fun i => t (α i)) = fun i => algebraMap A B (α i) := by
      apply vB_injective x hx
      rw [vB_comp_t, vB_comp_s x hcs hct, hα',
        show c (t a) = inr₁ t (t a) from RingHom.congr_fun hct a]
    choose w hw using fun i => (hst (α i)).1 (congrFun h3 i).symm
    refine ⟨w, t_injective hequiv ?_⟩
    rw [hcomm]
    have : (fun i => algebraMap C A (w i)) = α := funext hw
    rw [this, hα']

include hequiv hinj hinv hx in

private theorem isPushout_of_basis :
    IsPushout (CommRingCat.ofHom (algebraMap C A)) (CommRingCat.ofHom (algebraMap C A))
      (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom t) := by
  classical
  letI : Algebra C B := ((algebraMap A B).comp (algebraMap C A)).toAlgebra
  haveI : IsScalarTower C A B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let sC : A →ₐ[C] B := IsScalarTower.toAlgHom C A B
  let tC : A →ₐ[C] B :=
    { t with commutes' := fun c => ((hinv (algebraMap C A c)).2 ⟨c, rfl⟩).symm }
  let Φ : A ⊗[C] A →ₐ[C] B := Algebra.TensorProduct.lift sC tC (fun _ _ => .all _ _)
  have hΦ : ∀ a a' : A, Φ (a ⊗ₜ a') = algebraMap A B a * t a' := fun a a' =>
    Algebra.TensorProduct.lift_tmul ..

  let eC : (Fin r → C) ≃ₗ[C] A := LinearEquiv.ofBijective (vC (C := C) x) (by
    convert vC_bijective hequiv hinj hinv x hx using 1
    funext w
    exact vC_apply x w)
  let 𝓍 : Module.Basis (Fin r) C A := Module.Basis.ofEquivFun eC.symm
  have h𝓍 : ∀ i, 𝓍 i = x i := fun i => by
    rw [Module.Basis.coe_ofEquivFun, LinearEquiv.symm_symm]
    change vC (C := C) x (Pi.single i 1) = _
    simp [vC, Fintype.linearCombination_apply_single]
  let 𝓍A : Module.Basis (Fin r) A (A ⊗[C] A) := Algebra.TensorProduct.basis A 𝓍
  have hΦ' : ∀ a : Fin r → A, Φ (𝓍A.equivFun.symm a) = ∑ i, algebraMap A B (a i) * t (x i) := by
    intro a
    rw [Module.Basis.equivFun_symm_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [𝓍A, Algebra.TensorProduct.basis_apply, h𝓍]
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, hΦ]
  have hbij : Function.Bijective Φ := by
    have hcomp : (fun a : Fin r → A => ∑ i, algebraMap A B (a i) * t (x i)) =
        Φ ∘ 𝓍A.equivFun.symm := by funext a; exact (hΦ' a).symm
    have := hx
    rw [hcomp] at this
    exact (Function.Bijective.of_comp_iff Φ 𝓍A.equivFun.symm.bijective).mp this
  let ΦR : A ⊗[C] A ≃+* B := RingEquiv.ofBijective Φ.toRingHom hbij
  refine (CommRingCat.isPushout_tensorProduct C A A).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ΦR.toCommRingCatIso (by simp) (by simp) ?_ ?_
  · ext a
    change ΦR (a ⊗ₜ 1) = algebraMap A B a
    change Φ (a ⊗ₜ 1) = _
    rw [hΦ, map_one, mul_one]
  · ext a
    change ΦR (1 ⊗ₜ a) = t a
    change Φ (1 ⊗ₜ a) = _
    rw [hΦ, map_one, one_mul]

end L6
open FiniteLocallyFreeQuotient.QuotFLF.Tgt FiniteLocallyFreeQuotient.QuotFLF.L1

namespace L8

variable (R : Type u) [CommRing R] [IsLocalRing R]

private noncomputable abbrev primeX : Ideal R[X] := (IsLocalRing.maximalIdeal R).map (C : R →+*
  R[X])

private abbrev RX : Type u := Localization.AtPrime (primeX R)

private scoped instance : IsLocalHom (algebraMap R (RX R)) := by
  refine ⟨fun a ha => ?_⟩
  rw [IsScalarTower.algebraMap_apply R R[X] (RX R),
    IsLocalization.AtPrime.isUnit_to_map_iff (RX R) (primeX R)] at ha
  by_contra h
  exact ha (Ideal.mem_map_of_mem C ((IsLocalRing.mem_maximalIdeal a).mpr h))

private theorem faithfullyFlat : Module.FaithfullyFlat R (RX R) :=
  Module.FaithfullyFlat.of_flat_of_isLocalHom

private theorem residue_X_pow_injective :
    Function.Injective fun n : ℕ =>
      IsLocalRing.residue (RX R) (algebraMap R[X] (RX R) (X ^ n)) := by
  intro m n h
  by_contra hmn
  have h1 : IsLocalRing.residue (RX R) (algebraMap R[X] (RX R) (X ^ m - X ^ n)) = 0 := by
    rw [map_sub, map_sub, sub_eq_zero]
    exact h
  rw [IsLocalRing.residue_eq_zero_iff,
    IsLocalization.AtPrime.to_map_mem_maximal_iff (RX R) (primeX R), Ideal.mem_map_C_iff] at h1
  have h2 := h1 m
  rw [coeff_sub, coeff_X_pow, coeff_X_pow, if_pos rfl, if_neg hmn, sub_zero] at h2
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    ((Ideal.eq_top_iff_one _).mpr h2)

private theorem infinite_residueField : Infinite (IsLocalRing.ResidueField (RX R)) :=
  Infinite.of_injective _ (residue_X_pow_injective R)

end L8
open FiniteLocallyFreeQuotient.QuotFLF.Tgt FiniteLocallyFreeQuotient.QuotFLF.L1
  FiniteLocallyFreeQuotient.QuotFLF.L8

private theorem L8_exists_flat_local_infinite (R : Type u) [CommRing R] [IsLocalRing R] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsLocalRing R') (_ : Algebra R R'),
      Module.FaithfullyFlat R R' ∧ IsLocalHom (algebraMap R R') ∧
      Infinite (IsLocalRing.ResidueField R') :=
  ⟨L8.RX R, inferInstance, inferInstance, inferInstance, L8.faithfullyFlat R, inferInstance,
    L8.infinite_residueField R⟩

namespace L7

section generic

variable {C A B : Type u} [CommRing C] [CommRing A] [CommRing B] [Algebra C A] [Algebra C B]
  (C' : Type u) [CommRing C'] [Algebra C C'] (u : A →+* B)
  (hu : u.comp (algebraMap C A) = algebraMap C B)

private def algHomOf : A →ₐ[C] B :=
  { u with commutes' := fun c => RingHom.congr_fun hu c }

@[scoped simp] private theorem algHomOf_apply (a : A) : algHomOf u hu a = u a := rfl

private noncomputable def bc : C' ⊗[C] A →ₐ[C'] C' ⊗[C] B :=
  Algebra.TensorProduct.map (AlgHom.id C' C') (algHomOf u hu)

@[scoped simp] private theorem bc_tmul (c : C') (a : A) : bc C' u hu (c ⊗ₜ[C] a) = c ⊗ₜ[C] u a := by
  simp [bc]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in

private theorem bc_eq_comp :
    letI : Algebra A B := u.toAlgebra
    haveI : IsScalarTower C A B :=
      IsScalarTower.of_algebraMap_eq fun c => (RingHom.congr_fun hu c).symm
    (bc C' u hu).toRingHom =
      (Algebra.IsPushout.cancelBaseChangeAlg C C' A (C' ⊗[C] A) B).toRingEquiv.toRingHom.comp
        (algebraMap (C' ⊗[C] A) ((C' ⊗[C] A) ⊗[A] B)) := by
  letI : Algebra A B := u.toAlgebra
  haveI : IsScalarTower C A B :=
    IsScalarTower.of_algebraMap_eq fun c => (RingHom.congr_fun hu c).symm
  have key := Algebra.IsPushout.cancelBaseChange_symm_comp_lTensor C A B C'
  have hg : IsScalarTower.toAlgHom C A B = algHomOf u hu := AlgHom.ext fun _ => rfl
  apply RingHom.ext
  intro x
  apply (Algebra.IsPushout.cancelBaseChangeAlg C C' A (C' ⊗[C] A) B).symm.injective
  have hx := AlgHom.congr_fun key x
  rw [hg] at hx
  refine hx.trans ?_
  change _ = (Algebra.IsPushout.cancelBaseChangeAlg C C' A (C' ⊗[C] A) B).symm
    ((Algebra.IsPushout.cancelBaseChangeAlg C C' A (C' ⊗[C] A) B)
      (algebraMap (C' ⊗[C] A) ((C' ⊗[C] A) ⊗[A] B) x))
  rw [AlgEquiv.symm_apply_apply]
  rfl

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
private theorem finite_bc (h : u.Finite) : (bc C' u hu).toRingHom.Finite := by
  letI : Algebra A B := u.toAlgebra
  haveI : IsScalarTower C A B :=
    IsScalarTower.of_algebraMap_eq fun c => (RingHom.congr_fun hu c).symm
  have h1 := RingHom.finite_isStableUnderBaseChange.tensorProduct (R := A) (S := B) (C' ⊗[C] A) h
  rw [bc_eq_comp]
  refine RingHom.finite_respectsIso.1 _ _ ?_
  convert h1

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
private theorem flat_bc (h : u.Flat) : (bc C' u hu).toRingHom.Flat := by
  letI : Algebra A B := u.toAlgebra
  haveI : IsScalarTower C A B :=
    IsScalarTower.of_algebraMap_eq fun c => (RingHom.congr_fun hu c).symm
  have h1 := RingHom.Flat.isStableUnderBaseChange.tensorProduct (R := A) (S := B) (C' ⊗[C] A) h
  rw [bc_eq_comp]
  refine RingHom.Flat.respectsIso.1 _ _ ?_
  convert h1

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
private theorem finitePresentation_bc (h : u.FinitePresentation) :
    (bc C' u hu).toRingHom.FinitePresentation := by
  letI : Algebra A B := u.toAlgebra
  haveI : IsScalarTower C A B :=
    IsScalarTower.of_algebraMap_eq fun c => (RingHom.congr_fun hu c).symm
  have h1 := RingHom.finitePresentation_isStableUnderBaseChange.tensorProduct (R := A) (S := B)
    (C' ⊗[C] A) h
  rw [bc_eq_comp]
  refine RingHom.finitePresentation_respectsIso.1 _ _ ?_
  convert h1

attribute [local instance] Algebra.TensorProduct.rightAlgebra in

private theorem projective_bc (hproj : letI : Algebra A B := u.toAlgebra; Module.Projective A B) :
    letI : Algebra (C' ⊗[C] A) (C' ⊗[C] B) := (bc C' u hu).toRingHom.toAlgebra
    Module.Projective (C' ⊗[C] A) (C' ⊗[C] B) := by
  letI : Algebra A B := u.toAlgebra
  haveI : IsScalarTower C A B :=
    IsScalarTower.of_algebraMap_eq fun c => (RingHom.congr_fun hu c).symm
  letI : Algebra (C' ⊗[C] A) (C' ⊗[C] B) := (bc C' u hu).toRingHom.toAlgebra
  haveI : Module.Projective A B := hproj
  let e := Algebra.IsPushout.cancelBaseChangeAlg C C' A (C' ⊗[C] A) B
  have he : ∀ a', e (algebraMap (C' ⊗[C] A) ((C' ⊗[C] A) ⊗[A] B) a') =
      algebraMap (C' ⊗[C] A) (C' ⊗[C] B) a' :=
    fun a' => (RingHom.congr_fun (bc_eq_comp C' u hu) a').symm
  let eL : ((C' ⊗[C] A) ⊗[A] B) ≃ₗ[C' ⊗[C] A] (C' ⊗[C] B) :=
    { e.toRingEquiv.toAddEquiv with
      map_smul' := fun a' x => by
        change e (a' • x) = a' • e x
        rw [Algebra.smul_def, ← he, ← map_mul]
        congr 1
        induction x using TensorProduct.induction_on with
        | zero => rw [smul_zero, mul_zero]
        | add x y hx hy => rw [smul_add, mul_add, hx, hy]
        | tmul a₁ b =>
          rw [TensorProduct.smul_tmul', smul_eq_mul, Algebra.TensorProduct.algebraMap_apply,
            Algebra.algebraMap_self, RingHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul,
              one_mul] }
  exact Module.Projective.of_equiv eL

end generic
open FiniteLocallyFreeQuotient.QuotFLF.Tgt FiniteLocallyFreeQuotient.QuotFLF.L1
  FiniteLocallyFreeQuotient.QuotFLF.L8

section lift

variable {C : Type u} [CommRing C] (C' : Type u) [CommRing C'] [Algebra C C']
  {X : Type u} [CommRing X] [Algebra C X] {T : Type u} [CommRing T]

private theorem ringHom_ext_tmul {f g : C' ⊗[C] X →+* T} (h : ∀ (c : C') (x : X),
  f (c ⊗ₜ[C] x) = g (c ⊗ₜ[C] x)) :
    f = g := by
  apply RingHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => rw [map_add, map_add, hz, hw]
  | tmul c x => exact h c x

private noncomputable def liftPair (χ : C' →+* T) (φ : X →+* T)
    (h : φ.comp (algebraMap C X) = χ.comp (algebraMap C C')) : C' ⊗[C] X →+* T :=
  letI : Algebra C' T := χ.toAlgebra
  letI : Algebra C T := (χ.comp (algebraMap C C')).toAlgebra
  haveI : IsScalarTower C C' T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  (Algebra.TensorProduct.lift (Algebra.ofId C' T)
    ({ φ with commutes' := fun c => RingHom.congr_fun h c } : X →ₐ[C] T)
    (fun _ _ => Commute.all _ _)).toRingHom

@[scoped simp] private theorem liftPair_tmul (χ : C' →+* T) (φ : X →+* T)
    (h : φ.comp (algebraMap C X) = χ.comp (algebraMap C C')) (c : C') (x : X) :
    liftPair C' χ φ h (c ⊗ₜ[C] x) = χ c * φ x := by
  letI : Algebra C' T := χ.toAlgebra
  letI : Algebra C T := (χ.comp (algebraMap C C')).toAlgebra
  haveI : IsScalarTower C C' T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  change Algebra.TensorProduct.lift (Algebra.ofId C' T)
    ({ φ with commutes' := fun c => RingHom.congr_fun h c } : X →ₐ[C] T)
    (fun _ _ => Commute.all _ _) (c ⊗ₜ[C] x) = _
  rw [Algebra.TensorProduct.lift_tmul]
  rfl

end lift
open FiniteLocallyFreeQuotient.QuotFLF.Tgt FiniteLocallyFreeQuotient.QuotFLF.L1
  FiniteLocallyFreeQuotient.QuotFLF.L8

end L7
open FiniteLocallyFreeQuotient.QuotFLF.Tgt FiniteLocallyFreeQuotient.QuotFLF.L1
  FiniteLocallyFreeQuotient.QuotFLF.L8 FiniteLocallyFreeQuotient.QuotFLF.L7

section L7

open L7

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra C A]
  [Algebra C B] [IsScalarTower C A B]
  (t : A →+* B) (C' : Type u) [CommRing C'] [Algebra C C']

private theorem s_comp_algebraMap : (algebraMap A B).comp (algebraMap C A) = algebraMap C B :=
  RingHom.ext fun c => (IsScalarTower.algebraMap_apply C A B c).symm

variable {t} in
private theorem t_comp_algebraMap (hinv : ∀ a : A,
  algebraMap A B a = t a ↔ a ∈ Set.range (algebraMap C A)) :
    t.comp (algebraMap C A) = algebraMap C B :=
  RingHom.ext fun c => ((hinv _).mpr ⟨c,
    rfl⟩).symm.trans (IsScalarTower.algebraMap_apply C A B c).symm

private noncomputable def s' : C' ⊗[C] A →ₐ[C'] C' ⊗[C] B :=
  Algebra.TensorProduct.map (AlgHom.id C' C') (IsScalarTower.toAlgHom C A B)

noncomputable scoped instance instAlgebraPrimed : Algebra (C' ⊗[C] A) (C' ⊗[C] B) :=
  (s' C' : C' ⊗[C] A →ₐ[C'] C' ⊗[C] B).toRingHom.toAlgebra

private scoped instance instIsScalarTowerPrimed : IsScalarTower C' (C' ⊗[C] A) (C' ⊗[C] B) :=
  IsScalarTower.of_algebraMap_eq fun c =>
    ((s' C' : C' ⊗[C] A →ₐ[C'] C' ⊗[C] B).commutes c).symm

@[scoped simp] private theorem algebraMap_primed_tmul (c : C') (a : A) :
    algebraMap (C' ⊗[C] A) (C' ⊗[C] B) (c ⊗ₜ[C] a) = c ⊗ₜ[C] algebraMap A B a := by
  change s' C' (c ⊗ₜ[C] a) = _
  simp [s']

private theorem algebraMap_primed_eq_bc :
    algebraMap (C' ⊗[C] A) (C' ⊗[C] B) = (bc C' (algebraMap A B) (s_comp_algebraMap)).toRingHom :=
      by
  have h : IsScalarTower.toAlgHom C A B = algHomOf (algebraMap A B) s_comp_algebraMap :=
    AlgHom.ext fun _ => rfl
  change (s' C').toRingHom = _
  rw [s', h]
  rfl

omit [Algebra A B] [Algebra C B] [IsScalarTower C A B] in
private theorem algebraMap_left_apply (x : C') : algebraMap C' (C' ⊗[C] A) x = x ⊗ₜ[C] 1 := rfl

private noncomputable def t' (ht : t.comp (algebraMap C A) = algebraMap C B) : C' ⊗[C] A →+* C'
  ⊗[C] B :=
  (bc C' t ht).toRingHom

omit [Algebra A B] [IsScalarTower C A B] in
@[scoped simp] private theorem t'_tmul (ht : t.comp (algebraMap C A) = algebraMap C B) (c : C') (a
  : A) :
    t' t C' ht (c ⊗ₜ[C] a) = c ⊗ₜ[C] t a :=
  bc_tmul C' t ht c a

omit [Algebra A B] [IsScalarTower C A B] in
private theorem t'_algebraMap (ht : t.comp (algebraMap C A) = algebraMap C B) (c : C') :
    t' t C' ht (algebraMap C' (C' ⊗[C] A) c) = algebraMap C' (C' ⊗[C] B) c :=
  (bc C' t ht).commutes c

private theorem includeRight_comp_s :
    (Algebra.TensorProduct.includeRight (R := C) (A := C') (B := B)).toRingHom.comp (algebraMap A
      B) =
      (algebraMap (C' ⊗[C] A) (C' ⊗[C] B)).comp
        (Algebra.TensorProduct.includeRight (R := C) (A := C') (B := A)).toRingHom := by
  apply RingHom.ext
  intro a
  simp

omit [Algebra A B] [IsScalarTower C A B] in
private theorem includeRight_comp_t (ht : t.comp (algebraMap C A) = algebraMap C B) :
    (Algebra.TensorProduct.includeRight (R := C) (A := C') (B := B)).toRingHom.comp t =
      (t' t C' ht).comp (Algebra.TensorProduct.includeRight (R := C) (A := C') (B := A)).toRingHom
        := by
  apply RingHom.ext
  intro a
  simp

private theorem L7_finite_s (h : (algebraMap A B).Finite) : (algebraMap (C' ⊗[C] A) (C' ⊗[C]
  B)).Finite :=
  by
  rw [algebraMap_primed_eq_bc]; exact finite_bc C' _ _ h

private theorem L7_flat_s (h : (algebraMap A B).Flat) : (algebraMap (C' ⊗[C] A) (C' ⊗[C] B)).Flat
  := by
  rw [algebraMap_primed_eq_bc]; exact flat_bc C' _ _ h

private theorem L7_finitePresentation_s (h : (algebraMap A B).FinitePresentation) :
    (algebraMap (C' ⊗[C] A) (C' ⊗[C] B)).FinitePresentation := by
  rw [algebraMap_primed_eq_bc]; exact finitePresentation_bc C' _ _ h

omit [Algebra A B] [IsScalarTower C A B] in
private theorem L7_finite_t (ht : t.comp (algebraMap C A) = algebraMap C B) (h : t.Finite) :
    (t' t C' ht).Finite :=
  finite_bc C' t ht h

omit [Algebra A B] [IsScalarTower C A B] in
private theorem L7_flat_t (ht : t.comp (algebraMap C A) = algebraMap C B) (h : t.Flat) :
    (t' t C' ht).Flat :=
  flat_bc C' t ht h

omit [Algebra A B] [IsScalarTower C A B] in
private theorem L7_finitePresentation_t (ht : t.comp (algebraMap C A) = algebraMap C B)
    (h : t.FinitePresentation) : (t' t C' ht).FinitePresentation :=
  finitePresentation_bc C' t ht h

private scoped instance L7_moduleFinite [Module.Finite A B] : Module.Finite (C' ⊗[C] A) (C' ⊗[C] B)
  :=
  RingHom.finite_algebraMap.mp (L7_finite_s C' (RingHom.finite_algebraMap.mpr inferInstance))

private scoped instance L7_moduleFlat [Module.Flat A B] : Module.Flat (C' ⊗[C] A) (C' ⊗[C] B) :=
  RingHom.flat_algebraMap_iff.mp (L7_flat_s C' (RingHom.flat_algebraMap_iff.mpr inferInstance))

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
private scoped instance L7_moduleProjective [Module.Projective A B] :
    Module.Projective (C' ⊗[C] A) (C' ⊗[C] B) := by
  let e := Algebra.IsPushout.cancelBaseChangeAlg C C' A (C' ⊗[C] A) B
  have key := Algebra.IsPushout.cancelBaseChange_symm_comp_lTensor C A B C'
  have he : ∀ a', e (algebraMap (C' ⊗[C] A) ((C' ⊗[C] A) ⊗[A] B) a') =
      algebraMap (C' ⊗[C] A) (C' ⊗[C] B) a' := by
    intro a'
    have h1 := AlgHom.congr_fun key a'
    have h2 := congrArg e h1
    rw [AlgHom.comp_apply] at h2
    change e (e.symm (s' C' a')) = e _ at h2
    rw [AlgEquiv.apply_symm_apply] at h2
    exact h2.symm
  let eL : ((C' ⊗[C] A) ⊗[A] B) ≃ₗ[C' ⊗[C] A] (C' ⊗[C] B) :=
    { e.toRingEquiv.toAddEquiv with
      map_smul' := fun a' x => by
        change e (a' • x) = a' • e x
        rw [Algebra.smul_def, ← he, ← map_mul]
        congr 1
        induction x using TensorProduct.induction_on with
        | zero => rw [smul_zero, mul_zero]
        | add x y hx hy => rw [smul_add, mul_add, hx, hy]
        | tmul a₁ b =>
          rw [TensorProduct.smul_tmul', smul_eq_mul, Algebra.TensorProduct.algebraMap_apply,
            Algebra.algebraMap_self, RingHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul,
              one_mul] }
  exact Module.Projective.of_equiv eL

private scoped instance L7_finite_Tgt (ht : t.comp (algebraMap C A) = algebraMap C B) [h :
  Module.Finite A
  (Tgt t)] :
    Module.Finite (C' ⊗[C] A) (Tgt (t' t C' ht)) :=
  L7_finite_t t C' ht h

private scoped instance L7_flat_Tgt (ht : t.comp (algebraMap C A) = algebraMap C B) [h :
  Module.Flat A (Tgt
  t)] :
    Module.Flat (C' ⊗[C] A) (Tgt (t' t C' ht)) :=
  L7_flat_t t C' ht h

private scoped instance L7_projective_Tgt (ht : t.comp (algebraMap C A) = algebraMap C B)
    [h : Module.Projective A (Tgt t)] :
    Module.Projective (C' ⊗[C] A) (Tgt (t' t C' ht)) :=
  projective_bc C' t ht h

private theorem L7_hgen (ht : t.comp (algebraMap C A) = algebraMap C B)
    (hgen : (algebraMap A B).range ⊔ t.range = ⊤) :
    (algebraMap (C' ⊗[C] A) (C' ⊗[C] B)).range ⊔ (t' t C' ht).range = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x using TensorProduct.induction_on with
  | zero => exact Subring.zero_mem _
  | add x y hx hy => exact Subring.add_mem _ hx hy
  | tmul c b =>
    have h1 : c ⊗ₜ[C] b = (c ⊗ₜ[C] (1 : B)) * ((1 : C') ⊗ₜ[C] b) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [h1]
    refine Subring.mul_mem _ ((le_sup_left : (algebraMap (C' ⊗[C] A) (C' ⊗[C] B)).range ≤ _) ⟨c
      ⊗ₜ[C] 1, by simp⟩) ?_
    have hb : b ∈ (algebraMap A B).range ⊔ t.range := hgen ▸ Subring.mem_top b
    have hmap : Subring.map (Algebra.TensorProduct.includeRight (R := C) (A := C') (B :=
      B)).toRingHom
        ((algebraMap A B).range ⊔ t.range) ≤
        (algebraMap (C' ⊗[C] A) (C' ⊗[C] B)).range ⊔ (t' t C' ht).range := by
      rw [Subring.map_sup]
      refine sup_le_sup ?_ ?_
      · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
        exact ⟨(1 : C') ⊗ₜ[C] a, by simp⟩
      · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
        exact ⟨(1 : C') ⊗ₜ[C] a, by simp⟩
    exact hmap ⟨b, hb, rfl⟩

omit [Algebra A B] [Algebra C B] [IsScalarTower C A B] in
private theorem L7_algebraMap_injective [Module.Flat C C'] (hinj : Function.Injective (algebraMap C
  A)) :
    Function.Injective (algebraMap C' (C' ⊗[C] A)) := by
  have h1 : Function.Injective (LinearMap.lTensor C' (Algebra.linearMap C A)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hinj
  have h2 : (algebraMap C' (C' ⊗[C] A) : C' → C' ⊗[C] A) =
      LinearMap.lTensor C' (Algebra.linearMap C A) ∘ (TensorProduct.rid C C').symm := by
    funext c
    simp [Algebra.TensorProduct.algebraMap_apply]
  rw [h2]
  exact h1.comp (TensorProduct.rid C C').symm.injective

private theorem L7_invariants [Module.Flat C C']
    (hinv : ∀ a : A, algebraMap A B a = t a ↔ a ∈ Set.range (algebraMap C A))
    (a' : C' ⊗[C] A) :
    algebraMap (C' ⊗[C] A) (C' ⊗[C] B) a' = t' t C' (t_comp_algebraMap hinv) a' ↔
      a' ∈ Set.range (algebraMap C' (C' ⊗[C] A)) := by
  set sL : A →ₗ[C] B := (IsScalarTower.toAlgHom C A B).toLinearMap with hsL
  set tL : A →ₗ[C] B := (algHomOf t (t_comp_algebraMap hinv)).toLinearMap with htL
  have hex : Function.Exact (Algebra.linearMap C A) (sL - tL) := by
    intro a
    rw [LinearMap.sub_apply, sub_eq_zero]
    exact hinv a
  have hex' := Module.Flat.lTensor_exact C' hex
  have e1 : ∀ x : C' ⊗[C] A, (LinearMap.lTensor C' (sL - tL)) x =
      algebraMap (C' ⊗[C] A) (C' ⊗[C] B) x - t' t C' (t_comp_algebraMap hinv) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]; abel
    | tmul c a => simp [LinearMap.lTensor_tmul, hsL, htL]
  have e2 : Set.range (LinearMap.lTensor C' (Algebra.linearMap C A)) =
      Set.range (algebraMap C' (C' ⊗[C] A)) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      induction y using TensorProduct.induction_on with
      | zero => exact ⟨0, by simp⟩
      | add y z hy hz =>
        obtain ⟨c₁, h₁⟩ := hy
        obtain ⟨c₂, h₂⟩ := hz
        exact ⟨c₁ + c₂, by rw [map_add, h₁, h₂, map_add]⟩
      | tmul c' c =>
        refine ⟨c • c', ?_⟩
        rw [LinearMap.lTensor_tmul, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one c,
          ← TensorProduct.smul_tmul, algebraMap_left_apply]
    · rintro ⟨c', rfl⟩
      refine ⟨c' ⊗ₜ[C] 1, ?_⟩
      rw [LinearMap.lTensor_tmul, Algebra.linearMap_apply, map_one, algebraMap_left_apply]
  rw [← sub_eq_zero, ← e1, ← e2]
  exact hex' a'

omit [Algebra A B] [Algebra C B] [IsScalarTower C A B] in
private theorem one_tmul_algebraMap (c : C) :
    (1 : C') ⊗ₜ[C] algebraMap C A c = algebraMap C' (C' ⊗[C] A) (algebraMap C C' c) := by
  rw [← IsScalarTower.algebraMap_apply C C' (C' ⊗[C] A) c,
    ← (Algebra.TensorProduct.includeRight (R := C) (A := C') (B := A)).commutes c]
  rfl

private theorem rel_primed_iff (ht : t.comp (algebraMap C A) = algebraMap C B) {T : Type u}
  [CommRing T]
    (x y : C' ⊗[C] A →+* T) :
    Rel (algebraMap (C' ⊗[C] A) (C' ⊗[C] B)) (t' t C' ht) T x y ↔
      x.comp (algebraMap C' (C' ⊗[C] A)) = y.comp (algebraMap C' (C' ⊗[C] A)) ∧
      Rel (algebraMap A B) t T
        (x.comp (Algebra.TensorProduct.includeRight (R := C) (A := C') (B := A)).toRingHom)
        (y.comp (Algebra.TensorProduct.includeRight (R := C) (A := C') (B := A)).toRingHom) := by
  constructor
  · rintro ⟨φ', rfl, rfl⟩
    refine ⟨?_, φ'.comp (Algebra.TensorProduct.includeRight (R := C) (A := C') (B := B)).toRingHom,
      ?_, ?_⟩
    · apply RingHom.ext
      intro c
      simp only [RingHom.comp_apply]
      rw [t'_algebraMap, ← IsScalarTower.algebraMap_apply]
    · rw [RingHom.comp_assoc, includeRight_comp_s, ← RingHom.comp_assoc]
    · rw [RingHom.comp_assoc, includeRight_comp_t, ← RingHom.comp_assoc]
  · rintro ⟨hχ, φ, hφs, hφt⟩
    have hcompat : φ.comp (algebraMap C B) = (x.comp (algebraMap C' (C' ⊗[C] A))).comp (algebraMap
      C C') := by
      apply RingHom.ext
      intro c
      have := RingHom.congr_fun hφs (algebraMap C A c)
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        Algebra.TensorProduct.includeRight_apply] at this ⊢
      rw [← one_tmul_algebraMap, ← this, IsScalarTower.algebraMap_apply C A B c]
    refine ⟨liftPair C' (x.comp (algebraMap C' (C' ⊗[C] A))) φ hcompat, ?_, ?_⟩
    · apply ringHom_ext_tmul
      intro c a
      have h1 := RingHom.congr_fun hφs a
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        Algebra.TensorProduct.includeRight_apply] at h1
      rw [RingHom.comp_apply, algebraMap_primed_tmul, liftPair_tmul, h1, RingHom.comp_apply,
        ← map_mul, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
          RingHom.id_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    · apply ringHom_ext_tmul
      intro c a
      have h1 := RingHom.congr_fun hφt a
      have h2 := RingHom.congr_fun hχ c
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        Algebra.TensorProduct.includeRight_apply] at h1 h2
      rw [RingHom.comp_apply, t'_tmul, liftPair_tmul, h1, RingHom.comp_apply, h2,
        ← map_mul, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
          RingHom.id_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

private theorem L7_hequiv (ht : t.comp (algebraMap C A) = algebraMap C B)
    (hequiv : ∀ (T : Type u) [CommRing T], _root_.Equivalence (Rel (algebraMap A B) t T))
    (T : Type u) [CommRing T] :
    _root_.Equivalence (Rel (algebraMap (C' ⊗[C] A) (C' ⊗[C] B)) (t' t C' ht) T) where
  refl x := (rel_primed_iff t C' ht x x).mpr ⟨rfl, (hequiv T).refl _⟩
  symm h := by
    rw [rel_primed_iff] at h ⊢
    exact ⟨h.1.symm, (hequiv T).symm h.2⟩
  trans h₁ h₂ := by
    rw [rel_primed_iff] at h₁ h₂ ⊢
    exact ⟨h₁.1.trans h₂.1, (hequiv T).trans h₁.2 h₂.2⟩

end L7
open FiniteLocallyFreeQuotient.QuotFLF.Tgt FiniteLocallyFreeQuotient.QuotFLF.L1
  FiniteLocallyFreeQuotient.QuotFLF.L8 FiniteLocallyFreeQuotient.QuotFLF.L7

end QuotFLF
open FiniteLocallyFreeQuotient.QuotFLF.Tgt FiniteLocallyFreeQuotient.QuotFLF.L1
  FiniteLocallyFreeQuotient.QuotFLF.L8 FiniteLocallyFreeQuotient.QuotFLF.L7
    FiniteLocallyFreeQuotient.QuotFLF

namespace QuotFLF

section L4

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra C A]
  {t : A →+* B}

omit [Algebra A B] in
private theorem L4a_comap_surjective [Algebra.IsIntegral C A] (hinj : Function.Injective
  (algebraMap C A)) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap C A)) := by
  have : FaithfulSMul C A := (faithfulSMul_iff_algebraMap_injective C A).mpr hinj
  exact Algebra.IsIntegral.comap_surjective C A

section antipode

variable (hgen : (algebraMap A B).range ⊔ t.range = ⊤)
  (hequiv : ∀ (T : Type u) [CommRing T], _root_.Equivalence (Rel (algebraMap A B) t T))

include hgen hequiv in

private theorem exists_antipodeAlgEquiv : ∃ ι : B ≃ₐ[A] Tgt t,
    (∀ a, ι (t a) = Tgt.of t (algebraMap A B a)) ∧
    (∀ a, ι (algebraMap A B a) = Tgt.of t (t a)) := by
  obtain ⟨ι, hιs, hιt⟩ := exists_antipode hequiv
  have hιι : ι.comp ι = RingHom.id B :=
    hom_ext hgen (by rw [RingHom.comp_assoc, hιs, hιt, RingHom.id_comp])
      (by rw [RingHom.comp_assoc, hιt, hιs, RingHom.id_comp])
  have hinv : Function.Involutive ι := fun b => RingHom.congr_fun hιι b
  let e : B ≃+* Tgt t := (RingEquiv.ofBijective ι hinv.bijective).trans (Tgt.of t)
  refine ⟨AlgEquiv.ofRingEquiv (f := e) (fun a => ?_), fun a => ?_, fun a => ?_⟩
  · change Tgt.of t (ι (algebraMap A B a)) = algebraMap A (Tgt t) a
    rw [Tgt.algebraMap_apply]
    exact congrArg _ (RingHom.congr_fun hιs a)
  · change Tgt.of t (ι (t a)) = _
    exact congrArg _ (RingHom.congr_fun hιt a)
  · change Tgt.of t (ι (algebraMap A B a)) = _
    exact congrArg _ (RingHom.congr_fun hιs a)

omit [Algebra A B] in

private def counitTgt (e : B →+* A) (he : e.comp t = RingHom.id A) : Tgt t →ₐ[A] A :=
  { e.comp (Tgt.of t).symm.toRingHom with
    commutes' := fun a => by
      change e ((Tgt.of t).symm (algebraMap A (Tgt t) a)) = a
      rw [Tgt.algebraMap_apply]
      exact RingHom.congr_fun he a }

omit [Algebra A B] in
private theorem counitTgt_of (e : B →+* A) (he : e.comp t = RingHom.id A) (b : B) :
    counitTgt e he (Tgt.of t b) = e b := rfl

end antipode
open FiniteLocallyFreeQuotient.QuotFLF.Tgt FiniteLocallyFreeQuotient.QuotFLF.L1
  FiniteLocallyFreeQuotient.QuotFLF.L8 FiniteLocallyFreeQuotient.QuotFLF.L7
    FiniteLocallyFreeQuotient.QuotFLF

section norm

open L1

omit [Algebra A B] in

private theorem comap_comap_includeRight_eq (S : Type u) [CommRing S] [Algebra A S] (q : Ideal A)
  [q.IsMaximal]
    (𝔐 : Ideal ((A ⧸ q) ⊗[A] S)) (h𝔐 : 𝔐 ≠ ⊤) :
    (𝔐.comap ((Algebra.TensorProduct.includeRight : S →ₐ[A] (A ⧸ q) ⊗[A] S) : S →+* (A ⧸ q) ⊗[A]
      S)).comap
      (algebraMap A S) = q := by
  letI : Field (A ⧸ q) := Ideal.Quotient.field q
  rw [Ideal.comap_comap, AlgHom.comp_algebraMap,
    IsScalarTower.algebraMap_eq A (A ⧸ q) ((A ⧸ q) ⊗[A] S), ← Ideal.comap_comap]
  have hbot : 𝔐.comap (algebraMap (A ⧸ q) ((A ⧸ q) ⊗[A] S)) = ⊥ := by
    rcases Ideal.eq_bot_or_top (𝔐.comap (algebraMap (A ⧸ q) ((A ⧸ q) ⊗[A] S))) with h | h
    · exact h
    · exact absurd h (Ideal.comap_ne_top _ h𝔐)
  rw [hbot, ← RingHom.ker_eq_comap_bot, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]

omit [Algebra A B] in
private theorem isUnit_mulLeft_iff (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (x : S) :
    IsUnit (LinearMap.mulLeft R x) ↔ IsUnit x := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := (Module.End.isUnit_iff _).mp h |>.2 1
    exact isUnit_iff_exists_inv.mpr ⟨y, by simpa using hy⟩
  · intro h
    have : Algebra.lmul R S x = LinearMap.mulLeft R x := rfl
    rw [← this]
    exact h.map _

omit [Algebra A B] in

private theorem coeff_zero_charpoly_notMem_iff (S : Type u) [CommRing S] [Algebra A S]
  [Module.Finite A S]
    [Module.Projective A S] (r : ℕ) (hr : ∀ p, Module.rankAtStalk (R := A) S p = r) (b : S)
    (q : Ideal A) [q.IsMaximal] :
    (charpoly A S r hr b).coeff 0 ∉ q ↔ IsUnit ((1 : A ⧸ q) ⊗ₜ[A] b : (A ⧸ q) ⊗[A] S) := by
  letI : Field (A ⧸ q) := Ideal.Quotient.field q
  have hrκ : ∀ p, Module.rankAtStalk (R := A ⧸ q) ((A ⧸ q) ⊗[A] S) p = r := fun p => by
    rw [L1_rankAtStalk_baseChange]; exact hr _
  have h1 := L1_map_baseChange A S r hr (A ⧸ q) hrκ b
  have h2 := L1_eq_linearMap_charpoly (A ⧸ q) ((A ⧸ q) ⊗[A] S) r hrκ ((1 : A ⧸ q) ⊗ₜ[A] b)
  have h3 := LinearMap.det_eq_sign_charpoly_coeff (LinearMap.mulLeft (A ⧸ q) ((1 : A ⧸ q) ⊗ₜ[A] b))
  have hc : algebraMap A (A ⧸ q) ((charpoly A S r hr b).coeff 0) =
      (LinearMap.charpoly (LinearMap.mulLeft (A ⧸ q) ((1 : A ⧸ q) ⊗ₜ[A] b))).coeff 0 := by
    rw [← Polynomial.coeff_map, h1, h2]
  rw [← isUnit_mulLeft_iff (A ⧸ q), LinearMap.isUnit_iff_isUnit_det, h3, IsUnit.mul_iff,
    and_iff_right ((isUnit_one.neg).pow _), isUnit_iff_ne_zero, ← hc, Ideal.Quotient.algebraMap_eq,
    Ne, Ideal.Quotient.eq_zero_iff_mem]

end norm
open FiniteLocallyFreeQuotient.QuotFLF.Tgt FiniteLocallyFreeQuotient.QuotFLF.L1
  FiniteLocallyFreeQuotient.QuotFLF.L8 FiniteLocallyFreeQuotient.QuotFLF.L7
    FiniteLocallyFreeQuotient.QuotFLF

section L4b

variable [Module.Finite A B] [Module.Projective A B]
  [Module.Finite A (Tgt t)] [Module.Projective A (Tgt t)]
  (hgen : (algebraMap A B).range ⊔ t.range = ⊤)
  (hequiv : ∀ (T : Type u) [CommRing T], _root_.Equivalence (Rel (algebraMap A B) t T))
  (hinv : ∀ a : A, algebraMap A B a = t a ↔ a ∈ Set.range (algebraMap C A))
  (r : ℕ) (hr : ∀ p, Module.rankAtStalk (R := A) B p = r)

include hgen hequiv hinv hr in

private theorem L4b_exists_prime_of_comap_eq_of_isMaximal (q q' : Ideal A) [hq : q.IsMaximal] [hq' :
  q'.IsMaximal]
    (h : q.comap (algebraMap C A) = q'.comap (algebraMap C A)) :
    ∃ 𝔯 : Ideal B, 𝔯.IsPrime ∧ 𝔯.comap (algebraMap A B) = q ∧ 𝔯.comap t = q' := by
  classical
  by_contra hcon
  push Not at hcon

  have hfin : ((PrimeSpectrum.comap (algebraMap A B)) ⁻¹' {⟨q, hq.isPrime⟩}).Finite :=
    Algebra.QuasiFinite.finite_comap_preimage_singleton ⟨q, hq.isPrime⟩
  set K : Finset (Ideal A) := (hfin.image fun 𝔯 => 𝔯.asIdeal.comap t).toFinset with hK
  have hKmem : ∀ I, I ∈ K ↔ ∃ 𝔯 : PrimeSpectrum B, 𝔯.asIdeal.comap (algebraMap A B) = q ∧
      𝔯.asIdeal.comap t = I := fun I => by
    simp only [hK, Set.Finite.mem_toFinset, Set.mem_image, Set.mem_preimage, Set.mem_singleton_iff,
      PrimeSpectrum.ext_iff, PrimeSpectrum.comap_asIdeal]
  have hKprime : ∀ I ∈ K, I.IsPrime := fun I hI => by
    obtain ⟨𝔯, -, rfl⟩ := (hKmem I).1 hI
    exact Ideal.comap_isPrime t 𝔯.asIdeal

  have havoid : ¬ ((q' : Set A) ⊆ ⋃ I ∈ (↑K : Set (Ideal A)), (I : Set A)) := by
    rw [Ideal.subset_union_prime q' q' (fun I hI _ _ => hKprime I hI)]
    rintro ⟨I, hI, hle⟩
    obtain ⟨𝔯, h𝔯s, rfl⟩ := (hKmem I).1 hI
    have hne : 𝔯.asIdeal.comap t ≠ ⊤ := Ideal.comap_ne_top t 𝔯.isPrime.ne_top
    exact hcon 𝔯.asIdeal 𝔯.isPrime h𝔯s (hq'.eq_of_le hne hle).symm
  obtain ⟨f, hfq', hfK⟩ := Set.not_subset.mp havoid
  simp only [Set.mem_iUnion, SetLike.mem_coe, not_exists] at hfK

  set g : A := (charpoly A B r hr (t f)).coeff 0 with hg

  have hgq : g ∉ q := by
    rw [hg, coeff_zero_charpoly_notMem_iff]
    by_contra hu
    obtain ⟨𝔐, h𝔐max, hf𝔐⟩ := exists_max_ideal_of_mem_nonunits hu
    set 𝔯 : Ideal B := 𝔐.comap ((Algebra.TensorProduct.includeRight : B →ₐ[A] (A ⧸ q) ⊗[A] B) :
      B →+* (A ⧸ q) ⊗[A] B) with h𝔯
    have h𝔯prime : 𝔯.IsPrime := Ideal.comap_isPrime _ 𝔐
    have h𝔯s : 𝔯.comap (algebraMap A B) = q :=
      comap_comap_includeRight_eq B q 𝔐 h𝔐max.ne_top
    have htf : t f ∈ 𝔯 := by
      change Algebra.TensorProduct.includeRight (t f) ∈ 𝔐
      exact hf𝔐
    have hmem : 𝔯.comap t ∈ K := (hKmem _).2 ⟨⟨𝔯, h𝔯prime⟩, h𝔯s, rfl⟩
    exact hfK _ hmem htf

  have hgq' : g ∈ q' := by
    obtain ⟨ι, hιt, hιs⟩ := exists_antipodeAlgEquiv (t := t) hgen hequiv
    have hrT : ∀ p, Module.rankAtStalk (R := A) (Tgt t) p = r := fun p => by
      rw [← Module.rankAtStalk_eq_of_equiv ι.toLinearEquiv]; exact hr p
    have key := L1_algEquiv A B r hr (Tgt t) hrT ι (t f)
    rw [hιt] at key

    by_contra hn
    rw [hg, ← key, coeff_zero_charpoly_notMem_iff] at hn
    obtain ⟨e, hes, het⟩ := exists_counit hequiv
    letI : Field (A ⧸ q') := Ideal.Quotient.field q'
    let lam : (A ⧸ q') ⊗[A] Tgt t →ₐ[A] A ⧸ q' :=
      Algebra.TensorProduct.lift (AlgHom.id A (A ⧸ q'))
        ((Ideal.Quotient.mkₐ A q').comp (counitTgt e het)) (fun _ _ => .all _ _)
    have hlam : lam ((1 : A ⧸ q') ⊗ₜ[A] Tgt.of t (algebraMap A B f)) = 0 := by
      simp only [lam, Algebra.TensorProduct.lift_tmul, map_one, one_mul, AlgHom.comp_apply,
        counitTgt_of, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      have : e (algebraMap A B f) = f := RingHom.congr_fun hes f
      rw [this]; exact hfq'
    have := hn.map lam
    rw [hlam] at this
    exact not_isUnit_zero this

  have hginv : algebraMap A B g = t g := coeff_charpoly_invariant (t := t) hgen hequiv r hr f 0
  obtain ⟨c, hc⟩ := (hinv g).1 hginv
  have hcq' : c ∈ q'.comap (algebraMap C A) := by rw [Ideal.mem_comap, hc]; exact hgq'
  rw [← h, Ideal.mem_comap, hc] at hcq'
  exact hgq hcq'

include hgen hequiv hinv hr in

private theorem L4c_setOf_isMaximal_finite [IsLocalRing C] [Algebra.IsIntegral C A] :
    {q : Ideal A | q.IsMaximal}.Finite := by
  classical
  rcases subsingleton_or_nontrivial A with hA | hA
  · have : {q : Ideal A | q.IsMaximal} = ∅ :=
      Set.eq_empty_of_forall_notMem fun q hq => hq.ne_top (Subsingleton.elim _ _)
    rw [this]; exact Set.finite_empty
  obtain ⟨q₀, hq₀⟩ := Ideal.exists_maximal A
  have hfin : ((PrimeSpectrum.comap (algebraMap A B)) ⁻¹' {⟨q₀, hq₀.isPrime⟩}).Finite :=
    Algebra.QuasiFinite.finite_comap_preimage_singleton ⟨q₀, hq₀.isPrime⟩
  refine (hfin.image fun 𝔯 => 𝔯.asIdeal.comap t).subset fun q hq => ?_
  haveI : q.IsMaximal := hq
  have hcontract : ∀ (I : Ideal A) [I.IsMaximal],
    I.comap (algebraMap C A) = IsLocalRing.maximalIdeal C :=
    fun I _ => IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := C) I)
  obtain ⟨𝔯, h𝔯p, h𝔯s,
    h𝔯t⟩ := L4b_exists_prime_of_comap_eq_of_isMaximal (t := t) hgen hequiv hinv r hr
    q₀ q ((hcontract q₀).trans (hcontract q).symm)
  refine ⟨⟨𝔯, h𝔯p⟩, ?_, h𝔯t⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff, PrimeSpectrum.ext_iff,
    PrimeSpectrum.comap_asIdeal]
  exact h𝔯s

end L4b
open FiniteLocallyFreeQuotient.QuotFLF.Tgt FiniteLocallyFreeQuotient.QuotFLF.L1
  FiniteLocallyFreeQuotient.QuotFLF.L8 FiniteLocallyFreeQuotient.QuotFLF.L7
    FiniteLocallyFreeQuotient.QuotFLF

end L4
open FiniteLocallyFreeQuotient.QuotFLF.Tgt FiniteLocallyFreeQuotient.QuotFLF.L1
  FiniteLocallyFreeQuotient.QuotFLF.L8 FiniteLocallyFreeQuotient.QuotFLF.L7
    FiniteLocallyFreeQuotient.QuotFLF

end QuotFLF
open FiniteLocallyFreeQuotient.QuotFLF.Tgt FiniteLocallyFreeQuotient.QuotFLF.L1
  FiniteLocallyFreeQuotient.QuotFLF.L8 FiniteLocallyFreeQuotient.QuotFLF.L7
    FiniteLocallyFreeQuotient.QuotFLF

namespace QuotFLF

section L5

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra C A]
  {t : A →+* B}

private theorem span_range_t_eq_top (hgen : (algebraMap A B).range ⊔ t.range = ⊤) :
    Submodule.span A (Set.range t) = (⊤ : Submodule A B) := by
  set N : Submodule A B := Submodule.span A (Set.range t) with hN
  have hmul : ∀ x ∈ N, ∀ y ∈ N, x * y ∈ N := by
    intro x hx y hy
    have hle : N * N ≤ N := by
      rw [hN, Submodule.span_mul_span, Submodule.span_le]
      rintro _ ⟨_, ⟨a, rfl⟩, _, ⟨a', rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨a * a', by simp⟩
    exact hle (Submodule.mul_mem_mul hx hy)
  let S : Subring B :=
    { carrier := N
      mul_mem' := fun {x y} hx hy => hmul x hx y hy
      one_mem' := Submodule.subset_span ⟨1, map_one t⟩
      add_mem' := fun {x y} hx hy => add_mem hx hy
      zero_mem' := zero_mem N
      neg_mem' := fun {x} hx => neg_mem hx }
  have hS : (⊤ : Subring B) ≤ S := by
    rw [← hgen, sup_le_iff]
    constructor
    · rintro _ ⟨a, rfl⟩
      change algebraMap A B a ∈ N
      rw [Algebra.algebraMap_eq_smul_one, ← map_one t]
      exact N.smul_mem a (Submodule.subset_span ⟨1, rfl⟩)
    · rintro _ ⟨a, rfl⟩
      exact Submodule.subset_span ⟨a, rfl⟩
  rw [eq_top_iff]
  intro b _
  exact hS (Subring.mem_top b)

section fibre

variable (t) (𝔪 : Ideal A)

private abbrev Fib : Type u := (A ⧸ 𝔪) ⊗[A] B

omit [Algebra C A] in
private theorem t_algebraMap_eq [Algebra C A]
    (hinv : ∀ a : A, algebraMap A B a = t a ↔ a ∈ Set.range (algebraMap C A)) (c : C) :
    t (algebraMap C A c) = algebraMap A B (algebraMap C A c) :=
  ((hinv _).2 ⟨c, rfl⟩).symm

private noncomputable def Tfib (hinv : ∀ a : A,
  algebraMap A B a = t a ↔ a ∈ Set.range (algebraMap C A)) :
    A →ₗ[C] Fib 𝔪 (B := B) where
  toFun a := (1 : A ⧸ 𝔪) ⊗ₜ[A] t a
  map_add' a b := by simp [tmul_add]
  map_smul' c a := by
    simp only [RingHom.id_apply]
    rw [Algebra.smul_def, map_mul, t_algebraMap_eq t hinv c, ← Algebra.smul_def, tmul_smul,
      IsScalarTower.algebraMap_smul]

private theorem Tfib_apply (hinv : ∀ a : A, algebraMap A B a = t a ↔ a ∈ Set.range (algebraMap C A))
    (a : A) : Tfib t 𝔪 hinv a = (1 : A ⧸ 𝔪) ⊗ₜ[A] t a := rfl

variable (hinv : ∀ a : A, algebraMap A B a = t a ↔ a ∈ Set.range (algebraMap C A))

private theorem span_range_Tfib (hgen : (algebraMap A B).range ⊔ t.range = ⊤) :
    Submodule.span (A ⧸ 𝔪) (Set.range (Tfib t 𝔪 hinv)) = ⊤ := by
  have h := congrArg (Submodule.baseChange (A ⧸ 𝔪)) (span_range_t_eq_top (t := t) hgen)
  rw [Submodule.baseChange_top, Submodule.baseChange_span, ← Set.range_comp] at h
  exact h

private theorem smul_Tfib_eq_zero {c : C} (hc : algebraMap C A c ∈ 𝔪) (a : A) : c • Tfib t 𝔪 hinv a
  = 0 :=
  by
  rw [Tfib_apply, ← IsScalarTower.algebraMap_smul (A ⧸ 𝔪) c,
    IsScalarTower.algebraMap_apply C A (A ⧸ 𝔪),
    Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr hc, zero_smul]

variable [Module.Finite A B] [Module.Projective A B] (r : ℕ)
  (hr : ∀ p, Module.rankAtStalk (R := A) B p = r)

include hr in
omit [Algebra C A] in

private theorem finrank_Fib [𝔪.IsMaximal] : Module.finrank (A ⧸ 𝔪) (Fib 𝔪 (B := B)) = r := by
  letI : Field (A ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  let p₀ : PrimeSpectrum (A ⧸ 𝔪) := ⟨⊥, Ideal.isPrime_bot⟩
  have h1 := congrFun (Module.rankAtStalk_eq_finrank_of_free (R := A ⧸ 𝔪) (M := Fib 𝔪 (B := B))) p₀
  simp only [Pi.natCast_apply, Nat.cast_id] at h1
  rw [← h1, Module.rankAtStalk_baseChange, hr]

end fibre
open FiniteLocallyFreeQuotient.QuotFLF.Tgt FiniteLocallyFreeQuotient.QuotFLF.L1
  FiniteLocallyFreeQuotient.QuotFLF.L8 FiniteLocallyFreeQuotient.QuotFLF.L7
    FiniteLocallyFreeQuotient.QuotFLF

section select

variable [IsLocalRing C] [Module.Finite A B] [Module.Projective A B]
  (hgen : (algebraMap A B).range ⊔ t.range = ⊤)
  (hinv : ∀ a : A, algebraMap A B a = t a ↔ a ∈ Set.range (algebraMap C A))
  (r : ℕ) (hr : ∀ p, Module.rankAtStalk (R := A) B p = r)

omit [IsLocalRing C] [Module.Finite A B] [Module.Projective A B] in

private def ofResidue (I : Ideal C) {W : Type u} [AddCommGroup W] [Module C W]
    [Module (C ⧸ I) W] [IsScalarTower C (C ⧸ I) W] (N : Submodule C W) : Submodule (C ⧸ I) W where
  carrier := N
  add_mem' := N.add_mem
  zero_mem' := N.zero_mem
  smul_mem' r w hw := by
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective r
    rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
    exact N.smul_mem c hw

omit [IsLocalRing C] [Module.Finite A B] [Module.Projective A B] in
private theorem mem_ofResidue (I : Ideal C) {W : Type u} [AddCommGroup W] [Module C W]
    [Module (C ⧸ I) W] [IsScalarTower C (C ⧸ I) W] (N : Submodule C W) (w : W) :
    w ∈ ofResidue I N ↔ w ∈ N := Iff.rfl

omit [Module.Finite A B] [Module.Projective A B] in

private theorem exists_forall_Tfib_notMem [Infinite (IsLocalRing.ResidueField C)]
    (ℳ : Finset (Ideal A)) (hℳ : ∀ 𝔪 ∈ ℳ, (IsLocalRing.maximalIdeal C).map (algebraMap C A) ≤ 𝔪)
    (V : ∀ 𝔪 : Ideal A, Submodule (A ⧸ 𝔪) (Fib 𝔪 (B := B)))
    (hV : ∀ 𝔪 ∈ ℳ, ∃ a : A, Tfib t 𝔪 hinv a ∉ V 𝔪) :
    ∃ a : A, ∀ 𝔪 ∈ ℳ, Tfib t 𝔪 hinv a ∉ V 𝔪 := by
  classical
  letI : Field (C ⧸ IsLocalRing.maximalIdeal C) := Ideal.Quotient.field _
  haveI : Infinite (C ⧸ IsLocalRing.maximalIdeal C) := ‹Infinite (IsLocalRing.ResidueField C)›

  let U : Ideal A → Submodule C A := fun 𝔪 => ((V 𝔪).restrictScalars C).comap (Tfib t 𝔪 hinv)
  let W : Type u := A ⧸ (IsLocalRing.maximalIdeal C • (⊤ : Submodule C A))
  let p : Ideal A → Submodule (C ⧸ IsLocalRing.maximalIdeal C) W := fun 𝔪 =>
    ofResidue (IsLocalRing.maximalIdeal C)
      ((U 𝔪).map (IsLocalRing.maximalIdeal C • (⊤ : Submodule C A)).mkQ)
  have hU𝔫 : ∀ 𝔪 ∈ ℳ, IsLocalRing.maximalIdeal C • (⊤ : Submodule C A) ≤ U 𝔪 := by
    intro 𝔪 h𝔪
    rw [Submodule.smul_le]
    intro c hc a _
    change Tfib t 𝔪 hinv (c • a) ∈ V 𝔪
    rw [map_smul, smul_Tfib_eq_zero t 𝔪 hinv (hℳ 𝔪 h𝔪 (Ideal.mem_map_of_mem _ hc))]
    exact zero_mem _
  have hp : ∀ 𝔪 ∈ ℳ, p 𝔪 ≠ ⊤ := by
    intro 𝔪 h𝔪 htop
    obtain ⟨a, ha⟩ := hV 𝔪 h𝔪
    apply ha
    have : Submodule.Quotient.mk a ∈ p 𝔪 := by rw [htop]; trivial
    rw [mem_ofResidue] at this
    have h2 : a ∈ ((U 𝔪).map (IsLocalRing.maximalIdeal C • (⊤ : Submodule C A)).mkQ).comap
        (IsLocalRing.maximalIdeal C • (⊤ : Submodule C A)).mkQ := this
    rw [Submodule.comap_map_mkQ, sup_eq_right.mpr (hU𝔫 𝔪 h𝔪)] at h2
    exact h2

  let ι := {𝔪 // 𝔪 ∈ ℳ}
  have hcard : (Finset.univ : Finset ι).card < ENat.card (C ⧸ IsLocalRing.maximalIdeal C) := by
    rw [ENat.card_eq_top_of_infinite]
    exact ENat.coe_lt_top _
  have hss := Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt (Finset.univ : Finset ι)
    (fun i => p i.1) (fun i => hp i.1 i.2) hcard
  obtain ⟨w, -, hw⟩ := Set.exists_of_ssubset hss
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective (IsLocalRing.maximalIdeal C • (⊤ : Submodule
    C A)) w
  refine ⟨a, fun 𝔪 h𝔪 hmem => hw ?_⟩
  simp only [Set.mem_iUnion, Finset.mem_univ, SetLike.mem_coe, exists_prop, true_and]
  refine ⟨⟨𝔪, h𝔪⟩, ?_⟩
  rw [mem_ofResidue]
  exact Submodule.mem_map_of_mem (show a ∈ U 𝔪 from hmem)

include hgen hr in

private theorem exists_forall_linearIndependent [Infinite (IsLocalRing.ResidueField C)]
    (ℳ : Finset (Ideal A)) (hℳmax : ∀ 𝔪 ∈ ℳ, 𝔪.IsMaximal)
    (hℳ : ∀ 𝔪 ∈ ℳ, (IsLocalRing.maximalIdeal C).map (algebraMap C A) ≤ 𝔪)
    (m : ℕ) (hm : m ≤ r) :
    ∃ x : Fin m → A, ∀ 𝔪 ∈ ℳ, LinearIndependent (A ⧸ 𝔪) (fun j => Tfib t 𝔪 hinv (x j)) := by
  induction m with
  | zero => exact ⟨Fin.elim0, fun 𝔪 _ => linearIndependent_empty_type⟩
  | succ m ih =>
    obtain ⟨x, hx⟩ := ih (Nat.le_of_succ_le hm)

    let V : ∀ 𝔪 : Ideal A, Submodule (A ⧸ 𝔪) (Fib 𝔪 (B := B)) := fun 𝔪 =>
      Submodule.span (A ⧸ 𝔪) (Set.range fun j => Tfib t 𝔪 hinv (x j))
    have hV : ∀ 𝔪 ∈ ℳ, ∃ a : A, Tfib t 𝔪 hinv a ∉ V 𝔪 := by
      intro 𝔪 h𝔪
      haveI := hℳmax 𝔪 h𝔪
      letI : Field (A ⧸ 𝔪) := Ideal.Quotient.field 𝔪
      by_contra hall
      push Not at hall

      have hle : (⊤ : Submodule (A ⧸ 𝔪) (Fib 𝔪 (B := B))) ≤ V 𝔪 := by
        rw [← span_range_Tfib t 𝔪 hinv hgen, Submodule.span_le]
        rintro _ ⟨a, rfl⟩
        exact hall a
      have h1 : Module.finrank (A ⧸ 𝔪) (Fib 𝔪 (B := B)) ≤ m := by
        rw [← finrank_top, ← eq_top_iff.mpr hle]
        exact (finrank_range_le_card _).trans (by simp)
      rw [finrank_Fib 𝔪 r hr] at h1
      omega
    obtain ⟨a, ha⟩ := exists_forall_Tfib_notMem (t := t) hinv ℳ hℳ V hV
    refine ⟨(Fin.cons a x : Fin (m + 1) → A), fun 𝔪 h𝔪 => ?_⟩
    haveI := hℳmax 𝔪 h𝔪
    letI : Field (A ⧸ 𝔪) := Ideal.Quotient.field 𝔪
    have : (fun j => Tfib t 𝔪 hinv ((Fin.cons a x : Fin (m + 1) → A) j)) =
        Fin.cons (Tfib t 𝔪 hinv a) (fun j => Tfib t 𝔪 hinv (x j)) := by
      ext j; refine Fin.cases ?_ (fun i => ?_) j <;> simp
    rw [this, linearIndependent_finCons]
    exact ⟨hx 𝔪 h𝔪, ha 𝔪 h𝔪⟩

end select
open FiniteLocallyFreeQuotient.QuotFLF.Tgt FiniteLocallyFreeQuotient.QuotFLF.L1
  FiniteLocallyFreeQuotient.QuotFLF.L8 FiniteLocallyFreeQuotient.QuotFLF.L7
    FiniteLocallyFreeQuotient.QuotFLF

section heart

variable [IsLocalRing C] [Module.Finite A B] [Module.Projective A B]
  (hinv : ∀ a : A, algebraMap A B a = t a ↔ a ∈ Set.range (algebraMap C A))

omit [IsLocalRing C] [Module.Projective A B] in

private theorem range_linearCombination_eq_top (ℳ : Finset (Ideal A))
    (hall : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → 𝔪 ∈ ℳ) {r : ℕ} (x : Fin r → A)
    (hx : ∀ 𝔪 ∈ ℳ, Submodule.span (A ⧸ 𝔪) (Set.range fun j => Tfib t 𝔪 hinv (x j)) = ⊤) :
    LinearMap.range (Fintype.linearCombination A (fun j => t (x j))) = ⊤ := by
  classical
  set N : Submodule A B := LinearMap.range (Fintype.linearCombination A (fun j => t (x j))) with hN
  have hNspan : N = Submodule.span A (Set.range fun j => t (x j)) :=
    Fintype.range_linearCombination A _

  have step1 : ∀ 𝔪 ∈ ℳ, (⊤ : Submodule A B) ≤ N ⊔ 𝔪 • ⊤ := by
    intro 𝔪 h𝔪 b _
    have hb : (1 : A ⧸ 𝔪) ⊗ₜ[A] b ∈
        (Submodule.span (A ⧸ 𝔪) (Set.range fun j => Tfib t 𝔪 hinv (x j))).restrictScalars A := by
      rw [hx 𝔪 h𝔪]; trivial
    rw [Submodule.restrictScalars_span A (A ⧸ 𝔪) Ideal.Quotient.mk_surjective] at hb
    have hb' := Submodule.mem_map_of_mem (f := (TensorProduct.quotTensorEquivQuotSMul B
      𝔪).toLinearMap) hb
    rw [Submodule.map_span, ← Set.range_comp] at hb'
    simp only [LinearEquiv.coe_coe, Function.comp_def, Tfib_apply,
      TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul] at hb'

    have : Submodule.Quotient.mk b ∈ N.map (𝔪 • (⊤ : Submodule A B)).mkQ := by
      rw [hNspan, Submodule.map_span, ← Set.range_comp]
      exact hb'
    have hmem : b ∈ (N.map (𝔪 • (⊤ : Submodule A B)).mkQ).comap (𝔪 • (⊤ : Submodule A B)).mkQ :=
      this
    rwa [Submodule.comap_map_mkQ, sup_comm] at hmem

  have step2 : ∀ S : Finset (Ideal A), S ⊆ ℳ → (⊤ : Submodule A B) ≤ N ⊔ (S.prod id) • ⊤ := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro
      rw [Finset.prod_empty, Ideal.one_eq_top, Submodule.top_smul]
      exact le_sup_right
    | insert 𝔪 S h𝔪S ih =>
      intro hS
      rw [Finset.prod_insert h𝔪S, id]
      have h1 := step1 𝔪 (hS (Finset.mem_insert_self _ _))
      have h2 := ih ((Finset.subset_insert _ _).trans hS)
      calc (⊤ : Submodule A B) ≤ N ⊔ 𝔪 • ⊤ := h1
        _ ≤ N ⊔ 𝔪 • (N ⊔ (S.prod id) • ⊤) := sup_le_sup_left (Submodule.smul_mono le_rfl h2) _
        _ = N ⊔ (𝔪 • N ⊔ (𝔪 * S.prod id) • ⊤) := by rw [Submodule.smul_sup, Submodule.mul_smul]
        _ ≤ N ⊔ (𝔪 * S.prod id) • ⊤ :=
          sup_le le_sup_left (sup_le (Submodule.smul_le_right.trans le_sup_left) le_sup_right)

  have hjac : ℳ.prod id ≤ Ideal.jacobson ⊥ := by
    apply le_sInf
    rintro J ⟨-, hJ⟩
    exact Ideal.prod_le_inf.trans (Finset.inf_le (hall J hJ))
  have hfg : (⊤ : Submodule A B).FG := Module.Finite.fg_top
  have key := Submodule.sup_eq_sup_smul_of_le_smul_of_le_jacobson hfg hjac (step2 ℳ subset_rfl)
  rwa [sup_top_eq, Submodule.bot_smul, sup_bot_eq, eq_comm] at key

omit [IsLocalRing C] [Algebra C A] in

private theorem bijective_of_surjective_of_rankAtStalk_eq {r : ℕ}
    (hr : ∀ p, Module.rankAtStalk (R := A) B p = r)
    (Φ : (Fin r → A) →ₗ[A] B) (hΦ : Function.Surjective Φ) : Function.Bijective Φ := by
  refine ⟨?_, hΦ⟩
  rcases subsingleton_or_nontrivial A with hA | hA
  · haveI : Subsingleton (Fin r → A) := inferInstance
    exact Function.injective_of_subsingleton _
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property Φ LinearMap.id hΦ
  let 𝓔 : L1.Envelope A B := ⟨r, Φ, σ, hσ⟩
  haveI := L1.finite_ker 𝓔
  haveI := L1.flat_ker 𝓔
  have hrk := Module.rankAtStalk_eq_of_equiv (L1.splitEquiv 𝓔)
  rw [Module.rankAtStalk_prod, Module.rankAtStalk_eq_finrank_of_free, Module.finrank_fin_fun] at hrk
  have h0 : Module.rankAtStalk (R := A) (LinearMap.ker Φ) = 0 := by
    funext p
    have := congrFun hrk p
    simp only [Pi.add_apply, Pi.natCast_apply, Nat.cast_id] at this
    change r = Module.rankAtStalk B p + Module.rankAtStalk (LinearMap.ker Φ) p at this
    rw [hr] at this
    simp only [Pi.zero_apply]
    omega
  rw [Module.rankAtStalk_eq_zero_iff_subsingleton] at h0
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro v hv
  have : (⟨v, hv⟩ : LinearMap.ker Φ) = 0 := Subsingleton.elim _ _
  exact congrArg Subtype.val this

variable [Module.Finite A (Tgt t)] [Module.Projective A (Tgt t)]
  (hgen : (algebraMap A B).range ⊔ t.range = ⊤)
  (hequiv : ∀ (T : Type u) [CommRing T], _root_.Equivalence (Rel (algebraMap A B) t T))
  (r : ℕ) (hr : ∀ p, Module.rankAtStalk (R := A) B p = r)

include hgen hequiv hinv hr in

private theorem L5_exists_basis_of_isLocalRing [Infinite (IsLocalRing.ResidueField C)]
    [Algebra.IsIntegral C A] :
    ∃ x : Fin r → A, Function.Bijective fun a : Fin r → A => ∑ i,
      algebraMap A B (a i) * t (x i) := by
  classical

  have hfin := L4c_setOf_isMaximal_finite (t := t) hgen hequiv hinv r hr
  set ℳ : Finset (Ideal A) := hfin.toFinset with hℳdef
  have hℳmax : ∀ 𝔪 ∈ ℳ, 𝔪.IsMaximal := fun 𝔪 h => by simpa [hℳdef] using h
  have hall : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → 𝔪 ∈ ℳ := fun 𝔪 h => by simpa [hℳdef] using h
  have hℳ : ∀ 𝔪 ∈ ℳ, (IsLocalRing.maximalIdeal C).map (algebraMap C A) ≤ 𝔪 := by
    intro 𝔪 h𝔪
    haveI := hℳmax 𝔪 h𝔪
    rw [Ideal.map_le_iff_le_comap,
      show 𝔪.comap (algebraMap C A) = 𝔪.under C from rfl,
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := C) 𝔪)]

  obtain ⟨x, hx⟩ := exists_forall_linearIndependent (t := t) hgen hinv r hr ℳ hℳmax hℳ r le_rfl
  have hspan : ∀ 𝔪 ∈ ℳ, Submodule.span (A ⧸ 𝔪) (Set.range fun j => Tfib t 𝔪 hinv (x j)) = ⊤ := by
    intro 𝔪 h𝔪
    haveI := hℳmax 𝔪 h𝔪
    letI : Field (A ⧸ 𝔪) := Ideal.Quotient.field 𝔪
    exact (hx 𝔪 h𝔪).span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, finrank_Fib 𝔪 r hr])

  refine ⟨x, ?_⟩
  have hsurj : Function.Surjective (Fintype.linearCombination A (fun j => t (x j))) :=
    LinearMap.range_eq_top.mp (range_linearCombination_eq_top (t := t) hinv ℳ hall x hspan)
  have hbij := bijective_of_surjective_of_rankAtStalk_eq (B := B) hr _ hsurj
  convert hbij using 1
  ext a
  simp [Fintype.linearCombination_apply, Algebra.smul_def]

end heart
open FiniteLocallyFreeQuotient.QuotFLF.Tgt FiniteLocallyFreeQuotient.QuotFLF.L1
  FiniteLocallyFreeQuotient.QuotFLF.L8 FiniteLocallyFreeQuotient.QuotFLF.L7
    FiniteLocallyFreeQuotient.QuotFLF

end L5
open FiniteLocallyFreeQuotient.QuotFLF.Tgt FiniteLocallyFreeQuotient.QuotFLF.L1
  FiniteLocallyFreeQuotient.QuotFLF.L8 FiniteLocallyFreeQuotient.QuotFLF.L7
    FiniteLocallyFreeQuotient.QuotFLF

end QuotFLF
open FiniteLocallyFreeQuotient.QuotFLF.Tgt FiniteLocallyFreeQuotient.QuotFLF.L1
  FiniteLocallyFreeQuotient.QuotFLF.L8 FiniteLocallyFreeQuotient.QuotFLF.L7
    FiniteLocallyFreeQuotient.QuotFLF

namespace QuotFLF

section theta

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra C A]
  [Algebra C B] [IsScalarTower C A B] (t : A →+* B)
  (hinv : ∀ a : A, algebraMap A B a = t a ↔ a ∈ Set.range (algebraMap C A))

private def tAlgHom : A →ₐ[C] B :=
  { t with
    commutes' := fun c => by
      change t (algebraMap C A c) = algebraMap C B c
      rw [IsScalarTower.algebraMap_apply C A B]
      exact ((hinv _).2 ⟨c, rfl⟩).symm }

@[scoped simp] private theorem tAlgHom_apply (a : A) : tAlgHom t hinv a = t a := rfl

private noncomputable def theta : A ⊗[C] A →ₐ[A] B :=
  Algebra.TensorProduct.lift (Algebra.ofId A B) (tAlgHom t hinv) (fun _ _ => .all _ _)

@[scoped simp] private theorem theta_tmul (a a' : A) : theta t hinv (a ⊗ₜ[C] a') = algebraMap A B a
  * t a'
  := by
  simp [theta, Algebra.ofId_apply]

private theorem isPushout_of_bijective_theta (hθ : Function.Bijective (theta t hinv)) :
    IsPushout (CommRingCat.ofHom (algebraMap C A)) (CommRingCat.ofHom (algebraMap C A))
      (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom t) := by
  let e : A ⊗[C] A ≃+* B := RingEquiv.ofBijective (theta t hinv) hθ
  have h := CommRingCat.isPushout_tensorProduct C A A

  refine (h.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e.toCommRingCatIso ?_ ?_ ?_ ?_)
  · simp
  · simp
  · ext a
    change theta t hinv (a ⊗ₜ[C] 1) = algebraMap A B a
    simp
  · ext a
    change theta t hinv (1 ⊗ₜ[C] a) = t a
    simp

end theta
open FiniteLocallyFreeQuotient.QuotFLF.Tgt FiniteLocallyFreeQuotient.QuotFLF.L1
  FiniteLocallyFreeQuotient.QuotFLF.L8 FiniteLocallyFreeQuotient.QuotFLF.L7
    FiniteLocallyFreeQuotient.QuotFLF

end QuotFLF
open FiniteLocallyFreeQuotient.QuotFLF.Tgt FiniteLocallyFreeQuotient.QuotFLF.L1
  FiniteLocallyFreeQuotient.QuotFLF.L8 FiniteLocallyFreeQuotient.QuotFLF.L7
    FiniteLocallyFreeQuotient.QuotFLF

namespace QuotFLF

section descent

variable {C : Type u} [CommRing C]

private theorem isLocalizedModule_map_eq_baseChange (P : Ideal C) [P.IsMaximal]
    {M N : Type u} [AddCommGroup M] [Module C M] [AddCommGroup N] [Module C N] (θ : M →ₗ[C] N) :
    IsLocalizedModule.map P.primeCompl (TensorProduct.mk C (Localization.AtPrime P) M 1)
      (TensorProduct.mk C (Localization.AtPrime P) N 1) θ =
      (θ.baseChange (Localization.AtPrime P)).restrictScalars C := by
  apply IsLocalizedModule.linearMap_ext P.primeCompl (TensorProduct.mk C (Localization.AtPrime P) M
    1)
    (TensorProduct.mk C (Localization.AtPrime P) N 1)
  rw [IsLocalizedModule.map_comp]
  ext m
  simp

private theorem baseChange_baseChange_bijective_iff {R : Type u} [CommRing R] [Algebra C R] (C' :
  Type u)
  [CommRing C']
    [Algebra C C'] [Algebra R C'] [IsScalarTower C R C']
    {M N : Type u} [AddCommGroup M] [Module C M] [AddCommGroup N] [Module C N] (θ : M →ₗ[C] N) :
    Function.Bijective ((θ.baseChange R).baseChange C') ↔ Function.Bijective (θ.baseChange C') := by
  let eM := TensorProduct.AlgebraTensorModule.cancelBaseChange C R C' C' M
  let eN := TensorProduct.AlgebraTensorModule.cancelBaseChange C R C' C' N
  have hcomm : (θ.baseChange C').restrictScalars C' ∘ₗ eM.toLinearMap =
      eN.toLinearMap ∘ₗ ((θ.baseChange R).baseChange C').restrictScalars C' := by
    ext m
    simp [eM, eN]
  have h1 : (θ.baseChange C' : C' ⊗[C] M → C' ⊗[C] N) ∘ eM = eN ∘ ((θ.baseChange R).baseChange C')
    := by
    funext z; exact LinearMap.congr_fun hcomm z
  constructor
  · intro h
    have : Function.Bijective ((θ.baseChange C' : C' ⊗[C] M → C' ⊗[C] N) ∘ eM) := by
      rw [h1]; exact eN.bijective.comp h
    exact (Function.Bijective.of_comp_iff _ eM.bijective).mp this
  · intro h
    have : Function.Bijective (eN ∘ ((θ.baseChange R).baseChange C')) := by
      rw [← h1]; exact h.comp eM.bijective
    exact (Function.Bijective.of_comp_iff' eN.bijective _).mp this

private theorem bijective_of_forall_exists_faithfullyFlat {M N : Type u} [AddCommGroup M] [Module C
  M]
    [AddCommGroup N] [Module C N] (θ : M →ₗ[C] N)
    (H : ∀ (P : Ideal C) [P.IsMaximal], ∃ (C' : Type u) (_ : CommRing C') (_ : Algebra C C')
      (_ : Algebra (Localization.AtPrime P) C') (_ : IsScalarTower C (Localization.AtPrime P) C')
      (_ : Module.FaithfullyFlat (Localization.AtPrime P) C'),
      Function.Bijective (θ.baseChange C')) :
    Function.Bijective θ := by
  refine bijective_of_isLocalized_maximal
    (fun P _ => Localization.AtPrime P ⊗[C] M)
    (fun P _ => TensorProduct.mk C (Localization.AtPrime P) M 1)
    (fun P _ => Localization.AtPrime P ⊗[C] N)
    (fun P _ => TensorProduct.mk C (Localization.AtPrime P) N 1) θ fun P hP => ?_
  obtain ⟨C', _, _, _, _, _, hbij⟩ := H P
  rw [isLocalizedModule_map_eq_baseChange]
  change Function.Bijective (θ.baseChange (Localization.AtPrime P))
  rw [← Module.FaithfullyFlat.lTensor_bijective_iff_bijective (R := Localization.AtPrime P) (M :=
    C'),
    ← LinearMap.baseChange_eq_ltensor, baseChange_baseChange_bijective_iff]
  exact hbij

private theorem flat_of_forall_exists_faithfullyFlat {M : Type u} [AddCommGroup M] [Module C M]
    (H : ∀ (P : Ideal C) [P.IsMaximal], ∃ (C' : Type u) (_ : CommRing C') (_ : Algebra C C')
      (_ : Algebra (Localization.AtPrime P) C') (_ : IsScalarTower C (Localization.AtPrime P) C')
      (_ : Module.FaithfullyFlat (Localization.AtPrime P) C'),
      Module.Flat C' (C' ⊗[C] M)) :
    Module.Flat C M := by
  refine Module.flat_of_isLocalized_maximal C M (fun P _ => Localization.AtPrime P ⊗[C] M)
    (fun P _ => TensorProduct.mk C (Localization.AtPrime P) M 1) fun P hP => ?_
  obtain ⟨C', _, _, _, _, _, hflat⟩ := H P

  have : Module.Flat C' (C' ⊗[Localization.AtPrime P] (Localization.AtPrime P ⊗[C] M)) :=
    Module.Flat.of_linearEquiv
      (TensorProduct.AlgebraTensorModule.cancelBaseChange C (Localization.AtPrime P) C' C' M)
  have hP : Module.Flat (Localization.AtPrime P) (Localization.AtPrime P ⊗[C] M) :=
    Module.Flat.of_flat_tensorProduct _ _ C'
  exact Module.Flat.trans C (Localization.AtPrime P) _

end descent
open FiniteLocallyFreeQuotient.QuotFLF.Tgt FiniteLocallyFreeQuotient.QuotFLF.L1
  FiniteLocallyFreeQuotient.QuotFLF.L8 FiniteLocallyFreeQuotient.QuotFLF.L7
    FiniteLocallyFreeQuotient.QuotFLF

end QuotFLF
open FiniteLocallyFreeQuotient.QuotFLF.Tgt FiniteLocallyFreeQuotient.QuotFLF.L1
  FiniteLocallyFreeQuotient.QuotFLF.L8 FiniteLocallyFreeQuotient.QuotFLF.L7
    FiniteLocallyFreeQuotient.QuotFLF

namespace QuotFLF

section assembly

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra C A]
  [Algebra C B] [IsScalarTower C A B] (t : A →+* B)
  (hinv : ∀ a : A, algebraMap A B a = t a ↔ a ∈ Set.range (algebraMap C A))

private noncomputable abbrev thetaLin : A ⊗[C] A →ₗ[C] B := ((theta t
  hinv).toLinearMap).restrictScalars C

private theorem finite_projective_faithfullyFlat_bijective_of_local
    [Module.Finite A B] [Module.Projective A B]
    (H : ∀ (P : Ideal C) [P.IsMaximal], ∃ (C' : Type u) (_ : CommRing C') (_ : Algebra C C')
      (_ : Algebra (Localization.AtPrime P) C') (_ : IsScalarTower C (Localization.AtPrime P) C')
      (_ : Module.FaithfullyFlat (Localization.AtPrime P) C'),
      Module.Flat C' (C' ⊗[C] A) ∧ Function.Bijective ((thetaLin t hinv).baseChange C') ∧
      ∃ Q : Ideal A, Q.IsPrime ∧ Q.comap (algebraMap C A) = P) :
    Module.Finite C A ∧ Module.Projective C A ∧ Module.FaithfullyFlat C A ∧
      Function.Bijective (theta t hinv) := by

  have hflat : Module.Flat C A := flat_of_forall_exists_faithfullyFlat fun P _ => by
    obtain ⟨C', i1, i2, i3, i4, i5, hf, -, -⟩ := H P
    exact ⟨C', i1, i2, i3, i4, i5, hf⟩
  have hbij : Function.Bijective (theta t hinv) := by
    change Function.Bijective (thetaLin t hinv)
    exact bijective_of_forall_exists_faithfullyFlat _ fun P _ => by
      obtain ⟨C', i1, i2, i3, i4, i5, -, hb, -⟩ := H P
      exact ⟨C', i1, i2, i3, i4, i5, hb⟩

  have hff : Module.FaithfullyFlat C A := by
    refine ⟨fun m hm htop => ?_⟩
    obtain ⟨-, -, -, -, -, -, -, -, Q, hQ, hQm⟩ := H m
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_eq_top_iff, Ideal.eq_top_iff_one] at htop
    have : (1 : A) ∈ Q := by
      have hle : m.map (algebraMap C A) ≤ Q := by rw [Ideal.map_le_iff_le_comap, hQm]
      exact hle htop
    exact hQ.ne_top ((Ideal.eq_top_iff_one _).mpr this)

  let e : A ⊗[C] A ≃ₐ[A] B := AlgEquiv.ofBijective (theta t hinv) hbij
  haveI : Module.Finite A (A ⊗[C] A) := Module.Finite.equiv e.toLinearEquiv.symm
  have hfin : Module.Finite C A := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat (T := A)
  haveI : Module.FinitePresentation A B := Module.finitePresentation_of_projective A B
  haveI : Algebra.FinitePresentation A (A ⊗[C] A) := Algebra.FinitePresentation.equiv e.symm
  haveI : Algebra.FinitePresentation C A :=
    Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat A
  haveI := hfin
  haveI : Module.FinitePresentation C A :=
    Module.FinitePresentation.of_finite_of_finitePresentation C A
  exact ⟨hfin, Module.Flat.projective_of_finitePresentation, hff, hbij⟩

end assembly
open FiniteLocallyFreeQuotient.QuotFLF.Tgt FiniteLocallyFreeQuotient.QuotFLF.L1
  FiniteLocallyFreeQuotient.QuotFLF.L8 FiniteLocallyFreeQuotient.QuotFLF.L7
    FiniteLocallyFreeQuotient.QuotFLF

end QuotFLF
open FiniteLocallyFreeQuotient.QuotFLF.Tgt FiniteLocallyFreeQuotient.QuotFLF.L1
  FiniteLocallyFreeQuotient.QuotFLF.L8 FiniteLocallyFreeQuotient.QuotFLF.L7
    FiniteLocallyFreeQuotient.QuotFLF

namespace QuotFLF

section localPackage

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra C A]
  [Algebra C B] [IsScalarTower C A B] {t : A →+* B}

private theorem bijective_baseChange_theta_of_isPushout (C' : Type u) [CommRing C'] [Algebra C C']
    (hinv : ∀ a : A, algebraMap A B a = t a ↔ a ∈ Set.range (algebraMap C A))
    (hpo : IsPushout (CommRingCat.ofHom (algebraMap C' (C' ⊗[C] A)))
      (CommRingCat.ofHom (algebraMap C' (C' ⊗[C] A)))
      (CommRingCat.ofHom (algebraMap (C' ⊗[C] A) (C' ⊗[C] B)))
      (CommRingCat.ofHom (t' t C' (t_comp_algebraMap hinv)))) :
    Function.Bijective ((thetaLin t hinv).baseChange C') := by
  set ht := t_comp_algebraMap hinv

  have h₂ := CommRingCat.isPushout_tensorProduct C' (C' ⊗[C] A) (C' ⊗[C] A)
  let ψ : (C' ⊗[C] A) ⊗[C'] (C' ⊗[C] A) ≃+* C' ⊗[C] B :=
    (h₂.isoIsPushout _ _ hpo).commRingCatIsoToRingEquiv
  have hψl : ∀ x, ψ (x ⊗ₜ[C'] 1) = algebraMap (C' ⊗[C] A) (C' ⊗[C] B) x := fun x =>
    RingHom.congr_fun (congrArg CommRingCat.Hom.hom (h₂.inl_isoIsPushout_hom _ _ hpo)) x
  have hψr : ∀ y, ψ (1 ⊗ₜ[C'] y) = t' t C' ht y := fun y =>
    RingHom.congr_fun (congrArg CommRingCat.Hom.hom (h₂.inr_isoIsPushout_hom _ _ hpo)) y
  have hψ : ∀ (c₁ c₂ : C') (a₁ a₂ : A), ψ ((c₁ ⊗ₜ[C] a₁) ⊗ₜ[C'] (c₂ ⊗ₜ[C] a₂)) =
      (c₁ * c₂) ⊗ₜ[C] (algebraMap A B a₁ * t a₂) := by
    intro c₁ c₂ a₁ a₂
    have : (c₁ ⊗ₜ[C] a₁) ⊗ₜ[C'] (c₂ ⊗ₜ[C] a₂) =
        ((c₁ ⊗ₜ[C] a₁) ⊗ₜ[C'] 1) * (1 ⊗ₜ[C'] (c₂ ⊗ₜ[C] a₂)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [this, map_mul, hψl, hψr, algebraMap_primed_tmul, t'_tmul,
      Algebra.TensorProduct.tmul_mul_tmul]

  let κ : (C' ⊗[C] A) ⊗[C'] (C' ⊗[C] A) ≃ₗ[C'] C' ⊗[C] (A ⊗[C] A) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange C C' C' (C' ⊗[C] A) A).trans
      (TensorProduct.AlgebraTensorModule.assoc C C C' C' A A)
  have hκ : ∀ (c₁ c₂ : C') (a₁ a₂ : A), κ ((c₁ ⊗ₜ[C] a₁) ⊗ₜ[C'] (c₂ ⊗ₜ[C] a₂)) =
      (c₂ * c₁) ⊗ₜ[C] (a₁ ⊗ₜ[C] a₂) := by
    intro c₁ c₂ a₁ a₂
    simp [κ, TensorProduct.smul_tmul']

  have key : ∀ z, ((thetaLin t hinv).baseChange C') (κ z) = ψ z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [LinearEquiv.map_zero, LinearMap.map_zero, RingEquiv.map_zero]
    | add x y hx hy => rw [LinearEquiv.map_add, LinearMap.map_add, RingEquiv.map_add, hx, hy]
    | tmul x y =>
      induction x using TensorProduct.induction_on with
      | zero => rw [TensorProduct.zero_tmul, LinearEquiv.map_zero, LinearMap.map_zero,
        RingEquiv.map_zero]
      | add x x' hx hx' =>
        rw [TensorProduct.add_tmul, LinearEquiv.map_add, LinearMap.map_add, RingEquiv.map_add, hx,
          hx']
      | tmul c₁ a₁ =>
        induction y using TensorProduct.induction_on with
        | zero => rw [TensorProduct.tmul_zero, LinearEquiv.map_zero, LinearMap.map_zero,
          RingEquiv.map_zero]
        | add y y' hy hy' =>
          rw [TensorProduct.tmul_add, LinearEquiv.map_add, LinearMap.map_add, RingEquiv.map_add, hy,
            hy']
        | tmul c₂ a₂ =>
          rw [hκ, hψ, LinearMap.baseChange_tmul, mul_comm c₂ c₁]
          rfl
  have hcomp : ((thetaLin t hinv).baseChange C' : C' ⊗[C] (A ⊗[C] A) → C' ⊗[C] B) =
      ψ ∘ κ.symm := by
    funext z
    rw [Function.comp_apply, ← key, LinearEquiv.apply_symm_apply]
  rw [hcomp]
  exact ψ.bijective.comp κ.symm.bijective

variable [Module.Finite A B] [Module.Projective A B]
  [Module.Finite A (Tgt t)] [Module.Projective A (Tgt t)]
  (hgen : (algebraMap A B).range ⊔ t.range = ⊤)
  (hequiv : ∀ (T : Type u) [CommRing T], _root_.Equivalence (Rel (algebraMap A B) t T))
  (hinj : Function.Injective (algebraMap C A))
  (hinv : ∀ a : A, algebraMap A B a = t a ↔ a ∈ Set.range (algebraMap C A))

include hgen hequiv hinj in

private theorem local_world (C' : Type u) [CommRing C'] [Algebra C C'] [Module.Flat C C']
  [IsLocalRing C']
    [Infinite (IsLocalRing.ResidueField C')] :
    Module.Flat C' (C' ⊗[C] A) ∧ Function.Bijective ((thetaLin t hinv).baseChange C') ∧
      ∃ Q : Ideal A, Q.IsPrime ∧
        Q.comap (algebraMap C A) = (IsLocalRing.maximalIdeal C').comap (algebraMap C C') := by
  classical
  have hgen' := L7_hgen t C' (t_comp_algebraMap hinv) hgen
  have hequiv' := L7_hequiv t C' (t_comp_algebraMap hinv) hequiv
  have hinj' : Function.Injective (algebraMap C' (C' ⊗[C] A)) := L7_algebraMap_injective C' hinj
  have hinv' : ∀ a' : C' ⊗[C] A, algebraMap (C' ⊗[C] A) (C' ⊗[C] B) a' =
      t' t C' (t_comp_algebraMap hinv) a' ↔ a' ∈ Set.range (algebraMap C' (C' ⊗[C] A)) :=
    L7_invariants t C' hinv

  obtain ⟨r, hr⟩ := exists_rankAtStalk_eq_of_isLocalRing (t := t' t C' (t_comp_algebraMap hinv))
    hgen' hequiv' hinj' hinv'

  haveI : Algebra.IsIntegral C' (C' ⊗[C] A) := by
    refine L3_isIntegral (algebraMap (C' ⊗[C] A) (C' ⊗[C] B)) (t' t C' (t_comp_algebraMap hinv))
      hequiv' hinj' hinv' fun f => ?_
    refine ⟨charpoly (C' ⊗[C] A) (C' ⊗[C] B) r hr (t' t C' (t_comp_algebraMap hinv) f),
      L1_monic _ _ r hr _, coeff_charpoly_invariant (t := t' t C' (t_comp_algebraMap hinv))
        hgen' hequiv' r hr f, ?_⟩
    rw [aeval_map_algebraMap]
    exact L1_aeval_self _ _ r hr _

  obtain ⟨x, hx⟩ := L5_exists_basis_of_isLocalRing (t := t' t C' (t_comp_algebraMap hinv))
    hinv' hgen' hequiv' r hr
  have hfree : Function.Bijective (vC (C := C') x) := by
    have h := vC_bijective (t := t' t C' (t_comp_algebraMap hinv)) hequiv' hinj' hinv' x hx
    have heq : (fun w : Fin r → C' => ∑ i,
      algebraMap C' (C' ⊗[C] A) (w i) * x i) = vC (C := C') x :=
      funext fun w => (vC_apply x w).symm
    rwa [heq] at h
  have hpo := isPushout_of_basis (t := t' t C' (t_comp_algebraMap hinv)) hequiv' hinj' hinv' x hx
  refine ⟨Module.Flat.of_linearEquiv (LinearEquiv.ofBijective (vC (C := C') x) hfree).symm,
    bijective_baseChange_theta_of_isPushout (t := t) C' hinv hpo, ?_⟩

  obtain ⟨Q', hQ'⟩ := L4a_comap_surjective (C := C') (A := C' ⊗[C] A) hinj'
    ⟨IsLocalRing.maximalIdeal C', inferInstance⟩
  refine ⟨Q'.asIdeal.comap (Algebra.TensorProduct.includeRight (R := C) (A := C') (B :=
    A)).toRingHom,
    Ideal.comap_isPrime _ _, ?_⟩
  rw [Ideal.comap_comap, AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap,
    IsScalarTower.algebraMap_eq C C' (C' ⊗[C] A), ← Ideal.comap_comap]
  have h1 : Q'.asIdeal.comap (algebraMap C' (C' ⊗[C] A)) = IsLocalRing.maximalIdeal C' := by
    have := congrArg PrimeSpectrum.asIdeal hQ'
    simpa using this
  rw [h1]

include hgen hequiv hinj in

private theorem local_package (P : Ideal C) [P.IsMaximal] :
    ∃ (C' : Type u) (_ : CommRing C') (_ : Algebra C C')
      (_ : Algebra (Localization.AtPrime P) C') (_ : IsScalarTower C (Localization.AtPrime P) C')
      (_ : Module.FaithfullyFlat (Localization.AtPrime P) C'),
      Module.Flat C' (C' ⊗[C] A) ∧ Function.Bijective ((thetaLin t hinv).baseChange C') ∧
      ∃ Q : Ideal A, Q.IsPrime ∧ Q.comap (algebraMap C A) = P := by
  haveI hffP : Module.FaithfullyFlat (Localization.AtPrime P) (L8.RX (Localization.AtPrime P)) :=
    L8.faithfullyFlat _
  haveI : Module.Flat C (Localization.AtPrime P) := IsLocalization.flat _ P.primeCompl
  haveI : Module.Flat C (L8.RX (Localization.AtPrime P)) :=
    Module.Flat.trans C (Localization.AtPrime P) _
  haveI : Infinite (IsLocalRing.ResidueField (L8.RX (Localization.AtPrime P))) :=
    L8.infinite_residueField _
  obtain ⟨hflat, hbij, Q, hQ, hQP⟩ :=
    local_world (t := t) hgen hequiv hinj hinv (L8.RX (Localization.AtPrime P))
  refine ⟨L8.RX (Localization.AtPrime P), inferInstance, inferInstance, inferInstance,
    inferInstance,
    hffP, hflat, hbij, Q, hQ, ?_⟩
  rw [hQP, IsScalarTower.algebraMap_eq C (Localization.AtPrime P) (L8.RX (Localization.AtPrime P)),
    ← Ideal.comap_comap]
  have h2 : (IsLocalRing.maximalIdeal (L8.RX (Localization.AtPrime P))).comap
      (algebraMap (Localization.AtPrime P) (L8.RX (Localization.AtPrime P))) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
    ext c
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff,
      mem_nonunits_iff, isUnit_map_iff]
  rw [h2]
  exact Localization.AtPrime.under_maximalIdeal (I := P)

end localPackage
open FiniteLocallyFreeQuotient.QuotFLF.Tgt FiniteLocallyFreeQuotient.QuotFLF.L1
  FiniteLocallyFreeQuotient.QuotFLF.L8 FiniteLocallyFreeQuotient.QuotFLF.L7
    FiniteLocallyFreeQuotient.QuotFLF

end QuotFLF
open FiniteLocallyFreeQuotient.QuotFLF.Tgt FiniteLocallyFreeQuotient.QuotFLF.L1
  FiniteLocallyFreeQuotient.QuotFLF.L8 FiniteLocallyFreeQuotient.QuotFLF.L7
    FiniteLocallyFreeQuotient.QuotFLF

open QuotFLF in

private theorem solution
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra C A]
    (s t : A →+* B)
    (hs : letI := s.toAlgebra; Module.Finite A B) (hs' : letI := s.toAlgebra; Module.Projective A B)
    (ht : letI := t.toAlgebra; Module.Finite A B) (ht' : letI := t.toAlgebra; Module.Projective A B)
    (hgen : s.range ⊔ t.range = ⊤)
    (hequiv : ∀ (T : Type u) [CommRing T],
      _root_.Equivalence fun x y : A →+* T => ∃ φ : B →+* T, φ.comp s = x ∧ φ.comp t = y)
    (hinj : Function.Injective (algebraMap C A))
    (hinv : ∀ a : A, s a = t a ↔ a ∈ Set.range (algebraMap C A)) :
    Module.Finite C A ∧ Module.Projective C A ∧ Module.FaithfullyFlat C A ∧
      IsPushout (CommRingCat.ofHom (algebraMap C A)) (CommRingCat.ofHom (algebraMap C A))
        (CommRingCat.ofHom s) (CommRingCat.ofHom t) := by
  letI : Algebra A B := s.toAlgebra
  letI : Algebra C B := (s.comp (algebraMap C A)).toAlgebra
  haveI : IsScalarTower C A B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Module.Finite A B := hs
  haveI : Module.Projective A B := hs'
  haveI : Module.Finite A (Tgt t) := ht
  haveI : Module.Projective A (Tgt t) := ht'
  have hinv₁ : ∀ a : A, algebraMap A B a = t a ↔ a ∈ Set.range (algebraMap C A) := hinv
  have hgen₁ : (algebraMap A B).range ⊔ t.range = ⊤ := hgen
  have hequiv₁ : ∀ (T : Type u) [CommRing T],
    _root_.Equivalence (Rel (algebraMap A B) t T) := hequiv
  obtain ⟨hfin, hproj, hff, hbij⟩ :=
    finite_projective_faithfullyFlat_bijective_of_local t hinv₁
      (fun P _ => local_package (t := t) hgen₁ hequiv₁ hinj hinv₁ P)
  exact ⟨hfin, hproj, hff, isPushout_of_bijective_theta t hinv₁ hbij⟩

end FiniteLocallyFreeQuotient

universe u

/-- A finite locally free affine equivalence relation is the kernel pair of
its invariant-ring quotient: given ring maps `s t : A →+* B` that are finite
and projective for both module structures, jointly generate `B`, and induce
an equivalence relation on ring-valued points, the invariant ring `C` (with
`s a = t a` exactly on its range and `C → A` injective) makes `A` finite,
projective and faithfully flat over `C`, and exhibits `B` as the pushout of
`A` with itself over `C` along `s` and `t`. -/
public theorem RingHom.isPushout_eqLocus_of_finiteLocallyFree_equivalenceRelation
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra C A]
    (s t : A →+* B)
    (hs : letI := s.toAlgebra; Module.Finite A B)
    (hs' : letI := s.toAlgebra; Module.Projective A B)
    (ht : letI := t.toAlgebra; Module.Finite A B)
    (ht' : letI := t.toAlgebra; Module.Projective A B)
    (hgen : s.range ⊔ t.range = ⊤)
    (hequiv : ∀ (T : Type u) [CommRing T],
      _root_.Equivalence fun x y : A →+* T => ∃ φ : B →+* T, φ.comp s = x ∧ φ.comp t = y)
    (hinj : Function.Injective (algebraMap C A))
    (hinv : ∀ a : A, s a = t a ↔ a ∈ Set.range (algebraMap C A)) :
    Module.Finite C A ∧ Module.Projective C A ∧ Module.FaithfullyFlat C A ∧
      CategoryTheory.IsPushout (CommRingCat.ofHom (algebraMap C A))
        (CommRingCat.ofHom (algebraMap C A)) (CommRingCat.ofHom s)
        (CommRingCat.ofHom t) :=
  FiniteLocallyFreeQuotient.solution s t hs hs' ht ht' hgen hequiv hinj hinv
