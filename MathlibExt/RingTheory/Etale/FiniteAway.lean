/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Algebra_exists_etale_isIdempotentElem_finite_away_forall_liesOver_notMem.lean`
and
`P2M/Sol/S_Algebra_exists_etale_isIdempotentElem_finite_away_forall_liesOver_notMem.lean`
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

public import Mathlib.RingTheory.Etale.QuasiFinite
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.TensorProduct.Tower

@[expose] public section

open scoped TensorProduct

universe u v

/-!
# Étale neighborhoods splitting quasi-finite algebras

Auxiliary idempotent manipulations and an induction on the number of
bad primes over an étale neighborhood.
-/


set_option autoImplicit false

open scoped TensorProduct



namespace EtaleFiniteAwayAux

section Idem
variable {T : Type*} [CommRing T]

private def idemCompl (e : T) : T := 1 - e

private def idemJoin (e f : T) : T := e + f - e * f

private theorem idemCompl_def (e : T) : idemCompl e = 1 - e := rfl
private theorem idemJoin_def (e f : T) : idemJoin e f = e + f - e * f := rfl

private theorem IsIdempotentElem.idemJoin' {e f : T} (he : IsIdempotentElem e)
  (hf : IsIdempotentElem f) :
    IsIdempotentElem (idemJoin e f) := he.add_sub_mul hf

private scoped instance isLocalizationAway_quot (e : T) [Fact (IsIdempotentElem e)] :
    IsLocalization.Away e (T ⧸ Ideal.span {idemCompl e}) :=
  IsLocalization.away_of_isIdempotentElem (Fact.out) Ideal.mk_ker Ideal.Quotient.mk_surjective

private noncomputable def awayEquivQuot (e : T) (he : IsIdempotentElem e) :
    Localization.Away e ≃ₐ[T] T ⧸ Ideal.span {idemCompl e} :=
  haveI : Fact (IsIdempotentElem e) := ⟨he⟩
  IsLocalization.algEquiv (Submonoid.powers e) (Localization.Away e) (T ⧸ Ideal.span {idemCompl e})

private theorem finite_away_iff (A : Type*) [CommRing A] [Algebra A T] (e : T)
  (he : IsIdempotentElem e) :
    Module.Finite A (Localization.Away e) ↔ Module.Finite A (T ⧸ Ideal.span {idemCompl e}) := by
  let f := (awayEquivQuot e he).restrictScalars A
  exact ⟨fun _ => Module.Finite.equiv f.toLinearEquiv,
    fun _ => Module.Finite.equiv f.symm.toLinearEquiv⟩

private theorem mem_iff_one_sub_not_mem {e : T} (he : IsIdempotentElem e) {Q : Ideal T}
  (hQ : Q.IsPrime) :
    e ∈ Q ↔ 1 - e ∉ Q := by
  constructor
  · intro h h'
    apply hQ.ne_top
    rw [Ideal.eq_top_iff_one]
    have := Q.add_mem h h'
    rwa [add_sub_cancel] at this
  · intro h
    have h0 : e * (1 - e) ∈ Q := by
      rw [mul_sub, mul_one, he.eq, sub_self]
      exact Q.zero_mem
    exact (hQ.mem_or_mem h0).resolve_right h

private theorem idemJoin_mem_iff {e f : T} (he : IsIdempotentElem e)
  (hf : IsIdempotentElem f) {Q : Ideal T}
    (hQ : Q.IsPrime) : idemJoin e f ∈ Q ↔ e ∈ Q ∧ f ∈ Q := by
  have hj : IsIdempotentElem (idemJoin e f) := IsIdempotentElem.idemJoin' he hf
  rw [mem_iff_one_sub_not_mem hj hQ, mem_iff_one_sub_not_mem he hQ, mem_iff_one_sub_not_mem hf hQ]
  have : (1 : T) - idemJoin e f = (1 - e) * (1 - f) := by rw [idemJoin_def]; ring
  rw [this]
  constructor
  · intro h
    exact ⟨fun h1 => h (Q.mul_mem_right _ h1), fun h2 => h (Q.mul_mem_left _ h2)⟩
  · rintro ⟨h1, h2⟩ h
    rcases hQ.mem_or_mem h with h' | h'
    exacts [h1 h', h2 h']

private theorem finite_quot_idemJoin (A : Type*) [CommRing A] [Algebra A T] {e f : T}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (h1 : Module.Finite A (T ⧸ Ideal.span {idemCompl e})) (h2 : Module.Finite A
      (T ⧸ Ideal.span {idemCompl f})) :
    Module.Finite A (T ⧸ Ideal.span {idemCompl (idemJoin e f)}) := by
  let J : Ideal T := Ideal.span {idemCompl (idemJoin e f)}

  have hwd1 : ∀ x : T, x ∈ Ideal.span {idemCompl e} → Ideal.Quotient.mk J (x * e) = 0 := by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [mul_assoc, show idemCompl e * e = 0 by rw [idemCompl_def, sub_mul, one_mul, he.eq,
      sub_self], mul_zero,
      map_zero]
  have hwd2 : ∀ y : T, y ∈ Ideal.span {idemCompl f} →
      Ideal.Quotient.mk J (y * (f * (1 - e))) = 0 := by
    intro y hy
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    rw [mul_assoc, ← mul_assoc (idemCompl f), show idemCompl f * f = 0 by
      rw [idemCompl_def, sub_mul, one_mul, hf.eq, sub_self], zero_mul, mul_zero, map_zero]
  let φ₁ : (T ⧸ Ideal.span {idemCompl e}) →ₗ[A] (T ⧸ J) :=
    Submodule.liftQ ((Ideal.span {idemCompl e}).restrictScalars A)
      (((Ideal.Quotient.mkₐ A J).toLinearMap).comp (LinearMap.mulRight A e))
      (fun x hx => by
        simp only [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.mulRight_apply,
          AlgHom.toLinearMap_apply,
          Ideal.Quotient.mkₐ_eq_mk]
        exact hwd1 x hx)
  let φ₂ : (T ⧸ Ideal.span {idemCompl f}) →ₗ[A] (T ⧸ J) :=
    Submodule.liftQ ((Ideal.span {idemCompl f}).restrictScalars A)
      (((Ideal.Quotient.mkₐ A J).toLinearMap).comp (LinearMap.mulRight A (f * (1 - e))))
      (fun y hy => by
        simp only [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.mulRight_apply,
          AlgHom.toLinearMap_apply,
          Ideal.Quotient.mkₐ_eq_mk]
        exact hwd2 y hy)
  let φ : (T ⧸ Ideal.span {idemCompl e}) × (T ⧸ Ideal.span {idemCompl f}) →ₗ[A]
    (T ⧸ J) := φ₁.coprod φ₂
  have hφ₁ : ∀ x : T, φ₁ (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk J (x * e) := fun x => rfl
  have hφ₂ : ∀ y : T, φ₂ (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk J (y * (f *
    (1 - e))) := fun y => rfl
  refine Module.Finite.of_surjective φ ?_
  intro z
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨(Ideal.Quotient.mk _ z, Ideal.Quotient.mk _ z), ?_⟩
  show φ₁ (Ideal.Quotient.mk _ z) + φ₂ (Ideal.Quotient.mk _ z) = _
  rw [hφ₁, hφ₂, ← map_add, Ideal.Quotient.eq]
  have : z * e + z * (f * (1 - e)) - z = -(z * idemCompl (idemJoin e f)) := by
    rw [idemCompl_def, idemJoin_def]; ring
  rw [this]
  exact J.neg_mem (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))

end Idem

end EtaleFiniteAwayAux

namespace EtaleFiniteAwayAux

section BaseChange
variable (A A' : Type*) [CommRing A] [CommRing A'] [Algebra A A']
variable {T : Type*} [CommRing T] [Algebra A T]

private theorem finite_quot_baseChange (e : T)
    (h : Module.Finite A (T ⧸ Ideal.span {idemCompl e})) :
    Module.Finite A'
      ((A' ⊗[A] T) ⧸ Ideal.span {idemCompl ((1 : A') ⊗ₜ[A] e)}) := by
  set I : Ideal T := Ideal.span {idemCompl e}

  have hIJ : ∀ x ∈ I, (Ideal.Quotient.mkₐ A (Ideal.span {idemCompl ((1 : A') ⊗ₜ[A] e)}))
      (Algebra.TensorProduct.includeRight (R := A) (A := A') x) = 0 := by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    have h1 : (Algebra.TensorProduct.includeRight (R := A) (A := A') (c *
      idemCompl e) : A' ⊗[A] T) =
        Algebra.TensorProduct.includeRight (R := A) (A := A') c * idemCompl ((1 : A') ⊗ₜ[A] e) := by
      rw [idemCompl_def, idemCompl_def, map_mul, map_sub, map_one]
      rfl
    rw [h1]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  let ψ₂ : (T ⧸ I) →ₐ[A] (A' ⊗[A] T) ⧸ Ideal.span {idemCompl ((1 : A') ⊗ₜ[A] e)} :=
    Ideal.Quotient.liftₐ I
      ((Ideal.Quotient.mkₐ A (Ideal.span {idemCompl ((1 : A') ⊗ₜ[A] e)})).comp
        Algebra.TensorProduct.includeRight)
      (fun x hx => hIJ x hx)
  let Q := (A' ⊗[A] T) ⧸ Ideal.span {idemCompl ((1 : A') ⊗ₜ[A] e)}
  let f : A' →ₗ[A'] ((T ⧸ I) →ₗ[A] Q) := (LinearMap.id : A' →ₗ[A'] A').smulRight ψ₂.toLinearMap
  let ψ : A' ⊗[A] (T ⧸ I) →ₗ[A'] Q := TensorProduct.AlgebraTensorModule.lift f
  have hψ : ∀ (a : A') (t : T), ψ (a ⊗ₜ[A] Ideal.Quotient.mk I t) =
      a • Ideal.Quotient.mk (Ideal.span {idemCompl ((1 : A') ⊗ₜ[A] e)}) ((1 : A') ⊗ₜ[A] t) := by
    intro a t
    show f a (Ideal.Quotient.mk I t) = _
    rfl
  haveI : Module.Finite A' (A' ⊗[A] (T ⧸ I)) := inferInstance
  refine Module.Finite.of_surjective ψ ?_

  intro z
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul a t =>
      refine ⟨a ⊗ₜ[A] Ideal.Quotient.mk I t, ?_⟩
      rw [hψ, ← Ideal.Quotient.mkₐ_eq_mk A', ← map_smul, TensorProduct.smul_tmul', smul_eq_mul,
        mul_one]
  | add x y hx hy =>
      obtain ⟨x', hx'⟩ := hx
      obtain ⟨y', hy'⟩ := hy
      exact ⟨x' + y', by rw [map_add, hx', hy', map_add]⟩

end BaseChange

section Transport
variable {A : Type*} [CommRing A] {T₁ T₂ : Type*} [CommRing T₁] [CommRing T₂]
  [Algebra A T₁] [Algebra A T₂]

private theorem map_span_one_sub (ε : T₁ ≃ₐ[A] T₂) (e : T₁) :
    Ideal.span {idemCompl (ε e)} = (Ideal.span {idemCompl e}).map (ε : T₁ →+* T₂) := by
  rw [Ideal.map_span, Set.image_singleton]
  simp [idemCompl_def]

private theorem finite_quot_transport (ε : T₁ ≃ₐ[A] T₂) (e : T₁)
    (h : Module.Finite A (T₁ ⧸ Ideal.span {idemCompl e})) :
    Module.Finite A (T₂ ⧸ Ideal.span {idemCompl (ε e)}) :=
  Module.Finite.equiv
    (Ideal.quotientEquivAlg (Ideal.span {idemCompl e})
      (Ideal.span {idemCompl (ε e)}) ε (map_span_one_sub ε e)).toLinearEquiv

private theorem liesOver_comap_ringEquiv (ε : T₁ ≃+* T₂) (hε : ∀ a : A, ε (algebraMap A T₁ a) =
  algebraMap A T₂ a)
    (Q : Ideal T₂) (P : Ideal A) [Q.LiesOver P] :
    (Q.comap ε.toRingHom).LiesOver P := by
  constructor
  have hcomp : ε.toRingHom.comp (algebraMap A T₁) = algebraMap A T₂ := RingHom.ext hε
  rw [Ideal.under_def, Ideal.comap_comap, hcomp, ← Ideal.under_def]
  exact Ideal.over_def Q P

end Transport

section Kappa
variable {R R' R'' : Type*} [CommRing R] [CommRing R'] [CommRing R'']
  [Algebra R R'] [Algebra R' R''] [Algebra R R'']
  [IsScalarTower R R' R'']

private theorem bijective_mapₐ_self (p : Ideal R) [p.IsPrime] [p.LiesOver p] :
    Function.Bijective (Ideal.ResidueField.mapₐ p p (Algebra.ofId R R) (p.over_def p)) := by
  have : Ideal.ResidueField.mapₐ p p (Algebra.ofId R R) (p.over_def p) = AlgHom.id R _ :=
    Ideal.ResidueField.algHom_ext (Subsingleton.elim _ _)
  rw [this]
  exact Function.bijective_id

private theorem bijective_mapₐ_trans (p : Ideal R) [p.IsPrime]
  (P' : Ideal R') [P'.IsPrime] [P'.LiesOver p]
    (P'' : Ideal R'') [P''.IsPrime] [P''.LiesOver P'] [P''.LiesOver p]
    (h₁ : Function.Bijective (Ideal.ResidueField.mapₐ p P' (Algebra.ofId R R') (P'.over_def p)))
    (h₂ : Function.Bijective (Ideal.ResidueField.mapₐ P' P'' (Algebra.ofId R' R'')
      (P''.over_def P'))) :
    Function.Bijective (Ideal.ResidueField.mapₐ p P'' (Algebra.ofId R R'') (P''.over_def p)) := by
  have : Ideal.ResidueField.mapₐ p P'' (Algebra.ofId R R'') (P''.over_def p) =
      ((Ideal.ResidueField.mapₐ P' P'' (Algebra.ofId R' R'')
        (P''.over_def P')).restrictScalars R).comp
        (Ideal.ResidueField.mapₐ p P' (Algebra.ofId R R') (P'.over_def p)) :=
    Ideal.ResidueField.algHom_ext (Subsingleton.elim _ _)
  rw [this]
  exact h₂.comp h₁

end Kappa

end EtaleFiniteAwayAux

namespace EtaleFiniteAwayAux

section Main
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FiniteType R S] [Algebra.QuasiFinite R S] (p : Ideal R) [p.IsPrime]

private def bad (R' : Type u) [CommRing R'] [Algebra R R'] (P : Ideal R') (e : R' ⊗[R] S) :
    Set (Ideal (R' ⊗[R] S)) :=
  {Q | Q.IsPrime ∧ Q.LiesOver P ∧ e ∈ Q}

omit [Algebra.FiniteType R S] [p.IsPrime] in
private theorem bad_finite (R' : Type u) [CommRing R'] [Algebra R R'] (P : Ideal R') [P.IsPrime]
  (e : R' ⊗[R] S) :
    (bad (S := S) R' P e).Finite :=
  (Algebra.QuasiFinite.finite_primesOver (R := R') (S := R' ⊗[R] S) P).subset
    (fun Q hQ => ⟨hQ.1, hQ.2.1⟩)

set_option maxHeartbeats 6400000 in
private theorem claim (n : ℕ) :
    ∀ (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra.Etale R R'] (P : Ideal R') [P.IsPrime]
      [P.LiesOver p],
      Function.Bijective (Ideal.ResidueField.mapₐ p P (Algebra.ofId R R') (P.over_def p)) →
      ∀ (e : R' ⊗[R] S), IsIdempotentElem e → Module.Finite R'
        ((R' ⊗[R] S) ⧸ Ideal.span {idemCompl e}) →
      (bad (S := S) R' P e).ncard = n →
      ∃ (R'' : Type u) (_ : CommRing R'') (_ : Algebra R R'') (_ : Algebra.Etale R R'')
        (P'' : Ideal R'')
        (_ : P''.IsPrime) (_ : P''.LiesOver p) (e'' : R'' ⊗[R] S) (_ : IsIdempotentElem e''),
        Function.Bijective (Ideal.ResidueField.mapₐ p P'' (Algebra.ofId _ _) (P''.over_def p)) ∧
        Module.Finite R'' (Localization.Away e'') ∧
        ∀ Q : Ideal (R'' ⊗[R] S), Q.IsPrime → Q.LiesOver P'' → e'' ∉ Q := by
  induction n with
  | zero =>
    intro R' _ _ _ P _ _ hκ e he hfin h0
    refine ⟨R', inferInstance, inferInstance, inferInstance, P, inferInstance, inferInstance, e,
      he, hκ,
      (finite_away_iff R' e he).mpr hfin, ?_⟩
    intro Q hQ hQP heQ
    have hmem : Q ∈ bad (S := S) R' P e := ⟨hQ, hQP, heQ⟩
    rw [(Set.ncard_eq_zero (bad_finite R' P e)).mp h0] at hmem
    exact hmem
  | succ n ih =>
    intro R' _ _ _ P _ _ hκ e he hfin hn
    classical

    obtain ⟨Q, hQ, hQP, heQ⟩ : (bad (S := S) R' P e).Nonempty :=
      (Set.ncard_pos (bad_finite R' P e)).mp (by omega)
    haveI := hQ
    haveI := hQP

    obtain ⟨R'', i1, i2, i3, P'', i4, i5, e₁, he₁, Q', i6, i7, hQ'Q, he₁Q', hκ', hfin₁, huniq⟩ :=
      Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq (R := R') (S := R' ⊗[R] S) P Q

    letI : Algebra R R'' := ((algebraMap R' R'').comp (algebraMap R R')).toAlgebra
    haveI : IsScalarTower R R' R'' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    haveI : Algebra.Etale R R'' := Algebra.Etale.comp R R' R''
    haveI : P''.LiesOver p := Ideal.LiesOver.trans P'' P p
    have hκ'' := bijective_mapₐ_trans p P P'' hκ hκ'

    let a₁ : (R'' ⊗[R'] (R' ⊗[R] S)) := (1 : R'') ⊗ₜ[R'] e
    have ha₁ : IsIdempotentElem a₁ := he.map (Algebra.TensorProduct.includeRight (R := R')
      (A := R''))
    have hg₁ : IsIdempotentElem (idemJoin a₁ e₁) := IsIdempotentElem.idemJoin' (T := (R'' ⊗[R']
      (R' ⊗[R] S))) ha₁ he₁
    have hfin_a : Module.Finite R'' ((R'' ⊗[R']
      (R' ⊗[R] S)) ⧸ Ideal.span {idemCompl a₁}) := finite_quot_baseChange R' R'' e hfin
    have hfin_b : Module.Finite R'' ((R'' ⊗[R'] (R' ⊗[R] S)) ⧸ Ideal.span {idemCompl e₁}) :=
      (finite_away_iff (T := (R'' ⊗[R'] (R' ⊗[R] S))) R'' e₁ he₁).mp hfin₁
    have hfin_g : Module.Finite R''
        ((R'' ⊗[R'] (R' ⊗[R] S)) ⧸ Ideal.span {idemCompl (idemJoin a₁ e₁)}) :=
      finite_quot_idemJoin (T := (R'' ⊗[R'] (R' ⊗[R] S))) R'' ha₁ he₁ hfin_a hfin_b

    let F : Ideal (R'' ⊗[R'] (R' ⊗[R] S)) → Ideal (R' ⊗[R] S) := fun Q₁ =>
      Q₁.comap (Algebra.TensorProduct.includeRight (R := R') (A := R'')).toRingHom
    have hF_over : ∀ Q₁ : Ideal (R'' ⊗[R'] (R' ⊗[R] S)), Q₁.IsPrime → Q₁.LiesOver P'' →
        (F Q₁).LiesOver P := by
      intro Q₁ _ _
      haveI : Q₁.LiesOver P := Ideal.LiesOver.trans Q₁ P'' P
      constructor
      rw [Ideal.under_def, Ideal.comap_comap, AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap,
        ← Ideal.under_def]
      exact Ideal.over_def Q₁ P
    have hF_mem : ∀ Q₁ : Ideal (R'' ⊗[R'] (R' ⊗[R] S)), e ∈ F Q₁ ↔ a₁ ∈ Q₁ := fun Q₁ => Iff.rfl
    have hFQ' : F Q' = Q := hQ'Q
    have hF_inj : ∀ Q₁ Q₂ : Ideal (R'' ⊗[R'] (R' ⊗[R] S)), Q₁.IsPrime → Q₁.LiesOver P'' →
      Q₂.IsPrime → Q₂.LiesOver P'' →
        F Q₁ = F Q₂ → Q₁ = Q₂ := by
      intro Q₁ Q₂ _ _ _ _ h
      exact Ideal.eq_of_comap_eq_comap_of_bijective_residueFieldMap hκ' Q₁ Q₂ h
    have hcount₁ : {Q₁ : Ideal (R'' ⊗[R'] (R' ⊗[R] S)) | Q₁.IsPrime ∧ Q₁.LiesOver P'' ∧
        idemJoin a₁ e₁ ∈ Q₁}.ncard = n := by
      have hsub : (bad (S := S) R' P e \ {Q}).ncard = n := by
        rw [Set.ncard_diff_singleton_of_mem (show Q ∈ bad (S := S) R' P e from ⟨hQ, hQP, heQ⟩), hn]
        rfl
      rw [← hsub]
      apply Set.ncard_congr (fun Q₁ _ => F Q₁)
      · rintro Q₁ ⟨hQ₁, hQ₁P, hgQ₁⟩
        haveI := hQ₁
        haveI := hQ₁P
        have hgQ₁' := (idemJoin_mem_iff (T := (R'' ⊗[R'] (R' ⊗[R] S))) ha₁ he₁ hQ₁).mp hgQ₁
        refine ⟨⟨Ideal.comap_isPrime _ _, hF_over Q₁ hQ₁ hQ₁P, (hF_mem Q₁).mpr hgQ₁'.1⟩, ?_⟩
        intro hEq
        apply he₁Q'
        have : Q₁ = Q' := hF_inj Q₁ Q' hQ₁ hQ₁P i6 i7 (hEq.trans hFQ'.symm)
        rw [← this]
        exact hgQ₁'.2
      · rintro Q₁ Q₂ ⟨hQ₁, hQ₁P, -⟩ ⟨hQ₂, hQ₂P, -⟩ h
        exact hF_inj Q₁ Q₂ hQ₁ hQ₁P hQ₂ hQ₂P h
      · rintro Q₂ ⟨⟨hQ₂, hQ₂P, heQ₂⟩, hQ₂ne⟩
        haveI := hQ₂
        haveI := hQ₂P
        obtain ⟨⟨Q₁, hQ₁prime, hQ₁over⟩, hQ₁F⟩ :
            ∃ Q₁sub : P''.primesOver (R'' ⊗[R'] (R' ⊗[R] S)), F Q₁sub.1 = Q₂ := by
          refine ⟨(Ideal.fiberIsoOfBijectiveResidueField (S := R' ⊗[R] S) hκ').symm ⟨Q₂, hQ₂,
            hQ₂P⟩, ?_⟩
          have := Ideal.comap_fiberIsoOfBijectiveResidueField_symm (S := R' ⊗[R] S) hκ' ⟨Q₂, hQ₂,
            hQ₂P⟩
          rw [← AlgHom.toRingHom_eq_coe] at this
          exact this
        haveI : Q₁.IsPrime := hQ₁prime
        haveI : Q₁.LiesOver P'' := hQ₁over
        change F Q₁ = Q₂ at hQ₁F
        refine ⟨Q₁, ⟨hQ₁prime, hQ₁over, ?_⟩, hQ₁F⟩
        refine (idemJoin_mem_iff (T := (R'' ⊗[R'] (R' ⊗[R] S))) ha₁ he₁ hQ₁prime).mpr
          ⟨(hF_mem _).mp (by rw [hQ₁F]; exact heQ₂), ?_⟩
        by_contra hne
        have hQ₁eq : Q₁ = Q' := huniq Q₁ hQ₁prime hQ₁over hne
        apply hQ₂ne
        rw [Set.mem_singleton_iff, ← hQ₁F, hQ₁eq, hFQ']

    let ε : (R'' ⊗[R'] (R' ⊗[R] S)) ≃ₐ[R''] R'' ⊗[R] S :=
      Algebra.TensorProduct.cancelBaseChange R R' R'' R'' S
    let g : R'' ⊗[R] S := ε (idemJoin a₁ e₁)
    have hg : IsIdempotentElem g := hg₁.map ε
    have hfin_g' := finite_quot_transport ε (idemJoin a₁ e₁) hfin_g
    have hcount : (bad (S := S) R'' P'' g).ncard = n := by
      rw [← hcount₁]
      let εr : (R'' ⊗[R'] (R' ⊗[R] S)) ≃+* R'' ⊗[R] S := ε.toRingEquiv
      have hεr : ∀ a : R'', εr (algebraMap R'' _ a) = algebraMap R'' _ a := fun a => ε.commutes a
      have hεr' : ∀ a : R'', εr.symm (algebraMap R'' _ a) =
        algebraMap R'' _ a := fun a => ε.symm.commutes a
      apply Set.ncard_congr (fun Q₂ _ => Q₂.comap εr.toRingHom)
      · rintro Q₂ ⟨hQ₂, hQ₂P, hgQ₂⟩
        haveI := hQ₂
        haveI := hQ₂P
        refine ⟨Ideal.comap_isPrime _ _, ⟨?_⟩, hgQ₂⟩
        rw [Ideal.under_def, Ideal.comap_comap, show εr.toRingHom.comp (algebraMap R'' _) =
          algebraMap R'' _ from
          RingHom.ext hεr, ← Ideal.under_def]
        exact Ideal.over_def Q₂ P''
      · rintro Q₂ Q₃ - - h
        exact Ideal.comap_injective_of_surjective _ εr.surjective h
      · rintro Q₁ ⟨hQ₁, hQ₁P, hgQ₁⟩
        haveI := hQ₁
        haveI := hQ₁P
        refine ⟨Q₁.comap εr.symm.toRingHom, ⟨Ideal.comap_isPrime _ _, ⟨?_⟩, ?_⟩, ?_⟩
        · rw [Ideal.under_def, Ideal.comap_comap, show εr.symm.toRingHom.comp (algebraMap R'' _) =
            algebraMap R'' _ from RingHom.ext hεr', ← Ideal.under_def]
          exact Ideal.over_def Q₁ P''
        · show εr.symm (εr (idemJoin a₁ e₁)) ∈ Q₁
          rw [RingEquiv.symm_apply_apply]
          exact hgQ₁
        · rw [Ideal.comap_comap, RingEquiv.symm_toRingHom_comp_toRingHom, Ideal.comap_id]
    exact ih R'' P'' hκ'' g hg hfin_g' hcount

private theorem main :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R') (P : Ideal R')
      (_ : P.IsPrime) (_ : P.LiesOver p) (e : R' ⊗[R] S) (_ : IsIdempotentElem e),
      Function.Bijective (Ideal.ResidueField.mapₐ p P (Algebra.ofId _ _) (P.over_def p)) ∧
      Module.Finite R' (Localization.Away e) ∧
      ∀ P'' : Ideal (R' ⊗[R] S), P''.IsPrime → P''.LiesOver P → e ∉ P'' := by
  haveI : p.LiesOver p := ⟨by rw [Ideal.under_def]; exact (Ideal.comap_id p).symm⟩
  have hκ := bijective_mapₐ_self p
  have h0 : IsIdempotentElem (0 : R ⊗[R] S) := IsIdempotentElem.zero
  have hfin : Module.Finite R ((R ⊗[R] S) ⧸ Ideal.span {idemCompl (0 : R ⊗[R] S)}) := by
    have hsub : Subsingleton ((R ⊗[R] S) ⧸ Ideal.span {idemCompl (0 : R ⊗[R] S)}) := by
      rw [idemCompl_def, sub_zero, Ideal.span_singleton_one]
      exact Ideal.Quotient.subsingleton_iff.mpr rfl
    exact Module.Finite.of_surjective
      (0 : R →ₗ[R] (R ⊗[R] S) ⧸ Ideal.span {idemCompl (0 : R ⊗[R] S)})
      (fun x => ⟨0, Subsingleton.elim _ _⟩)
  exact claim p _ R p hκ 0 h0 hfin rfl

end Main

end EtaleFiniteAwayAux

/-- Étale-local structure of quasi-finite algebras: for `S` of finite type
and quasi-finite over `R` and a prime `p` of `R`, there is an étale
`R`-algebra `R'` with a prime `P` over `p` and `κ(p) ≅ κ(P)`, and an
idempotent `e ∈ R' ⊗[R] S` such that `(R' ⊗[R] S)ₑ` is finite over `R'`
and every prime of `R' ⊗[R] S` over `P` lies in `D(e)`. -/
theorem Algebra.exists_etale_isIdempotentElem_finite_away_forall_liesOver_notMem
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] [Algebra.QuasiFinite R S]
    (p : Ideal R) [p.IsPrime] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R') (P : Ideal R')
      (_ : P.IsPrime) (_ : P.LiesOver p) (e : R' ⊗[R] S) (_ : IsIdempotentElem e),
      Function.Bijective (Ideal.ResidueField.mapₐ p P (Algebra.ofId _ _) (P.over_def p)) ∧
      Module.Finite R' (Localization.Away e) ∧
      ∀ P'' : Ideal (R' ⊗[R] S), P''.IsPrime → P''.LiesOver P → e ∉ P'' :=
  EtaleFiniteAwayAux.main p
