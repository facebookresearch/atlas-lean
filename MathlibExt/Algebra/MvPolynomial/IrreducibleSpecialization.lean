/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_
irreducible_map_algebraicClosure.lean`
and
`P2M/Sol/S_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_
irreducible_map_algebraicClosure.lean`
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

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Localization.FractionRing

import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.MvPolynomial.Localization

@[expose] public section

open MvPolynomial

namespace MvPolynomialIrreducibleSpecializationAux

universe u v w

variable {σ : Type v}

private def BddExp (σ : Type v) (d : ℕ) : Type v := {α : σ →₀ ℕ // ∀ s, α s ≤ d}

private scoped instance instFiniteBddExp [Finite σ] (d : ℕ) : Finite (BddExp σ d) := by
  classical
  refine Finite.of_injective (fun α : BddExp σ d => fun s : σ => (⟨α.1 s, Nat.lt_succ_of_le
    (α.2 s)⟩ : Fin (d + 1))) ?_
  intro α β h
  apply Subtype.ext
  ext s
  have := congrArg (fun f : σ → Fin (d + 1) => (f s : ℕ)) h
  simpa using this

private noncomputable scoped instance instFintypeBddExp [Finite σ] (d : ℕ) : Fintype (BddExp σ d) :=
  Fintype.ofFinite _

private abbrev Vars (σ : Type v) (d : ℕ) : Type v := BddExp σ d ⊕ BddExp σ d ⊕ Bool

private scoped instance instFiniteVars [Finite σ] (d : ℕ) : Finite (Vars σ d) := by
  unfold Vars; infer_instance

section System

variable {R : Type u} [CommRing R] [Finite σ] (d : ℕ)

private noncomputable def genG : MvPolynomial σ (MvPolynomial (Vars σ d) R) :=
  ∑ b : BddExp σ d, monomial b.1 (X (Sum.inl b))

private noncomputable def genH : MvPolynomial σ (MvPolynomial (Vars σ d) R) :=
  ∑ b : BddExp σ d, monomial b.1 (X (Sum.inr (Sum.inl b)))

private noncomputable def genRel (F : MvPolynomial σ R) : MvPolynomial σ (MvPolynomial (Vars σ
    d) R) :=
  genG d * genH d - map (C : R →+* MvPolynomial (Vars σ d) R) F

private noncomputable def sysIdeal (F : MvPolynomial σ R) (a b : BddExp σ d) :
    Ideal (MvPolynomial (Vars σ d) R) :=
  Ideal.span (Set.range fun m : σ →₀ ℕ => (genRel d F).coeff m) ⊔
    Ideal.span {X (Sum.inr (Sum.inr false)) * X (Sum.inl a) - 1,
      X (Sum.inr (Sum.inr true)) * X (Sum.inr (Sum.inl b)) - 1}

variable {d}

private noncomputable def readG {E : Type w} [CommRing E] (ψ : MvPolynomial (Vars σ d) R →+* E) :
    MvPolynomial σ E :=
  ∑ b : BddExp σ d, monomial b.1 (ψ (X (Sum.inl b)))

private noncomputable def readH {E : Type w} [CommRing E] (ψ : MvPolynomial (Vars σ d) R →+* E) :
    MvPolynomial σ E :=
  ∑ b : BddExp σ d, monomial b.1 (ψ (X (Sum.inr (Sum.inl b))))

private lemma map_genG {E : Type w} [CommRing E] (ψ : MvPolynomial (Vars σ d) R →+* E) :
    map ψ (genG (R := R) d) = readG ψ := by
  simp only [genG, readG, map_sum, map_monomial]

private lemma map_genH {E : Type w} [CommRing E] (ψ : MvPolynomial (Vars σ d) R →+* E) :
    map ψ (genH (R := R) d) = readH ψ := by
  simp only [genH, readH, map_sum, map_monomial]

private lemma map_genRel {E : Type w} [CommRing E] (ψ : MvPolynomial (Vars σ d) R →+* E)
    (F : MvPolynomial σ R) :
    map ψ (genRel d F) = readG ψ * readH ψ - map (ψ.comp C) F := by
  simp only [genRel, map_sub, map_mul, map_genG, map_genH, map_map]

private lemma coeff_sum_monomial {E : Type w} [CommRing E] (c : BddExp σ d → E) (a : BddExp σ d) :
    (∑ b : BddExp σ d, monomial b.1 (c b) : MvPolynomial σ E).coeff a.1 = c a := by
  classical
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    rw [ite_eq_right]
    intro h
    exact hb (Subtype.ext h)
  · intro h; exact absurd (Finset.mem_univ a) h

private lemma coeff_readG {E : Type w} [CommRing E] (ψ : MvPolynomial (Vars σ d) R →+* E)
    (a : BddExp σ d) : (readG ψ).coeff a.1 = ψ (X (Sum.inl a)) :=
  coeff_sum_monomial _ a

private lemma coeff_readH {E : Type w} [CommRing E] (ψ : MvPolynomial (Vars σ d) R →+* E)
    (b : BddExp σ d) : (readH ψ).coeff b.1 = ψ (X (Sum.inr (Sum.inl b))) :=
  coeff_sum_monomial _ b

private lemma factor_of_forall_mem_sysIdeal {E : Type w} [CommRing E]
    (ψ : MvPolynomial (Vars σ d) R →+* E) (F : MvPolynomial σ R) (a b : BddExp σ d)
    (hψ : ∀ p ∈ sysIdeal d F a b, ψ p = 0) :
    readG ψ * readH ψ = map (ψ.comp C) F ∧
      ψ (X (Sum.inr (Sum.inr false))) * (readG ψ).coeff a.1 = 1 ∧
      ψ (X (Sum.inr (Sum.inr true))) * (readH ψ).coeff b.1 = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · have h0 : map ψ (genRel d F) = 0 := by
      ext m
      rw [coeff_map, MvPolynomial.coeff_zero, Finsupp.zero_apply]
      exact hψ _ (Ideal.mem_sup_left (Ideal.subset_span ⟨m, rfl⟩))
    rw [map_genRel] at h0
    exact sub_eq_zero.mp h0
  · rw [coeff_readG]
    have := hψ _ (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_insert _ _)))
    rw [map_sub, map_one, map_mul, sub_eq_zero] at this
    exact this
  · rw [coeff_readH]
    have := hψ _ (Ideal.mem_sup_right (Ideal.subset_span
      (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
    rw [map_sub, map_one, map_mul, sub_eq_zero] at this
    exact this

private lemma eq_sum_monomial_of_bdd {E : Type w} [CommRing E] (g : MvPolynomial σ E)
    (hg : ∀ m ∈ g.support, ∀ s, m s ≤ d) :
    g = ∑ b : BddExp σ d, monomial b.1 (g.coeff b.1) := by
  classical
  ext m
  by_cases hm : ∀ s, m s ≤ d
  · rw [coeff_sum_monomial (fun b : BddExp σ d => g.coeff b.1) ⟨m, hm⟩]
  · rw [coeff_sum]
    simp only [coeff_monomial]
    rw [Finset.sum_eq_zero]
    · by_contra h
      exact hm (hg m (mem_support_iff.mpr h))
    · intro b _
      rw [ite_eq_right]
      intro h
      exact hm (h ▸ b.2)

private lemma exists_hom_of_factor {E : Type w} [CommRing E] (φ : R →+* E) (F : MvPolynomial σ R)
    (g h : MvPolynomial σ E) (hg : ∀ m ∈ g.support, ∀ s, m s ≤ d)
    (hh : ∀ m ∈ h.support, ∀ s, m s ≤ d) (hgh : g * h = map φ F) (a b : BddExp σ d)
    (t t' : E) (ht : t * g.coeff a.1 = 1) (ht' : t' * h.coeff b.1 = 1) :
    ∃ ψ : MvPolynomial (Vars σ d) R →+* E, ψ.comp C = φ ∧ ∀ p ∈ sysIdeal d F a b, ψ p = 0 := by
  classical
  let x : Vars σ d → E := Sum.elim (fun b => g.coeff b.1)
    (Sum.elim (fun b => h.coeff b.1) (fun bb => cond bb t' t))
  refine ⟨eval₂Hom φ x, eval₂Hom_comp_C φ x, ?_⟩
  have hG : readG (eval₂Hom φ x) = g := by
    rw [readG, eq_sum_monomial_of_bdd g hg]
    simp only [coe_eval₂Hom, eval₂_X, x, Sum.elim_inl]
  have hH : readH (eval₂Hom φ x) = h := by
    rw [readH, eq_sum_monomial_of_bdd h hh]
    simp only [coe_eval₂Hom, eval₂_X, x, Sum.elim_inr, Sum.elim_inl]
  intro p hp
  rw [← RingHom.mem_ker]
  revert p
  change sysIdeal d F a b ≤ RingHom.ker (eval₂Hom φ x)
  rw [sysIdeal, sup_le_iff, Ideal.span_le, Ideal.span_le]
  constructor
  · rintro _ ⟨m, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, ← coeff_map, map_genRel, hG, hH, eval₂Hom_comp_C, hgh,
      sub_self, MvPolynomial.coeff_zero, Finsupp.zero_apply]
  · intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rw [SetLike.mem_coe, RingHom.mem_ker]
    rcases hp with rfl | rfl
    · rw [map_sub, map_mul, map_one]
      simp only [coe_eval₂Hom, eval₂_X, x, Sum.elim_inr, Sum.elim_inl, cond_false]
      rw [ht, sub_self]
    · rw [map_sub, map_mul, map_one]
      simp only [coe_eval₂Hom, eval₂_X, x, Sum.elim_inr, Sum.elim_inl, cond_true]
      rw [ht', sub_self]

end System

set_option backward.isDefEq.respectTransparency false in

private theorem exists_C_mem_of_forall_exists_aeval_ne_zero
    {R : Type u} [CommRing R] [IsDomain R] {ι : Type v} [Finite ι]
    (J : Ideal (MvPolynomial ι R))
    (hJ : ∀ x : ι → AlgebraicClosure (FractionRing R), ∃ p ∈ J, aeval x p ≠ 0) :
    ∃ c : R, c ≠ 0 ∧ C c ∈ J := by
  classical
  by_contra hcon
  push Not at hcon
  letI : Algebra (MvPolynomial ι R) (MvPolynomial ι (FractionRing R)) :=
    MvPolynomial.algebraMvPolynomial
  haveI : IsLocalization ((nonZeroDivisors R).map (C : R →+* MvPolynomial ι R))
      (MvPolynomial ι (FractionRing R)) :=
    MvPolynomial.isLocalization _ _
  have hdisj : Disjoint
      (((nonZeroDivisors R).map (C : R →+* MvPolynomial ι R) : Submonoid (MvPolynomial ι R)) :
        Set (MvPolynomial ι R)) (J : Set (MvPolynomial ι R)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨c, hc, rfl⟩ hcJ
    exact hcon c (nonZeroDivisors.ne_zero hc) hcJ
  have hne : J.map (algebraMap (MvPolynomial ι R) (MvPolynomial ι (FractionRing R))) ≠ ⊤ :=
    (IsLocalization.map_algebraMap_ne_top_iff_disjoint
      ((nonZeroDivisors R).map (C : R →+* MvPolynomial ι R)) _ J).mpr hdisj
  obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal _ hne
  haveI : m.IsMaximal := hm
  have hint : ((Ideal.Quotient.mk m).comp C :
      FractionRing R →+* MvPolynomial ι (FractionRing R) ⧸ m).IsIntegral := by
    letI : Field (MvPolynomial ι (FractionRing R) ⧸ m) := Ideal.Quotient.field m
    exact MvPolynomial.comp_C_integral_of_surjective_of_isJacobsonRing _
      Ideal.Quotient.mk_surjective
  haveI : Algebra.IsIntegral (FractionRing R) (MvPolynomial ι (FractionRing R) ⧸ m) :=
    ⟨fun x => hint x⟩
  haveI : IsDomain (MvPolynomial ι (FractionRing R) ⧸ m) := Ideal.Quotient.isDomain m
  let θ : (MvPolynomial ι (FractionRing R) ⧸ m) →ₐ[FractionRing R]
      AlgebraicClosure (FractionRing R) :=
    IsAlgClosed.lift (R := FractionRing R) (M := AlgebraicClosure (FractionRing R))
      (S := MvPolynomial ι (FractionRing R) ⧸ m)
  let f : MvPolynomial ι R →+* AlgebraicClosure (FractionRing R) :=
    θ.toRingHom.comp ((Ideal.Quotient.mk m).comp
      (MvPolynomial.map (algebraMap R (FractionRing R))))
  have hfC : ∀ r : R, f (C r) = algebraMap R (AlgebraicClosure (FractionRing R)) r := by
    intro r
    simp only [f, RingHom.coe_comp, Function.comp_apply, map_C]
    rw [← MvPolynomial.algebraMap_eq, ← Ideal.Quotient.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  set x : ι → AlgebraicClosure (FractionRing R) := fun i => f (X i) with hx
  have hfx : ∀ p, aeval x p = f p := by
    intro p
    have : (aeval x : MvPolynomial ι R →ₐ[R] _).toRingHom = f := by
      apply MvPolynomial.ringHom_ext
      · intro r
        rw [hfC]
        simp
      · intro i
        simp [hx]
    exact congrArg (fun g : MvPolynomial ι R →+* _ => g p) this
  obtain ⟨p, hpJ, hp⟩ := hJ x
  apply hp
  rw [hfx]
  have hpm : MvPolynomial.map (algebraMap R (FractionRing R)) p ∈ m :=
    hJm (Ideal.mem_map_of_mem _ hpJ)
  simp only [f, RingHom.coe_comp, Function.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hpm,
    map_zero]

section Main

variable {R : Type u} [CommRing R]

private lemma exists_coeff_ne_zero_of_not_isUnit {E : Type w} [Field E] {p : MvPolynomial σ E}
    (hp0 : p ≠ 0) (hp : ¬ IsUnit p) : ∃ m : σ →₀ ℕ, m ≠ 0 ∧ p.coeff m ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  apply hp
  rw [MvPolynomial.isUnit_iff_eq_C_of_isReduced]
  refine ⟨p.coeff 0, ?_, ?_⟩
  · rw [isUnit_iff_ne_zero]
    intro h0
    apply hp0
    ext m
    by_cases hm : m = 0
    · rw [hm, h0, MvPolynomial.coeff_zero, Finsupp.zero_apply]
    · rw [hcon m hm, MvPolynomial.coeff_zero, Finsupp.zero_apply]
  · ext m
    rw [coeff_C]
    by_cases hm : m = 0
    · subst hm; simp
    · rw [ite_eq_right (Ne.symm hm), hcon m hm]

private lemma not_isUnit_of_coeff_ne_zero {E : Type w} [CommRing E] [IsReduced E] {p :
    MvPolynomial σ E}
    {m : σ →₀ ℕ} (hm : m ≠ 0) (h : p.coeff m ≠ 0) : ¬ IsUnit p := by
  classical
  intro hu
  rw [MvPolynomial.isUnit_iff_eq_C_of_isReduced] at hu
  obtain ⟨r, -, rfl⟩ := hu
  rw [coeff_C, ite_eq_right (Ne.symm hm)] at h
  exact h rfl

private lemma totalDegree_map_le {E : Type w} [CommRing E] (φ : R →+* E) (F : MvPolynomial σ R) :
    (map φ F).totalDegree ≤ F.totalDegree :=
  Finset.sup_mono (support_map_subset φ F)

private lemma bdd_of_dvd {E : Type w} [Field E] {φ : R →+* E} {F : MvPolynomial σ R}
    {g : MvPolynomial σ E} (hg : g ∣ map φ F) (hF : map φ F ≠ 0) :
    ∀ m ∈ g.support, ∀ s, m s ≤ F.totalDegree := by
  intro m hm s
  calc m s ≤ m.sum (fun _ e => e) := by
        have h__af := Finsupp.le_degree s m
        simp [Finsupp.degree] at h__af
        exact h__af
    _ ≤ g.totalDegree := le_totalDegree hm
    _ ≤ (map φ F).totalDegree := totalDegree_le_of_dvd_of_isDomain hg hF
    _ ≤ F.totalDegree := totalDegree_map_le φ F

end Main

section Final

set_option backward.isDefEq.respectTransparency false in

private theorem bertiniNoether {R : Type u} [CommRing R] [IsDomain R] [Finite σ]
    (F : MvPolynomial σ R)
    (hF : Irreducible (map (algebraMap R (AlgebraicClosure (FractionRing R))) F)) :
    ∃ c : R, c ≠ 0 ∧ ∀ (E : Type w) [Field E] (φ : R →+* E), φ c ≠ 0 →
      Irreducible (map φ F) := by
  classical

  have hnopt : ∀ a b : BddExp σ F.totalDegree, a.1 ≠ 0 → b.1 ≠ 0 →
      ∀ x : Vars σ F.totalDegree → AlgebraicClosure (FractionRing R),
        ∃ p ∈ sysIdeal F.totalDegree F a b, aeval x p ≠ 0 := by
    intro a b ha hb x
    by_contra hcon
    push Not at hcon
    obtain ⟨hgh, ht, ht'⟩ := factor_of_forall_mem_sysIdeal
      ((aeval x : MvPolynomial (Vars σ F.totalDegree) R →ₐ[R]
        AlgebraicClosure (FractionRing R)) :
        MvPolynomial (Vars σ F.totalDegree) R →+* AlgebraicClosure (FractionRing R)) F a b hcon
    have hC : ((aeval x : MvPolynomial (Vars σ F.totalDegree) R →ₐ[R]
        AlgebraicClosure (FractionRing R)) :
        MvPolynomial (Vars σ F.totalDegree) R →+* AlgebraicClosure (FractionRing R)).comp C =
        algebraMap R (AlgebraicClosure (FractionRing R)) := by
      ext r
      simp
    rw [hC] at hgh
    have hg : ¬ IsUnit (readG ((aeval x : MvPolynomial (Vars σ F.totalDegree) R →ₐ[R]
        AlgebraicClosure (FractionRing R)) :
        MvPolynomial (Vars σ F.totalDegree) R →+* AlgebraicClosure (FractionRing R))) :=
      not_isUnit_of_coeff_ne_zero ha (fun h0 => by
        rw [h0, mul_zero] at ht; exact zero_ne_one ht)
    have hh : ¬ IsUnit (readH ((aeval x : MvPolynomial (Vars σ F.totalDegree) R →ₐ[R]
        AlgebraicClosure (FractionRing R)) :
        MvPolynomial (Vars σ F.totalDegree) R →+* AlgebraicClosure (FractionRing R))) :=
      not_isUnit_of_coeff_ne_zero hb (fun h0 => by
        rw [h0, mul_zero] at ht'; exact zero_ne_one ht')
    rcases hF.isUnit_or_isUnit hgh.symm with h | h
    exacts [hg h, hh h]

  have hc : ∀ a b : BddExp σ F.totalDegree, ∃ c : R, c ≠ 0 ∧
      (a.1 ≠ 0 → b.1 ≠ 0 → C c ∈ sysIdeal F.totalDegree F a b) := by
    intro a b
    by_cases hab : a.1 ≠ 0 ∧ b.1 ≠ 0
    · obtain ⟨c, hc0, hcJ⟩ :=
        exists_C_mem_of_forall_exists_aeval_ne_zero _ (hnopt a b hab.1 hab.2)
      exact ⟨c, hc0, fun _ _ => hcJ⟩
    · exact ⟨1, one_ne_zero, fun ha hb => (hab ⟨ha, hb⟩).elim⟩
  choose cf hcf0 hcfJ using hc

  obtain ⟨m₁, hm₁, hFm₁⟩ := exists_coeff_ne_zero_of_not_isUnit hF.ne_zero hF.not_isUnit
  rw [coeff_map] at hFm₁
  have hFm₁' : F.coeff m₁ ≠ 0 := fun h => hFm₁ (by rw [h, map_zero])
  refine ⟨F.coeff m₁ * ∏ ab : BddExp σ F.totalDegree × BddExp σ F.totalDegree, cf ab.1 ab.2,
    mul_ne_zero hFm₁' (Finset.prod_ne_zero_iff.mpr fun ab _ => hcf0 ab.1 ab.2), ?_⟩
  intro E _ φ hφ
  rw [map_mul, map_prod] at hφ
  have hφ₁ : φ (F.coeff m₁) ≠ 0 := left_ne_zero_of_mul hφ
  have hφ₂ : ∀ a b : BddExp σ F.totalDegree, φ (cf a b) ≠ 0 := fun a b =>
    (Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hφ)) (a, b) (Finset.mem_univ _)
  have hφF0 : map φ F ≠ 0 := fun h =>
    hφ₁ (by rw [← coeff_map, h, MvPolynomial.coeff_zero, Finsupp.zero_apply])
  refine irreducible_iff.mpr ⟨not_isUnit_of_coeff_ne_zero hm₁ (by rwa [coeff_map]), ?_⟩
  intro g h hgh
  by_contra hu
  push Not at hu
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact hφF0 (by rw [hgh, zero_mul])
  have hh0 : h ≠ 0 := by
    rintro rfl
    exact hφF0 (by rw [hgh, mul_zero])
  obtain ⟨ma, hma, hga⟩ := exists_coeff_ne_zero_of_not_isUnit hg0 hu.1
  obtain ⟨mb, hmb, hhb⟩ := exists_coeff_ne_zero_of_not_isUnit hh0 hu.2
  have hgbd := bdd_of_dvd (Dvd.intro _ hgh.symm) hφF0
  have hhbd := bdd_of_dvd (Dvd.intro_left _ hgh.symm) hφF0
  obtain ⟨ψ, hψC, hψ⟩ := exists_hom_of_factor φ F g h hgbd hhbd hgh.symm
    ⟨ma, hgbd ma (mem_support_iff.mpr hga)⟩ ⟨mb, hhbd mb (mem_support_iff.mpr hhb)⟩
    (g.coeff ma)⁻¹ (h.coeff mb)⁻¹ (inv_mul_cancel₀ hga) (inv_mul_cancel₀ hhb)
  have := hψ _ (hcfJ ⟨ma, hgbd ma (mem_support_iff.mpr hga)⟩
    ⟨mb, hhbd mb (mem_support_iff.mpr hhb)⟩ hma hmb)
  rw [← RingHom.comp_apply, hψC] at this
  exact hφ₂ _ _ this

end Final


end MvPolynomialIrreducibleSpecializationAux

namespace MvPolynomial

universe u v w

/-- Irreducibility of a multivariate polynomial after base change to the
algebraic closure of the fraction field spreads to every field
specialization away from one nonzero element of the coefficient ring.

If `F` over a domain `R` becomes irreducible over the algebraic closure of
`FractionRing R`, then there is a nonzero `c : R` such that `F` stays
irreducible over every field `E` under every ring map `R →+* E` that does
not kill `c`. -/
public theorem exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure
    {R : Type u} [CommRing R] [IsDomain R] {σ : Type v} [Finite σ] (F : MvPolynomial σ R)
    (hF : Irreducible (MvPolynomial.map (algebraMap R (AlgebraicClosure (FractionRing R))) F)) :
    ∃ c : R, c ≠ 0 ∧ ∀ (E : Type w) [Field E] (φ : R →+* E), φ c ≠ 0 →
      Irreducible (MvPolynomial.map φ F) :=
  MvPolynomialIrreducibleSpecializationAux.bertiniNoether F hF

end MvPolynomial
