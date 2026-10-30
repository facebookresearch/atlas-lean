/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsLocalRing_of_isDomain_of_module_finite_of_isAdicComplete.lean`
and
`P2M/Sol/S_IsLocalRing_of_isDomain_of_module_finite_of_isAdicComplete.lean`
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

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Idempotents
public import Mathlib.Algebra.GroupWithZero.Idempotent
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Push

/-!
# Finite domain algebras over adically complete local rings are local

A finite algebra `S` over an adically complete Noetherian local ring `R`
that is a domain is itself local. The proof: if `S` had two distinct
maximal ideals, the quotient of `S` by the image of the maximal ideal of
`R` would be Artinian with two maximal ideals, hence would carry a
nontrivial idempotent; Hensel lifting (from adic completeness) lifts
it to `S`, contradicting that a domain has no nontrivial idempotents.
-/

@[expose] public section

open IsLocalRing Polynomial
open scoped TensorProduct

namespace AdicCompleteDomainAux

section Complete

universe u

variable {R : Type u} [CommRing R] (I : Ideal R)

private theorem isAdicComplete_of_finite (M : Type u) [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M] [IsAdicComplete I R] :
    IsAdicComplete I M := by
  rw [← AdicCompletion.of_bijective_iff]
  have h1 : Function.Bijective (AdicCompletion.of I R) := AdicCompletion.of_bijective I R
  let e1 : R ≃ₗ[R] AdicCompletion I R := LinearEquiv.ofBijective _ h1
  let e2 : M ≃ₗ[R] AdicCompletion I R ⊗[R] M :=
    (TensorProduct.lid R M).symm ≪≫ₗ TensorProduct.congr e1 (LinearEquiv.refl R M)
  have he1 : e1 (1 : R) = (1 : AdicCompletion I R) := by
    change AdicCompletion.of I R 1 = 1
    have : algebraMap R (AdicCompletion I R) 1 = AdicCompletion.of I R (algebraMap R R 1) :=
      AdicCompletion.algebraMap_apply I 1
    simpa using this.symm
  have key : ∀ x : M, AdicCompletion.ofTensorProduct I M (e2 x) = AdicCompletion.of I M x := by
    intro x
    change AdicCompletion.ofTensorProduct I M
      (TensorProduct.congr e1 (LinearEquiv.refl R M) ((TensorProduct.lid R M).symm x)) = _
    rw [TensorProduct.lid_symm_apply, TensorProduct.congr_tmul, LinearEquiv.refl_apply, he1,
      AdicCompletion.ofTensorProduct_tmul, one_smul]
  have hcomp : ⇑(AdicCompletion.of I M) = ⇑(AdicCompletion.ofTensorProduct I M) ∘ ⇑e2 :=
    funext fun x => (key x).symm
  rw [hcomp]
  exact (AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian I M).comp e2.bijective

private theorem isAdicComplete_map_algebraMap (S : Type u) [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Module.Finite R S] [IsAdicComplete I R] :
    IsAdicComplete (I.map (algebraMap R S)) S :=
  (IsAdicComplete.map_algebraMap_iff I S).mpr (isAdicComplete_of_finite I S)

end Complete

section Idempotent

private theorem exists_nontrivial_isIdempotentElem {B : Type*} [CommRing B] [IsArtinianRing B]
    {m₁ m₂ : Ideal B} (h₁ : m₁.IsMaximal) (h₂ : m₂.IsMaximal) (hne : m₁ ≠ m₂) :
    ∃ e : B, IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1 := by
  classical
  let i₁ : MaximalSpectrum B := ⟨m₁, h₁⟩
  let i₂ : MaximalSpectrum B := ⟨m₂, h₂⟩
  have hii : i₁ ≠ i₂ := fun h => hne (congrArg MaximalSpectrum.asIdeal h)
  obtain ⟨ε, hε, hε0, hε1⟩ :
      ∃ ε : ∀ I : MaximalSpectrum B, B ⧸ I.asIdeal, IsIdempotentElem ε ∧ ε ≠ 0 ∧ ε ≠ 1 := by
    refine ⟨Pi.single i₁ 1, ?_, ?_, ?_⟩
    · change Pi.single i₁ 1 * Pi.single i₁ 1 = Pi.single i₁ 1
      rw [← Pi.single_mul, one_mul]
    · intro h
      have h' := congrFun h i₁
      rw [Pi.single_eq_same, Pi.zero_apply] at h'
      exact one_ne_zero h'
    · intro h
      have h' := congrFun h i₂
      rw [Pi.single_eq_of_ne (Ne.symm hii), Pi.one_apply] at h'
      exact zero_ne_one h'
  let E := IsArtinianRing.quotNilradicalEquivPi B
  have hē : IsIdempotentElem (E.symm ε) := by
    change E.symm ε * E.symm ε = E.symm ε
    rw [← map_mul, hε]
  have hē0 : E.symm ε ≠ 0 := by
    intro h
    exact hε0 (by simpa using congrArg E h)
  have hē1 : E.symm ε ≠ 1 := by
    intro h
    exact hε1 (by simpa using congrArg E h)
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (I := nilradical B) (E.symm ε)
  obtain ⟨e, he, heq⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent
    (f := Ideal.Quotient.mk (nilradical B))
    (fun y hy => by
      rw [RingHom.mem_ker, ← RingHom.mem_ker, Ideal.mk_ker] at hy
      exact hy)
    (E.symm ε) ⟨x, hx⟩ hē
  refine ⟨e, he, ?_, ?_⟩
  · intro h
    exact hē0 (by rw [← heq, h, map_zero])
  · intro h
    exact hē1 (by rw [← heq, h, map_one])

end Idempotent

end AdicCompleteDomainAux

namespace IsLocalRing

universe u

/-- A finite algebra over an adically complete Noetherian local ring that is
a domain is itself local. -/
theorem of_isDomain_of_module_finite_of_isAdicComplete
    {R S : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S] : IsLocalRing S := by
  by_contra hS
  obtain ⟨m₁, hm₁⟩ := Ideal.exists_maximal S
  obtain ⟨m₂, hm₂, hne⟩ : ∃ m₂ : Ideal S, m₂.IsMaximal ∧ m₂ ≠ m₁ := by
    by_contra h
    push Not at h
    exact hS (IsLocalRing.of_unique_max_ideal ⟨m₁, hm₁, fun I hI => h I hI⟩)
  set J : Ideal S := (IsLocalRing.maximalIdeal R).map (algebraMap R S) with hJdef
  haveI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  have hJle : ∀ (m : Ideal S), m.IsMaximal → J ≤ m := by
    intro m hm
    rw [hJdef, Ideal.map_le_iff_le_comap]
    haveI := hm
    have hcm : (m.under R).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal m
    exact (IsLocalRing.eq_maximalIdeal hcm).ge
  haveI hAC : IsAdicComplete J S :=
    AdicCompleteDomainAux.isAdicComplete_map_algebraMap (IsLocalRing.maximalIdeal R) S
  haveI : Module.Finite R (S ⧸ J) :=
    Module.Finite.of_surjective (IsScalarTower.toAlgHom R S (S ⧸ J)).toLinearMap
      Ideal.Quotient.mk_surjective
  have hJcomap : IsLocalRing.maximalIdeal R ≤ J.comap (algebraMap R S) := by
    rw [hJdef]
    exact Ideal.le_comap_map
  letI : Algebra (ResidueField R) (S ⧸ J) :=
    Ideal.Quotient.algebraQuotientOfLEComap hJcomap
  haveI : IsScalarTower R (ResidueField R) (S ⧸ J) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change Ideal.Quotient.mk J (algebraMap R S x) =
        Ideal.quotientMap J (algebraMap R S) hJcomap
          (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) x)
      rw [Ideal.quotientMap_mk]
  haveI : Module.Finite (ResidueField R) (S ⧸ J) :=
    Module.Finite.of_restrictScalars_finite R _ _
  haveI : IsArtinianRing (S ⧸ J) := isArtinian_of_tower (ResidueField R) inferInstance
  have hm₁' : (m₁.map (Ideal.Quotient.mk J)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hJle m₁ hm₁)
  have hm₂' : (m₂.map (Ideal.Quotient.mk J)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hJle m₂ hm₂)
  have hcomap : ∀ (m : Ideal S), m.IsMaximal →
      (m.map (Ideal.Quotient.mk J)).comap (Ideal.Quotient.mk J) = m := by
    intro m hm
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr (hJle m hm)]
  have hne' : m₁.map (Ideal.Quotient.mk J) ≠ m₂.map (Ideal.Quotient.mk J) := by
    intro h
    apply hne
    have := congrArg (Ideal.comap (Ideal.Quotient.mk J)) h
    rw [hcomap m₁ hm₁, hcomap m₂ hm₂] at this
    exact this.symm
  obtain ⟨ē, hē, hē0, hē1⟩ :=
    AdicCompleteDomainAux.exists_nontrivial_isIdempotentElem hm₁' hm₂' hne'
  obtain ⟨ε, hε⟩ := Ideal.Quotient.mk_surjective (I := J) ē
  have hmonic : (X ^ 2 - X : S[X]).Monic :=
    Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; exact_mod_cast Nat.one_lt_two)
  have heval : (X ^ 2 - X : S[X]).eval ε ∈ J := by
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, hε, sq, hē.eq, sub_self]
  have hderiv : IsUnit (Ideal.Quotient.mk J ((X ^ 2 - X : S[X]).derivative.eval ε)) := by
    have hd : (X ^ 2 - X : S[X]).derivative.eval ε = 2 * ε - 1 := by
      simp only [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_X,
        Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
        Polynomial.eval_X, Polynomial.eval_one]
      push_cast
      ring
    rw [hd]
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk J (2 * ε - 1)) ?_
    have hmk : Ideal.Quotient.mk J (2 * ε - 1) = 2 * ē - 1 := by
      rw [map_sub, map_mul, hε, map_ofNat, map_one]
    rw [hmk]
    have expand : (2 * ē - 1) * (2 * ē - 1) = 4 * (ē * ē) - 4 * ē + 1 := by ring
    rw [expand, hē.eq]
    ring
  obtain ⟨a, ha_root, ha_close⟩ :=
    HenselianRing.is_henselian (R := S) (I := J) (X ^ 2 - X) hmonic ε heval hderiv
  have ha : IsIdempotentElem a := by
    have h0 : a ^ 2 - a = 0 := by
      simpa [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow] using ha_root
    change a * a = a
    rw [← sq]
    exact sub_eq_zero.mp h0
  have hmk : Ideal.Quotient.mk J a = ē := by
    have h0 : Ideal.Quotient.mk J (a - ε) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha_close
    rw [map_sub, sub_eq_zero] at h0
    rw [h0, hε]
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp ha with h | h
  · exact hē0 (by rw [← hmk, h, map_zero])
  · exact hē1 (by rw [← hmk, h, map_one])

end IsLocalRing
