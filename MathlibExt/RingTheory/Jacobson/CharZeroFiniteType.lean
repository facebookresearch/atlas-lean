/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Algebra_FiniteType_exists_isMaximal_natCast_mem_of_ne_of_charZero.lean`
and
`P2M/Sol/S_Algebra_FiniteType_exists_isMaximal_natCast_mem_of_ne_of_charZero.lean`
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

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Data.Int.Basic
public import Mathlib.RingTheory.Ideal.Int
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Integral
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.RingTheory.Ideal.NatInt

@[expose] public section

private theorem isJacobsonRing_int : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  rcases eq_or_ne P ⊥ with rfl | hne
  · apply eq_bot_iff.mpr
    intro x hx
    rw [Submodule.mem_bot]
    by_contra hx0
    have hn1 : x.natAbs + 1 ≠ 1 := by
      intro h
      apply hx0
      have hxnat : x.natAbs = 0 := by omega
      exact Int.natAbs_eq_zero.mp hxnat
    obtain ⟨q, hqprime, hqdvd⟩ := Nat.exists_prime_and_dvd hn1
    have hqdvd' : ¬ (q : ℤ) ∣ x := by
      intro hd
      have h1 : ((q : ℤ)) ∣ (((x.natAbs : ℕ)) : ℤ) :=
        dvd_trans hd (Int.dvd_natAbs.mpr (dvd_refl x))
      have h2 : q ∣ x.natAbs := Int.natCast_dvd_natCast.mp h1
      have h3 : q ∣ 1 := (Nat.dvd_add_right h2).mp hqdvd
      have h4 : q = 1 := Nat.dvd_one.mp h3
      exact hqprime.ne_one h4
    have hxspan : x ∉ Ideal.span ({(q : ℤ)} : Set ℤ) := by
      rw [Ideal.mem_span_singleton]
      exact hqdvd'
    have hmax : (Ideal.span ({(q : ℤ)} : Set ℤ)).IsMaximal := by
      have hP : Prime ((q : ℤ)) := Nat.prime_iff_prime_int.mp hqprime
      exact PrincipalIdealRing.isMaximal_of_irreducible hP.irreducible
    have hmem : x ∈ Ideal.span ({(q : ℤ)} : Set ℤ) :=
      Submodule.mem_sInf.mp hx _ ⟨bot_le, hmax⟩
    exact hxspan hmem
  · obtain rfl | ⟨p, hp, hPeq⟩ := Ideal.isPrime_int_iff.mp hP
    · exact absurd rfl hne
    · rw [hPeq]
      have hmax : (Ideal.span ({(p : ℤ)} : Set ℤ)).IsMaximal := by
        have hP : Prime ((p : ℤ)) := Nat.prime_iff_prime_int.mp hp
        exact PrincipalIdealRing.isMaximal_of_irreducible hP.irreducible
      exact Ideal.jacobson_eq_self_of_isMaximal (I := Ideal.span {(p : ℤ)})

private theorem exists_prime_natCast_eq_zero
    {K : Type*} [Field K] [Algebra ℤ K] [Algebra.FiniteType ℤ K] :
    ∃ p : ℕ, p.Prime ∧ (p : K) = 0 := by
  haveI := isJacobsonRing_int
  haveI := finite_of_finite_type_of_isJacobsonRing ℤ K
  haveI : Algebra.IsIntegral ℤ K := Algebra.IsIntegral.of_finite ℤ K
  obtain ⟨p, hp⟩ := CharP.exists K
  haveI : CharP K p := hp
  have hp0 : p ≠ 0 := by
    rintro rfl
    haveI : CharZero K := CharP.charP_to_charZero K
    have hinj : Function.Injective (algebraMap ℤ K) := RingHom.injective_int (algebraMap ℤ K)
    exact Int.not_isField
      ((Algebra.IsIntegral.isField_iff_isField hinj).2 (Field.toIsField K))
  have hpp : p.Prime := (CharP.char_is_prime_or_zero K p).resolve_right hp0
  exact ⟨p, hpp, CharP.cast_eq_zero K p⟩

private theorem exists_prime_natCast_mem
    {B : Type*} [CommRing B] [Algebra ℤ B] [Algebra.FiniteType ℤ B]
    (𝔪 : Ideal B) (h𝔪 : 𝔪.IsMaximal) :
    ∃ p : ℕ, p.Prime ∧ (p : B) ∈ 𝔪 := by
  letI : Field (B ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  obtain ⟨p, hpp, hp⟩ := exists_prime_natCast_eq_zero (K := B ⧸ 𝔪)
  refine ⟨p, hpp, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact hp

/-- A characteristic-zero domain of finite type over `ℤ` has maximal ideals
containing two distinct prime natural numbers. -/
public theorem Algebra.FiniteType.exists_isMaximal_natCast_mem_of_ne_of_charZero
    {A : Type*} [CommRing A] [IsDomain A] [CharZero A] [Algebra ℤ A]
    [Algebra.FiniteType ℤ A] :
    ∃ (p₁ p₂ : ℕ) (𝔪₁ 𝔪₂ : Ideal A), p₁.Prime ∧ p₂.Prime ∧ p₁ ≠ p₂ ∧
      𝔪₁.IsMaximal ∧ 𝔪₂.IsMaximal ∧ (p₁ : A) ∈ 𝔪₁ ∧ (p₂ : A) ∈ 𝔪₂ := by
  classical
  haveI := isJacobsonRing_int
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := ℤ) (B := A)
  obtain ⟨𝔪₁, h𝔪₁⟩ := Ideal.exists_maximal A
  obtain ⟨p₁, hp₁, hp₁m⟩ := exists_prime_natCast_mem 𝔪₁ h𝔪₁
  have hp₁0 : (p₁ : A) ≠ 0 := by exact_mod_cast hp₁.ne_zero
  let B := Localization.Away (p₁ : A)
  haveI : IsDomain B :=
    IsLocalization.isDomain_localization
      (powers_le_nonZeroDivisors_of_noZeroDivisors hp₁0)
  obtain ⟨𝔫, h𝔫⟩ := Ideal.exists_maximal B
  obtain ⟨h𝔪₂, hp₁not⟩ :=
    (IsLocalization.isMaximal_iff_isMaximal_disjoint B (p₁ : A) 𝔫).1 h𝔫
  obtain ⟨p₂, hp₂, hp₂m⟩ := exists_prime_natCast_mem (𝔫.under A) h𝔪₂
  have hne : p₁ ≠ p₂ := by
    rintro rfl
    exact hp₁not hp₂m
  exact ⟨p₁, p₂, 𝔪₁, 𝔫.under A, hp₁, hp₂, hne, h𝔪₁, h𝔪₂, hp₁m, hp₂m⟩
